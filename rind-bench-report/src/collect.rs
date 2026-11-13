//! `collect`: copy one commit to each host and run `admin/bench-report run` there.

use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use crate::error::{Error, Result};
use crate::format::py_string;
use crate::paths::Paths;
use crate::tables::{COPY_FAILED, LEASE_HELD, REMOTE_DIR, host, hosts};

/// `shlex.quote` from CPython 3.12.
pub fn shell_quote(text: &str) -> String {
    if text.is_empty() {
        return "''".to_string();
    }
    if text.chars().all(is_shell_safe) {
        text.to_string()
    } else {
        format!("'{}'", text.replace('\'', "'\"'\"'"))
    }
}

fn is_shell_safe(ch: char) -> bool {
    ch.is_ascii_alphanumeric()
        || matches!(
            ch,
            '_' | '@' | '%' | '+' | '=' | ':' | ',' | '.' | '/' | '-'
        )
}

pub fn host_script(host_name: &str, work: &str, cmd: &str) -> Result<String> {
    let spec = host(host_name).ok_or_else(|| Error::new(format!("unknown host {host_name}")))?;
    let w = shell_quote(work);
    let script = format!(
        "mkdir -p {w} && src=$(mktemp -d {w}/src.XXXXXX) && tar -x -C \"$src\" || exit {COPY_FAILED}\n(cd \"$src\" && {cmd}) </dev/null >&2\ncat \"$src/result.json\"; code=$?; rm -rf \"$src\"; exit $code\n"
    );
    if spec.lease.is_none() {
        return Ok(script);
    }
    let lock = shell_quote(spec.lease.unwrap_or(""));
    Ok(format!(
        "exec 9>{lock} && {{ flock -n -E {LEASE_HELD} 9 || exit; }}\ntrap 'rm -rf {w}' EXIT\n{script}"
    ))
}

pub fn collect(paths: &Paths, commit_rev: &str, only: &[String], out: Option<&Path>) -> Result<()> {
    if std::env::var("QUEST_GATE_ADMITTED").ok().as_deref() == Some("1") {
        return Err(Error::new(
            "run collect outside quest gate: it gates each host's run itself",
        ));
    }
    let mut git = Command::new("git");
    git.args([
        "-C",
        paths.root.to_str().unwrap_or("."),
        "rev-parse",
        &format!("{commit_rev}^{{commit}}"),
    ]);
    let commit = command_output(git)?;
    let selected: Vec<&str> = if only.is_empty() {
        hosts().iter().map(|spec| spec.name).collect()
    } else {
        for name in only {
            if host(name).is_none() {
                let known = hosts()
                    .iter()
                    .map(|spec| spec.name)
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(Error::new(format!("unknown host {name}; known: {known}")));
            }
        }
        only.iter().map(String::as_str).collect()
    };
    let out_dir = match out {
        Some(path) => path.to_path_buf(),
        None => paths
            .root
            .join(".tmp/bench-report")
            .join(&commit[..commit.len().min(12)]),
    };
    fs::create_dir_all(&out_dir).map_err(|err| Error::new(err.to_string()))?;
    for name in selected {
        collect_host(paths, name, &commit, &out_dir)?;
    }
    println!("{}", out_dir.display());
    Ok(())
}

fn collect_host(paths: &Paths, name: &str, commit: &str, out_dir: &Path) -> Result<()> {
    let spec = host(name).expect("checked");
    let out = out_dir.join(format!("{name}.json"));
    let local = is_local(name);
    let work = if local {
        paths.root.join(".tmp/bench-report/host")
    } else {
        Path::new(REMOTE_DIR).to_path_buf()
    };
    let record = |status: &str, reason: &str| -> Result<()> {
        let body = format!(
            "{{\n \"schema\": 1,\n \"host\": {},\n \"commit\": {},\n \"status\": {},\n \"reason\": {}\n}}\n",
            py_string(name),
            py_string(commit),
            py_string(status),
            py_string(reason)
        );
        fs::write(&out, body).map_err(|err| Error::new(err.to_string()))?;
        eprintln!("bench-report: {name}: {status}: {reason}");
        Ok(())
    };
    let probe = on_host(name, "true", None)?;
    if probe.code != 0 {
        return record("unreachable", probe.stderr.trim());
    }
    let archive = Command::new("git")
        .args([
            "-C",
            paths.root.to_str().unwrap_or("."),
            "archive",
            "--format=tar",
            commit,
        ])
        .output()
        .map_err(|err| Error::new(err.to_string()))?;
    if !archive.status.success() {
        return Err(Error::new(
            String::from_utf8_lossy(&archive.stderr).trim().to_string(),
        ));
    }
    let quest = quest_locked(paths)?;
    let mut cmd = format!(
        "nix develop \"path:$PWD\" --command python3 admin/bench-report run --host {} --commit {} --jobs {} --target-dir ../target --out result.json",
        shell_quote(name),
        shell_quote(commit),
        spec.jobs
    );
    cmd = format!(
        "nix shell github:{}/{}/{} --command quest gate {cmd}",
        quest.0, quest.1, quest.2
    );
    if spec.lease.is_some() {
        cmd = format!("CARGO_HOME=\"$PWD/../cargo\" {cmd}");
    }
    cmd = format!("export PATH=\"$PATH:/nix/var/nix/profiles/default/bin\" && {cmd}");
    let script = host_script(name, &work.display().to_string(), &cmd)?;
    let ran = on_host(name, &script, Some(&archive.stdout))?;
    if ran.code == LEASE_HELD {
        return record("busy", "another run holds its lease");
    }
    if ran.code == COPY_FAILED {
        return record("failed", "could not copy the commit");
    }
    if ran.code != 0 {
        return record("failed", "the run wrote no result; see its output above");
    }
    fs::write(&out, &ran.stdout).map_err(|err| Error::new(err.to_string()))?;
    let status = serde_json::from_slice::<serde_json::Value>(&ran.stdout)
        .ok()
        .and_then(|value| {
            value
                .get("status")
                .and_then(|s| s.as_str())
                .map(str::to_string)
        })
        .unwrap_or_else(|| "unknown".to_string());
    eprintln!("bench-report: {name}: {status}");
    Ok(())
}

struct Ran {
    code: i32,
    stdout: Vec<u8>,
    stderr: String,
}

fn on_host(name: &str, script: &str, input: Option<&[u8]>) -> Result<Ran> {
    let mut command = if is_local(name) {
        let mut cmd = Command::new("sh");
        cmd.arg("-c").arg(script);
        cmd
    } else {
        let mut cmd = Command::new("ssh");
        for option in [
            "BatchMode=yes",
            "ConnectTimeout=10",
            "ServerAliveInterval=15",
            "ServerAliveCountMax=4",
        ] {
            cmd.arg("-o").arg(option);
        }
        let spec = host(name).expect("checked");
        cmd.arg(spec.ssh.unwrap_or(name)).arg(script);
        cmd
    };
    command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn().map_err(|err| Error::new(err.to_string()))?;
    if let Some(bytes) = input
        && let Some(mut stdin) = child.stdin.take()
    {
        stdin
            .write_all(bytes)
            .map_err(|err| Error::new(err.to_string()))?;
    }
    let output = child
        .wait_with_output()
        .map_err(|err| Error::new(err.to_string()))?;
    Ok(Ran {
        code: output.status.code().unwrap_or(1),
        stdout: output.stdout,
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}

fn is_local(name: &str) -> bool {
    hostname().split('.').next().unwrap_or("") == name
}

fn hostname() -> String {
    command_output(Command::new("hostname")).unwrap_or_default()
}

fn command_output(mut cmd: Command) -> Result<String> {
    let output = cmd.output().map_err(|err| Error::new(err.to_string()))?;
    if !output.status.success() {
        return Err(Error::new(
            String::from_utf8_lossy(&output.stderr).trim().to_string(),
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn quest_locked(paths: &Paths) -> Result<(String, String, String)> {
    let text = fs::read_to_string(paths.root.join("flake.lock"))
        .map_err(|err| Error::new(err.to_string()))?;
    let value: serde_json::Value =
        serde_json::from_str(&text).map_err(|err| Error::new(err.to_string()))?;
    let locked = &value["nodes"]["quest"]["locked"];
    Ok((
        locked["owner"].as_str().unwrap_or("").to_string(),
        locked["repo"].as_str().unwrap_or("").to_string(),
        locked["rev"].as_str().unwrap_or("").to_string(),
    ))
}
