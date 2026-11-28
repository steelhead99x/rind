//! Host smoke test: `devbench-cli catalog` or `devbench-cli run '<config json>'`.
fn main() {
    // Before any thread: this build's CPU denies, if any.
    // SAFETY: first statement of `main`, so no other thread exists yet.
    unsafe { rind_devbench::apply_build_denies() };
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("catalog") => println!("{}", rind_devbench::catalog()),
        Some("run") => {
            let cfg = a.get(2).map(|s| s.as_str()).unwrap_or("{}");
            // start() decides from the catalog listed for its settings, as the apps list it before Start: the
            // config's `env` goes in first, so the listing reads it.
            if let Ok(v) = serde_json::from_str::<serde_json::Value>(cfg) {
                for (k, val) in v["env"].as_object().into_iter().flatten() {
                    if let Some(val) = val.as_str().filter(|x| !k.is_empty() && !k.contains(['=', '\0']) && !x.contains('\0')) {
                        // SAFETY: no other thread exists yet (the catalog is listed next).
                        unsafe { std::env::set_var(k, val) };
                    }
                }
            }
            let _ = rind_devbench::catalog();
            if let Err(e) = rind_devbench::start(cfg) {
                eprintln!("devbench-cli: not started: {e}");
                std::process::exit(1);
            }
            std::thread::sleep(std::time::Duration::from_millis(200));
            while rind_devbench::status()["running"] == true {
                std::thread::sleep(std::time::Duration::from_millis(500));
            }
            let st = rind_devbench::status();
            println!("{st}");
            // No run, or a run that failed: an error for scripts.
            if st.get("run_id").is_none() || st.get("error").is_some() {
                let why = st["error"].as_str().unwrap_or("no run");
                eprintln!("devbench-cli: not run: {why}");
                std::process::exit(1);
            }
        }
        _ => eprintln!("usage: devbench-cli catalog|run CONFIG"),
    }
}
