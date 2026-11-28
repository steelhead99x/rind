//! Host smoke test: `devbench-cli catalog` or `devbench-cli run '<config json>'`.
fn main() {
    // Before any thread: this build's CPU denies, if any.
    // SAFETY: first statement of `main`, so no other thread exists yet.
    unsafe { rind_devbench::apply_build_denies() };
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("catalog") => println!("{}", rind_devbench::catalog()),
        Some("run") => {
            if let Err(e) = rind_devbench::start(a.get(2).map(|s| s.as_str()).unwrap_or("{}")) {
                eprintln!("devbench-cli: not started: {e}");
                std::process::exit(1);
            }
            std::thread::sleep(std::time::Duration::from_millis(200));
            while rind_devbench::status()["running"] == true {
                std::thread::sleep(std::time::Duration::from_millis(500));
            }
            let st = rind_devbench::status();
            println!("{st}");
            // No run (a start refused once its thread listed the tests), or a run that failed: an error for
            // scripts.
            if st.get("run_id").is_none() || st.get("error").is_some() {
                let why = st["start_error"].as_str().or(st["error"].as_str()).unwrap_or("no run");
                eprintln!("devbench-cli: not run: {why}");
                std::process::exit(1);
            }
        }
        _ => eprintln!("usage: devbench-cli catalog|run CONFIG"),
    }
}
