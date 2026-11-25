//! Host smoke test: `devbench-cli catalog` or `devbench-cli run '<config json>'`.
fn main() {
    // Before any thread: this build's CPU denies, if any.
    // SAFETY: first statement of `main`, so no other thread exists yet.
    unsafe { rind_devbench::apply_build_denies() };
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("catalog") => println!("{}", rind_devbench::catalog()),
        Some("run") => {
            rind_devbench::start(a.get(2).map(|s| s.as_str()).unwrap_or("{}")).unwrap();
            std::thread::sleep(std::time::Duration::from_millis(200));
            while rind_devbench::status()["running"] == true {
                std::thread::sleep(std::time::Duration::from_millis(500));
            }
            println!("{}", rind_devbench::status());
        }
        _ => eprintln!("usage: devbench-cli catalog|run CONFIG"),
    }
}
