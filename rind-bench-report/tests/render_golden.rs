use rind_bench_report::{Paths, render_files};

#[test]
fn render_matches_committed_files() {
    let paths = Paths::discover();
    let files = render_files(&paths).unwrap();
    for (path, content) in files {
        // A checkout that converts line endings, as Git on Windows does by
        // default, has CRLF on disk where the renderer writes LF.
        let disk = std::fs::read_to_string(&path)
            .unwrap_or_default()
            .replace("\r\n", "\n");
        if disk == content {
            continue;
        }
        let name = path.display().to_string();
        for (i, (a, b)) in disk.lines().zip(content.lines()).enumerate() {
            if a != b {
                panic!("{name} line {}\n disk: {a}\n rust: {b}", i + 1);
            }
        }
        panic!(
            "{name} length disk {} rust {} trailing disk {:?} rust {:?}",
            disk.len(),
            content.len(),
            disk.chars().rev().take(20).collect::<String>(),
            content.chars().rev().take(20).collect::<String>()
        );
    }
}
