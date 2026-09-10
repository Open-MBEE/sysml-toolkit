//! Triage: unused private imports over the corpus via the Session check.
fn main() {
    let paths = sysmlv2_testkit::user_files();
    let session = sysmlv2_transform::Session::open(&paths).unwrap();
    let mut session = session
        .with_library(&sysmlv2_testkit::library_dir())
        .unwrap();
    let findings = session.unused_private_imports();
    let mut lines = Vec::new();
    for (unit, span) in &findings {
        let (_, name, text) = session.units().find(|(i, _, _)| i == unit).unwrap();
        let snippet = text[span.start as usize..(span.end as usize).min(span.start as usize + 60)]
            .replace('\n', " ");
        lines.push(format!("{name}: {snippet}"));
    }
    for l in &lines {
        println!("{l}");
    }
    println!("total: {}", lines.len());
}
