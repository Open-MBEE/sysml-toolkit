//! Complete CLI cache lifecycle, independent of the installed library/cache.
use std::{fs, process::Command};
#[test]
fn prepared_cli_reuses_repairs_and_invalidates_its_cache() {
    let root = std::env::temp_dir().join(format!("sysml-prepared-cli-{}", uuid::Uuid::new_v4()));
    let lib = root.join("library");
    let cache = root.join("cache");
    fs::create_dir_all(&lib).unwrap();
    let source = lib.join("Lib.sysml");
    let user = root.join("user.sysml");
    fs::write(&source, "package Lib { part def T; }").unwrap();
    fs::write(&user, "package U { part x : Lib::T; }").unwrap();
    let run = || {
        Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
            .args(["check", "--lib"])
            .arg(&lib)
            .arg(&user)
            .env("SYSMLV2_AMBIENT", "off")
            .env("SYSMLV2_CACHE_DIR", &cache)
            .env_remove("SYSMLV2_LIB_CACHE")
            .output()
            .unwrap()
    };
    let first = run();
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let files: Vec<_> = fs::read_dir(&cache)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    // The complete snapshot plus the resolution recording that joint
    // fallback builds replay.
    assert_eq!(files.len(), 2, "{files:?}");
    let path = files
        .iter()
        .find(|p| p.extension().unwrap() == "prepared")
        .unwrap();
    assert!(files.iter().any(|p| p.extension().unwrap() == "libcache"));
    let original = fs::read(path).unwrap();
    let modified = fs::metadata(path).unwrap().modified().unwrap();
    let warm = run();
    assert_eq!(first.stderr, warm.stderr);
    assert!(warm.status.success());
    assert_eq!(
        fs::metadata(path).unwrap().modified().unwrap(),
        modified,
        "warm load must not rewrite the snapshot"
    );
    fs::write(path, b"damaged cache").unwrap();
    let repaired = run();
    assert_eq!(first.stderr, repaired.stderr);
    assert!(repaired.status.success());
    assert!(fs::read(path).unwrap().len() > 20);
    // The filename/content identity changes even when the library name stays put.
    fs::write(&source, "package Lib { part def Renamed; }").unwrap();
    let changed = run();
    assert_ne!(first.stderr, changed.stderr);
    assert!(String::from_utf8_lossy(&changed.stderr).contains("unresolved reference"));
    assert_eq!(fs::read_dir(&cache).unwrap().count(), 4);
    assert!(!original.is_empty());
    // An unwritable cache location still analyses, and says once why every
    // run will be slow.
    let blocked = root.join("blocked");
    fs::write(&blocked, b"not a directory").unwrap();
    let unsaved = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .args(["check", "--lib"])
        .arg(&lib)
        .arg(&user)
        .env("SYSMLV2_AMBIENT", "off")
        .env("SYSMLV2_CACHE_DIR", &blocked)
        .env_remove("SYSMLV2_LIB_CACHE")
        .output()
        .unwrap();
    assert!(unsaved.status.success());
    let stderr = String::from_utf8_lossy(&unsaved.stderr);
    assert_eq!(
        stderr.matches("could not save the library cache").count(),
        1,
        "{stderr}"
    );
    assert!(stderr.contains("unresolved reference"), "{stderr}");
    fs::remove_dir_all(root).unwrap();
}
