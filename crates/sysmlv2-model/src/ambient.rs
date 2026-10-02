//! Ambient libraries: SysML libraries compiled into the toolkit and added
//! to every model that loads a library (`--lib`, a session library, the
//! browser bundle), so models can reference them without naming the
//! files. There is one: `TransformMeta`, the metadata vocabulary that
//! generated elements and their provenance records are annotated with.
//! Its source of truth is `local-packages/TransformMeta.sysml` at the
//! repository root (see `local-packages/README.md`); this module is its
//! build-time mirror.
//!
//! Interim mechanism: once the SysML package manager can install these
//! as published library packages, project installation provides them
//! and this module (and its `include_str!` reach outside the crate,
//! which `cargo package` cannot ship) can disappear.

use crate::model::Model;

/// `(unit name, source text)` in load order.
pub const LIBRARIES: &[(&str, &str)] = &[(
    "local-packages/TransformMeta.sysml",
    include_str!("../../../local-packages/TransformMeta.sysml"),
)];

/// Are the ambient libraries enabled? `SYSMLV2_AMBIENT=off` keeps them
/// out — to check an edited copy as a candidate without its built-in
/// copy colliding, or to run against a bare standard library.
/// Always on where there is no environment (the browser target).
#[must_use]
pub fn enabled() -> bool {
    !std::env::var_os("SYSMLV2_AMBIENT").is_some_and(|v| v == "off")
}

/// The ambient units in load order, honoring [`enabled`].
#[must_use]
pub fn units() -> Vec<(String, String)> {
    if !enabled() {
        return Vec::new();
    }
    LIBRARIES
        .iter()
        .map(|(name, text)| (name.to_string(), text.to_string()))
        .collect()
}

/// Add every ambient library to `model` as library content, after the
/// standard library. A no-op when disabled.
pub fn add_to(model: &mut Model) {
    if !enabled() {
        return;
    }
    for (name, text) in LIBRARIES {
        model.add_library_source(*name, text);
    }
}

/// A content hash over the ambient sources (and whether they are
/// enabled), mixed into library cache keys so an edited library never
/// replays a stale recording.
#[must_use]
pub fn content_hash() -> u64 {
    if !enabled() {
        return 0x6f66_6600; // "off"
    }
    // FNV-1a over names and texts.
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut feed = |bytes: &[u8]| {
        for b in bytes {
            h ^= *b as u64;
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
    };
    for (name, text) in LIBRARIES {
        feed(name.as_bytes());
        feed(&[0]);
        feed(text.as_bytes());
        feed(&[0]);
    }
    h
}

/// Mix an ambient content hash into a library-directory cache key.
#[must_use]
pub fn mix_key(dir_key: u64) -> u64 {
    dir_key.rotate_left(17).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ content_hash()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ambient_sources_parse_and_are_stable() {
        let names: Vec<&str> = LIBRARIES.iter().map(|(name, _)| *name).collect();
        assert_eq!(names, ["local-packages/TransformMeta.sysml"]);
        for (name, text) in LIBRARIES {
            assert!(name.starts_with("local-packages/"), "{name}");
            assert!(
                text.starts_with("library package "),
                "{name} is a library package"
            );
        }
        assert_eq!(content_hash(), content_hash());
        assert_ne!(mix_key(1), mix_key(2));
    }
}
