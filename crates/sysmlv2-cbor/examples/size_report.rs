use std::fs;
fn main() {
    let dir = std::env::args().nth(1).unwrap();
    let (mut jm, mut jp, mut cb, mut n) = (0usize, 0usize, 0usize, 0usize);
    for entry in fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let text = fs::read_to_string(&path).unwrap();
        let v: serde_json::Value = serde_json::from_str(&text).unwrap();
        n += v.as_array().unwrap().len();
        jp += text.len();
        jm += serde_json::to_string(&v).unwrap().len();
        cb += sysmlv2_cbor::to_compact_cbor(&v).unwrap().len();
    }
    println!(
        "elements {n}  pretty {jp}  minified {jm}  cbor {cb}  ratio(min/cbor) {:.1}  bytes/elem {:.1}",
        jm as f64 / cb as f64,
        cb as f64 / n as f64
    );
}
