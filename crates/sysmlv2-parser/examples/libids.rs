//! Throwaway triage: print the normative library ID table (`id\tqname`)
//! per KerML 9.1 (INTEROP.md).

use sysmlv2_parser::model::Model;

fn main() {
    let lib = std::env::args()
        .nth(1)
        .expect("usage: libids <sysml.library>");
    let mut model = Model::new();
    model
        .load_library_dir(std::path::Path::new(&lib))
        .expect("library loads");
    let map = sysmlv2_parser::json::library_name_map(&model);
    let mut rows: Vec<(String, String)> = map
        .into_iter()
        .map(|(id, segs)| (id, segs.join("::")))
        .collect();
    rows.sort();
    for (id, qn) in rows {
        println!("{id}\t{qn}");
    }
}
