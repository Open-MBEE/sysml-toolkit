//! Quantity-dimension analysis gates (`sysmlv2_model::quantity`): type
//! dimensions from `mRef` power factors, bracket-unit dimensions
//! composed into base-quantity space, candidate lookup, and spelling.

use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

fn resolved(src: &str) -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_source("t.sysml", src);
    ResolvedModel::build(&model)
}

#[test]
fn type_and_unit_dims_agree_for_acceleration() {
    let mut r = resolved(
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute gravity = 9.8 [m/s**2];\n}\n",
    );
    let accel = r
        .resolve_qualified("ISQ::AccelerationValue")
        .expect("AccelerationValue");
    let tdims = r.quantity_dims_of_type(accel).expect("type dims");
    let g = r.resolve_qualified("G::gravity").expect("gravity");
    let v = r.evaluate(g).expect("evaluates");
    let sysmlv2_parser::eval::Value::Quantity(_, unit) = v else {
        panic!("not a quantity: {v:?}");
    };
    let udims = r.unit_quantity_dims(&unit).expect("unit dims");
    assert_eq!(tdims, udims, "L*T^-2 both ways");
    assert_eq!(udims.render(&r), "L*T^-2");
    let cands = r.quantity_type_candidates(&udims);
    assert!(
        cands.first() == Some(&accel),
        "preferred candidate should be AccelerationValue: {:?}",
        cands
            .iter()
            .map(|&c| r.element_qualified_name(c))
            .collect::<Vec<_>>()
    );
}
