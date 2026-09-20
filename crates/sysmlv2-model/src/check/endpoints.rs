//! Reference-property metaclasses from the KerML abstract syntax. This also
//! checks standalone relationships, which are not owned by their specific type.
use super::facts::{Facts, is};
use crate::{json::ResolvedModel, model::Model};
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(r: &ResolvedModel, model: &Model, g: &Facts) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    for (e, relation) in r.b.elements.iter().enumerate().take(r.b.explicit_len()) {
        let unit = r.b.unit_of_elem(e);
        if model.is_library_unit(unit) {
            continue;
        }
        let properties: &[(&str, &str)] = match relation.ty {
            "Specialization" => &[("specific", "Type"), ("general", "Type")],
            "Subclassification" => &[
                ("subclassifier", "Classifier"),
                ("superclassifier", "Classifier"),
            ],
            "FeatureTyping" => &[("typedFeature", "Feature"), ("type", "Type")],
            "Subsetting" => &[
                ("subsettingFeature", "Feature"),
                ("subsettedFeature", "Feature"),
            ],
            "Redefinition" => &[
                ("redefiningFeature", "Feature"),
                ("redefinedFeature", "Feature"),
            ],
            "ReferenceSubsetting" => &[
                ("subsettingFeature", "Feature"),
                ("referencedFeature", "Feature"),
            ],
            "Conjugation" => &[("conjugatedType", "Type"), ("originalType", "Type")],
            "FeatureInverting" => &[
                ("featureInverted", "Feature"),
                ("invertingFeature", "Feature"),
            ],
            "Disjoining" => &[("typeDisjoined", "Type"), ("disjoiningType", "Type")],
            "TypeFeaturing" => &[("featureOfType", "Feature"), ("featuringType", "Type")],
            _ => &[],
        };
        for &(property, expected) in properties {
            if let Some(t) = g.target(&r.b, e, property) {
                if !is(&r.b, t, expected) {
                    out.push((unit, Diagnostic::error(g.span(&r.b, e), format!("{}::{property} must refer to a {expected} [relationship-endpoint-metaclass]", relation.ty))));
                }
            }
        }
    }
    out
}
