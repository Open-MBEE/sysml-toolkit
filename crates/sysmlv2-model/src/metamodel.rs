//! Normative declaration metadata for SDK generation. Declaration availability
//! does not imply executable semantic support or whole-model conformance.

pub use crate::operation_catalog::{OperationSpec, ParameterSpec};
pub use crate::semantic_catalog::PropertySpec;

/// A property name on a concrete or abstract metaclass and its redefinition.
#[derive(Debug)]
pub struct PropertyDescriptor {
    /// The declaration determining the shape of the requested name.
    pub requested: &'static PropertySpec,
    /// The most specific redefinition. `None` means incomparable redefinitions;
    /// callers must not arbitrarily select a branch of multiple inheritance.
    pub effective: Option<&'static PropertySpec>,
}

/// Resolve a specification property name, including inherited spellings.
pub fn property(metaclass: &str, name: &str) -> Option<PropertyDescriptor> {
    crate::semantic_catalog::property(metaclass, name).map(|(requested, effective)| {
        PropertyDescriptor {
            requested,
            effective,
        }
    })
}

/// All visible property names, in lexical order; unknown metaclasses yield none.
pub fn properties(metaclass: &str) -> impl Iterator<Item = PropertyDescriptor> {
    crate::semantic_catalog::properties(metaclass)
        .unwrap_or(&[])
        .iter()
        .map(|&(requested, effective)| PropertyDescriptor {
            requested: &crate::semantic_catalog::PROPERTIES[requested as usize],
            effective: crate::semantic_catalog::PROPERTIES.get(effective as usize),
        })
}

/// All declared operations in normative identity order. Overrides remain
/// separate declarations with explicit redefinition links. This is an inventory,
/// not an execution dispatcher; parameter metadata is preserved without guessing
/// missing result declarations or directions in the source XMI.
pub fn operations() -> &'static [OperationSpec] {
    crate::operation_catalog::OPERATIONS
}

/// Find one operation by normative declaration identity (not its ambiguous name).
pub fn operation(id: &str) -> Option<&'static OperationSpec> {
    operations()
        .binary_search_by_key(&id, |op| op.id)
        .ok()
        .map(|i| &operations()[i])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn property_metadata_preserves_identity_shape_and_ambiguity() {
        let usage = property("PartUsage", "isVariable").unwrap();
        assert_eq!(usage.requested.declaring_metaclass, "Feature");
        assert_eq!(usage.effective.unwrap().name, "mayTimeVary");
        assert!(usage.effective.unwrap().derived);
        let source = property("FeatureTyping", "source").unwrap();
        assert_eq!(source.requested.upper, None);
        assert!(source.requested.ordered);
        assert!(
            !property("Element", "owningRelationship")
                .unwrap()
                .requested
                .ordered
        );
        assert!(
            property("Namespace", "ownedMember")
                .unwrap()
                .requested
                .ordered
        );
        assert_eq!(source.effective.unwrap().upper, Some(1));
        assert!(
            property("BindingConnectorAsUsage", "type")
                .unwrap()
                .effective
                .is_none()
        );
        assert!(property("Missing", "type").is_none());
        assert_eq!(properties("Missing").count(), 0);
    }

    #[test]
    fn every_visible_property_resolves_by_its_declared_name() {
        use crate::semantic_catalog::{CLASSES, PROPERTIES};
        for &(metaclass, rows) in CLASSES {
            let names: Vec<_> = rows
                .iter()
                .map(|&(requested, _)| PROPERTIES[requested as usize].name)
                .collect();
            assert!(names.windows(2).all(|w| w[0] < w[1]), "{metaclass}");
            for (descriptor, name) in properties(metaclass).zip(names) {
                let found = property(metaclass, name).unwrap();
                assert!(std::ptr::eq(found.requested, descriptor.requested));
                assert_eq!(
                    found.effective.map(|e| e as *const _),
                    descriptor.effective.map(|e| e as *const _),
                    "{metaclass}.{name}"
                );
            }
        }
    }

    #[test]
    fn operation_inventory_preserves_declarations_without_inventing_signatures() {
        let ops = operations();
        assert_eq!(ops.len(), 103);
        let names: std::collections::HashSet<_> = ops.iter().map(|op| op.name).collect();
        assert_eq!(names.len(), 69);
        for op in ops {
            assert!(std::ptr::eq(operation(op.id).unwrap(), op));
            for id in op.redefines {
                assert!(operation(id).is_some(), "{id}");
            }
        }
        let name = ops
            .iter()
            .find(|o| o.declaring_metaclass == "Element" && o.name == "effectiveName")
            .unwrap();
        assert_eq!(name.parameters.len(), 1);
        assert_eq!(name.parameters[0].name, "");
        assert_eq!(name.parameters[0].direction, None);
        assert_eq!(name.parameters[0].target, "String");
        let compatible = ops
            .iter()
            .find(|o| o.declaring_metaclass == "Type" && o.name == "isCompatibleWith")
            .unwrap();
        assert_eq!(compatible.parameters.len(), 1);
        assert_eq!(compatible.parameters[0].name, "otherType");
        assert!(operation("effectiveName").is_none());
    }
}
