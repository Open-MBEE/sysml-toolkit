//! Context-independent semantic results tied to one resolved graph. Cached
//! lookups replay their import evidence; user graph rebuilds get fresh tables.
use crate::{eval::Dim, layered::LayeredMap, quantity::QuantityDims, rational::Rational};
use serde::{Deserialize, Serialize};
#[derive(Clone, Serialize, Deserialize)]
pub(crate) struct Proven<T> {
    pub value: T,
    pub imports: Vec<usize>,
}
pub(crate) type UnitKey = (usize, usize, String, bool);
/// A unit's dimensions and scale. `footprint` is kept when the expansion ran
/// with nothing in evaluation that could steer it except the features in
/// evaluation and the value overrides, so an evaluation in progress can tell
/// whether its own stack would have changed the expansion.
#[derive(Clone, Serialize, Deserialize)]
pub(crate) struct UnitExpansion {
    pub dims: Vec<Dim>,
    pub scale: Rational,
    pub footprint: Option<UnitFootprint>,
}
/// Every feature whose value an expansion asked for (sorted, distinct; the
/// cycle guard and the overrides are keyed by them) and the most features it
/// had in evaluation at once.
#[derive(Clone, Serialize, Deserialize)]
pub(crate) struct UnitFootprint {
    pub features: Box<[usize]>,
    pub depth: usize,
}
#[derive(Clone, Default, Serialize, Deserialize)]
pub(crate) struct SemanticMemo {
    pub types: LayeredMap<(usize, bool), Proven<Option<QuantityDims>>>,
    pub definitions: LayeredMap<(usize, bool), Proven<Option<QuantityDims>>>,
    pub units: LayeredMap<UnitKey, Proven<UnitExpansion>>,
}
impl SemanticMemo {
    pub fn valid(&self, n: usize, scopes: usize) -> bool {
        self.types
            .iter()
            .chain(self.definitions.iter())
            .all(|(&(e, _), proof)| {
                e < n
                    && proof.imports.iter().all(|&i| i < n)
                    && proof.value.as_ref().is_none_or(|v| v.valid(n))
            })
            && self.units.iter().all(|((scope, e, _, _), proof)| {
                *scope < scopes
                    && *e < n
                    && proof.imports.iter().all(|&i| i < n)
                    && proof
                        .value
                        .dims
                        .iter()
                        .all(|d| d.elem < n && d.num != 0 && d.den > 0)
                    && proof.value.footprint.as_ref().is_none_or(|f| {
                        f.features.iter().all(|&e| e < n)
                            && f.features.windows(2).all(|w| w[0] < w[1])
                    })
            })
    }
    /// Drop the results over a build's own rows, keeping the frozen library
    /// results: those read library rows only.
    pub fn clear_local(&mut self) {
        self.types.clear_local();
        self.definitions.clear_local();
        self.units.clear_local();
    }
    pub fn freeze(&mut self) {
        self.types.freeze();
        self.definitions.freeze();
        self.units.freeze();
    }
}
