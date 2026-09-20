//! Context-independent semantic results tied to one resolved graph. Cached
//! lookups replay their import evidence; user graph rebuilds get fresh tables.
use crate::{eval::Dim, layered::LayeredMap, quantity::QuantityDims};
use serde::{Deserialize, Serialize};
#[derive(Clone, Serialize, Deserialize)]
pub(crate) struct Proven<T> {
    pub value: T,
    pub imports: Vec<usize>,
}
pub(crate) type UnitKey = (usize, usize, String, bool);
#[derive(Clone, Default, Serialize, Deserialize)]
pub(crate) struct SemanticMemo {
    pub types: LayeredMap<(usize, bool), Proven<Option<QuantityDims>>>,
    pub definitions: LayeredMap<(usize, bool), Proven<Option<QuantityDims>>>,
    pub units: LayeredMap<UnitKey, Proven<(Vec<Dim>, crate::rational::Rational)>>,
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
                        .0
                        .iter()
                        .all(|d| d.elem < n && d.num != 0 && d.den > 0)
            })
    }
    pub fn freeze(&mut self) {
        self.types.freeze();
        self.definitions.freeze();
        self.units.freeze();
    }
}
