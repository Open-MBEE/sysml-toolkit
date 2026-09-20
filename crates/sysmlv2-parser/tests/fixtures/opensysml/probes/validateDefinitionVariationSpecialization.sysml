// Census: validateDefinitionVariationSpecialization
// Expect: error: A variation must not specialize another variation.
package P { abstract variation part def V1; abstract variation part def V2 :> V1; }
