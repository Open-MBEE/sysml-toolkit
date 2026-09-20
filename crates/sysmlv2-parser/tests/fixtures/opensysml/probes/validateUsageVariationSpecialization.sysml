// Census: validateUsageVariationSpecialization
// Expect: error: A variation must not specialize another variation.
package P { part def D; abstract variation part v1 : D; abstract variation part v2 :> v1; }
