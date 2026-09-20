// Census: validateUsageVariationMembership
// Expect: error: An owned usage of a variation must be a variant.
package P { part def D; abstract variation part v : D { part a : D; } }
