// Census: validateExposeOwningNamespace
// Expect: error: expose is only allowed in a view usage body
package P { part def D; part def E { expose D::*; } }
