// Hazard: expression forms — dangling operators, unclosed groups,
// negative multiplicity bounds (grammatically literal/reference only).
package P {
    attribute a = 1 + ; //~ ERROR expected an expression, found `;`
    part def Fine1;
    attribute b = (1, 2; //~ ERROR expected `)`
    part def Fine2;
    part many [-1] : Fine1; //~ ERROR expected a multiplicity bound
    part def Fine3;
}
