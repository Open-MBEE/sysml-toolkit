// Hazard: an unterminated string literal legitimately spans lines (the
// grammar's STRING_VALUE admits raw newlines), so it runs to end of
// file: ONE lexer diagnostic at the opening quote — the parser must not
// re-report the malformed token — plus the unclosed package body.
package P {
    attribute bad = "no closing quote; //~ ERROR unterminated string literal
    part def SwallowedWithTheRest;
}
//~ ERROR expected `}` closing package body