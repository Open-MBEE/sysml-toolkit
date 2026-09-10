// Hazard: an unterminated unrestricted name runs to end of file — one
// lexer diagnostic, no parser cascade.
package P {
    part 'no closing quote; //~ ERROR unterminated unrestricted name
}
//~ ERROR expected `}` closing package body