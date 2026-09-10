// Hazard: bodies left open at end of file — one clear diagnostic per
// unclosed level at the point the parser ran out of input, no cascade.
package P {
    part def D {
        attribute x : Positive;
//~v ERROR expected `}` closing body
//~ ERROR expected `}` closing package body