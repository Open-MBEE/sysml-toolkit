// KerML has the same requirement after the 2026-05 grammar correction.
package P {
    flow of; //~ ERROR a payload requires a type, specialization, or value
    flow of [1]; //~ ERROR expected a name
    flow of p = x; //~ ERROR a flow payload requires a type
    flow of = x; //~ ERROR a flow payload requires a type
    flow of p :> base; //~ ERROR a flow payload requires a type
}
