// KerML has the same requirement in the pinned grammar.
package P {
    flow of; //~ ERROR a payload requires a type, specialization, or value
    flow of [1]; //~ ERROR expected a name
    flow of p = x; //~ ERROR a flow payload requires a type
    flow of = x; //~ ERROR a flow payload requires a type
    flow of p :> base; //~ ERROR a flow payload requires a type
}
