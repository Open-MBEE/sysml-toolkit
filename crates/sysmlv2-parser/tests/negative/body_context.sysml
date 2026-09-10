// Hazard: members that parse (superset grammar) but are illegal in
// their surrounding body context (the body-context matrix), plus duplicate names.
package P {
    part def D {
        variant part v : D; //~ ERROR variant
        entry action init; //~ ERROR entry
    }
    part def Dup;
    part def Dup; //~ ERROR already used by an earlier member
    part ok : D;
}
