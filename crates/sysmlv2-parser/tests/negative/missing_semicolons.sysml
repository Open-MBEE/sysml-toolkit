// Hazard: a forgotten `;` member terminator. The parser must report the
// `;` missing at the end of the declaration's own line (not at the next
// token), keep the declaration in the tree, and parse the following
// member normally — including when the next token is the closing `}`.
// A trailing result expression (`calc c { x }`) must NOT trip the
// repair, and a same-line stray token keeps the point-of-discovery
// message.
package P {
    part def D;
    part q : D //~ ERROR missing `;` at end of declaration
    part r : D;
    calc c {
        x
    }
    attribute a = 1 //~ ERROR missing `;` at end of declaration
}
package Q //~ ERROR missing `;` after package declaration
package R {
    private import D::*
    part s : D; //~^ ERROR missing `;` after import
    requirement id '1' r1; //~ ERROR expected `;` or `{`, found `'1'`
}
