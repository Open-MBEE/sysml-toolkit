// Hazard: C-style logical operators — KerML spells them `&`/`and` and
// `|`/`or`; `&&`/`||` are not tokens of the expression grammar (the
// GfSE HVAC model uses them).
package P {
    part def R {
        attribute a : Positive;
        attribute b : Positive;
        constraint c1 { a > b && a > 0 } //~ ERROR expected an expression, found `&`
        constraint c2 { a > b || a > 0 } //~ ERROR expected an expression, found `|`
        constraint ok { a > b and a > 0 }
    }
}
