// Hazard: a `;` where a feature value's expression belongs. The error is
// the missing expression, reported at the `;`, which still ends the
// declaration; a second `;` is a stray terminator of its own.
package K {
    feature a = ; //~ ERROR expected an expression, found `;`
    feature b := ; //~ ERROR expected an expression, found `;`
    feature c default ; //~ ERROR expected an expression, found `;`
    feature d default = ; //~ ERROR expected an expression, found `;`
    feature e default := ; //~ ERROR expected an expression, found `;`
    feature f = ;; //~ ERROR expected an expression, found `;`
    //~^ ERROR unsupported or unexpected construct at `;`
    feature g = 1 + ; //~ ERROR expected an expression, found `;`
    function F {
        in x;
        return r = ; //~ ERROR expected an expression, found `;`
    }
    classifier Fine;
}
