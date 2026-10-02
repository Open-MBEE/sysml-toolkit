// Hazard: a `;` where an expression belongs — a value begun but not yet
// written (`attribute x = ;`). The bare `;` alternative a calculation
// body gives SysML's expression body is not read as an expression: the
// error is the missing expression, reported at the `;`, and the `;` still
// ends the declaration, so the members after it parse normally. A second
// `;` is a stray terminator of its own.
package P {
    attribute a = ; //~ ERROR expected an expression, found `;`
    attribute b := ; //~ ERROR expected an expression, found `;`
    attribute c default ; //~ ERROR expected an expression, found `;`
    attribute d default = ; //~ ERROR expected an expression, found `;`
    attribute e default := ; //~ ERROR expected an expression, found `;`
    attribute f = ;; //~ ERROR expected an expression, found `;`
    //~^ ERROR unsupported or unexpected construct at `;`
    attribute g = xs.; //~ ERROR expected a name, found `;`
    attribute h = xs.?; //~ ERROR expected `{`, found `;`
    attribute i = xs->F ; //~ ERROR expected a name, found `;`
    part def V {
        attribute m : Real = ; //~ ERROR expected an expression, found `;`
        attribute n : Real;
        assert constraint { m > ; } //~ ERROR expected an expression, found `;`
    }
    part v : V {
        attribute :>> n = ; //~ ERROR expected an expression, found `;`
    }
    enum def E {
        enum red = ; //~ ERROR expected an expression, found `;`
        enum green;
    }
    metadata def M { attribute level; }
    part w { @M { level = ; } } //~ ERROR expected an expression, found `;`
    calc def F {
        in x : Real;
        return r : Real = ; //~ ERROR expected an expression, found `;`
    }
    calc def G {
        in x : Real;
        ; //~ ERROR unsupported or unexpected construct at `;`
    }
    action def A {
        assign x := ; //~ ERROR expected an expression, found `;`
        action next;
    }
    part def Fine;
}
