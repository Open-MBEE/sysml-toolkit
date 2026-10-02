// Hazard: a body's result expression terminated like a statement. In a
// body that takes a result (calculation, constraint, case), the error is
// the `;` itself — not the operator the member parse trips over — and the
// expression stays the body's result, so the body closes and the members
// after it parse normally. A `;` after an expression that does not end its
// body, or in a body that takes no result, keeps the point-of-discovery
// message.
package P {
    part def V {
        attribute mass : Real;
        attribute limit : Real;
        assert constraint {
            mass <= limit; //~ ERROR a result expression takes no terminating `;`
        }
        assert constraint { mass > 0; } //~ ERROR a result expression takes no terminating `;`
        attribute fine : Real;
    }
    calc def F {
        in x : Real;
        x * 2;; //~ ERROR a result expression takes no terminating `;`
        //~^ ERROR a result expression takes no terminating `;`
    }
    constraint def C {
        in a : Real;
        if a > 0 ? true else false; //~ ERROR a result expression takes no terminating `;`
    }
    constraint def D {
        in a : Real;
        a > 0; //~ ERROR expected `;` or `{`, found `>`
        in b : Real;
    }
    part def W {
        attribute m : Real;
        m > 0; //~ ERROR expected `;` or `{`, found `>`
    }
    part def Fine;
}
