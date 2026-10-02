// Hazard: a function body's result expression terminated like a
// statement — the `;` is the error, and the function keeps its result.
package K {
    function F {
        in x : Real;
        x * 2; //~ ERROR a result expression takes no terminating `;`
    }
    feature y = {in x; x + 1;}; //~ ERROR a result expression takes no terminating `;`
    classifier Fine;
}
