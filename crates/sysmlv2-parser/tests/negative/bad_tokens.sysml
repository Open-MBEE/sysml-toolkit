// Hazard: characters outside the lexical alphabet and invalid string
// escapes — diagnosed once by the lexer, parser recovers at the member
// boundary.
package P {
    attribute a = 1 § 2; //~ ERROR unexpected character
    part def Fine1;
    attribute b = "bad \q escape"; //~ ERROR invalid escape sequence
    part def Fine2;
}
