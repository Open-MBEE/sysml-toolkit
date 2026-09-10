// Hazard: KerML dialect — its own reserved words and relationship
// spellings; `specializes` without a target, a SysML-only keyword used
// as a KerML member (which is legal as a *name* but not a keyword —
// `part` parses as a feature name, so misuse must involve real syntax).
package K {
    classifier A specializes ; //~ ERROR expected a name
    classifier B;
    feature f : B redefines ; //~ ERROR expected a name
    feature g : B;
}
