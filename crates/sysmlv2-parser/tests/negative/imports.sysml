// Hazard: imports require an explicit visibility in the 2025 grammar
// (ImportPrefix), and older community models write them bare.
package P {
    import ScalarValues::*; //~ ERROR an import must declare an explicit visibility
    private import Other::*;
    part def D;
    import Other::member; //~ ERROR an import must declare an explicit visibility
}
