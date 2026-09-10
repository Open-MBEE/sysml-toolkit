// Hazard: pilot-era (pre-formal-spec) spellings that circulate in older
// models (GfSE VehicleModel): `alias X as Y`, `id '1'`, `stream`,
// `@[unit]` quantities, `{…}` sequence literals, `do ref(args)`.
package P {
    part def D;
    alias ISQ::TorqueValue as Torque; //~ ERROR expected `for`, found `::`
    //~^ ERROR expected a name, found `::`
    alias Torque2 for D;
    part p1 : D;
    attribute m = 75 @[kg]; //~ ERROR expected a name, found `[`
    //~^ ERROR expected `;` or `{`, found `[`
    attribute parts = {p1, p1}; //~ ERROR expected `;` or `{`, found `,`
    requirement id '1' r1; //~ ERROR expected `;` or `{`, found `'1'`
    state def S {
        do p1(out t); //~ ERROR expected `;` or `{`, found `(`
    }
}
