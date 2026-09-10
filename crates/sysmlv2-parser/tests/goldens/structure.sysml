// Golden fixture: structural SysML — packages, parts, attributes, items,
// ports, connections, interfaces, allocations, enumerations, metadata,
// dependencies, annotations, individuals.
package Structure {
    private import ScalarValues::*;

    part def Vehicle {
        attribute mass : Real = 1500.0;
        attribute vin : String;
        part engine : Engine;
        part wheels : Wheel[4] ordered;
        port fuelPort : FuelPort;
        ref part driver : Person;
    }
    part def Engine;
    part def Wheel {
        attribute diameter : Real default 17.0;
    }
    part def Person;
    abstract part def Ground;

    attribute def Pressure :> Real;

    item def Fuel {
        attribute octane : Positive;
    }

    port def FuelPort {
        in item fuel : Fuel;
        attribute maxFlow : Real;
    }
    part def Tank {
        port outlet : ~FuelPort;
    }

    enum def Color {
        red;
        green;
        blue;
    }

    part vehicle1 : Vehicle {
        attribute redefines mass = 1700.0;
        attribute paint : Color = Color::red;
    }

    connection def FuelLine {
        end supplier : Tank;
        end consumer : Vehicle;
    }
    part tank1 : Tank;
    connection fuelLine : FuelLine connect tank1 to vehicle1;
    connect vehicle1.engine to vehicle1.wheels;

    interface def FuelInterface {
        end supplierPort : ~FuelPort;
        end consumerPort : FuelPort;
    }
    interface fuelInterface : FuelInterface
        connect tank1.outlet to vehicle1.fuelPort;

    binding bind vehicle1.mass = vehicle1.engine;

    allocation def Realization {
        end logical : Vehicle;
        end physical : Engine;
    }
    allocation realization : Realization allocate vehicle1 to vehicle1.engine;

    individual part def MyVehicle :> Vehicle;
    individual part myCar : MyVehicle;

    metadata def Safety {
        attribute level : Integer;
    }
    #Safety part def SafePart;
    part critical : SafePart {
        @Safety {
            level = 3;
        }
    }

    dependency Uses from vehicle1 to tank1;

    alias car for vehicle1;

    comment about vehicle1 /* the primary vehicle configuration */

    doc /* Structural fixture for the per-metaclass golden gate. */

    rep inOcl language "ocl" /* self.mass > 0 */
}
