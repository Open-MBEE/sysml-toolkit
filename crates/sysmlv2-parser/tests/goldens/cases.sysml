// Golden fixture: requirements, constraints, calculations, cases,
// views/viewpoints/renderings, variability, expressions.
package Cases {
    private import ScalarValues::*;

    calc def Efficiency {
        in power : Real;
        in loss : Real;
        return : Real = (power - loss) / power;
    }
    calc eff1 : Efficiency {
        in power = 100.0;
        in loss = 12.5;
    }

    constraint def Positive_ {
        in x : Real;
        x > 0.0
    }
    part def Cell {
        attribute voltage : Real = 3.7;
        assert constraint volts : Positive_ {
            in x = voltage;
        }
        constraint margin { voltage < 4.2 }
    }

    requirement def <'R-1'> SafeVoltage {
        doc /* Cells shall stay under the voltage ceiling. */
        subject cell : Cell;
        attribute ceiling : Real;
        require constraint { cell.voltage < ceiling }
        assume constraint { cell.voltage > 0.0 }
    }
    part battery {
        part cell1 : Cell;
        satisfy requirement svr : SafeVoltage by cell1 {
            attribute redefines ceiling = 4.2;
        }
    }

    concern def Affordability {
        doc /* unit cost stays in budget */
        stakeholder buyer : Party;
    }
    part def Party;
    requirement framed {
        frame concern afford : Affordability;
    }

    use case def Operate {
        subject sys : Cell;
        actor operator : Party;
        objective {
            doc /* keep the system within limits */
        }
        include use case charge : Charge;
    }
    use case def Charge {
        subject sys : Cell;
    }

    analysis def TradeStudy {
        subject alt : Cell;
        objective {
            doc /* pick the best cell */
        }
    }
    analysis trade1 : TradeStudy;

    verification def VoltageTest {
        subject dut : Cell;
        objective verifyReq {
            verify requirement svr2 : SafeVoltage;
        }
    }
    verification test1 : VoltageTest;

    view def Overview {
        viewpoint vp : Clarity;
        render asTree;
    }
    viewpoint def Clarity {
        frame concern afford2 : Affordability;
    }
    rendering def TreeRendering;
    rendering asTree : TreeRendering;
    view overview1 : Overview {
        expose Cases::battery::*;
        filter @Meta;
    }
    metadata def Meta;

    #Meta def CustomDef;
    #Meta customThing : CustomDef;

    use case operate1 : Operate;

    library package LocalLib {
        part def Shared;
    }
    private import LocalLib::Shared;

    view exposed {
        expose Cases::battery::cell1;
    }

    attribute flag : Boolean = true;
    attribute picked = (1, 2, 3).?{in x; x > 1};

    variation part def CellChoice :> Cell {
        variant part def LiIon :> CellChoice;
        variant part def NiMh :> CellChoice;
    }

    attribute exprZoo : Real = if 1 > 0 ? 2.0 else (3.0 as Real);
    attribute seq = (1, 2, 3)#(1);
    attribute sel = (1, 2, 3)->select {in x; x > 1};
    attribute nullish = null ?? 5;
    attribute text : String = "literal";
    attribute inf = *;
    attribute meta1 = Meta.metadata;
    attribute cons = new Complex_(1.0, 2.0);
    attribute def Complex_ {
        attribute re : Real;
        attribute im : Real;
    }
}
