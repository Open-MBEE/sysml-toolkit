// Golden fixture: behavioral SysML — actions with control/loop nodes,
// accept/send/assign, states with transitions, flows, occurrences,
// events, perform/exhibit.
package Behavior {
    private import ScalarValues::*;

    attribute def Command;
    attribute def Ack;

    occurrence def Mission;
    occurrence mission1 : Mission {
        event occurrence launch;
    }

    action def Cycle {
        in load : Real;
        out result : Real;

        first start;
        then action prepare {
            in x : Real;
        }
        then decide d1;
            if load > 100.0 then heavy;
            else light;
        action heavy;
        action light;
        then fork f1;
            then a1;
            then a2;
        action a1;
        action a2;
        then join j1;
        then merge m1;
        action calc1 : Compute {
            in x = load;
        }
        assign result := load * 2.0;
        if load > 0.0 {
            action inner1;
        } else {
            action inner2;
        }
        while load < 10.0 {
            action step1;
        }
        for i : Positive in 1..4 {
            action step2;
        }
        accept cmd : Command via receiverPort;
        accept later : Command after 3.0;
        accept moment : Command at 5.0;
        accept condition : Command when 1 > 0;
        send Ack() to receiverPort;
        terminate;
        then done;
    }
    action def Compute {
        in x : Real;
    }
    port def CmdPort;
    part def Controller {
        port receiverPort : CmdPort;
        perform action run : Cycle;
        exhibit state modes : Modes;
    }

    state def Modes {
        entry action init;
        do action monitor;
        exit action shutdown;

        state off;
        then on;
        state on {
            constraint { 1 > 0 }
        }
        transition t1
            first off
            accept c : Command
            if c != null
            do send Ack() to c
            then on;
        transition on then off;
    }

    flow def FuelFlow {
        end supply : Behavior::Controller;
        end demand : Behavior::Controller;
    }
    part c1 : Controller;
    part c2 : Controller;
    flow of Command from c1.receiverPort to c2.receiverPort;
    succession flow c1.receiverPort to c2.receiverPort;

    action calcChain {
        attribute total = c1.run.result;
    }
}
