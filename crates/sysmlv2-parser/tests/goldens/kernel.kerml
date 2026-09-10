// Golden fixture: KerML kernel — classifiers, features, connectors,
// expressions, invariants, type operators, annotations.
package Kernel {
    private import ScalarValues::*;

    abstract classifier Base;
    classifier Refined specializes Base {
        feature f1 : Real;
        member feature f2 : Real;
    }
    class Block {
        composite feature parts : Base[0..*] ordered nonunique;
        var feature mode : Base;
        end feature terminal : Base;
    }
    struct Assembly {
        feature counted : Real;
        inv positiveCount { counted >= 0.0 }
    }
    assoc Link {
        end feature a : Block;
        end feature b : Assembly;
    }
    behavior Act {
        in feature input1 : Real;
        step s1 : Act;
        succession s1 then s1;
    }
    function Calc {
        in feature x : Real;
        x * 2.0
    }
    predicate IsHot {
        in feature t : Real;
        t > 100.0
    }
    interaction Exchange specializes Link, Act;
    datatype Ratio specializes Real;

    feature block1 : Block {
        feature redefines mode;
    }
    feature assembly1 : Assembly;
    connector link1 : Link from block1 to assembly1;
    binding bind1 of block1.mode = block1.mode;
    flow of Ratio from block1.mode to assembly1.counted;

    feature chained chains block1.mode;
    feature disjoint1 : Base disjoint from block1;
    feature inverted : Base inverse of chained;
    classifier Unioned unions Base, Refined;
    classifier Intersected intersects Base, Refined;
    classifier Differenced differences Base, Refined;
    feature inContext : Base featured by block1;

    feature typed1 : Base;
    feature crossed : Base crosses block1.mode;
    feature narrowed subsets block1;
    feature multi : Base[2..*];

    metaclass Note {
        feature text : ScalarValues::String;
    }
    #Note classifier Annotated;

    comment about Base /* kernel golden fixture */

    expr lambda1 {
        in feature y : Real;
        y + 1.0
    }
}
