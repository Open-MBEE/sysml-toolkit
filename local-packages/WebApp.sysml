library package WebApp {
    doc /* Framework-neutral Web application layer: entry modules that mount or hydrate a root
       component, static assets, and an optional navigation graph a router adapter supplies.
       GENERATED from the generator's application schema - do not edit; regenerate with
       the websysml generator.
       */
    private import ScalarValues::*;
    private import Template::*;

    part def Application {
        attribute entryModule : String;
        attribute startupMode : String;
        attribute mountTarget : SourceExpression[0..1];
        ref part rootComponent : ComponentDefinition[0..1];
        attribute rootComponentExpression : SourceExpression[0..1];
        attribute router : String[0..1];
        part assets : Asset[0..*] ordered;
        part navigation : NavigationGraph[0..1];
        part dependencies : SourceDependency[0..*] ordered;
    }

    part def Asset {
        attribute path : String;
        attribute kind : String[0..1];
        attribute contentHash : String[0..1];
    }

    part def NavigationGraph {
        attribute router : String;
        attribute adapter : String[0..1];
        part routes : Route[0..*] ordered;
    }

    part def Route {
        attribute path : String;
        attribute name : String[0..1];
        ref part component : ComponentDefinition[0..1];
        attribute componentExpression : SourceExpression[0..1];
        part children : Route[0..*] ordered;
    }
}
