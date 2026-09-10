library package SvelteKit {
    doc /* SvelteKit route/SSR overlay: the source route tree (segments, files with roles and
       execution loci, declared render policies), hooks, parameter matchers, server-boundary
       diagnostics and the deployment adapter. Effective layout chains, page policies and
       adapter requirements are constructed from route ancestry, never repeated here.
       GENERATED from the generator's application schema - do not edit; regenerate with
       the websysml generator.
       */
    private import ScalarValues::*;
    private import Template::*;

    part def BoundaryViolation {
        attribute module : String;
        attribute imported : String;
        attribute path : String[0..*] ordered;
        attribute reason : String;
    }

    part def Hook {
        attribute file : String;
        attribute locus : String;
        attribute exports : String[0..*] ordered;
    }

    part def KitProject {
        attribute routesDir : String;
        attribute adapter : String[0..1];
        part hooks : Hook[0..*] ordered;
        part matchers : Matcher[0..*] ordered;
        part routes : RouteSegment;
        part violations : BoundaryViolation[0..*] ordered;
    }

    part def Matcher {
        attribute name : String;
        attribute file : String;
    }

    part def RenderPolicy {
        attribute ssr : Boolean[0..1];
        attribute csr : Boolean[0..1];
        attribute prerender : String[0..1];
        attribute trailingSlash : String[0..1];
    }

    part def RouteFile {
        attribute name : String;
        attribute uri : String;
        attribute role : String;
        attribute locus : String;
        attribute reset : String[0..1];
        attribute exports : String[0..*] ordered;
        attribute actions : String[0..*] ordered;
        attribute methods : String[0..*] ordered;
        ref part component : ComponentDefinition[0..1];
    }

    part def RouteSegment {
        attribute segment : String;
        attribute id : String;
        attribute kind : String;
        attribute parameters : String[0..*] ordered;
        attribute matchers : String[0..*] ordered;
        attribute contentNegotiation : Boolean;
        part files : RouteFile[0..*] ordered;
        part policy : RenderPolicy[0..1];
        part children : RouteSegment[0..*] ordered;
    }
}
