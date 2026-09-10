library package Template {
    doc /* Engine-neutral template core: a DOM tree with extra node kinds. Engine overlays
       specialize this package; expression sources retain an evaluator-specific datatype
       and environment. GENERATED from a template compiler's public AST declarations
       (see the .provenance.json sidecar) - do not edit; regenerate with the websysml generator.
       */
    private import ScalarValues::*;

    abstract part def AttributeLike :> Web::DOM::Attr;

    part def Attribute :> AttributeLike;

    part def ComponentDefinition {
        attribute uri : String;
        attribute export : String;
        attribute contentHash : String;
        attribute module : String;
        attribute restProps : Boolean;
        part props : PropDeclaration[0..*] ordered;
        ref part root : Root[0..1];
        part dependencies : SourceDependency[0..*] ordered;
    }

    part def ExpressionEnvironment {
        attribute implementation : String;
        attribute version : String[0..1];
        attribute module : String[0..1];
        attribute scope : String[0..1];
        attribute bindings : String[0..*] ordered;
        attribute imports : String[0..*] ordered;
        attribute capabilities : String[0..*] ordered;
        part dependencies : SourceDependency[0..*] ordered;
        part inputs : InputBinding[0..*] ordered;
    }

    part def InputBinding {
        attribute name : String;
        attribute selection : KerML[0..1];
    }

    part def PropDeclaration {
        attribute name : String;
        attribute typeText : String[0..1];
        attribute defaultValue : SourceExpression[0..1];
        attribute bindable : Boolean;
        attribute snippet : Boolean;
        attribute required : Boolean;
        attribute legacy : Boolean;
        attribute modelType : String[0..1];
    }

    part def SourceDependency {
        attribute specifier : String;
        attribute resolvedUri : String[0..1];
        attribute contentHash : String[0..1];
    }

    attribute def SourceExpression :> String;

    attribute def KerML :> SourceExpression;

    attribute def Python :> SourceExpression;

    attribute def SPARQL :> SourceExpression;

    part def SpreadAttribute :> AttributeLike {
        attribute expression : SourceExpression;
    }

    abstract part def TemplateNode :> Web::DOM::Node;

    abstract part def Block :> TemplateNode;

    part def Comment :> TemplateNode, Web::DOM::Comment;

    part def Component :> TemplateNode {
        attribute name : String;
        part props : AttributeLike[0..*] ordered;
    }

    part def EachBlock :> Block {
        attribute expression : SourceExpression;
        attribute context : SourceExpression[0..1];
        part body : Fragment;
        part fallback : Fragment[0..1];
        attribute index : String[0..1];
        attribute key : SourceExpression[0..1];
        attribute kerml : KerML[0..1];
        attribute kermlContext : KerML[0..1];
        attribute kermlKey : KerML[0..1];
    }

    part def Element :> TemplateNode, Web::DOM::Element {
        :>> attributes : AttributeLike[0..*] ordered;
    }

    part def ExpressionTag :> TemplateNode {
        attribute expression : SourceExpression;
        part embedded : TemplateNode[0..*];
        attribute kerml : KerML[0..1];
        attribute python : Python[0..1];
        attribute sparql : SPARQL[0..1];
        attribute 'view' : KerML[0..1];
        ref part environment : ExpressionEnvironment[0..1];
    }

    part def Fragment :> TemplateNode, Web::DOM::DocumentFragment;

    part def HtmlTag :> TemplateNode {
        attribute expression : SourceExpression;
        attribute kerml : KerML[0..1];
        attribute 'view' : KerML[0..1];
        ref part environment : ExpressionEnvironment[0..1];
    }

    part def IfBlock :> Block {
        attribute test : SourceExpression;
        part consequent : Fragment;
        part alternate : Fragment[0..1];
        attribute kerml : KerML[0..1];
    }

    part def Root :> TemplateNode {
        part environment : ExpressionEnvironment;
        part queryEnvironments : ExpressionEnvironment[0..*] ordered;
    }

    part def Text :> TemplateNode, Web::DOM::Text;
}
