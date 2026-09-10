library package Svelte {
    doc /* Overlay for the component-template compiler's AST: its node kinds specialize the
       core; only engine-specific kinds are new. GENERATED from the compiler's public AST
       declarations (see the .provenance.json sidecar) - do not edit.
       */
    private import ScalarValues::*;
    public import Template::*;

    part def AttachTag :> TemplateNode {
        attribute expression : SourceExpression;
    }

    part def AwaitBlock :> Block {
        attribute expression : SourceExpression;
        attribute value : SourceExpression[0..1];
        attribute error : SourceExpression[0..1];
        part pending : Fragment[0..1];
        part 'then' : Fragment[0..1];
        part catch : Fragment[0..1];
    }

    part def ConstTag :> TemplateNode {
        attribute declaration : SourceExpression;
    }

    part def DebugTag :> TemplateNode {
        attribute identifiers : SourceExpression[0..*] ordered;
    }

    part def DeclarationTag :> TemplateNode {
        attribute declaration : SourceExpression;
    }

    abstract part def Directive :> AttributeLike;

    part def AnimateDirective :> Directive {
        attribute expression : SourceExpression[0..1];
    }

    part def BindDirective :> Directive {
        attribute expression : SourceExpression;
    }

    part def ClassDirective :> Directive {
        :>> localName = "class";
        attribute expression : SourceExpression;
    }

    part def Environment :> ExpressionEnvironment;

    attribute def JavaScript :> SourceExpression;

    part def KeyBlock :> Block {
        attribute expression : SourceExpression;
        part body : Fragment;
    }

    part def LetDirective :> Directive {
        attribute expression : SourceExpression[0..1];
    }

    part def OnDirective :> Directive {
        attribute expression : SourceExpression[0..1];
        attribute modifiers : String[0..*] ordered;
    }

    part def RegularElement :> Element;

    part def RenderTag :> TemplateNode {
        attribute expression : SourceExpression;
    }

    part def SlotElement :> Element {
        :>> localName = "slot";
    }

    part def SnippetBlock :> Block {
        attribute expression : SourceExpression;
        attribute parameters : SourceExpression[0..*] ordered;
        attribute typeParams : String[0..1];
        part body : Fragment;
    }

    part def StyleDirective :> Directive {
        part value : TemplateNode[0..*] ordered;
        attribute modifiers : String[0..*] ordered;
    }

    part def SvelteBody :> Element {
        :>> localName = "svelte:body";
    }

    part def SvelteBoundary :> Element {
        :>> localName = "svelte:boundary";
    }

    part def SvelteComponent :> Element {
        :>> localName = "svelte:component";
        attribute expression : SourceExpression;
    }

    part def SvelteDocument :> Element {
        :>> localName = "svelte:document";
    }

    part def SvelteElement :> Element {
        :>> localName = "svelte:element";
        attribute tag : SourceExpression;
    }

    part def SvelteFragment :> Element {
        :>> localName = "svelte:fragment";
    }

    part def SvelteHead :> Element {
        :>> localName = "svelte:head";
    }

    part def SvelteOptions :> Element {
        :>> localName = "svelte:options";
    }

    part def SvelteSelf :> Element {
        :>> localName = "svelte:self";
    }

    part def SvelteWindow :> Element {
        :>> localName = "svelte:window";
    }

    part def TitleElement :> Element {
        :>> localName = "title";
    }

    part def TransitionDirective :> Directive {
        attribute expression : SourceExpression[0..1];
        attribute modifiers : String[0..*] ordered;
        attribute intro : Boolean;
        attribute outro : Boolean;
    }

    attribute def TypeScript :> JavaScript;

    part def UseDirective :> Directive {
        attribute expression : SourceExpression[0..1];
    }
}
