library package Web {
    doc /* Web platform library. GENERATED - do not edit; regenerate with the websysml generator.
       Source: the standards' machine-readable WebIDL corpus, @webref/idl 3.83.0, @webref/elements 2.8.0.
       Packages: DOM (dom, css-shadow); HTML (html); HTML::Elements (html element metadata).
       Conventions: unsigned integers -> Natural, signed -> Integer, floating point -> Real, strings -> String;
       T? -> [0..1]; sequence/FrozenArray/ObservableArray/NodeList/HTMLCollection/NamedNodeMap -> T[0..*] ordered (wrapper dropped);
       readonly -> constant; tree-node references (Node/Attr and their collections) are derived navigation the
       toolkit constructs from ownership; mixins are abstract definitions with multiple specialization;
       operations are nested action definitions (in parameters, out result; Promise<T> -> T, recorded async;
       overloads merged); callbacks are action definitions; record<K, V> is an entry attribute definition.
       Element kinds fix localName once and specialize the element's interface. Provenance: the sidecar.
       */

    package DOM {
        private import ScalarValues::*;

        abstract part def AbstractRange {
            derived ref part startContainer : Node;
            constant attribute startOffset : Natural;
            derived ref part endContainer : Node;
            constant attribute endOffset : Natural;
            constant attribute collapsed : Boolean;
        }

        abstract part def ChildNode {
            action def before {
                in nodes : Base::Anything[0..*] ordered;
            }
            action def 'after' {
                in nodes : Base::Anything[0..*] ordered;
            }
            action def replaceWith {
                in nodes : Base::Anything[0..*] ordered;
            }
            action def remove;
        }

        part def DOMImplementation {
            action def createDocumentType {
                in name : String;
                in publicId : String;
                in systemId : String;
                out result : DocumentType;
            }
            action def createDocument {
                in namespace : String[0..1];
                in qualifiedName : String;
                in doctype : DocumentType[0..1];
                out result : XMLDocument;
            }
            action def createHTMLDocument {
                in title : String[0..1];
                out result : Document;
            }
            action def hasFeature {
                out result : Boolean;
            }
        }

        abstract part def DocumentOrShadowRoot {
            constant ref part customElementRegistry : HTML::CustomElementRegistry[0..1];
            derived ref part activeElement : Element[0..1];
        }

        part def Event {
            constant attribute type : String;
            constant ref part target : EventTarget[0..1];
            constant ref part srcElement : EventTarget[0..1];
            constant ref part currentTarget : EventTarget[0..1];
            constant attribute NONE : Natural = 0;
            constant attribute CAPTURING_PHASE : Natural = 1;
            constant attribute AT_TARGET : Natural = 2;
            constant attribute BUBBLING_PHASE : Natural = 3;
            constant attribute eventPhase : Natural;
            attribute cancelBubble : Boolean;
            constant attribute bubbles : Boolean;
            constant attribute cancelable : Boolean;
            attribute returnValue : Boolean;
            constant attribute defaultPrevented : Boolean;
            constant attribute composed : Boolean;
            constant attribute isTrusted : Boolean;
            constant attribute timeStamp : Real;
            action def composedPath {
                out result : EventTarget[0..*] ordered;
            }
            action def stopPropagation;
            action def stopImmediatePropagation;
            action def preventDefault;
            action def initEvent {
                in type : String;
                in bubbles : Boolean[0..1];
                in cancelable : Boolean[0..1];
            }
        }

        action def EventListener {
            in 'event' : Event;
        }

        part def EventTarget {
            action def addEventListener {
                in type : String;
                in callback : EventListener[0..1];
                in options : Base::Anything[0..1];
            }
            action def removeEventListener {
                in type : String;
                in callback : EventListener[0..1];
                in options : Base::Anything[0..1];
            }
            action def dispatchEvent {
                in 'event' : Event;
                out result : Boolean;
            }
        }

        attribute def GetRootNodeOptions {
            attribute composed : Boolean[0..1] default = false;
        }

        abstract part def Node :> EventTarget {
            constant attribute ELEMENT_NODE : Natural = 1;
            constant attribute ATTRIBUTE_NODE : Natural = 2;
            constant attribute TEXT_NODE : Natural = 3;
            constant attribute CDATA_SECTION_NODE : Natural = 4;
            constant attribute ENTITY_REFERENCE_NODE : Natural = 5;
            constant attribute ENTITY_NODE : Natural = 6;
            constant attribute PROCESSING_INSTRUCTION_NODE : Natural = 7;
            constant attribute COMMENT_NODE : Natural = 8;
            constant attribute DOCUMENT_NODE : Natural = 9;
            constant attribute DOCUMENT_TYPE_NODE : Natural = 10;
            constant attribute DOCUMENT_FRAGMENT_NODE : Natural = 11;
            constant attribute NOTATION_NODE : Natural = 12;
            constant attribute nodeType : Natural;
            constant attribute nodeName : String;
            constant attribute baseURI : String;
            constant attribute isConnected : Boolean;
            derived ref part ownerDocument : Document[0..1];
            derived ref part parentNode : Node[0..1];
            derived ref part parentElement : Element[0..1];
            derived ref part childNodes : Node[0..*] ordered;
            derived ref part firstChild : Node[0..1];
            derived ref part lastChild : Node[0..1];
            derived ref part previousSibling : Node[0..1];
            derived ref part nextSibling : Node[0..1];
            attribute nodeValue : String[0..1];
            attribute textContent : String[0..1];
            constant attribute DOCUMENT_POSITION_DISCONNECTED : Natural = 1;
            constant attribute DOCUMENT_POSITION_PRECEDING : Natural = 2;
            constant attribute DOCUMENT_POSITION_FOLLOWING : Natural = 4;
            constant attribute DOCUMENT_POSITION_CONTAINS : Natural = 8;
            constant attribute DOCUMENT_POSITION_CONTAINED_BY : Natural = 16;
            constant attribute DOCUMENT_POSITION_IMPLEMENTATION_SPECIFIC : Natural = 32;
            action def getRootNode {
                in options : GetRootNodeOptions[0..1];
                out result : Node;
            }
            action def hasChildNodes {
                out result : Boolean;
            }
            action def normalize;
            action def cloneNode {
                in subtree : Boolean[0..1];
                out result : Node;
            }
            action def isEqualNode {
                in otherNode : Node[0..1];
                out result : Boolean;
            }
            action def isSameNode {
                in otherNode : Node[0..1];
                out result : Boolean;
            }
            action def compareDocumentPosition {
                in other : Node;
                out result : Natural;
            }
            action def contains {
                in other : Node[0..1];
                out result : Boolean;
            }
            action def lookupPrefix {
                in namespace : String[0..1];
                out result : String[0..1];
            }
            action def lookupNamespaceURI {
                in prefix : String[0..1];
                out result : String[0..1];
            }
            action def isDefaultNamespace {
                in namespace : String[0..1];
                out result : Boolean;
            }
            action def insertBefore {
                in node : Node;
                in child : Node[0..1];
                out result : Node;
            }
            action def appendChild {
                in node : Node;
                out result : Node;
            }
            action def replaceChild {
                in node : Node;
                in child : Node;
                out result : Node;
            }
            action def removeChild {
                in child : Node;
                out result : Node;
            }
        }

        part def Attr :> Node {
            constant attribute namespaceURI : String[0..1];
            constant attribute prefix : String[0..1];
            constant attribute localName : String;
            constant attribute name : String;
            attribute value : String;
            derived ref part ownerElement : Element[0..1];
            constant attribute specified : Boolean;
        }

        part def DocumentType :> Node, ChildNode {
            constant attribute name : String;
            constant attribute publicId : String;
            constant attribute systemId : String;
        }

        action def NodeFilter {
            in node : Node;
            out result : Natural;
        }

        part def NodeIterator {
            derived ref part root : Node;
            derived ref part referenceNode : Node;
            constant attribute pointerBeforeReferenceNode : Boolean;
            constant attribute whatToShow : Natural;
            action def nextNode {
                out result : Node[0..1];
            }
            action def previousNode {
                out result : Node[0..1];
            }
            action def detach;
        }

        abstract part def NonDocumentTypeChildNode {
            derived ref part previousElementSibling : Element[0..1];
            derived ref part nextElementSibling : Element[0..1];
        }

        abstract part def CharacterData :> Node, NonDocumentTypeChildNode, ChildNode {
            attribute data : String;
            constant attribute length : Natural;
            action def substringData {
                in offset : Natural;
                in count : Natural;
                out result : String;
            }
            action def appendData {
                in data : String;
            }
            action def insertData {
                in offset : Natural;
                in data : String;
            }
            action def deleteData {
                in offset : Natural;
                in count : Natural;
            }
            action def replaceData {
                in offset : Natural;
                in count : Natural;
                in data : String;
            }
        }

        part def Comment :> CharacterData;

        abstract part def NonElementParentNode {
            action def getElementById {
                in elementId : String;
                out result : Element[0..1];
            }
        }

        abstract part def ParentNode {
            derived ref part children : Element[0..*] ordered;
            derived ref part firstElementChild : Element[0..1];
            derived ref part lastElementChild : Element[0..1];
            constant attribute childElementCount : Natural;
            action def prepend {
                in nodes : Base::Anything[0..*] ordered;
            }
            action def append {
                in nodes : Base::Anything[0..*] ordered;
            }
            action def replaceChildren {
                in nodes : Base::Anything[0..*] ordered;
            }
            action def moveBefore {
                in node : Node;
                in child : Node[0..1];
            }
            action def querySelector {
                in selectors : String;
                out result : Element[0..1];
            }
            action def querySelectorAll {
                in selectors : String;
                out result : Node[0..*] ordered;
            }
        }

        part def DocumentFragment :> Node, NonElementParentNode, ParentNode;

        part def ProcessingInstruction :> CharacterData {
            constant attribute target : String;
            action def hasAttributes {
                out result : Boolean;
            }
            action def getAttributeNames {
                out result : String[0..*] ordered;
            }
            action def getAttribute {
                in name : String;
                out result : String[0..1];
            }
            action def setAttribute {
                in name : String;
                in value : String;
            }
            action def removeAttribute {
                in name : String;
            }
            action def toggleAttribute {
                in name : String;
                in force : Boolean[0..1];
                out result : Boolean;
            }
            action def hasAttribute {
                in name : String;
                out result : Boolean;
            }
        }

        part def Range :> AbstractRange {
            derived ref part commonAncestorContainer : Node;
            constant attribute START_TO_START : Natural = 0;
            constant attribute START_TO_END : Natural = 1;
            constant attribute END_TO_END : Natural = 2;
            constant attribute END_TO_START : Natural = 3;
            action def setStart {
                in node : Node;
                in offset : Natural;
            }
            action def setEnd {
                in node : Node;
                in offset : Natural;
            }
            action def setStartBefore {
                in node : Node;
            }
            action def setStartAfter {
                in node : Node;
            }
            action def setEndBefore {
                in node : Node;
            }
            action def setEndAfter {
                in node : Node;
            }
            action def collapse {
                in toStart : Boolean[0..1];
            }
            action def selectNode {
                in node : Node;
            }
            action def selectNodeContents {
                in node : Node;
            }
            action def compareBoundaryPoints {
                in how : Natural;
                in sourceRange : Range;
                out result : Integer;
            }
            action def deleteContents;
            action def extractContents {
                out result : DocumentFragment;
            }
            action def cloneContents {
                out result : DocumentFragment;
            }
            action def insertNode {
                in node : Node;
            }
            action def surroundContents {
                in newParent : Node;
            }
            action def cloneRange {
                out result : Range;
            }
            action def detach;
            action def isPointInRange {
                in node : Node;
                in offset : Natural;
                out result : Boolean;
            }
            action def comparePoint {
                in node : Node;
                in offset : Natural;
                out result : Integer;
            }
            action def intersectsNode {
                in node : Node;
                out result : Boolean;
            }
            action def createContextualFragment {
                in string : Base::Anything;
                out result : DocumentFragment;
            }
        }

        part def ShadowRoot :> DocumentFragment, DocumentOrShadowRoot {
            constant attribute mode : ShadowRootMode;
            constant attribute delegatesFocus : Boolean;
            constant attribute serializable : Boolean;
            constant attribute slotAssignment : SlotAssignmentMode;
            constant attribute clonable : Boolean;
            derived ref part host : Element;
            attribute innerHTML : Base::Anything;
            action def setHTML {
                in html : String;
                in options : HTML::SetHTMLOptions[0..1];
            }
            action def setHTMLUnsafe {
                in html : Base::Anything;
                in options : HTML::SetHTMLUnsafeOptions[0..1];
            }
            action def getHTML {
                in options : HTML::GetHTMLOptions[0..1];
                out result : String;
            }
        }

        attribute def ShadowRootInit {
            attribute mode : ShadowRootMode;
            attribute delegatesFocus : Boolean[0..1] default = false;
            attribute serializable : Boolean[0..1] default = false;
            attribute slotAssignment : SlotAssignmentMode[0..1] default = "named";
            attribute clonable : Boolean[0..1] default = false;
            ref part customElementRegistry : HTML::CustomElementRegistry[0..1];
        }

        enum def ShadowRootMode {
            open;
            closed;
        }

        enum def SlotAssignmentMode {
            manual;
            named;
        }

        abstract part def Slottable {
            derived ref part assignedSlot : HTML::HTMLSlotElement[0..1];
        }

        part def Element :> Node, ParentNode, NonDocumentTypeChildNode, ChildNode, Slottable {
            constant attribute namespaceURI : String[0..1];
            constant attribute prefix : String[0..1];
            constant attribute localName : String;
            constant attribute tagName : String;
            attribute id : String;
            attribute className : String;
            attribute classList : String[0..*] ordered;
            attribute slot : String;
            derived ref part attributes : Attr[0..*] ordered;
            derived ref part shadowRoot : ShadowRoot[0..1];
            constant ref part customElementRegistry : HTML::CustomElementRegistry[0..1];
            attribute 'part' : String[0..*] ordered;
            attribute innerHTML : Base::Anything;
            attribute outerHTML : Base::Anything;
            action def hasAttributes {
                out result : Boolean;
            }
            action def getAttributeNames {
                out result : String[0..*] ordered;
            }
            action def getAttribute {
                in qualifiedName : String;
                out result : String[0..1];
            }
            action def getAttributeNS {
                in namespace : String[0..1];
                in localName : String;
                out result : String[0..1];
            }
            action def setAttribute {
                in qualifiedName : String;
                in value : Base::Anything;
            }
            action def setAttributeNS {
                in namespace : String[0..1];
                in qualifiedName : String;
                in value : Base::Anything;
            }
            action def removeAttribute {
                in qualifiedName : String;
            }
            action def removeAttributeNS {
                in namespace : String[0..1];
                in localName : String;
            }
            action def toggleAttribute {
                in qualifiedName : String;
                in force : Boolean[0..1];
                out result : Boolean;
            }
            action def hasAttribute {
                in qualifiedName : String;
                out result : Boolean;
            }
            action def hasAttributeNS {
                in namespace : String[0..1];
                in localName : String;
                out result : Boolean;
            }
            action def getAttributeNode {
                in qualifiedName : String;
                out result : Attr[0..1];
            }
            action def getAttributeNodeNS {
                in namespace : String[0..1];
                in localName : String;
                out result : Attr[0..1];
            }
            action def setAttributeNode {
                in attr : Attr;
                out result : Attr[0..1];
            }
            action def setAttributeNodeNS {
                in attr : Attr;
                out result : Attr[0..1];
            }
            action def removeAttributeNode {
                in attr : Attr;
                out result : Attr;
            }
            action def attachShadow {
                in init : ShadowRootInit;
                out result : ShadowRoot;
            }
            action def closest {
                in selectors : String;
                out result : Element[0..1];
            }
            action def matches {
                in selectors : String;
                out result : Boolean;
            }
            action def webkitMatchesSelector {
                in selectors : String;
                out result : Boolean;
            }
            action def getElementsByTagName {
                in qualifiedName : String;
                out result : Element[0..*] ordered;
            }
            action def getElementsByTagNameNS {
                in namespace : String[0..1];
                in localName : String;
                out result : Element[0..*] ordered;
            }
            action def getElementsByClassName {
                in classNames : String;
                out result : Element[0..*] ordered;
            }
            action def insertAdjacentElement {
                in where : String;
                in element : Element;
                out result : Element[0..1];
            }
            action def insertAdjacentText {
                in where : String;
                in data : String;
            }
            action def setHTML {
                in html : String;
                in options : HTML::SetHTMLOptions[0..1];
            }
            action def setHTMLUnsafe {
                in html : Base::Anything;
                in options : HTML::SetHTMLUnsafeOptions[0..1];
            }
            action def getHTML {
                in options : HTML::GetHTMLOptions[0..1];
                out result : String;
            }
            action def insertAdjacentHTML {
                in position : String;
                in string : Base::Anything;
            }
        }

        part def Text :> CharacterData, Slottable {
            constant attribute wholeText : String;
            action def splitText {
                in offset : Natural;
                out result : Text;
            }
        }

        part def CDATASection :> Text;

        part def TreeWalker {
            derived ref part root : Node;
            constant attribute whatToShow : Natural;
            derived ref part currentNode : Node;
            action def parentNode {
                out result : Node[0..1];
            }
            action def firstChild {
                out result : Node[0..1];
            }
            action def lastChild {
                out result : Node[0..1];
            }
            action def previousSibling {
                out result : Node[0..1];
            }
            action def nextSibling {
                out result : Node[0..1];
            }
            action def previousNode {
                out result : Node[0..1];
            }
            action def nextNode {
                out result : Node[0..1];
            }
        }

        abstract part def XPathEvaluatorBase {
            action def createExpression {
                in expression : String;
                in resolver : XPathNSResolver[0..1];
                out result : XPathExpression;
            }
            action def createNSResolver {
                in nodeResolver : Node;
                out result : Node;
            }
            action def evaluate {
                in expression : String;
                in contextNode : Node;
                in resolver : XPathNSResolver[0..1];
                in type : Natural[0..1];
                in result : XPathResult[0..1];
                out 'return' : XPathResult;
            }
        }

        part def Document :> Node, NonElementParentNode, DocumentOrShadowRoot, ParentNode, XPathEvaluatorBase, HTML::GlobalEventHandlers {
            constant ref part implementation : DOMImplementation;
            constant attribute URL : String;
            constant attribute documentURI : String;
            constant attribute compatMode : String;
            constant attribute characterSet : String;
            constant attribute charset : String;
            constant attribute inputEncoding : String;
            constant attribute contentType : String;
            derived ref part doctype : DocumentType[0..1];
            derived ref part documentElement : Element[0..1];
            ref part location : HTML::Location[0..1];
            attribute domain : String;
            constant attribute referrer : String;
            attribute cookie : String;
            constant attribute lastModified : String;
            constant attribute readyState : HTML::DocumentReadyState;
            attribute title : String;
            attribute dir : String;
            derived ref part body : HTML::HTMLElement[0..1];
            derived ref part head : HTML::HTMLHeadElement[0..1];
            derived ref part images : Element[0..*] ordered;
            derived ref part embeds : Element[0..*] ordered;
            derived ref part plugins : Element[0..*] ordered;
            derived ref part links : Element[0..*] ordered;
            derived ref part forms : Element[0..*] ordered;
            derived ref part scripts : Element[0..*] ordered;
            derived ref part currentScript : Element[0..1];
            attribute designMode : String;
            constant attribute hidden : Boolean;
            constant attribute visibilityState : HTML::DocumentVisibilityState;
            attribute fgColor : String;
            attribute linkColor : String;
            attribute vlinkColor : String;
            attribute alinkColor : String;
            attribute bgColor : String;
            derived ref part anchors : Element[0..*] ordered;
            derived ref part applets : Element[0..*] ordered;
            derived ref part 'all' : Element[0..*] ordered;
            action def getElementsByTagName {
                in qualifiedName : String;
                out result : Element[0..*] ordered;
            }
            action def getElementsByTagNameNS {
                in namespace : String[0..1];
                in localName : String;
                out result : Element[0..*] ordered;
            }
            action def getElementsByClassName {
                in classNames : String;
                out result : Element[0..*] ordered;
            }
            action def createElement {
                in localName : String;
                in options : Base::Anything[0..1];
                out result : Element;
            }
            action def createElementNS {
                in namespace : String[0..1];
                in qualifiedName : String;
                in options : Base::Anything[0..1];
                out result : Element;
            }
            action def createDocumentFragment {
                out result : DocumentFragment;
            }
            action def createTextNode {
                in data : String;
                out result : Text;
            }
            action def createCDATASection {
                in data : String;
                out result : CDATASection;
            }
            action def createComment {
                in data : String;
                out result : Comment;
            }
            action def createProcessingInstruction {
                in target : String;
                in data : String;
                out result : ProcessingInstruction;
            }
            action def importNode {
                in node : Node;
                in options : Base::Anything[0..1];
                out result : Node;
            }
            action def adoptNode {
                in node : Node;
                out result : Node;
            }
            action def createAttribute {
                in localName : String;
                out result : Attr;
            }
            action def createAttributeNS {
                in namespace : String[0..1];
                in qualifiedName : String;
                out result : Attr;
            }
            action def createEvent {
                in 'interface' : String;
                out result : Event;
            }
            action def createRange {
                out result : Range;
            }
            action def createNodeIterator {
                in root : Node;
                in whatToShow : Natural[0..1];
                in 'filter' : NodeFilter[0..1];
                out result : NodeIterator;
            }
            action def createTreeWalker {
                in root : Node;
                in whatToShow : Natural[0..1];
                in 'filter' : NodeFilter[0..1];
                out result : TreeWalker;
            }
            action def getElementsByName {
                in elementName : String;
                out result : Node[0..*] ordered;
            }
            action def close;
            action def write {
                in text : Base::Anything[0..*] ordered;
            }
            action def writeln {
                in text : Base::Anything[0..*] ordered;
            }
            action def hasFocus {
                out result : Boolean;
            }
            action def execCommand {
                in commandId : String;
                in showUI : Boolean[0..1];
                in value : String[0..1];
                out result : Boolean;
            }
            action def queryCommandEnabled {
                in commandId : String;
                out result : Boolean;
            }
            action def queryCommandIndeterm {
                in commandId : String;
                out result : Boolean;
            }
            action def queryCommandState {
                in commandId : String;
                out result : Boolean;
            }
            action def queryCommandSupported {
                in commandId : String;
                out result : Boolean;
            }
            action def queryCommandValue {
                in commandId : String;
                out result : String;
            }
            action def clear;
            action def captureEvents;
            action def releaseEvents;
        }

        part def XMLDocument :> Document;

        part def XPathExpression {
            action def evaluate {
                in contextNode : Node;
                in type : Natural[0..1];
                in result : XPathResult[0..1];
                out 'return' : XPathResult;
            }
        }

        action def XPathNSResolver {
            in prefix : String[0..1];
            out result : String[0..1];
        }

        part def XPathResult {
            constant attribute ANY_TYPE : Natural = 0;
            constant attribute NUMBER_TYPE : Natural = 1;
            constant attribute STRING_TYPE : Natural = 2;
            constant attribute BOOLEAN_TYPE : Natural = 3;
            constant attribute UNORDERED_NODE_ITERATOR_TYPE : Natural = 4;
            constant attribute ORDERED_NODE_ITERATOR_TYPE : Natural = 5;
            constant attribute UNORDERED_NODE_SNAPSHOT_TYPE : Natural = 6;
            constant attribute ORDERED_NODE_SNAPSHOT_TYPE : Natural = 7;
            constant attribute ANY_UNORDERED_NODE_TYPE : Natural = 8;
            constant attribute FIRST_ORDERED_NODE_TYPE : Natural = 9;
            constant attribute resultType : Natural;
            constant attribute numberValue : Real;
            constant attribute stringValue : String;
            constant attribute booleanValue : Boolean;
            derived ref part singleNodeValue : Node[0..1];
            constant attribute invalidIteratorState : Boolean;
            constant attribute snapshotLength : Natural;
            action def iterateNext {
                out result : Node[0..1];
            }
            action def snapshotItem {
                in index : Natural;
                out result : Node[0..1];
            }
        }
    }

    package HTML {
        private import ScalarValues::*;
        private import DOM::*;

        attribute def AssignedNodesOptions {
            attribute flatten : Boolean[0..1] default = false;
        }

        part def AudioTrack {
            constant attribute id : String;
            constant attribute kind : String;
            constant attribute label : String;
            constant attribute 'language' : String;
            attribute enabled : Boolean;
        }

        part def AudioTrackList :> EventTarget {
            constant attribute length : Natural;
            action def getTrackById {
                in id : String;
                out result : AudioTrack[0..1];
            }
        }

        action def BlobCallback;

        enum def CanPlayTypeResult {
            maybe;
            probably;
        }

        action def CustomElementConstructor {
            out result : HTMLElement;
        }

        part def CustomElementRegistry {
            action def define {
                in name : String;
                in constructor : CustomElementConstructor;
                in options : ElementDefinitionOptions[0..1];
            }
            action def getName {
                in constructor : CustomElementConstructor;
                out result : String[0..1];
            }
            action def whenDefined {
                in name : String;
                out result : CustomElementConstructor;
            }
            action def upgrade {
                in root : Node;
            }
            action def initialize {
                in root : Node;
            }
        }

        part def CustomStateSet;

        part def DOMStringList {
            constant attribute length : Natural;
            action def 'item' {
                in index : Natural;
                out result : String[0..1];
            }
            action def contains {
                in string : String;
                out result : Boolean;
            }
        }

        enum def DocumentReadyState {
            loading;
            interactive;
            complete;
        }

        enum def DocumentVisibilityState {
            visible;
            hidden;
        }

        abstract part def ElementContentEditable {
            attribute contentEditable : String;
            attribute enterKeyHint : String;
            constant attribute isContentEditable : Boolean;
            attribute inputMode : String;
        }

        attribute def ElementDefinitionOptions {
            attribute extends : String[0..1];
        }

        part def ElementInternals {
            derived ref part shadowRoot : ShadowRoot[0..1];
            derived ref part form : HTMLFormElement[0..1];
            constant attribute willValidate : Boolean;
            constant ref part validity : ValidityState;
            constant attribute validationMessage : String;
            derived ref part labels : Node[0..*] ordered;
            constant ref part states : CustomStateSet;
            action def setFormValue {
                in value : Base::Anything[0..1];
                in 'state' : Base::Anything[0..1];
            }
            action def setValidity {
                in flags : ValidityStateFlags[0..1];
                in 'message' : String[0..1];
                in anchor : HTMLElement[0..1];
            }
            action def checkValidity {
                out result : Boolean;
            }
            action def reportValidity {
                out result : Boolean;
            }
        }

        attribute def FocusOptions {
            attribute preventScroll : Boolean[0..1] default = false;
            attribute focusVisible : Boolean[0..1];
        }

        attribute def GetHTMLOptions {
            attribute serializableShadowRoots : Boolean[0..1] default = false;
            ref part shadowRoots : ShadowRoot[0..*] ordered;
        }

        abstract part def GlobalEventHandlers;

        abstract part def HTMLHyperlinkElementUtils {
            attribute href : String;
            attribute target : String;
        }

        abstract part def HTMLOrSVGOrMathMLElement {
            attribute nonce : String;
            attribute autofocus : Boolean;
            attribute tabIndex : Integer;
            action def focus {
                in options : FocusOptions[0..1];
            }
            action def blur;
        }

        part def HTMLElement :> Element, GlobalEventHandlers, ElementContentEditable, HTMLOrSVGOrMathMLElement {
            attribute title : String;
            attribute lang : String;
            attribute translate : Boolean;
            attribute dir : String;
            attribute hidden : Base::Anything[0..1];
            attribute inert : Boolean;
            attribute accessKey : String;
            constant attribute accessKeyLabel : String;
            attribute draggable : Boolean;
            attribute spellcheck : Boolean;
            attribute writingSuggestions : String;
            attribute autocapitalize : String;
            attribute autocorrect : Boolean;
            attribute innerText : String;
            attribute outerText : String;
            attribute popover : String[0..1];
            attribute headingOffset : Natural;
            attribute headingReset : Boolean;
            action def click;
            action def attachInternals {
                out result : ElementInternals;
            }
            action def showPopover {
                in options : ShowPopoverOptions[0..1];
            }
            action def hidePopover;
            action def togglePopover {
                in options : Base::Anything[0..1];
                out result : Boolean;
            }
        }

        part def HTMLBRElement :> HTMLElement {
            attribute clear : String;
        }

        part def HTMLBaseElement :> HTMLElement {
            attribute href : String;
            attribute target : String;
        }

        part def HTMLCanvasElement :> HTMLElement {
            attribute width : Natural;
            attribute height : Natural;
            action def getContext {
                in contextId : String;
                in options : Base::Anything[0..1];
                out result : Base::Anything[0..1];
            }
            action def toDataURL {
                in type : String[0..1];
                in quality : Base::Anything[0..1];
                out result : String;
            }
            action def toBlob {
                in callback : BlobCallback;
                in type : String[0..1];
                in quality : Base::Anything[0..1];
            }
            action def transferControlToOffscreen {
                out result : OffscreenCanvas;
            }
        }

        part def HTMLDListElement :> HTMLElement {
            attribute compact : Boolean;
        }

        part def HTMLDataElement :> HTMLElement {
            attribute value : String;
        }

        part def HTMLDataListElement :> HTMLElement {
            derived ref part options : Element[0..*] ordered;
        }

        part def HTMLDetailsElement :> HTMLElement {
            attribute name : String;
            attribute open : Boolean;
        }

        part def HTMLDialogElement :> HTMLElement {
            attribute open : Boolean;
            attribute returnValue : String;
            attribute closedBy : String;
            action def show;
            action def showModal;
            action def close {
                in returnValue : String[0..1];
            }
            action def requestClose {
                in returnValue : String[0..1];
            }
        }

        part def HTMLDirectoryElement :> HTMLElement {
            attribute compact : Boolean;
        }

        part def HTMLDivElement :> HTMLElement {
            attribute align : String;
        }

        part def HTMLEmbedElement :> HTMLElement {
            attribute src : String;
            attribute type : String;
            attribute width : String;
            attribute height : String;
            attribute align : String;
            attribute name : String;
            action def getSVGDocument {
                out result : Document[0..1];
            }
        }

        part def HTMLFieldSetElement :> HTMLElement {
            attribute disabled : Boolean;
            derived ref part form : HTMLFormElement[0..1];
            attribute name : String;
            constant attribute type : String;
            derived ref part elements : Element[0..*] ordered;
            constant attribute willValidate : Boolean;
            constant ref part validity : ValidityState;
            constant attribute validationMessage : String;
            action def checkValidity {
                out result : Boolean;
            }
            action def reportValidity {
                out result : Boolean;
            }
            action def setCustomValidity {
                in error : String;
            }
        }

        part def HTMLFontElement :> HTMLElement {
            attribute color : String;
            attribute face : String;
            attribute size : String;
        }

        part def HTMLFormElement :> HTMLElement {
            attribute acceptCharset : String;
            attribute 'action' : String;
            attribute autocomplete : String;
            attribute enctype : String;
            attribute encoding : String;
            attribute method : String;
            attribute name : String;
            attribute noValidate : Boolean;
            attribute target : String;
            attribute rel : String;
            attribute relList : String[0..*] ordered;
            derived ref part elements : Element[0..*] ordered;
            constant attribute length : Natural;
            action def submit;
            action def requestSubmit {
                in submitter : HTMLElement[0..1];
            }
            action def reset;
            action def checkValidity {
                out result : Boolean;
            }
            action def reportValidity {
                out result : Boolean;
            }
        }

        part def HTMLFrameElement :> HTMLElement {
            attribute name : String;
            attribute scrolling : String;
            attribute src : String;
            attribute frameBorder : String;
            attribute longDesc : String;
            attribute noResize : Boolean;
            derived ref part contentDocument : Document[0..1];
            attribute marginHeight : String;
            attribute marginWidth : String;
        }

        part def HTMLHRElement :> HTMLElement {
            attribute align : String;
            attribute color : String;
            attribute noShade : Boolean;
            attribute size : String;
            attribute width : String;
        }

        part def HTMLHeadElement :> HTMLElement;

        part def HTMLHeadingElement :> HTMLElement {
            attribute align : String;
        }

        part def HTMLHtmlElement :> HTMLElement {
            attribute version : String;
        }

        part def HTMLIFrameElement :> HTMLElement {
            attribute src : String;
            attribute srcdoc : Base::Anything;
            attribute name : String;
            attribute sandbox : String[0..*] ordered;
            attribute allow : String;
            attribute allowFullscreen : Boolean;
            attribute width : String;
            attribute height : String;
            attribute referrerPolicy : String;
            attribute loading : String;
            derived ref part contentDocument : Document[0..1];
            attribute align : String;
            attribute scrolling : String;
            attribute frameBorder : String;
            attribute longDesc : String;
            attribute marginHeight : String;
            attribute marginWidth : String;
            action def getSVGDocument {
                out result : Document[0..1];
            }
        }

        part def HTMLImageElement :> HTMLElement {
            attribute alt : String;
            attribute src : String;
            attribute srcset : String;
            attribute sizes : String;
            attribute crossOrigin : String[0..1];
            attribute useMap : String;
            attribute isMap : Boolean;
            attribute controls : Boolean;
            attribute width : Natural;
            attribute height : Natural;
            constant attribute naturalWidth : Natural;
            constant attribute naturalHeight : Natural;
            constant attribute complete : Boolean;
            constant attribute currentSrc : String;
            attribute referrerPolicy : String;
            attribute decoding : String;
            attribute loading : String;
            attribute fetchPriority : String;
            attribute name : String;
            attribute lowsrc : String;
            attribute align : String;
            attribute hspace : Natural;
            attribute vspace : Natural;
            attribute longDesc : String;
            attribute border : String;
            action def decode;
        }

        part def HTMLLIElement :> HTMLElement {
            attribute value : Integer;
            attribute type : String;
        }

        part def HTMLLabelElement :> HTMLElement {
            derived ref part form : HTMLFormElement[0..1];
            attribute htmlFor : String;
            derived ref part control : HTMLElement[0..1];
        }

        part def HTMLLegendElement :> HTMLElement {
            derived ref part form : HTMLFormElement[0..1];
            attribute align : String;
        }

        part def HTMLLinkElement :> HTMLElement {
            attribute href : String;
            attribute crossOrigin : String[0..1];
            attribute rel : String;
            attribute 'as' : String;
            attribute relList : String[0..*] ordered;
            attribute media : String;
            attribute integrity : String;
            attribute hreflang : String;
            attribute type : String;
            attribute sizes : String[0..*] ordered;
            attribute imageSrcset : String;
            attribute imageSizes : String;
            attribute referrerPolicy : String;
            attribute blocking : String[0..*] ordered;
            attribute disabled : Boolean;
            attribute fetchPriority : String;
            attribute charset : String;
            attribute rev : String;
            attribute target : String;
        }

        part def HTMLMapElement :> HTMLElement {
            attribute name : String;
            derived ref part areas : Element[0..*] ordered;
        }

        part def HTMLMarqueeElement :> HTMLElement {
            attribute behavior : String;
            attribute bgColor : String;
            attribute direction : String;
            attribute height : String;
            attribute hspace : Natural;
            attribute 'loop' : Integer;
            attribute scrollAmount : Natural;
            attribute scrollDelay : Natural;
            attribute trueSpeed : Boolean;
            attribute vspace : Natural;
            attribute width : String;
            action def start;
            action def stop;
        }

        abstract part def HTMLMediaElement :> HTMLElement {
            constant ref part error : MediaError[0..1];
            attribute src : String;
            attribute srcObject : Base::Anything[0..1];
            constant attribute currentSrc : String;
            attribute crossOrigin : String[0..1];
            constant attribute NETWORK_EMPTY : Natural = 0;
            constant attribute NETWORK_IDLE : Natural = 1;
            constant attribute NETWORK_LOADING : Natural = 2;
            constant attribute NETWORK_NO_SOURCE : Natural = 3;
            constant attribute networkState : Natural;
            attribute preload : String;
            constant ref part buffered : TimeRanges;
            constant attribute HAVE_NOTHING : Natural = 0;
            constant attribute HAVE_METADATA : Natural = 1;
            constant attribute HAVE_CURRENT_DATA : Natural = 2;
            constant attribute HAVE_FUTURE_DATA : Natural = 3;
            constant attribute HAVE_ENOUGH_DATA : Natural = 4;
            constant attribute readyState : Natural;
            constant attribute seeking : Boolean;
            attribute currentTime : Real;
            constant attribute duration : Real;
            constant attribute paused : Boolean;
            attribute defaultPlaybackRate : Real;
            attribute playbackRate : Real;
            attribute preservesPitch : Boolean;
            constant ref part played : TimeRanges;
            constant ref part seekable : TimeRanges;
            constant attribute ended : Boolean;
            attribute autoplay : Boolean;
            attribute 'loop' : Boolean;
            attribute controls : Boolean;
            attribute volume : Real;
            attribute muted : Boolean;
            attribute defaultMuted : Boolean;
            attribute loading : String;
            constant ref part audioTracks : AudioTrackList;
            constant ref part videoTracks : VideoTrackList;
            constant ref part textTracks : TextTrackList;
            action def load;
            action def canPlayType {
                in type : String;
                out result : CanPlayTypeResult;
            }
            action def fastSeek {
                in time : Real;
            }
            action def getStartDate {
                out result : Base::Anything;
            }
            action def play;
            action def pause;
            action def addTextTrack {
                in kind : TextTrackKind;
                in label : String[0..1];
                in 'language' : String[0..1];
                out result : TextTrack;
            }
        }

        part def HTMLAudioElement :> HTMLMediaElement;

        part def HTMLMenuElement :> HTMLElement {
            attribute compact : Boolean;
        }

        part def HTMLMetaElement :> HTMLElement {
            attribute name : String;
            attribute httpEquiv : String;
            attribute content : String;
            attribute media : String;
            attribute scheme : String;
        }

        part def HTMLMeterElement :> HTMLElement {
            attribute value : Real;
            attribute min : Real;
            attribute max : Real;
            attribute low : Real;
            attribute high : Real;
            attribute optimum : Real;
            derived ref part labels : Node[0..*] ordered;
        }

        part def HTMLModElement :> HTMLElement {
            attribute cite : String;
            attribute dateTime : String;
        }

        part def HTMLOListElement :> HTMLElement {
            attribute reversed : Boolean;
            attribute start : Integer;
            attribute type : String;
            attribute compact : Boolean;
        }

        part def HTMLObjectElement :> HTMLElement {
            attribute data : String;
            attribute type : String;
            attribute name : String;
            derived ref part form : HTMLFormElement[0..1];
            attribute width : String;
            attribute height : String;
            derived ref part contentDocument : Document[0..1];
            constant attribute willValidate : Boolean;
            constant ref part validity : ValidityState;
            constant attribute validationMessage : String;
            attribute align : String;
            attribute archive : String;
            attribute code : String;
            attribute declare : Boolean;
            attribute hspace : Natural;
            attribute standby : String;
            attribute vspace : Natural;
            attribute codeBase : String;
            attribute codeType : String;
            attribute useMap : String;
            attribute border : String;
            action def getSVGDocument {
                out result : Document[0..1];
            }
            action def checkValidity {
                out result : Boolean;
            }
            action def reportValidity {
                out result : Boolean;
            }
            action def setCustomValidity {
                in error : String;
            }
        }

        part def HTMLOptGroupElement :> HTMLElement {
            attribute disabled : Boolean;
            attribute label : String;
        }

        part def HTMLOptionElement :> HTMLElement {
            attribute disabled : Boolean;
            derived ref part form : HTMLFormElement[0..1];
            attribute label : String;
            attribute defaultSelected : Boolean;
            attribute selected : Boolean;
            attribute value : String;
            attribute text : String;
            constant attribute index : Integer;
        }

        part def HTMLOutputElement :> HTMLElement {
            attribute htmlFor : String[0..*] ordered;
            derived ref part form : HTMLFormElement[0..1];
            attribute name : String;
            constant attribute type : String;
            attribute defaultValue : String;
            attribute value : String;
            constant attribute willValidate : Boolean;
            constant ref part validity : ValidityState;
            constant attribute validationMessage : String;
            derived ref part labels : Node[0..*] ordered;
            action def checkValidity {
                out result : Boolean;
            }
            action def reportValidity {
                out result : Boolean;
            }
            action def setCustomValidity {
                in error : String;
            }
        }

        part def HTMLParagraphElement :> HTMLElement {
            attribute align : String;
        }

        part def HTMLParamElement :> HTMLElement {
            attribute name : String;
            attribute value : String;
            attribute type : String;
            attribute valueType : String;
        }

        part def HTMLPictureElement :> HTMLElement;

        part def HTMLPreElement :> HTMLElement {
            attribute width : Integer;
        }

        part def HTMLProgressElement :> HTMLElement {
            attribute value : Real;
            attribute max : Real;
            constant attribute position : Real;
            derived ref part labels : Node[0..*] ordered;
        }

        part def HTMLQuoteElement :> HTMLElement {
            attribute cite : String;
        }

        part def HTMLScriptElement :> HTMLElement {
            attribute type : String;
            attribute src : String;
            attribute noModule : Boolean;
            attribute async : Boolean;
            attribute defer : Boolean;
            attribute blocking : String[0..*] ordered;
            attribute crossOrigin : String[0..1];
            attribute referrerPolicy : String;
            attribute integrity : String;
            attribute fetchPriority : String;
            attribute text : String;
            attribute charset : String;
            attribute 'event' : String;
            attribute htmlFor : String;
        }

        part def HTMLSelectElement :> HTMLElement {
            attribute autocomplete : String;
            attribute disabled : Boolean;
            derived ref part form : HTMLFormElement[0..1];
            attribute multiple : Boolean;
            attribute name : String;
            attribute required : Boolean;
            attribute size : Natural;
            constant attribute type : String;
            derived ref part options : Element[0..*] ordered;
            attribute length : Natural;
            derived ref part selectedOptions : Element[0..*] ordered;
            attribute selectedIndex : Integer;
            attribute value : String;
            constant attribute willValidate : Boolean;
            constant ref part validity : ValidityState;
            constant attribute validationMessage : String;
            derived ref part labels : Node[0..*] ordered;
            action def 'item' {
                in index : Natural;
                out result : HTMLOptionElement[0..1];
            }
            action def namedItem {
                in name : String;
                out result : HTMLOptionElement[0..1];
            }
            action def add {
                in element : HTMLElement;
                in before : Base::Anything[0..1];
            }
            action def remove {
                in index : Integer[0..1];
            }
            action def checkValidity {
                out result : Boolean;
            }
            action def reportValidity {
                out result : Boolean;
            }
            action def setCustomValidity {
                in error : String;
            }
            action def showPicker;
        }

        part def HTMLSelectedContentElement :> HTMLElement;

        part def HTMLSlotElement :> HTMLElement {
            attribute name : String;
            action def assignedNodes {
                in options : AssignedNodesOptions[0..1];
                out result : Node[0..*] ordered;
            }
            action def assignedElements {
                in options : AssignedNodesOptions[0..1];
                out result : Element[0..*] ordered;
            }
            action def 'assign' {
                in nodes : Node[0..*] ordered;
            }
        }

        part def HTMLSourceElement :> HTMLElement {
            attribute src : String;
            attribute type : String;
            attribute srcset : String;
            attribute sizes : String;
            attribute media : String;
            attribute width : Natural;
            attribute height : Natural;
        }

        part def HTMLSpanElement :> HTMLElement;

        part def HTMLStyleElement :> HTMLElement {
            attribute disabled : Boolean;
            attribute media : String;
            attribute blocking : String[0..*] ordered;
            attribute type : String;
        }

        part def HTMLTableCaptionElement :> HTMLElement {
            attribute align : String;
        }

        part def HTMLTableCellElement :> HTMLElement {
            attribute colSpan : Natural;
            attribute rowSpan : Natural;
            attribute headers : String;
            constant attribute cellIndex : Integer;
            attribute scope : String;
            attribute abbr : String;
            attribute align : String;
            attribute axis : String;
            attribute height : String;
            attribute width : String;
            attribute ch : String;
            attribute chOff : String;
            attribute noWrap : Boolean;
            attribute vAlign : String;
            attribute bgColor : String;
        }

        part def HTMLTableColElement :> HTMLElement {
            attribute span : Natural;
            attribute align : String;
            attribute ch : String;
            attribute chOff : String;
            attribute vAlign : String;
            attribute width : String;
        }

        part def HTMLTableElement :> HTMLElement {
            derived ref part caption : HTMLTableCaptionElement[0..1];
            derived ref part tHead : HTMLTableSectionElement[0..1];
            derived ref part tFoot : HTMLTableSectionElement[0..1];
            derived ref part tBodies : Element[0..*] ordered;
            derived ref part rows : Element[0..*] ordered;
            attribute align : String;
            attribute border : String;
            attribute 'frame' : String;
            attribute rules : String;
            attribute summary : String;
            attribute width : String;
            attribute bgColor : String;
            attribute cellPadding : String;
            attribute cellSpacing : String;
            action def createCaption {
                out result : HTMLTableCaptionElement;
            }
            action def deleteCaption;
            action def createTHead {
                out result : HTMLTableSectionElement;
            }
            action def deleteTHead;
            action def createTFoot {
                out result : HTMLTableSectionElement;
            }
            action def deleteTFoot;
            action def createTBody {
                out result : HTMLTableSectionElement;
            }
            action def insertRow {
                in index : Integer[0..1];
                out result : HTMLTableRowElement;
            }
            action def deleteRow {
                in index : Integer;
            }
        }

        part def HTMLTableRowElement :> HTMLElement {
            constant attribute rowIndex : Integer;
            constant attribute sectionRowIndex : Integer;
            derived ref part cells : Element[0..*] ordered;
            attribute align : String;
            attribute ch : String;
            attribute chOff : String;
            attribute vAlign : String;
            attribute bgColor : String;
            action def insertCell {
                in index : Integer[0..1];
                out result : HTMLTableCellElement;
            }
            action def deleteCell {
                in index : Integer;
            }
        }

        part def HTMLTableSectionElement :> HTMLElement {
            derived ref part rows : Element[0..*] ordered;
            attribute align : String;
            attribute ch : String;
            attribute chOff : String;
            attribute vAlign : String;
            action def insertRow {
                in index : Integer[0..1];
                out result : HTMLTableRowElement;
            }
            action def deleteRow {
                in index : Integer;
            }
        }

        part def HTMLTemplateElement :> HTMLElement {
            derived ref part content : DocumentFragment;
            attribute htmlFor : String;
            attribute shadowRootMode : String;
            attribute shadowRootDelegatesFocus : Boolean;
            attribute shadowRootSerializable : Boolean;
            attribute shadowRootSlotAssignment : String;
            attribute shadowRootClonable : Boolean;
            attribute shadowRootCustomElementRegistry : String;
        }

        part def HTMLTextAreaElement :> HTMLElement {
            attribute autocomplete : String;
            attribute cols : Natural;
            attribute dirName : String;
            attribute disabled : Boolean;
            derived ref part form : HTMLFormElement[0..1];
            attribute maxLength : Integer;
            attribute minLength : Integer;
            attribute name : String;
            attribute placeholder : String;
            attribute readOnly : Boolean;
            attribute required : Boolean;
            attribute rows : Natural;
            attribute wrap : String;
            constant attribute type : String;
            attribute defaultValue : String;
            attribute value : String;
            constant attribute textLength : Natural;
            constant attribute willValidate : Boolean;
            constant ref part validity : ValidityState;
            constant attribute validationMessage : String;
            derived ref part labels : Node[0..*] ordered;
            attribute selectionStart : Natural;
            attribute selectionEnd : Natural;
            attribute selectionDirection : String;
            action def checkValidity {
                out result : Boolean;
            }
            action def reportValidity {
                out result : Boolean;
            }
            action def setCustomValidity {
                in error : String;
            }
            action def select;
            action def setRangeText {
                in replacement : String;
                in start : Natural[0..1];
                in 'end' : Natural[0..1];
                in selectionMode : SelectionMode[0..1];
            }
            action def setSelectionRange {
                in start : Natural;
                in 'end' : Natural;
                in direction : String[0..1];
            }
        }

        part def HTMLTimeElement :> HTMLElement {
            attribute dateTime : String;
        }

        part def HTMLTitleElement :> HTMLElement {
            attribute text : String;
        }

        part def HTMLTrackElement :> HTMLElement {
            attribute kind : String;
            attribute src : String;
            attribute srclang : String;
            attribute label : String;
            attribute 'default' : Boolean;
            constant attribute NONE : Natural = 0;
            constant attribute LOADING : Natural = 1;
            constant attribute LOADED : Natural = 2;
            constant attribute ERROR : Natural = 3;
            constant attribute readyState : Natural;
            constant ref part track : TextTrack;
        }

        part def HTMLUListElement :> HTMLElement {
            attribute compact : Boolean;
            attribute type : String;
        }

        part def HTMLUnknownElement :> HTMLElement;

        part def HTMLVideoElement :> HTMLMediaElement {
            attribute width : Natural;
            attribute height : Natural;
            constant attribute videoWidth : Natural;
            constant attribute videoHeight : Natural;
            attribute poster : String;
            attribute playsInline : Boolean;
        }

        abstract part def HyperlinkElementUtils {
            constant attribute origin : String;
            attribute protocol : String;
            attribute username : String;
            attribute password : String;
            attribute host : String;
            attribute hostname : String;
            attribute 'port' : String;
            attribute pathname : String;
            attribute search : String;
            attribute hash : String;
            attribute hreflang : String;
            attribute type : String;
        }

        part def HTMLAnchorElement :> HTMLElement, HyperlinkElementUtils, HTMLHyperlinkElementUtils {
            attribute download : String;
            attribute ping : String;
            attribute rel : String;
            attribute relList : String[0..*] ordered;
            attribute text : String;
            attribute referrerPolicy : String;
            attribute coords : String;
            attribute charset : String;
            attribute name : String;
            attribute rev : String;
            attribute shape : String;
        }

        part def HTMLAreaElement :> HTMLElement, HyperlinkElementUtils, HTMLHyperlinkElementUtils {
            attribute alt : String;
            attribute coords : String;
            attribute shape : String;
            attribute download : String;
            attribute ping : String;
            attribute rel : String;
            attribute relList : String[0..*] ordered;
            attribute referrerPolicy : String;
            attribute noHref : Boolean;
        }

        part def ImageBitmap {
            constant attribute width : Natural;
            constant attribute height : Natural;
            action def close;
        }

        attribute def ImageEncodeOptions {
            attribute type : String[0..1] default = "image/png";
            attribute quality : Real[0..1];
        }

        part def Location {
            attribute href : String;
            constant attribute origin : String;
            attribute protocol : String;
            attribute host : String;
            attribute hostname : String;
            attribute 'port' : String;
            attribute pathname : String;
            attribute search : String;
            attribute hash : String;
            constant ref part ancestorOrigins : DOMStringList;
            action def 'assign' {
                in url : String;
            }
            action def replace {
                in url : String;
            }
            action def reload;
        }

        part def MediaError {
            constant attribute MEDIA_ERR_ABORTED : Natural = 1;
            constant attribute MEDIA_ERR_NETWORK : Natural = 2;
            constant attribute MEDIA_ERR_DECODE : Natural = 3;
            constant attribute MEDIA_ERR_SRC_NOT_SUPPORTED : Natural = 4;
            constant attribute code : Natural;
            constant attribute 'message' : String;
        }

        part def OffscreenCanvas :> EventTarget {
            attribute width : Natural;
            attribute height : Natural;
            action def getContext {
                in contextId : OffscreenRenderingContextId;
                in options : Base::Anything[0..1];
                out result : Base::Anything[0..1];
            }
            action def transferToImageBitmap {
                out result : ImageBitmap;
            }
        }

        enum def OffscreenRenderingContextId {
            '2d';
            bitmaprenderer;
            webgl;
            webgl2;
            webgpu;
        }

        abstract part def PopoverTargetAttributes {
            derived ref part popoverTargetElement : Element[0..1];
            attribute popoverTargetAction : String;
        }

        part def HTMLButtonElement :> HTMLElement, PopoverTargetAttributes {
            attribute command : String;
            derived ref part commandForElement : Element[0..1];
            attribute disabled : Boolean;
            derived ref part form : HTMLFormElement[0..1];
            attribute formAction : String;
            attribute formEnctype : String;
            attribute formMethod : String;
            attribute formNoValidate : Boolean;
            attribute formTarget : String;
            attribute name : String;
            attribute type : String;
            attribute value : String;
            constant attribute willValidate : Boolean;
            constant ref part validity : ValidityState;
            constant attribute validationMessage : String;
            derived ref part labels : Node[0..*] ordered;
            action def checkValidity {
                out result : Boolean;
            }
            action def reportValidity {
                out result : Boolean;
            }
            action def setCustomValidity {
                in error : String;
            }
        }

        part def HTMLInputElement :> HTMLElement, PopoverTargetAttributes {
            attribute 'accept' : String;
            attribute alpha : Boolean;
            attribute alt : String;
            attribute autocomplete : String;
            attribute defaultChecked : Boolean;
            attribute checked : Boolean;
            attribute colorSpace : String;
            attribute dirName : String;
            attribute disabled : Boolean;
            derived ref part form : HTMLFormElement[0..1];
            attribute formAction : String;
            attribute formEnctype : String;
            attribute formMethod : String;
            attribute formNoValidate : Boolean;
            attribute formTarget : String;
            attribute height : Natural;
            attribute indeterminate : Boolean;
            derived ref part list : HTMLDataListElement[0..1];
            attribute max : String;
            attribute maxLength : Integer;
            attribute min : String;
            attribute minLength : Integer;
            attribute multiple : Boolean;
            attribute name : String;
            attribute pattern : String;
            attribute placeholder : String;
            attribute readOnly : Boolean;
            attribute required : Boolean;
            attribute size : Natural;
            attribute src : String;
            attribute step : String;
            attribute type : String;
            attribute defaultValue : String;
            attribute value : String;
            attribute valueAsDate : Base::Anything[0..1];
            attribute valueAsNumber : Real;
            attribute width : Natural;
            constant attribute willValidate : Boolean;
            constant ref part validity : ValidityState;
            constant attribute validationMessage : String;
            derived ref part labels : Node[0..*] ordered;
            attribute selectionStart : Natural[0..1];
            attribute selectionEnd : Natural[0..1];
            attribute selectionDirection : String[0..1];
            attribute align : String;
            attribute useMap : String;
            action def stepUp {
                in n : Integer[0..1];
            }
            action def stepDown {
                in n : Integer[0..1];
            }
            action def checkValidity {
                out result : Boolean;
            }
            action def reportValidity {
                out result : Boolean;
            }
            action def setCustomValidity {
                in error : String;
            }
            action def select;
            action def setRangeText {
                in replacement : String;
                in start : Natural[0..1];
                in 'end' : Natural[0..1];
                in selectionMode : SelectionMode[0..1];
            }
            action def setSelectionRange {
                in start : Natural;
                in 'end' : Natural;
                in direction : String[0..1];
            }
            action def showPicker;
        }

        enum def SelectionMode {
            select;
            start;
            'end';
            preserve;
        }

        attribute def SetHTMLOptions {
            attribute sanitizer : Base::Anything[0..1] default = "default";
        }

        attribute def SetHTMLUnsafeOptions {
            attribute sanitizer : Base::Anything[0..1];
            attribute runScripts : Boolean[0..1] default = false;
        }

        attribute def ShowPopoverOptions {
            ref part source : HTMLElement[0..1];
        }

        part def TextTrack :> EventTarget {
            constant attribute kind : TextTrackKind;
            constant attribute label : String;
            constant attribute 'language' : String;
            constant attribute id : String;
            constant attribute inBandMetadataTrackDispatchType : String;
            attribute mode : TextTrackMode;
            constant ref part cues : TextTrackCueList[0..1];
            constant ref part activeCues : TextTrackCueList[0..1];
            action def addCue {
                in cue : TextTrackCue;
            }
            action def removeCue {
                in cue : TextTrackCue;
            }
        }

        part def TextTrackCue :> EventTarget {
            constant ref part track : TextTrack[0..1];
            attribute id : String;
            attribute startTime : Real;
            attribute endTime : Real;
            attribute pauseOnExit : Boolean;
        }

        part def TextTrackCueList {
            constant attribute length : Natural;
            action def getCueById {
                in id : String;
                out result : TextTrackCue[0..1];
            }
        }

        enum def TextTrackKind {
            subtitles;
            captions;
            descriptions;
            chapters;
            'metadata';
        }

        part def TextTrackList :> EventTarget {
            constant attribute length : Natural;
            action def getTrackById {
                in id : String;
                out result : TextTrack[0..1];
            }
        }

        enum def TextTrackMode {
            disabled;
            hidden;
            showing;
        }

        part def TimeRanges {
            constant attribute length : Natural;
            action def start {
                in index : Natural;
                out result : Real;
            }
            action def 'end' {
                in index : Natural;
                out result : Real;
            }
        }

        part def ValidityState {
            constant attribute valueMissing : Boolean;
            constant attribute typeMismatch : Boolean;
            constant attribute patternMismatch : Boolean;
            constant attribute tooLong : Boolean;
            constant attribute tooShort : Boolean;
            constant attribute rangeUnderflow : Boolean;
            constant attribute rangeOverflow : Boolean;
            constant attribute stepMismatch : Boolean;
            constant attribute badInput : Boolean;
            constant attribute customError : Boolean;
            constant attribute valid : Boolean;
        }

        attribute def ValidityStateFlags {
            attribute valueMissing : Boolean[0..1] default = false;
            attribute typeMismatch : Boolean[0..1] default = false;
            attribute patternMismatch : Boolean[0..1] default = false;
            attribute tooLong : Boolean[0..1] default = false;
            attribute tooShort : Boolean[0..1] default = false;
            attribute rangeUnderflow : Boolean[0..1] default = false;
            attribute rangeOverflow : Boolean[0..1] default = false;
            attribute stepMismatch : Boolean[0..1] default = false;
            attribute badInput : Boolean[0..1] default = false;
            attribute customError : Boolean[0..1] default = false;
        }

        part def VideoTrack {
            constant attribute id : String;
            constant attribute kind : String;
            constant attribute label : String;
            constant attribute 'language' : String;
            attribute selected : Boolean;
        }

        part def VideoTrackList :> EventTarget {
            constant attribute length : Natural;
            constant attribute selectedIndex : Integer;
            action def getTrackById {
                in id : String;
                out result : VideoTrack[0..1];
            }
        }

        abstract part def WindowEventHandlers;

        part def HTMLBodyElement :> HTMLElement, WindowEventHandlers {
            attribute text : String;
            attribute link : String;
            attribute vLink : String;
            attribute aLink : String;
            attribute bgColor : String;
            attribute background : String;
        }

        part def HTMLFrameSetElement :> HTMLElement, WindowEventHandlers {
            attribute cols : String;
            attribute rows : String;
        }

        package Elements {
            part def A :> HTMLAnchorElement {
                :>> localName = "a";
            }

            part def Abbr :> HTMLElement {
                :>> localName = "abbr";
            }

            part def Acronym :> HTMLElement {
                :>> localName = "acronym";
            }

            part def Address :> HTMLElement {
                :>> localName = "address";
            }

            part def Applet :> HTMLUnknownElement {
                :>> localName = "applet";
            }

            part def Area :> HTMLAreaElement {
                :>> localName = "area";
            }

            part def Article :> HTMLElement {
                :>> localName = "article";
            }

            part def Aside :> HTMLElement {
                :>> localName = "aside";
            }

            part def Audio :> HTMLAudioElement {
                :>> localName = "audio";
            }

            part def B :> HTMLElement {
                :>> localName = "b";
            }

            part def Base :> HTMLBaseElement {
                :>> localName = "base";
            }

            part def Basefont :> HTMLElement {
                :>> localName = "basefont";
            }

            part def Bdi :> HTMLElement {
                :>> localName = "bdi";
            }

            part def Bdo :> HTMLElement {
                :>> localName = "bdo";
            }

            part def Bgsound :> HTMLUnknownElement {
                :>> localName = "bgsound";
            }

            part def Big :> HTMLElement {
                :>> localName = "big";
            }

            part def Blink :> HTMLUnknownElement {
                :>> localName = "blink";
            }

            part def Blockquote :> HTMLQuoteElement {
                :>> localName = "blockquote";
            }

            part def Body :> HTMLBodyElement {
                :>> localName = "body";
            }

            part def Br :> HTMLBRElement {
                :>> localName = "br";
            }

            part def Button :> HTMLButtonElement {
                :>> localName = "button";
            }

            part def Canvas :> HTMLCanvasElement {
                :>> localName = "canvas";
            }

            part def Caption :> HTMLTableCaptionElement {
                :>> localName = "caption";
            }

            part def Center :> HTMLElement {
                :>> localName = "center";
            }

            part def Cite :> HTMLElement {
                :>> localName = "cite";
            }

            part def Code :> HTMLElement {
                :>> localName = "code";
            }

            part def Col :> HTMLTableColElement {
                :>> localName = "col";
            }

            part def Colgroup :> HTMLTableColElement {
                :>> localName = "colgroup";
            }

            part def Data :> HTMLDataElement {
                :>> localName = "data";
            }

            part def Datalist :> HTMLDataListElement {
                :>> localName = "datalist";
            }

            part def Dd :> HTMLElement {
                :>> localName = "dd";
            }

            part def Del :> HTMLModElement {
                :>> localName = "del";
            }

            part def Details :> HTMLDetailsElement {
                :>> localName = "details";
            }

            part def Dfn :> HTMLElement {
                :>> localName = "dfn";
            }

            part def Dialog :> HTMLDialogElement {
                :>> localName = "dialog";
            }

            part def Dir :> HTMLDirectoryElement {
                :>> localName = "dir";
            }

            part def Div :> HTMLDivElement {
                :>> localName = "div";
            }

            part def Dl :> HTMLDListElement {
                :>> localName = "dl";
            }

            part def Dt :> HTMLElement {
                :>> localName = "dt";
            }

            part def Em :> HTMLElement {
                :>> localName = "em";
            }

            part def Embed :> HTMLEmbedElement {
                :>> localName = "embed";
            }

            part def Fieldset :> HTMLFieldSetElement {
                :>> localName = "fieldset";
            }

            part def Figcaption :> HTMLElement {
                :>> localName = "figcaption";
            }

            part def Figure :> HTMLElement {
                :>> localName = "figure";
            }

            part def Font :> HTMLFontElement {
                :>> localName = "font";
            }

            part def Footer :> HTMLElement {
                :>> localName = "footer";
            }

            part def Form :> HTMLFormElement {
                :>> localName = "form";
            }

            part def Frame :> HTMLFrameElement {
                :>> localName = "frame";
            }

            part def Frameset :> HTMLFrameSetElement {
                :>> localName = "frameset";
            }

            part def H1 :> HTMLHeadingElement {
                :>> localName = "h1";
            }

            part def H2 :> HTMLHeadingElement {
                :>> localName = "h2";
            }

            part def H3 :> HTMLHeadingElement {
                :>> localName = "h3";
            }

            part def H4 :> HTMLHeadingElement {
                :>> localName = "h4";
            }

            part def H5 :> HTMLHeadingElement {
                :>> localName = "h5";
            }

            part def H6 :> HTMLHeadingElement {
                :>> localName = "h6";
            }

            part def Head :> HTMLHeadElement {
                :>> localName = "head";
            }

            part def Header :> HTMLElement {
                :>> localName = "header";
            }

            part def Hgroup :> HTMLElement {
                :>> localName = "hgroup";
            }

            part def Hr :> HTMLHRElement {
                :>> localName = "hr";
            }

            part def Html :> HTMLHtmlElement {
                :>> localName = "html";
            }

            part def I :> HTMLElement {
                :>> localName = "i";
            }

            part def Iframe :> HTMLIFrameElement {
                :>> localName = "iframe";
            }

            part def Img :> HTMLImageElement {
                :>> localName = "img";
            }

            part def Input :> HTMLInputElement {
                :>> localName = "input";
            }

            part def Ins :> HTMLModElement {
                :>> localName = "ins";
            }

            part def Isindex :> HTMLUnknownElement {
                :>> localName = "isindex";
            }

            part def Kbd :> HTMLElement {
                :>> localName = "kbd";
            }

            part def Keygen :> HTMLUnknownElement {
                :>> localName = "keygen";
            }

            part def Label :> HTMLLabelElement {
                :>> localName = "label";
            }

            part def Legend :> HTMLLegendElement {
                :>> localName = "legend";
            }

            part def Li :> HTMLLIElement {
                :>> localName = "li";
            }

            part def Link :> HTMLLinkElement {
                :>> localName = "link";
            }

            part def Listing :> HTMLPreElement {
                :>> localName = "listing";
            }

            part def Main :> HTMLElement {
                :>> localName = "main";
            }

            part def Map :> HTMLMapElement {
                :>> localName = "map";
            }

            part def Mark :> HTMLElement {
                :>> localName = "mark";
            }

            part def Marquee :> HTMLMarqueeElement {
                :>> localName = "marquee";
            }

            part def Menu :> HTMLMenuElement {
                :>> localName = "menu";
            }

            part def Menuitem :> HTMLElement {
                :>> localName = "menuitem";
            }

            part def Meta :> HTMLMetaElement {
                :>> localName = "meta";
            }

            part def Meter :> HTMLMeterElement {
                :>> localName = "meter";
            }

            part def Multicol :> HTMLUnknownElement {
                :>> localName = "multicol";
            }

            part def Nav :> HTMLElement {
                :>> localName = "nav";
            }

            part def Nextid :> HTMLUnknownElement {
                :>> localName = "nextid";
            }

            part def Nobr :> HTMLElement {
                :>> localName = "nobr";
            }

            part def Noembed :> HTMLElement {
                :>> localName = "noembed";
            }

            part def Noframes :> HTMLElement {
                :>> localName = "noframes";
            }

            part def Noscript :> HTMLElement {
                :>> localName = "noscript";
            }

            part def Object :> HTMLObjectElement {
                :>> localName = "object";
            }

            part def Ol :> HTMLOListElement {
                :>> localName = "ol";
            }

            part def Optgroup :> HTMLOptGroupElement {
                :>> localName = "optgroup";
            }

            part def Option :> HTMLOptionElement {
                :>> localName = "option";
            }

            part def Output :> HTMLOutputElement {
                :>> localName = "output";
            }

            part def P :> HTMLParagraphElement {
                :>> localName = "p";
            }

            part def Param :> HTMLParamElement {
                :>> localName = "param";
            }

            part def Picture :> HTMLPictureElement {
                :>> localName = "picture";
            }

            part def Plaintext :> HTMLElement {
                :>> localName = "plaintext";
            }

            part def Pre :> HTMLPreElement {
                :>> localName = "pre";
            }

            part def Progress :> HTMLProgressElement {
                :>> localName = "progress";
            }

            part def Q :> HTMLQuoteElement {
                :>> localName = "q";
            }

            part def Rb :> HTMLElement {
                :>> localName = "rb";
            }

            part def Rp :> HTMLElement {
                :>> localName = "rp";
            }

            part def Rt :> HTMLElement {
                :>> localName = "rt";
            }

            part def Rtc :> HTMLElement {
                :>> localName = "rtc";
            }

            part def Ruby :> HTMLElement {
                :>> localName = "ruby";
            }

            part def S :> HTMLElement {
                :>> localName = "s";
            }

            part def Samp :> HTMLElement {
                :>> localName = "samp";
            }

            part def Script :> HTMLScriptElement {
                :>> localName = "script";
            }

            part def Search :> HTMLElement {
                :>> localName = "search";
            }

            part def Section :> HTMLElement {
                :>> localName = "section";
            }

            part def Select :> HTMLSelectElement {
                :>> localName = "select";
            }

            part def Selectedcontent :> HTMLSelectedContentElement {
                :>> localName = "selectedcontent";
            }

            part def Slot :> HTMLSlotElement {
                :>> localName = "slot";
            }

            part def Small :> HTMLElement {
                :>> localName = "small";
            }

            part def Source :> HTMLSourceElement {
                :>> localName = "source";
            }

            part def Spacer :> HTMLUnknownElement {
                :>> localName = "spacer";
            }

            part def Span :> HTMLSpanElement {
                :>> localName = "span";
            }

            part def Strike :> HTMLElement {
                :>> localName = "strike";
            }

            part def Strong :> HTMLElement {
                :>> localName = "strong";
            }

            part def Style :> HTMLStyleElement {
                :>> localName = "style";
            }

            part def Sub :> HTMLElement {
                :>> localName = "sub";
            }

            part def Summary :> HTMLElement {
                :>> localName = "summary";
            }

            part def Sup :> HTMLElement {
                :>> localName = "sup";
            }

            part def Table :> HTMLTableElement {
                :>> localName = "table";
            }

            part def Tbody :> HTMLTableSectionElement {
                :>> localName = "tbody";
            }

            part def Td :> HTMLTableCellElement {
                :>> localName = "td";
            }

            part def Template :> HTMLTemplateElement {
                :>> localName = "template";
            }

            part def Textarea :> HTMLTextAreaElement {
                :>> localName = "textarea";
            }

            part def Tfoot :> HTMLTableSectionElement {
                :>> localName = "tfoot";
            }

            part def Th :> HTMLTableCellElement {
                :>> localName = "th";
            }

            part def Thead :> HTMLTableSectionElement {
                :>> localName = "thead";
            }

            part def Time :> HTMLTimeElement {
                :>> localName = "time";
            }

            part def Title :> HTMLTitleElement {
                :>> localName = "title";
            }

            part def Tr :> HTMLTableRowElement {
                :>> localName = "tr";
            }

            part def Track :> HTMLTrackElement {
                :>> localName = "track";
            }

            part def Tt :> HTMLElement {
                :>> localName = "tt";
            }

            part def U :> HTMLElement {
                :>> localName = "u";
            }

            part def Ul :> HTMLUListElement {
                :>> localName = "ul";
            }

            part def Var :> HTMLElement {
                :>> localName = "var";
            }

            part def Video :> HTMLVideoElement {
                :>> localName = "video";
            }

            part def Wbr :> HTMLElement {
                :>> localName = "wbr";
            }

            part def Xmp :> HTMLPreElement {
                :>> localName = "xmp";
            }
        }
    }
}
