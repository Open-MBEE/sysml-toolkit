# Interchange conformance notes

How this toolkit's interchange JSON relates to the normative sources — the OMG pilot implementation (its Xtext grammars vendored in `spec-refs/`, the published 20250201 JSON schemas and XMI metamodel) — and what to expect when exchanging payloads with other SysML v2 implementations. Representation choices below were adjudicated against the pilot implementation as the normative reference (2026-07-16); where other tools serialize differently, this toolkit follows the pilot.

## Conformance level of the full form

Both compact (KerML 10.4) and full-form (Systems Modeling API element list) output validate against the published 20250201 JSON schemas. The full form computes derived properties where the derivation is structural and emits the inheritance/import closures as type-correct empty values — the API's "passthrough" level — so payload size stays proportional to the model. Implementations that materialize the inherited/implied closures per element will produce much larger payloads for the same model; both are schema-valid, and this toolkit reads either.

## Representation rules (per the pilot)

- **Operator-expression operands** are wrapped: each operand becomes the `FeatureValue` of an owned `in` parameter Feature under a **private** ParameterMembership (pilot `OperandEList` / `TypeUtil.addOwnedParameterTo`; the 20250201 metamodel removed the old `operand` containment). Explicit argument lists (`f(a, b)`) wrap the same way with default visibility (KerML.xtext `ArgumentMember`).
- **Effective names**: `Membership.memberName` and full-form `name` derive from an unnamed feature's naming feature — the first redefined feature (`attribute :>> uid = 4;` is member-named `uid`), a referenced feature, or a chain's last link (pilot `Element::name → effectiveName()` → `Feature::namingFeature`). Binary connector/succession ends take their computed positional names (`source`/`target`, `earlierOccurrence`/`laterOccurrence`), payloads `payload`, return parameters `result`, subjects `subj`, objectives `obj`.
- **`isComposite`/`isReference`**: SysML usages are composite by default, except the inherently referential metaclasses (attribute, reference, enumeration, binding/succession-as-usage, event, exhibit, include, perform — pilot `*Impl` constructors), `ref`/directed/`end` declarations, usages with no featuring type, and non-subport ports. `isReference` derives as the negation; the `ref` keyword round-trips exactly.
- **Membership-implied directions**: subjects/actors/stakeholders are `in`, return parameters `out` (pilot `ParameterMembershipAdapter`).
- **Metadata usages** are AnnotatingElements owned via **OwningMembership** even in type bodies (unfeatured, referential); a bare about-less `@M;` member canonicalizes to the `#M` prefix shape.
- **Comment/doc bodies** are normalized like the pilot's `ElementUtil.processCommentBody`, iterated to a fixpoint (the round-trip gate requires idempotence); requirement `text` derives from documentation bodies.
- **Classification/cast/extent expressions**: type references are owned parameter Features with a `FeatureTyping`; casts use a ReturnParameterMembership; the implicit subject spells as a self-reference; the `meta`/`@@` left side as a MetadataAccessExpression.
- **Connector ends** are ReferenceUsages (pilot `ConnectorEnd` rule), succession ends included; interface ends are PortUsages (pilot InterfaceEnd/DefaultInterfaceEnd). Flow ends follow the pilot's `FlowEnd` rule (prefix ReferenceSubsetting when spelled, plus an owned ReferenceUsage whose FlowRedefinition targets the last step).
- **Multiplicity bounds**: the pilot's `MultiplicityBounds` rule owns the bound literals directly under the MultiplicityRange (no operator wrapping).
- Variations (and enum definitions) are implicitly abstract; exposes force `isImportAll`; chain/index/collect/select expressions carry their fixed `operator`; multi-step chain expressions flatten to a single FeatureChainExpression + OwnedFeatureChain member.
- Every SysML port definition owns its implicit `~P` ConjugatedPortDefinition (OwningMembership, declaredName `~P`) with the PortConjugation pointing back at the original.
- Satisfy `by` targets bind per the pilot's `SatisfactionFeatureValue`; named invocation/constructor arguments own the pilot's `ParameterRedefinition` of the callee's parameter; positional arguments take the callee's `in` parameter names (in-document callees); binding connector ends take the `Links::SelfLink` positional names `thisThing`/`sameThing`.
- Implied relationships are emitted when resolving against `--lib`, following the pilot's anti-redundancy rule.

## Library element IDs (KerML 9.1)

Top-level standard-library packages get `uuid5(NameSpace_URL, prefix + escapedName)`; every named — including *effectively* named (KerML 8.2.3.5) — element under fully-named ancestry gets `uuid5(topPackageUuid, qualifiedName)`; the owning membership of such an element gets `…qualifiedName + "/owningMembership"`; alias Memberships get the alias's qualified name; each document root Namespace is `uuid5(top, "")`. The norm's *positional* ids for unnamed elements are 1-based `ownedRelationship` indices that count an implementation's implied-relationship closure, so they are not portable across implementations; such elements are never name-referenceable and keep deterministic path-based ids here (`cargo run --example libids` prints the table).

## Known gaps

- Implied end-**Redefinition elements** for binary connector ends are not emitted (the positional *names* are derived, the relationships are not).
- `mayTimeVary`/SysML `isVariable` stay passthrough-null (their derivation needs library conformance walks).
- Named invocation arguments keep the `memberName` spelling in some paths; the pilot additionally owns a `ParameterRedefinition` inside the argument Feature (no corpus coverage to gate a fix).
- The implicit `~P` `conjugatedPortDefinition` owner-side property is tracked in `tests/xmi_audit.rs`.

## Diagnostics philosophy: errors vs. warnings

Errors are reserved for what is *provably* wrong (syntax, illegal body context, a metadata feature typed by a resolved non-metaclass, provably violated multiplicity…). Unresolved references are **warnings** — the resolver covers 99.9%+ of the reference corpus, and conforming models must not fail on the long tail or on genuinely incomplete load paths. Pipelines that must refuse incomplete models (e.g. gating a Flexo commit) opt in with `check --strict`, which treats any finding as failure. Partial models are not second-class: in full-form output unresolved references become deterministic dangling `@id`s plus schema-valid `TextualRepresentation` recovery annotations by default, so converting the payload back to text restores the exact source references. Recovery is independent of the optional Flexo envelope.

## Compact-form CBOR

The binary form (`CBOR.md`) is a byte-level re-encoding of the compact interchange element array — schema-equivalent by construction, since decoding reproduces the exact compact JSON `Value` before any consumer sees it. It adds no conformance surface of its own: everything above about representation rules, library element IDs, and partial models applies unchanged. The payload header carries the generated-table version; a decoder refuses a version it does not carry rather than silently mis-indexing, and the reserved id-elision flag bit is likewise refused by decoders that predate it.

## Element ids (scheme 1)

User-element `@id`s are graph-derived (see `IDS.md`): chained UUIDv5 from the document root through ownership, with name-based segments for membership-owned named elements — chained past the membership's ordinal, so a named member and its membership derive from the owner and the member's name alone — and positional segments otherwise. Consequence for interchange consumers: every non-root id of a compact payload is recomputable from structure + names (`ids::derive_ids`), and re-emitting a model from text is id-stable under edits that do not move or rename the element's own ancestry — including inserting members before it. Payloads that carry explicit ids lift verbatim. Library element ids are unchanged (normative KerML 9.1 where named).
