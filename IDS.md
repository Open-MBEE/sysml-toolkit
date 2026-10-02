# Element identity: versioned graph-derived ids

How this toolkit assigns `@id`s to **user-model** elements. The scheme makes every user element's id a **pure function of the interchange graph**, so a consumer holding a compact element array can recompute every id from structure + names alone (the enabler for CBOR id elision) — and so ids survive edits: renaming or inserting a member never shifts unrelated siblings, and named members chain **past their membership's ordinal**, so a mid-body insertion re-derives none of the named siblings after it and an insertion-sized edit stays an insertion-sized delta.

On the wire, legacy lowering uses **scheme 2** and opt-in canonical lowering uses **scheme 3** (`CBOR.md`). Both use the derivation below; their authored graph shapes differ. ID-elided snapshots and deltas refuse unsupported schemes. Generic explicit-ID decoding retains historical scheme compatibility, while scheme 3 compact payloads additionally validate their conditional and constructor graph shapes.

Named standard-library elements keep their normative KerML 9.1 name-based UUIDs. Anonymous library path IDs depend on the selected lowering contract; regenerate library snapshots and resolvers when changing it.

## Opt-in canonical graphs

Existing constructors retain `GraphFormat::LegacyV2`. Rust clients can choose
`Model::with_graph_format(GraphFormat::CanonicalV3)` or
`Session::from_sources_with_graph_format(sources, library, format)` before loading
sources. Prepared libraries must use the same format; cache entries are separated.
Sessions retain the choice through edits and library reloads.

Canonical lowering inserts an authored `FeatureReferenceExpression` and its
`FeatureMembership` between each lazy operand's `FeatureValue` and expression.
This covers the right operand of `and`, `or`, `implies`, and `??`, and both
branches of `if`. Expression evaluation keeps its short-circuit behavior.
The graph-derived identity of the new wrapper can equal the former operand ID;
the operand and its descendants acquire new IDs. Graph walkers must follow the
owned membership to reach the original expression.

Canonical constructors own one `ReturnParameterMembership` containing an `out`
result Feature. Their argument ParameterMemberships belong to that result, with
named Redefinitions and FeatureValues retained on the argument Features. The
result membership uses the dedicated `result` identity segment and its Feature
uses `e0`; these identities cannot capture the old first argument's `r1/e0`
identity. Argument subtrees acquire new identities under the result. This is an
in-place revision of the unused experimental V3 contract; regenerate earlier V3
artifacts from source.

To migrate a complete graph-derived user document, call
`sysmlv2_model::migration::migrate_conditional_graph(document, external_name)`.
It returns a new compact document, every old-to-new ID mapping, added IDs, and
old-to-new row indices for updating unit-root tables. It refuses malformed or
already-canonical conditional or constructor structures and input IDs inconsistent with legacy
graph derivation. Decode old elided CBOR first. Regenerate normative library
snapshots from source under the target format. Foreign explicit-ID documents
remain loadable under their original contract; this migration does not guess
how their producers assign identities.

Include every document whose inbound references should be migrated in the same
call. Apply the returned mapping **simultaneously** to external inbound references;
sequential replacement is unsafe because old IDs can be reused by wrappers.
External library targets remain external and require the corresponding target
library/resolver version. Migration does not silently rewrite a separate library.

JSON has no format header. Retain the choice alongside the document and use
`load_document_with_format` or
`Session::from_interchange_json_with_graph_format` for replay. These reject a
conditional or constructor shape inconsistent with the selected contract. Existing unversioned
JSON loaders retain their warning/recovery behavior for foreign graphs; unmatched
identities can be lost there, so use the format-aware API to preserve canonical
structure and identities. Format validation is not a general
lossless-import or whole-model conformance certificate. Ordinary constructors continue to load legacy explicit-ID documents. Changing the default requires a
separate release migration; the opt-in is currently exposed through the Rust APIs.

## The derivation

Source-origin end Usage constancy is completed only when checked variability
evidence proves the required value. Imported flags retain their explicit values
and normative absent defaults. The graph migration preserves those flags; it does
not reinterpret an interchange document as source text. Checked reads qualify
unsupported evidence, while compatibility JSON output can retain syntax defaults
in those cases and is not a conformance certificate.

Every user element's id chains from its owner:

```
id(root)     = explicit — the document root Namespace is the anchor
id(child)    = uuid5(id(parent), segment(child))
```

`uuid5` is RFC 4122 v5 (SHA-1) with the parent id as the namespace. The root Namespace has no name in the payload (it stands for the source unit), so its id stays assigned, not derived; everything below it derives.

**Source names anchor documents.** When building a multi-source `Model`, the
text builder seeds each user document root from `"$root/" + source_name` in
its fixed toolkit UUID namespace. `Model::add_source` uses the supplied name
verbatim; it does not make duplicate names unique or normalize paths. Give
distinct documents distinct stable names, preferably project-relative paths
such as `examples/model.sysml` and `validation/model.sysml`, rather than only
`model.sysml`. Reusing a name can create duplicate root and descendant IDs.
Changing a name changes that document's freshly derived IDs; moving a checkout
need not change them if its relative source names stay the same. This is the
multi-source text-builder contract, not a change to explicit root IDs retained
in interchange payloads or standard-library name-based IDs.

**Segments.** For a relationship `rel` at position `i` of its owner's `ownedRelationship` array:

- a constructor's **ReturnParameterMembership owning one Feature** takes `"result"` under the constructor, and the Feature takes `"e0"` under that membership, regardless of effective names;
- a **single-member membership whose member has an id-name** chains past the membership: the member `k` takes `"::" + escape_name(idName(k))` **directly under the owner**, and `rel` takes `"m"` **under the member** (`id(rel) = uuid5(id(k), "m")`) — the shape of the normative library rule, where an element's owning membership derives from the element, not from a position. Neither id references the ordinal `i`;
- an **alias membership** — a bare `Membership` that owns no element and carries `memberName`/`memberShortName` — takes `"::" + escapedName` (the alias is a *named relationship*);
- every other relationship takes `"r{i}"`.

For an element `k` at position `j` of `rel.ownedRelatedElement`, when the first rule did not apply:

- if `rel` is a `*Membership` and `k` has an **id-name**, the segment is `"::" + escape_name(idName(k))` under `rel`;
- otherwise `"e{j}"` (elements under non-membership relationships are positional regardless of naming, mirroring the normative library rule).

**Id-name.** Scheme 2 retains a historical identity label independently of the semantic `name` property. For compatibility, its final fallback includes a generic ReferenceSubsetting target label even when the language gives that Feature no name. This does not confer a normative semantic name. Syntax replay can retain the resolver’s existing locator spelling independently. Changing this fallback would require a new ID scheme and explicit migration. The remaining precedence is `declaredName`, else `declaredShortName`, else the **versioned graph identity label**: the name of the first `Redefinition` target, or the referenced feature under the applicable SysML naming rule — resolved *through the graph*, iterated to fixpoint (a member may take its name from another effectively named member). A target outside the document resolves through the library name table; a hermetic `{"@ref": name}` target *is* the name. No resolvable name → positional segment. An anonymous feature chain does not take the last link's name. Performed actions (including exhibited states and included use cases) and required/assumed constraints name through the referenced feature's `featureTarget`; variants use the reference itself. These specialized reference rules take precedence over an explicit redefinition.

The transition from scheme 1 to scheme 2 changed freshly derived ids for affected features and their descendants. Semantic naming fixes within scheme 2 preserve this versioned identity algorithm. Persisted payloads with explicit ids retain those ids. Scheme 2 stamps the corrected naming rules. Scheme 1 ID-elided snapshots and deltas are refused; decode them with their original toolkit and export explicit-id JSON/CBOR before upgrading. Regenerate standard-library resolver artifacts for scheme 2.

**Collisions.** Named segments claim **owner scope**, first-come in `ownedRelationship` order — member names and alias names share one spelling space under an owner (positional labels live in a disjoint one). A later claimant of a taken segment falls back positional; for a member that means the member **and its membership** both revert to the positional chain (`r{i}`, `e{j}`), keeping the pair consistent. Deterministic in array order.

## Consequences

- **Derivable:** `sysmlv2_model::ids::derive_ids` recomputes every non-root user id from a compact element array + an external-name lookup; the corpus gate (`tests/ids_derive.rs`) holds it equal to the builder's assignment across every golden fixture. This function is the decoder-side twin the CBOR id-elision mode verifies against.
- **Edit stability:** renaming an element changes its own subtree's ids (its membership included — the membership is named by its member); inserting a member disturbs only *positional* later siblings — named members and their memberships chain past the ordinal entirely, so an insertion-sized edit produces an insertion-sized delta.
- **Ids are per-emission, not per-lifetime:** the metamodel wants an element's id immutable for the element's lifetime and set by tooling; under a derived scheme the honest reading is that each payload is a fresh emission — identity *across* commits is owned by the delta machinery (`rebase_ids`, portable applies) and, once elements live in a repository, by the service holding them.
- **Not portable across implementations:** positional segments count this implementation's relationship materialization, like the normative positional scheme they replace. Named-chain ids are stable for any producer that agrees on the segment grammar above.
- **Explicit ids are read back verbatim:** a persisted interchange payload keeps its ids on lift; re-emitting from text derives ids afresh, so external references into stored payloads re-map by qualified name (`Session::id_map_from`).

## Backlog: stable identity across renames

Renaming a named element currently changes its graph-derived id and the ids of its owned subtree. This is deliberate: deriving identity from the graph enables id elision and keeps ordinary insertion deltas compact. Changing it independently would discard those properties, so rename stability is deferred pending an identity-lifecycle design.

The design investigation must compare at least:

- a repository- or session-assigned stable `elementId` paired with a separate graph-derivation key used for CBOR elision and delta matching;
- persistent identity sidecars for text-authored models;
- explicit identity annotations in source;
- rename/move rebasing across snapshots and portable deltas; and
- migration behavior for already-emitted payloads.

No change to the derivation or wire scheme should land until the chosen design preserves deterministic reconstruction, compact internal deltas, and existing explicit-id payload compatibility.
