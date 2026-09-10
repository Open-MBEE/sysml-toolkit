# Element identity: graph-derived ids (id scheme 1)

How this toolkit assigns `@id`s to **user-model** elements. The scheme makes every user element's id a **pure function of the interchange graph**, so a consumer holding a compact element array can recompute every id from structure + names alone (the enabler for CBOR id elision) — and so ids survive edits: renaming or inserting a member never shifts unrelated siblings, and named members chain **past their membership's ordinal**, so a mid-body insertion re-derives none of the named siblings after it and an insertion-sized edit stays an insertion-sized delta.

On the wire, this derivation is stamped as **id-scheme 1** in the payload header of the binary interchange form (`CBOR.md`): id-elided payloads (snapshot or delta) refuse a scheme they don't carry, while explicit-id payloads ignore the stamp entirely.

Standard-library elements are unaffected: named library elements keep their normative KerML 9.1 name-based UUIDs, positional library elements keep their sealed-snapshot ids.

## The derivation

Every user element's id chains from its owner:

```
id(root)     = explicit — the document root Namespace is the anchor
id(child)    = uuid5(id(parent), segment(child))
```

`uuid5` is RFC 4122 v5 (SHA-1) with the parent id as the namespace. The root Namespace has no name in the payload (it stands for the source unit), so its id stays assigned, not derived; everything below it derives.

**Segments.** For a relationship `rel` at position `i` of its owner's `ownedRelationship` array:

- a **single-member membership whose member has an id-name** chains past the membership: the member `k` takes `"::" + escape_name(idName(k))` **directly under the owner**, and `rel` takes `"m"` **under the member** (`id(rel) = uuid5(id(k), "m")`) — the shape of the normative library rule, where an element's owning membership derives from the element, not from a position. Neither id references the ordinal `i`;
- an **alias membership** — a bare `Membership` that owns no element and carries `memberName`/`memberShortName` — takes `"::" + escapedName` (the alias is a *named relationship*);
- every other relationship takes `"r{i}"`.

For an element `k` at position `j` of `rel.ownedRelatedElement`, when the first rule did not apply:

- if `rel` is a `*Membership` and `k` has an **id-name**, the segment is `"::" + escape_name(idName(k))` under `rel`;
- otherwise `"e{j}"` (elements under non-membership relationships are positional regardless of naming, mirroring the normative library rule).

**Id-name.** `declaredName`, else `declaredShortName`, else the **graph-effective name** (KerML 8.2.3.5): the name of the first `Redefinition`/`ReferenceSubsetting` target among `k`'s owned relationships, in `ownedRelationship` order — resolved *through the graph*, iterated to fixpoint (a member may take its name from another effectively named member). A target outside the document resolves through the library name table; a hermetic `{"@ref": name}` target *is* the name. No resolvable name → positional segment.

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
