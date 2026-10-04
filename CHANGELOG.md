# Changelog

## v0.10.2

### Fixed

- A feature with no value of its own takes the value of a feature it subsets when the two must be equal: it has at least one value and the subsetted feature at most one. `subject :>> crawler :> tinycrawler;` in an analysis performed once (`[1]`) now reads `tinycrawler`, so the analysis result evaluates as it does with `= tinycrawler`. A subsetting feature that says more than the subsetted one, with members of its own or a type the subsetted feature does not have, keeps its own reading.

## v0.10.1

### Added

- Satisfaction claims are verified as a whole. Each `satisfy R by x;` gets one verdict, positioned on its statement: in `sysmlv2 verify` output (with the constraints behind a claim that is not satisfied listed under it), in the WebAssembly `verify` report's `satisfactions`, as a language-server code lens, and from Rust `check::satisfaction_claims`. A requirement's assumptions imply its required constraints and the requirements it composes, so a claim whose assumption fails holds vacuously, and a claim is undecided only when the known verdicts do not settle it. `not satisfy` inverts the verdict, and a requirement with no constraint to evaluate leaves its claim undecided.
- Rust `check::constraint_checks` returns the ordinary constraint verdicts over an already resolved model.

### Changed

- Quantity values evaluate sooner in models built on a prepared library. Preparing the standard library now records the dimensions of its quantity types and the expansions of its units (it had looked for the measurement unit type in the wrong package and recorded none), builds on the prepared library keep those records through every resolution pass, and an evaluation in progress reuses a unit's expansion unless a feature that expansion reads is being evaluated or overridden. On a model that imports the quantity libraries, the first inlay hint after an edit takes about a fifth less time and the first hover about a third less; preparing the standard library from its sources takes about 0.4 s longer.
- Hover, inlay hints, and code lenses answer sooner after an edit to a model built on a prepared library. A session derives the implied specializations and positional redefinitions of its own elements only, on top of those its prepared library derives once for its own; the language server's inlay hints and code lenses and WebAssembly `Session.verify` verify the session's resolved model instead of resolving the model again; and the typing, membership, and element-by-id indexes extend the prepared library's instead of covering every element again. On a model that imports the quantity libraries, the first hover or inlay hint after an edit takes a few milliseconds instead of a few hundred. An evaluation that ran out of steps deriving those relationships for the whole model may now complete.
- Inlay hints and code lenses answer sooner on models with satisfaction claims or calculations. A claim's subjects are read from the memberships of its requirement's types, and whether a calculation runs statements is answered through the specialization index, instead of scanning every element or every specialization, the standard library's included, on every verification. On a model that imports the quantity libraries, this takes about a third off the first inlay hint after an edit.
- Sessions on a prepared library build, check and plan sooner after an edit. The semantic checks pass over the library's elements and specialization rows without testing them; a session keeps the library's part of its lookup tables (per-scope lookup caches, relationship owners, specializations and multiplicities by element, chain redefinitions) instead of rebuilding it over the library's rows; its positional planning reads what the library's planning derived for the library's types instead of planning them again; and the inherited memberships of the library's scopes are read from the library's own build. On a model that imports the quantity libraries, a session builds in half the time, the WebAssembly `Session.check` takes about a third of the time, and the language server's first hover and first inlay hint after an edit about a third.
- `sysmlv2 verify` reports each satisfaction claim once, at its `satisfy` statement, instead of once per constraint at the requirement's constraint; the tally counts claims. A plain `constraint` member of a requirement is no longer part of the requirement's satisfaction (its `require` and `assume` members, assertions and nested requirements are).

### Fixed

- An unnamed usage that only references another feature (`satisfy R by x;`, `assert c;`) no longer answers a simple name. Two claims on a requirement declared in an enclosing namespace each resolve `R` to the requirement instead of to each other; a qualified path still reaches such a usage through the spelling it references.
- A claim that declares its own requirement (`satisfy requirement : R by x;`) is checked against `R`'s constraints; it was skipped.
- A valued redefinition of a feature chain (`attribute :>> chassis.mass = 2.5 [kg];`) supplies its value when the chain is read through the redefining part: directly, inside an inherited formula such as `totalMass = chassis.mass`, and from parts that specialize it.

### Upgrade notes

- `sysmlv2 verify` reports each satisfaction claim on one line at its `satisfy` statement (`SatisfyRequirementUsage, satisfies R by x`) instead of one `satisfies R` line per constraint at the requirement's constraint. The constraints behind a claim that is not satisfied follow it on indented lines that the tally does not count, so the tally counts each claim once. The WebAssembly `verify` report's `summary` now counts claims alongside constraints. Tools that read claim verdicts should read the claim lines, or the report's `satisfactions`.
- A plain `constraint` member of a requirement no longer takes part in a claim's satisfaction, so a claim that failed only on one of them may now be satisfied or undecided. Declare the member `require constraint` (or `assume constraint` for a precondition) to keep it in the check.
- Rust `VerifyReport` gains a `satisfactions` field, and `SatisfactionInfo` gains `unit`, `span`, `by`, `negated` and `nodes`. Code that constructs these structs or destructures them exhaustively needs updating.

## v0.10.0

### Added

- Checked property access in Rust, Python, and WebAssembly, with consistent scalar and collection shapes, defaults, enumeration values, and reference types. Rust `derived_exact` rejects approximate or unavailable answers instead of presenting them as exact.
- Generated property and operation declaration catalogs for SDK generators, including declaration identities, overrides, parameter types, and multiplicities. Rust can invoke supported operations by declaration identity.
- Strict full-form JSON export in Rust, Python, and WebAssembly, with checks for property fidelity, unique element IDs, and local-reference closure. Missing semantic evidence reports an error instead of producing placeholder values.
- Checked Rust reports for type features, inputs and memberships, specialization, featuring, variability, end constancy, model-level evaluability, and collection cardinality. Unsupported or incomplete cases remain explicitly qualified.
- Checked `Definition.usage` and `Definition.directedUsage` include supported inherited usages. Checked Usage typing now covers ordinary noncomposite usages and composite occurrence, item, and part usages in supported structural and nested usage contexts; nested compositions require a complete owner type proof. Missing specialization paths, cycles, unsupported contexts, and exhausted budgets still report incomplete evidence.
- Evaluation reports that retain failures suppressed by inherited-default fallback, including the declaration, receiver, and underlying cause. Existing result-only evaluation remains available.
- Opt-in `CanonicalV3` graphs in Rust, with owned conditional operands, constructor results, and supported expression bindings, typing, and implied relationships. Format-aware sessions, prepared libraries, snapshots, resolvers, and deltas preserve the selected graph contract; an explicit migration API reports changed identities.
- Editor member completion after indexed values, invocations, qualified and global receivers, conjugated port types, and quoted names after a dot. Member completion follows the source dialect and offers the `metadata` keyword after eligible receivers.
- Editor completion on `[` in unit positions, with units compatible with the declared quantity listed first. Names can also be completed inside multiplicity bounds and filters.
- Editor completion after a qualifier lists what the namespace re-exports, so `ISQ::` offers `MassValue`. Import paths offer `*` and `**` after a qualifier and rank packages ahead of their members.
- Editor signature help for calculation, function, and constraint invocations, including calls on a feature chain (`vehicle.ke(`), with standard-library types spelled where the call is read and the active parameter chosen by position or by name, and a quick fix that removes a stray `;`.
- Editor completion that follows the position being typed. A typing offers the definitions its usage kind admits, a specialization offers its own kind first, redefinitions and successions offer the enclosing element's features first (including a library base's `start` and `done`), metadata positions offer metadata definitions, a Boolean value offers `true` and `false` first, and units rank first where the declared type is a unit type. Shorter names rank first within a group. The enclosing element's features carry their documentation and their own kind, as the same names do everywhere else.
- WebAssembly `LspServer.withPreparedLibrary` and Rust `PushServer::with_library` build a language server on a prepared library, so a session normally reuses the library's prepared resolution instead of re-parsing the library's sources and rebuilding its graph.
- The npm package includes `stdlib/sysml-library.prepared.gz`, a prepared standard-library graph. WebAssembly `PreparedLibrary.fromSnapshot` and Rust `Library::prepared_snapshot` load it without resolving the library at startup or retaining its parsed syntax trees. Incompatible snapshots are rejected so the caller can prepare from source.
- WebAssembly `PreparedLibrary.fromSnapshotStream` reads a snapshot from the host's `Uint8Array` in chunks instead of copying the whole snapshot into module memory. Rust `PreparedLibrary::from_chunks` and `Library::prepared_snapshot_chunks` expose the same chunked loading, including checksum verification.
- WebAssembly `Session.settledOutcomes` and `Session.fromSourcesSettled` start a session on a prepared library from the outcomes a previous session settled on, as the language server's sessions do after every edit: a unit that resolves as it did is confirmed in one pass. The outcomes are a handle of their own, so a host frees the previous session before building the next, and the session answers as one built without.
- Text reports from `check`, `lint`, and parse errors mark each finding's span with carets on the line below its source line.
- Rust `LibraryCache::graph_format` reports the graph format a library resolution recording was made for.
- Constraint verification names a usage that is a collection only by the implicit default (an attribute, item or port a package owns, written without a multiplicity, subsetting or redefinition) and says to declare `[1]` for one value, instead of reporting a non-scalar or unknown cardinality. A parameter, connector end, reference usage or explicitly open multiplicity keeps the cardinality wording.

### Fixed

- A view-directed diagram (`viz --element` naming a view, or the WebAssembly `toGraph` and `toPlantuml` given one) no longer draws the members a view exposes through inheritance as nodes of their own. A part's exposed members include the ones it inherits, so `expose rig::**;` over `part amp : Amp;` also exposes the ports `Amp` declares; they render once, on `amp`'s box, rather than again as standalone port boxes. Likewise, `expose rig::*;` no longer draws a node for every feature `rig` inherits from the standard library.
- Intrinsic evaluation dispatches by resolved standard-library identity. Aliases work, while user declarations, inaccessible functions, and unrelated names no longer acquire intrinsic behavior by spelling alone.
- ID-bound references participate consistently in semantic queries, evaluation, checks, filters, and solving. Source-document and declaration identities survive lookup, replay, and symbolic translation.
- Imported and inherited members retain their membership identities, order, visibility, and alias provenance. Import distinguishability, redefinition hiding, and recursive package lookup respect the lookup context; bounded queries report incomplete expansion instead of silently truncating it.
- A parameter, end or result inherits the members of the feature its position pairs it with in its owner's generals, as the redefinition KerML implies reads: `in q;` declared first under `action def Swapped :> A { in q; in p; }` offers the members of `A`'s first parameter, `in x;` under a specialization whose general names it `p` offers them too, `return s;` offers those of the general's result, and `end f1;` those of the general's first end. A directed parameter used to take the members of the *same-named* feature its owner inherits — and, where no general declared one, of any element of that name in an enclosing package, an imported one, or the root namespace — while a renamed parameter, a result and an end inherited nothing. The derived `type` of a feature redefined only by position follows that redefinition when its target is a user feature (`Swapped::q` is typed as `A::p` is); implied redefinitions of library features stay out of `type`, with the implied library subsettings.
- A build that replays a library resolution snapshot resolves again every library reference that a workspace's root names can change, including one that reached a missing root name only through what resolving another reference computed: a type's specialization bases, a namespace's imports, or that reference's own outcome. Such a reference used to keep its recorded outcome, so an inherited member's type could stay unresolved after the workspace imported the base that declares it.
- A namespace's imports and a type's specialization bases resolve the same way whichever reference first needs them. A namespace import whose target is visible only through a sibling membership import (`import X::*; private import Other::X;`) could stay unresolved, together with the names it imports.
- A redefinition in a type with explicit generals resolves in those generals, in the order they are written, in every model. Without a library it used to resolve in the declaring type unless other content in the model enabled that rule, so redefining a general's private feature was reported as a blocked reference and a feature found in two generals as ambiguous.
- A build that replays a library resolution snapshot, or builds on a prepared library, resolves library references as a cold build does when the workspace adds a root import, or when only the workspace's content makes resolution consult redefinition headers and inherited members in later passes. Such a build could keep outcomes from resolving the library alone, such as a redefinition of a sibling feature instead of the general's.
- Required implied specialization paths remain reachable. Supported generated relationships and positional end, parameter, and result redefinitions are published consistently across semantic queries and export, with prerequisites checked before publication.
- Feature, Step, and Metaclass lookup follows their required standard-library bases, exposing inherited members such as `that` and `annotatedElement`. Step and binary connection roles require unique, correctly typed canonical library identities; unrelated declarations or duplicate identities cannot supply them.
- Connection and interface definitions with exactly two owned ends inherit their binary library members during lookup, so end redefinitions resolve `source` and `target` and unnamed ends recover their inherited names. Inherited ends alone do not trigger an additional binary base.
- KerML flows and successions use their own required library bases instead of SysML usage bases; the more specific flow bases are added only when their owned-end conditions hold. Composite usages retain the required subobject, suboccurrence, subitem, and subpart specialization paths in supported owning contexts.
- Literal, null, metadata-access, reference, and invocation results use the appropriate library and declaration identities. Generated feature defaults, result bindings, and local featuring no longer depend on placeholder relationships.
- Connector end names resolve in their owning scope. Generic relationship endpoints agree with connector-specific properties, ordered repeated endpoints are preserved, and authored featuring and end-constant defaults retain their meaning.
- Connector-end multiplicity bounds resolve declarations in the connector body without changing the scope of end targets. An owned cross feature's specialization and multiplicity references resolve in its owning end's scope, including members inherited through that end's type; missing or ambiguous members remain unresolved.
- Explicit metadata `about` associations participate in annotations, reflection, and filters alongside prefix metadata. Exposures preserve their membership and filter identities.
- Anonymous feature chains no longer take the final target's name. Contextual naming follows the semantic declaration.
- Semantic namespace lookup excludes anonymous reconstruction locators, so they cannot hide or conflict with declared members. Unresolved-reference reports now include ambiguous references as well as missing ones, with their source spans.
- Full-form export preserves semantic reference targets and fills absent owned scalar properties from their declared defaults, while retaining explicitly supplied values and computed end flags. `ConjugatedPortTyping.portDefinition` returns the original port definition as a single reference. Structural ownership reads follow published relationships consistently in both graph formats.
- Interchange round trips and edits preserve owned expression graphs, anonymous payload identities, source dialects, supplied IDs, and lexical references that resemble UUIDs. Edits that cannot preserve semantic identity fail without changing the session.
- Cardinality uses exact integer bounds from headers, body and named multiplicities, and inherited declarations in the receiver's context. Implicit usage multiplicities are honored; conflicting, cyclic, or unsupported bounds remain unknown.
- Collection size, emptiness, and indexing preserve the distinction between known cardinality and known values. Unknown members and positions remain unknown through chains, tuples, casts, and solver translation.
- Runtime arguments bind to parameter identities. Defaults and nested calls retain the correct receiver and visibility instead of capturing unrelated caller parameters with the same name.
- Invoking a calculation that specializes another binds the arguments to the parameters it declares, then to the inherited parameters none of its own redefine, in the order its generals are written. Only the nearest type declaring parameters used to supply them: with `calc def Diff { in a; in b; return r = a - b; }` and `calc def Sub :> Diff { in x; }`, `Sub(10, 3)` was rejected as having too many arguments and now evaluates to `7`. A calculation with no result of its own evaluates the nearest result its written heritage declares instead of evaluating as indeterminate, while a function-typed parameter still stands for an unknown calculation. As KerML requires, a parameter that explicitly redefines another also redefines the general's parameter at its own position, so `calc def Swap :> Diff { in :>> b; }` takes one argument, which both `a` and `b` stand for; a parameter that merely reuses an inherited name at another position hides nothing, so `calc def Partial :> Diff { in b; }` has two parameters of one name, which the namespace-distinguishability check now reports, no invocation can bind by name, and a name finding both inside a specialization leaves ambiguous rather than shadowed. A general's parameters are its own, then those it inherits after them, so a specialization's parameters pair with inherited ones too: `calc def C :> B { in s; in t; }` over `calc def B :> A { in r; }` and `calc def A { in p; in q; }` has the two parameters `s` and `t`, `t` standing for `q` (it used to have three, `q` still inherited), and `do 'sense temperature' { out temp; }` under an action usage that declares no parameters of its own redefines the one its definition declares. A parameter that redefines one feature by name and another by position (`calc def KE3 :> KineticEnergy { in speed redefines v; }`, whose `speed` also stands for the first parameter, `m`) inherits two measurement references; the unit bracket of an argument binding it measures the quantity the written redefinition spells. The invocation arity check and editor signature help read the same parameters, and Rust `ResolvedModel::callable_parameters` lists them, inherited through written generals, reference subsettings, and the implied library bases alike, without the model-wide positional plan: a requirement without a subject of its own lists its library base's, and a performed action the parameters of what it performs.
- Solving and interval propagation inline a calculation's inherited result as evaluation does: a calculation that declares none takes the nearest one its written heritage declares, read in its own context, so a constraint on `Sub(y, 3)` with `calc def Sub :> Diff { in x; }` constrains `y` instead of staying unknown. Rust `ResolvedModel::callable_body` answers which result an invocation evaluates and which callable declares it.
- A calculation whose generals, equally near, each declare a result evaluates to their common value: every inherited result binds the one result. It used to be unsupported outright; results that differ remain unsupported.
- Multiplicity checks compare bounds without precision loss and diagnose ranges invalidated by receiver values. Solver propagation requires sound evidence before reporting a positive result when definitions are approximate.
- Redefinition diagnostics require complete provenance, explain targets outside the inheritance chain, and distinguish fixed binding overrides from defaults. Queries through an untyped redefining part use that part's value rather than its owned parts.
- Views inherit their rendering from their definition or specialized views, with an owned rendering taking precedence and inherited choices following heritage order. In-place and chained renderings are reported by Rust, WebAssembly `viewInfo`, and view-directed diagrams.
- Qualification minimization handles feature-chain member references and no longer shortens a member import through its own target.
- A `;` where an expression belongs is reported as the missing expression, at the `;`, and still ends the declaration: `attribute x = ;` is reported at its `;` rather than at the next token, and `attribute x = ;;` is no longer accepted with the first `;` taken as an empty value. This applies after `=`, `:=`, and `default`, to an operand, and to a collect, select, or `->` body. SysML no longer reads a bare `;` as an expression body, which KerML never did, so a stray `;` just before a closing `}` is reported by the parser as well: it used to parse as an empty result expression, which only the body-context check rejected, and which a calculation body took as its result.
- Editor completion recovers usable declarations from incomplete sources, including missing terminators and unmatched closers. An unresolved member-access receiver no longer produces unrelated global suggestions. Import memberships are omitted from completion and workspace symbol search; operator functions are omitted from unqualified completion but remain available after a qualifier. Workspace symbol search no longer lists anonymous members by their outline placeholders (`«part»`, `«subject»`), and still finds the named members inside them.
- A member that cannot be read no longer takes its whole document out of editor completion. Recovery blanks only that member, including a value left out, a line that ends mid-expression, and a declaration cut off at the end of the text, so member access and inherited members keep working while an unrelated statement is broken.
- Accepting an editor completion no longer appends a statement terminator. Insert and replace ranges cover whole words and quoted names while preserving bracket repairs; multi-word matching handles Unicode and incomplete quotes without keeping stale suggestions open after a space.
- Editor automatic imports and import quick fixes name the conventional re-exporting package (`ISQ::MassValue` rather than `ISQBase::MassValue`) and are omitted when an existing import already provides the name through a re-export. Ambiguous, filtered, and private re-exports are never offered or imported through, so inserted imports resolve, and a workspace's private members are offered only where they are visible. Aliases complete with the kind of the element they name, and metadata definitions no longer complete as keywords.
- A `;` after the result expression of a calculation, constraint, case, or function body is reported at the `;`, and the expression stays the body's result. A conditional result followed by `;`, previously read as a second, empty result, is now reported.
- Editor completion offers nothing inside comments, strings, and numbers, and only keywords where a declaration's own name is typed. Each document gets only its own dialect's keywords. Statement boundaries are read from tokens, so a `;`, `{`, or `}` in a comment or string no longer splits a statement, and completion and signature help cut the same statement.
- Unit completion and inferred attribute typing use token-aware context, including comments, user-defined quantity types, parameters, and reference units. A unit infers an attribute's type only when it qualifies the whole value, and an untyped attribute's name is not mistaken for a keyword.
- Editor hover on a standard-library callable shows its parameter and return types instead of bare parameter names, and every callable's signature shows a declared multiplicity other than one (`sum(collection: Real[0..*]) → Real`).
- Editor signature help and hover list a callable's inherited parameters after its own — for a definition specializing a callable, or a usage typed by one — with a redefined parameter replaced by its redefinition and each parameter shown with its written type.
- Editor signature help and unit brackets read an invocation's arguments as its inputs, in order, as evaluation binds them: an output declared among the parameters takes no argument's place, so `f(1, |` for `calc def f { out o; in x; in y; }` highlights `y`, and naming an output highlights nothing.
- Editor hover, go-to-definition, and document highlights answer while a document has a syntax error, reading the workspace with its broken members recovered the way editor completion reads it. References, rename, code actions, and refactorings still wait until every document parses.
- Recovery of incomplete sources ends a string, quoted name, comment, or note left open at its own line, telling the literal left open from those written across lines, so the members after it stay usable. A declaration whose header does not parse (`package Fo}o {`, `part def X :> {`) keeps its body's members.
- Editor unit completion ranks units by the quantity the bracket's context names wherever it names one: a comparison or arithmetic operand (`mass <= 1500 [`), the unit another operand carries (`1200 [kg] + 300 [`, including a model's own units), and the parameter a call argument binds, declared or inherited (`KineticEnergy(1500 [`). An operand read on a measurement scale names no quantity for the difference compared with it or added to it (`t1 + 5 [`). The bracket's statement is read where completion starts it, so a body passed as an argument no longer ends the statement, and signature help finds a call typed below a quote left open on an earlier line.
- Editor completion offers a member of a type wherever its simple name finds it: inside the elements its owner types or specializes, at any depth and innermost first, and where an import, a re-exporting package, or a recursive import brings it in. It is no longer offered by that name where the name finds nothing or another element, and a statement is not offered the names it declares ahead of the cursor.
- Editor completion follows the namespace rules for imports and names. An alias whose target another document or the library declares completes and ranks as that element. `import all` brings in every member. A private or protected member no longer hides what a namespace's public imports bring in for its clients, and a member of a private namespace is offered only where it resolves. A scope's imports are judged together, so a name two imports make ambiguous comes with an import that settles it. A usage without a name of its own is found by the name of what it redefines or references.
- Editor automatic imports no longer take a name from references already in the document: where a name finds an element, that element is offered without an import. An inserted import whose first segment another element takes at the insertion point is written from the root (`private import $::Requirements::requirementChecks;`), and restricted names are quoted in the import's annotation.
- Editor unit completion keeps a document's own units, and accepting one declares its quantity type, when another open document declares a package of the same name.
- Editor completion classifies a qualified name by the position it stands in: `attribute x : ISQ::` lists definitions first, and `[SI::` in a unit bracket lists only units, ranked by the declared quantity and without import edits.
- Editor completion offers `then` after an accept in an action body and after an accept's payload type. After a payload it also offers the port (`via`) and, in a transition or a state body, the guard and the effect not yet written. At redefinitions, subsettings, and references the statement's own kind ranks ahead of the kinds specializing it, which stay offered (an individual item redefinition is offered the part its definition declares). A compound keyword (`perform action`, `exhibit state`, `include use case`, `satisfy requirement`, `assert constraint`, `event occurrence`) counts as its specific kind at a redefinition, while subsettings and references rank the plain kind first.
- Corrected copyright and third-party license notices. The npm package includes the bundled standard library's license and notices.
- Text reports show at most 160 characters of a finding's line, taken around the finding with `…` at each cut, instead of the whole line. A model written on one long line used to produce a report the size of its findings times its line: 960 findings on a 12 KB line wrote 12 MB of text, and now write 0.3 MB.
- A build that rejects a stale library resolution snapshot records a fresh one in the same build, where it used to leave that to the next build.
- Overriding a prepared library element's ID rebuilds the identity indexes that previously retained its old ID. Shared structural indexes also account for workspace rows that claim library rows or satisfy previously unresolved library references.
- Shipped WebAssembly and WASI modules remap build-machine checkout and Cargo-home paths, keeping absolute local paths out of panic locations and debug paths.

### Performance

- Reused revision-bound identity and structural indexes, inherited lookup snapshots, and positional traversal storage to reduce repeated graph scans and allocations. Interchange lifting reuses its validated identity index.
- Structural and implied-relationship proofs reuse complete sparse candidate lists instead of scanning unrelated rows repeatedly, keeping large-library checks within the existing work budget while preserving ownership and stale-evidence checks.
- Editor completion parses each source unit once and resolves once per session build. Unit classification and request-level token, bracket, quote, and repair scans are reused.
- Editor completion caches import routes per namespace, rebuilds only the edited document's symbols, and lists re-exported members without their documentation.
- Editor completion answers each position with its own candidates instead of the whole vocabulary, and caches an element's inherited members by the text around its body.
- Editor member access, unit brackets, and signature help reuse a model already built for other text when nothing they read has changed, so starting a new statement no longer rebuilds the model.
- Editor completion resolves an alias's target one name at a time when first needed, judges names at the cursor without copying their paths, and asks once per top-level name whether an import starts at the root. Signature help lexes the text ahead of a call once.
- Reference properties are written as references and the enumeration-valued strings the builder writes most are shared, instead of each being built as an interchange object and parsed back on insert: Apollo session builds 82 → 78 ms cold and 59 → 55 warm, the Vehicle example 48 → 45 cold.
- Session builds on a prepared standard library keep its lookup graph across resolution passes, and builds with a sealed library snapshot take the recorded library targets in every pass instead of resolving the library again. Library resolution snapshots record whether they hold the library's converged resolution (snapshot format 8).
- A root-level import of a user namespace no longer forces the standard library to be resolved together with the workspace when that namespace's own imports are private or protected.
- The structural index behind metadata associations and the structural checks is no longer rebuilt over a prepared library's rows for every reference-resolution pass: the library's rows are scanned once when it is prepared, and a build on it scans only its own rows. A five-unit Vehicle example workspace with metadata annotations builds about 30% faster on a prepared standard library; a 252-unit corpus workspace about 11%.
- Reference resolution keeps the lookup graph its confirming pass read instead of recomputing the metadata associations and building the graph once more after it: a one-file session on a sources-plus-snapshot standard library builds about 10% faster, prepared-library sessions up to 3%.
- A session on a prepared standard library no longer tables the library's rows to assign its own elements' identities: a one-file session builds in about a tenth of the time, a five-unit Vehicle example workspace about 12% faster.
- A session built over the units a previous session resolved starts from the outcomes that session settled on (`Session::from_sources_settled`, `Session::settled_outcomes`), as the language server's sessions now do after every edit: where the edit changed no outcome the build confirms them in one pass instead of resolving from nothing, and otherwise carries the edit's consequences through as many passes as they take. A five-unit Vehicle example workspace rebuilds in 37 ms instead of 56 after a comment, a 252-unit corpus workspace in 194 instead of 539. Answers are those of a session built without.
- A build keeps its element index by id across its resolution passes and, on a prepared standard library, tables only its own rows into it, and the library name tables its identity assignment may read are made once per prepared library: session builds about 7% faster on a five-unit workspace, 5% on the 252-unit corpus workspace.
- Name lookups hash their tables by a cheaper fold, share a scope's cached import list instead of copying it per lookup, and keep a recursive import's sub-scope lists for a pass: session builds about 13% faster on a five-unit workspace, 14% on the 252-unit corpus workspace, 16% on the Apollo model.
- A library prepared from in-memory sources keeps the resolution snapshot it was prepared with, or records one while preparing when the snapshot is unusable, so a session that must resolve the library together with its workspace takes that recording: a workspace root name that completes a library miss replays the library's recorded resolution instead of resolving the library again, and a root filter keeps the recording's element identities while resolving the library's references again.
- `check` locates its findings in one pass over the model's ownership, so its time no longer grows with the square of how deeply an expression nests.
- A model build keeps each element's ownership path, and the hashing that derives the element's identity from it, incremental over its owner's, so the time and memory of a build no longer grow with the square of its nesting depth. Element identities are unchanged. Checking one value spelled as a 960-term `and` chain took 2.7 s and 365 MB and now takes 0.05 s and 29 MB.

### Removed

- Rust `ResolvedModel::calc_params`, which listed only the input names a calculation declares itself. `calc_parameter_bindings` lists every input an invocation binds, inherited ones included, with its declaration.
- The `render` command, view template renderer, and WebAssembly `renderView` method. View information and view-directed diagrams remain available.
- The ambient `Web`, `Template`, `Svelte`, `WebApp`, and `SvelteKit` libraries, and the generator-only `pkg-node/stdlib-core` npm build artifact. User packages with those names are no longer shadowed; `TransformMeta` remains ambient.
- Evaluation of Web DOM navigation members and template slots over imported documents.

### Upgrade notes

- `LegacyV2` remains the default graph format. `CanonicalV3` is opt-in and has been revised in place; regenerate earlier canonical artifacts from source. The migration API converts complete legacy graphs with graph-derived IDs. Regenerate library snapshots and resolvers when changing formats; deltas do not migrate element identities.
- The default ID scheme changes from 1 to 2, changing freshly derived IDs for affected features and their descendants; persisted explicit IDs are preserved. Regenerate standard-library resolver artifacts. Scheme 1 ID-elided snapshots and deltas are no longer accepted; use an earlier toolkit to export explicit IDs before upgrading. CBOR scheme 3 carries canonical graphs, and format-aware readers reject incompatible artifacts.
- Checked properties, operations, and strict export cover supported semantic cases, not every specification derivation. Type-dependent properties no longer claim exact fidelity without complete evidence. Callers must handle typed refusals; best-effort readers remain available, and strict export is not a whole-model conformance check.
- The syntax tree's `ExprKind::BodyTerminator` variant is removed. The parser no longer reads a bare `;` as an expression body, so nothing produced it; drop matches on it. An empty expression body is `ExprKind::Body` with no members.
- Evaluation no longer takes every feature to be single-valued. A feature without a declared multiplicity takes the bounds shared by the features it subsets or redefines (a parameter or connector end also those it redefines by position; a bound that cannot be determined leaves it unknown). Failing those, attribute, item, part, and port usages owned by a definition or usage are `[1]`, and every other feature is `[0..*]`: usages a package owns, reference usages (including parameters written without a keyword, `in x : Real;`), and action, occurrence, requirement, and connection usages. A tuple containing such a feature, or a chain through one, now evaluates as indeterminate; declare `[1]` where a single value is intended for evaluation or solving.
- Text reports add a caret line under each finding's source line. Tools that read findings should use `--format json` rather than parse the text.

## v0.9.1

- Added summary mode for large tree graphs: collapsed containers report hidden element counts, references to hidden elements are grouped with counts, and excess notes are counted on their targets.
- Added configurable member and note limits, with per-container overrides to show every direct member.
- Added WebAssembly controls to expand containers by qualified name or element ID, report unresolved selections, and reveal an element's containing path with `revealPath`.
- Included the pinned Rust toolchain configuration in the public source release.

## v0.9.0

### Added

- Derived-property access in Rust, Python, and WebAssembly for names, ownership, annotations, types, connector ends, behaviors, expressions, requirements, and views. Property catalogs report which values are exact, approximate, or not computed.
- Optional inheritance and import closures in derived properties and full-form export, including implied library inheritance. Closure expansion is opt-in.
- JSON reports for `check` and `lint`, with consistent positions, stages, severities, rule identifiers, fixes, and summary counts.
- Checks for conflicting inherited member names, an `inherited-name-shadow` lint with a redefinition fix, and editor actions to fix all findings of one rule.
- Editor requests to preview and apply package splitting: `sysmlv2/splitPlan` and `sysmlv2/split`.
- Reusable prepared libraries across in-memory sessions, including a WebAssembly `PreparedLibrary` handle, and reusable parsed-source inputs for validation.
- Session checks reuse the session's resolved model without changing lint or unused-import findings; syntax-only checks are available separately.
- Python `Error` and `RefusedError` exceptions; Python checks release the interpreter lock while running.

### Fixed

- Interchange sessions preserve supplied element IDs across loading, edits, and export. Compact and full forms retain the same identities, including references to external elements.
- JSON and CBOR round trips preserve long expressions and owned element graphs. Cycles, excessive depth, and incomplete reconstruction report errors instead of silently dropping content.
- Numeric literals that exceed JSON numeric precision retain their exact text. Full-form output preserves external references and derives names, implied relationships, and connector structure consistently.
- Evaluation keeps type defaults unknown through unbound subjects, references, and inputs, including aliases, nested members, and calculation calls. Fixed formulas use the receiver's redefinitions; unsupported nested solver paths remain undecided.
- Parser handling of accept actions, conditional triggers, `else` branches, word-operator operands, and escaped names and strings. Binding and connector printing preserves ends in both dialects, including one-ended and multi-ended bindings.
- Deep nesting and long operator chains produce bounded diagnostics; parsing entry points reserve sufficient stack space and report reservation failures. Evaluation budgets cover all materialized values.
- Refactorings reject edits to library declarations and blank source names, avoid conflicting renames and overlapping qualification edits, and remove whole member lines correctly with either line ending. Inferred typing fixes account for values and redefinitions.
- Language-server sessions survive malformed requests and recoverable panics, report model and library failures, handle encoded file paths and large offsets correctly, and process documents in a stable order.
- Model-file extensions are recognized regardless of case. CLI output handles closed pipes quietly, and project archives validate offsets and total expanded size.
- Library caches handle concurrent writes and invalid data safely, with clearer failures and fewer repeated warnings.
- CBOR readers reject malformed references, invalid map lengths, and out-of-range integers and type codes without panicking or truncating values.
- Solver propagation continues tightening one-sided ranges, supports enumerations beyond 128 literals, and avoids repeated operand evaluation. Solver failures preserve their causes and clean up child processes.
- Diagram labels, notes, and links escape line breaks, backslashes, and delimiters correctly.
- Generated web libraries pass inherited-name checks; displayed element names follow the specification's naming rules.

### Performance

- Reduced repeated parsing, graph construction, metaclass lookup, import resolution, and full-form export work. Linting, editor diagnostics, binary conversion, and diagram generation reuse indexes and shared data.

### Upgrade notes

- Rust 1.97 or newer is required. Development and WebAssembly package builds use the pinned toolchain.
- Rust diagram options use default construction and setters. Several public error and result types are now typed or non-exhaustive; callers may need updated matches and error handling.
- Compact CBOR marks explicit IDs with a new flag. Sessions with explicit IDs reject ID-elided snapshots and delta export.
- JSON consumers must accept numeric literal values as either numbers or exact-text strings; the string form is a documented departure from the interchange schema.

## v0.8.0

### Added

- Guided lint repairs for incompatible usage kinds, composite port members, unqualified enumeration literals, inaccessible private members, and import visibility, with editor quick fixes and a fix-all action.
- Package splitting into per-child files through the transformation API, `refactor split`, and editor move actions.
- Opt-in repair of parse-broken sources for session construction, with records of removed or appended text and any unrepaired units.
- Diagnostic stages distinguish parse, context, reference-resolution, and semantic findings.
- Inherited-member enumeration and dialect-aware reference spelling in the model API and bindings.
- WebAssembly view information and view-directed diagrams based on exposed elements.

### Fixed

- Generated references and edits quote reserved words for the source dialect.
- Named dependencies, documentation, comments, and textual representations resolve in their namespaces. Inheritance and recursive imports respect lookup precedence and import order.
- Full-form interchange derives ownership, annotation endpoints, and type multiplicity correctly.
- Diagrams resolve library renderings, retain explicitly inherited library ports, omit generic implied ports, and draw nothing for views with no exposed elements.
- Anonymous comments keep their indentation; editor symbols always have nonempty labels; CLI diagnostics handle multibyte text safely.
- Diagnostic rendering and full-form relationship export reuse indexes to reduce repeated work.

## v0.7.2

- Constraint propagation uses exact rational interval endpoints, preserving decimal bounds without rounding drift. Solver witnesses also retain exact rational values.
- Editor and WebAssembly range reports provide marked approximate decimals alongside exact ranges.
- **Rust API change:** `WitnessValue::Real` now carries a rational value.

## v0.7.1

- Fixed diagram occurrence endpoints and implicit action succession, preserving the identity of connected elements.

## v0.7.0

### Added

- Exact rational arithmetic for numeric evaluation, comparisons, unit scales, and solver literals, exposed through Python and WebAssembly. Editor hints mark approximate displays of non-terminating decimals.
- Broader static checks for typing, dimensions, structure, relationships, expressions, connector accessibility, and action/state contracts, plus warnings for declarations that shadow standard-library roots.
- Evaluation limits for steps, ranges, strings, cumulative allocation, and exact-number size.
- WebAssembly lookup of anonymous elements by interchange ID.

### Fixed

- Anonymous redefinitions no longer target sibling declarations. KerML feature chains resolve in the preceding feature's context, and indexing is distinguished from quantity diagnostics.
- Full-form export includes effective qualified names for redefined elements and correct library-element flags. Calculation results receive typing and dimension checks.
- WebAssembly packaging selects the current package when older archives are present; generated web attributes with unrestricted types use `Base::DataValue`.

### Performance

- Prepared library graphs, shared lookup tables, deferred syntax loading, and compact semantic storage reduce library startup, memory use, and repeated validation work. Connector and unused-import checks reuse indexes; failed cache saves warn once per process.
