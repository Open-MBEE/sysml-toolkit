# sysmlv2-viz

PlantUML emission for OMG SysML v2 / KerML models, over the [sysmlv2](https://github.com/Open-MBEE/sysml-toolkit) toolkit's resolved model. Seven deterministic views, each tolerant of unresolved references — feed the text to any PlantUML build for SVG/PNG; this crate has no rendering stage of its own.

| View | Renders |
|---|---|
| `tree` (default) | structure: packages, definitions, usages with attribute compartments (evaluated `= value`), composition / typing / specialization edges |
| `interconnection` | parts as nested blocks with ports (definition ports render per usage box); connection / interface / binding / allocation / flow edges between resolved ends |
| `state` | state machines: composite states, `[*]` entry, transitions labelled `trigger [guard] / effect`, entry/do/exit lines |
| `action` | action flows: actions, fork/join/choice control nodes, successions, dashed payload-labelled flows |
| `sequence` | lifelines and `->>` messages, ordered by the events' succession partial order, boxed per owning definition |
| `case` | use cases: actors, `<<subject>>` rectangles, objectives as notes, `«include»` edges |
| `mixed` | everything on one canvas: structure, connectors, behavior edges, cases, typing |

Cross-view options (`VizOptions`): comment/doc bodies as attached notes, prefix metadata as extra node stereotypes, `^`-marked inherited compartment lines, referenced library types as marked nodes, `«import»` edges, polyline/ortho line routing, a stereotype-keyed color palette, and `[[hyperlink]]` templates (`{file}`/`{line}`/`{col}`/`{qname}`/`{id}`) that PlantUML carries into rendered SVG — diagram nodes click through to their source declarations. Options are built from `VizOptions::default()` with one `with_…` setter per option, so a later option does not break callers. `View` and `LineStyle` carry their host spellings (`tree`, `interconnection` / `ic`, …) through `FromStr`, `Display` and serde, so a host does not have to spell out its own table.

```rust
use sysmlv2_model::{json::ResolvedModel, model::Model};
use sysmlv2_viz::{plantuml, View, VizOptions};

let mut model = Model::new();
model.add_source("demo.sysml", "package P { part def V; part v : V; }");
let mut resolved = ResolvedModel::build(&model);
let opts = VizOptions::default().with_view(View::Interconnection);
let text = plantuml(&mut resolved, None, &opts);
// text is `@startuml … @enduml`; pipe it to plantuml.jar for SVG/PNG
```

The same emitter backs the CLI verb (`sysmlv2 viz --view …`) and the Python binding (`Session.to_plantuml(view=…)`); worked tours with real outputs live in the repository's `CLI.md` and `SDK.md`. Every view is gated by goldens and a whole-corpus sweep validated against a real PlantUML build (`cargo run -p sysmlv2-viz --example vizsweep`, then `plantuml.jar -checkonly`).

The structured `graph` API supports tree, interconnection, state and action
views. Interconnection endpoints retain their occurrence context: a flow through
`a.p.value` attaches to the rendered port on `a`, rather than the separate
`value` declaration on the port type. When deeper features are not drawn,
`sourcePath` / `targetPath` retain the complete feature-chain labels; PlantUML
emits the same information as end labels. Unresolved connector ends do not form
shortcut edges between the remaining ends.

Behavior successions use the declaration order of their owning body, including
parts and packages that are transparent in the view. Bare `then` members follow
the preceding action, inline targets are resolved to their following declaration,
and consecutive `then` members after a fork preserve fan-out. Initial markers
reset that context; unresolved markers do not become initial transitions.

## License

Apache License 2.0 — Copyright 2026 Open-MBEE.
