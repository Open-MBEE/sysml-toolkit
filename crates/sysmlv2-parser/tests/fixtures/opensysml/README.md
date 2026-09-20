# OpenSysML negative fixtures

Unmodified source fixtures from Open-MBEE/OpenSysML, pinned by `provenance.json`.
The Apache-2.0 license is retained in `LICENSE`; each source keeps its upstream
comments and references. `probes` ties examples to named validator rules;
`negative` contains the pilot-rejection corpus. Upstream's recorded pilot
adjudications are useful evidence, not an independently rerun oracle here.

The tests run each file independently through four stages — parsing,
body-context validation, referential checks, and semantic checks — with every
recorded row labelled by stage. `baseline.json` is the run without a standard
library: referential rows there are missing dependencies, so a file whose only
rows are referential stays **unknown without library**, and an empty list is
unknown too, not a successful rejection, except for explicitly adjudicated
accepted models. `baseline-library.json` is the run against the standard
library, where a referential row counts like any other. In neither file does a
nonempty list by itself prove that the diagnostic implements the fixture's
intended rule; the contract manifests and the paired checker tests do that.

Regenerate only after adjudicating every changed result:

```sh
UPDATE_OPENSYSML_BASELINE=1 cargo test -p sysmlv2-parser --test opensysml
```

The `opensysmlcheck` example prints the full-library run as JSON. It shares
the stage runner (`tests/support/census.rs`) and the contract check with the
tests, so its "unknown" means the same thing as the baseline's. The tests check
the fixture census; remove or modify no case to make a gate pass.
Implementation gaps are deliberately visible in the checked-in baselines.

`static-contracts.json` and `negative-contracts.json` register 147 intended
rejections and one adjudicated acceptance. The latter preserves the official
GradePoints enum/Real literal-value idiom despite an upstream pilot-negative
expectation. Paired tests check clean legal neighbors, exact diagnostic category
and meaningful source locations. The full-library baseline test and the
reporting example both fail if any registered contract regresses; neither
equates an unrelated diagnostic with success.
