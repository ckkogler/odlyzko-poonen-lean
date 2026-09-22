# Verification evidence

The current records cover 1056 proved declarations and 136 definitions or
structures in 287 modules. The default build and complete statement/axiom audit
passed. Only `propext`, `Classical.choice` and `Quot.sound` occur in the theorem
axiom lists. Full statement output agrees byte for byte with the output reviewed
for the finite model, quantifiers, constants, floors, exponents and uniformity.

The actual strict Comparator accepted all 35 independent Challenge claims.
Both NanoDa and Lean's default kernel accepted the exported proofs. Explicit
definition bodies are recursively compared; no definition holes are permitted.
Challenge's intentional theorem placeholders are excluded from the proved
Solution import closure. Metadata validation passed, and licensee 10.0.0
detected exactly 0BSD. Compilation emitted nonfatal linter messages; a successful
build is not a claim that the source is warning-free.

## Current records

- `current-source-snapshot.json` identifies the exact Lean and build/comparison
  configuration bytes checked by the completed runs.
- `current-checks.json` records actual exits, timestamps, raw-output hashes and
  the 35 compared theorem names.
- `current-fresh-checkout.json` records an actual fresh build of all authored
  modules while the original project path was unavailable. Only the ordinary
  dependency cache was reused. All nine dependencies had exact pinned revisions,
  unchanged tracked sources and contained paths; the full statement output was
  identical to the official run. The receipt identifies the checked commit and
  confirms restoration of the original project and dependency cache.
- `current-semantic-review.json` describes the developing agent's review of the
  actual definitions and full compared theorem types. It is not independent
  human review.
- `current-policy-check.json` records the policy and schema review, including
  exact project/Mathlib toolchain agreement and the pinned verification tools.
- `current-final-tree-checks.json` records the post-documentation metadata,
  license, full coverage-index and authored-tree checks.

The fresh checkout's commit precedes the final documentation and evidence
updates. Those updates leave every checked Lean and build/comparison
configuration byte unchanged; final metadata and packaging checks are recorded
separately. These receipts summarize actual checks and are not proof certificates.

## Historical records

`proof-source-baseline.json` identifies the 182 preserved original proof modules.
`official-source-snapshot.json`, `official-checks.json`, `standalone-checks.json`
and `classification-check.json` retain evidence for the earlier 182-module,
672-declaration, 20-claim development. They certify only their recorded
snapshots; use the `current-*` records for the completed 287-module development.

Reproduction commands and tool prerequisites are in the main README and pinned
CI. Each check saves its actual output, exit, timestamps and source snapshots.
Large raw logs stay outside the committed submission. No remote CI, independent
human review, registry acceptance or adversarial registry confinement is claimed.
