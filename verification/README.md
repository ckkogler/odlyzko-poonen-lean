# Verification evidence

The complete default build and statement audit passed for 288 authored modules,
1057 proved declarations and 136 definitions or structures. Their axiom lists
contain only `propext`, `Classical.choice` and `Quot.sound`. All 287 previous
proof modules are unchanged; a new module combines the irreducibility limit and
leading reducibility asymptotic into the statement of Theorem 1.1.

Challenge states three main theorems and three preliminary model lemmas.
The actual strict Comparator accepted all six declarations, and NanoDa and
Lean's default kernel accepted their exported proofs. Explicit definition bodies
are recursively compared; no definition holes are permitted. Challenge's
intentional placeholders are excluded from the proved Solution import closure.
Metadata validation passed, and licensee 10.0.0 detected exactly 0BSD. Compilation
may emit nonfatal linter messages; passing does not mean warning-free source.

## Current records

- `current-source-snapshot.json` identifies the 296 exact Lean and build/comparison
  configuration files checked by the completed runs.
- `current-checks.json` records actual exits, timestamps, output hashes, the six
  compared declarations, the full library scope, and the successful hosted
  verification of the compiler-portability update.
- `current-fresh-checkout.json` records a fresh build of all authored modules
  on a separate GitHub runner. Only the recorded dependency cache was reused;
  all nine pinned revisions were checked when that cache was populated, and
  every authored module was freshly compiled. The complete statement output
  was identical to the reviewed local run. The record identifies the successful
  hosted workflow and its exact commit.
- `current-semantic-review.json` records the developing agent's review of the
  actual definitions and compared types, and reuse of the source-bound review
  for unchanged declarations. This is not independent human review.
- `current-policy-check.json` reuses the recorded September 22 review of current
  public rules, schema and tool profiles, with updated Challenge size and scope.
- `current-final-tree-checks.json` records final metadata, license, coverage and
  authored-tree checks after the documentation and evidence updates.

The fresh checkout commit precedes the final documentation/evidence commit.
All checked Lean and build/comparison configuration bytes remain identical.
The reviewed CI and verifier-wrapper changes use Lean's bundled compiler by
default and preserve explicit caller overrides. Final metadata and packaging
checks are recorded separately. These receipts
summarize actual checks; they are not proof certificates.

## Historical records

`history/2026-09-22-35-claims/` preserves the earlier 287-module,
1056-declaration, 35-claim verification and its independent fresh build. Those
records certify only their recorded snapshots.

`proof-source-baseline.json` identifies the 182 preserved original proof modules.
`official-source-snapshot.json`, `official-checks.json`, `standalone-checks.json`
and `classification-check.json` retain evidence for the earlier 182-module,
672-declaration, 20-claim development.

Reproduction commands and tool prerequisites are in the main README and pinned
CI. Each check saves its actual output, exit, timestamps and source snapshots.
Large raw logs stay outside the committed submission. Recorded GitHub checks
identify their exact commit. No independent human review, registry acceptance
or adversarial registry confinement is claimed.
