# Verification evidence

The official default build and full audit checked 672 theorem statements/axiom
lists and 82 definitions from all 182 proof modules. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Complete statement output matches the
reviewed development output byte for byte. Full types and definitions were
inspected for the finite model, quantifiers, constants, floors and exponents.

The actual strict Comparator accepted all 20 Challenge claims. Both NanoDa and
Lean's default kernel accepted the exported proofs. Explicit definition bodies
are recursively compared; there are no permitted definition holes. Challenge's
intentional theorem holes are excluded from the proved Solution import closure.
Metadata and license checks passed; licensee 10.0.0 detected exactly 0BSD.

`proof-source-baseline.json` records preserved mathematical source hashes.
`official-source-snapshot.json` and `official-checks.json` bind the official
checks to exact source/configuration bytes, actual exits and raw output hashes.
These receipts summarize checks; they are not themselves proof certificates.
`standalone-checks.json` records an actual fresh authored build, complete
statement/axiom audit and metadata validation in a clean checkout while the
original project path was unavailable. All nine dependency sources were checked
for exact revisions, unchanged tracked files and contained paths. The complete
statement output was identical to the official run. The receipt identifies the
checked commit; `official-source-snapshot.json` identifies the proof and
configuration bytes shared by these checks.

Reproduction commands and tool prerequisites are in the main README and pinned
CI. Each check saves its actual output, exit, timestamps and source snapshots.
Large raw logs stay outside the committed submission. No remote CI, independent
human review, registry acceptance or adversarial registry confinement is claimed.
