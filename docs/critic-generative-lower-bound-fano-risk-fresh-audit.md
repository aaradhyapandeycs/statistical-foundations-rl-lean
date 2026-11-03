# Fresh-source compile and axiom audit: finite Fano/risk closure

The independent harness is
`.local/fano-risk-independent-audit/scripts/audit.sh`. It pins SHA-256 for all
30 staged source modules in the Fano and corrected-family deterministic risk
closure, refuses any source drift, copies the exact inputs into its
project-owned `.local/fano-risk-independent-audit/src`, then compiles them
sequentially in dependency order to the separate `out` directory. It uses the
repository's pinned `.local/lean` executable and the existing project/Mathlib
build artifacts; it does not invoke Lake or rebuild dependencies. Per-module
compile and axiom logs are retained in `.local/fano-risk-independent-audit/logs`.

**Result:** all 30 exact-source hash checks passed, all 30 fresh staged-source
compiles succeeded, and every generated `#print axioms` probe succeeded. The
probe enumerates all top-level theorem, lemma, definition, and abbreviation
declarations in each audited source. No custom axiom, `sorry`, or `admit` was
found in the exported closure. Dependencies report only `propext`,
`Classical.choice`, and `Quot.sound`; `HardFamilyIndex`,
`FamilyActiveCoordinates`, `familyEncode`, and `familyReconstruct` are
axiom-free, while the signature functions require only `propext`. Existing
unused-simp-argument and unused-variable linter warnings appeared; there
were no compilation errors.

This is an independent compile of the staged unqualified modules against the
existing project cache. It does not validate qualified production imports,
the umbrella project build, or a production export. The staged risk roots
still cover deterministic data-to-deterministic-policy estimators; the
randomized extension is a separate plan. The source correction also remains
proposed rather than author-approved.

Production integration: the relevant production module bodies match the independently reviewed staged sources, with qualified imports where needed. The complete project build compiled the actual exports and audited 2,279 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
