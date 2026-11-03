# Independent review: finite-horizon auxiliary terminal/depth closure

Reviewed `.local/FiniteHorizonAuxiliaryTerminal.lean`, SHA-256 `3683cd311fa674715e00d95dda59d1fca0f5314cedb14c8a620d43da49a6aefa`. The staged dependency hashes at review time were:

- `FiniteHorizonAuxiliaryVariance.lean`: `19f843f138314e21a14d5b29eef88e758add4389dbbcfa7eb225e496bc68d4ee`
- `FiniteHorizonAuxiliaryGrowth.lean`: `9df2d4d8bbeaf8ca5f9c47d66e6e06c85d161a90fb65082530b8eccb5a9bd1c3`
- `FiniteHorizonAuxiliaryResidualRecursion.lean`: `a0d565123dd0458b4db4ce10c2234f50de77c338eaa89ccf5100dd8f494ecc09`

## Semantic review

The module is a deterministic auxiliary-error closure, not a concentration theorem. It takes the residual condition at every level `l ≤ Nat.log 2 H` explicitly. `auxiliaryErrorNorm_unroll` consumes the strict-prefix levels `l < m`; the terminal estimate consumes the remaining level `m`, so for `m = Nat.log 2 H` no level is dropped. The terminal error is bounded from that level's actual residual premise and the source-derived forcing envelope. The comparison recursion uses the true-derived forcing and comparison transition only for propagation, consistent with the preceding source construction.

The natural-depth estimate uses `H < 2^(Nat.log 2 H + 1)`, hence `H ≤ 2^(m+1)`. With `q ≤ 1/2` and `q ≥ 0`, it obtains `H q^m ≤ 2`, retaining the factor two caused by rounding the real logarithmic depth down to a natural number. The geometric sum is bounded separately by two. The final arithmetic combines these two bounds and the `hhalf` premise in `auxiliary_six_constant`; inspection confirms the bound claimed is `6 H (a √(3H))`.

Scope includes all natural `H` for the standalone floor-power/contraction lemmas, including `H=0`. The final closure requires `0 < H`, which supplies `H≥1` to the constant lemma; it handles `H=1` (`m=0`) because the sole residual level is the terminal one. It assumes `0≤a`, `a√(3H)≤1/2`, `pairs.length≤H`, and the exact source residual condition for every level through the floor depth. No sample-size, probability, policy-independence, or Fano conclusion is smuggled into this deterministic result.

## Fresh compile and axiom evidence

Using Lean 4.27.0-rc1 and the existing pinned dependency artifacts, I freshly compiled the exact staged variance, growth, residual-recursion, and terminal sources in that order to `.local/finite-auxiliary-terminal-review/`. The terminal compile succeeded. A separate probe imported the freshly compiled terminal module and ran `#print axioms` on all seven terminal-module theorem exports. Every export reported exactly `propext`, `Classical.choice`, and `Quot.sound`; no other axioms were reported. The probe is `.local/finite-auxiliary-terminal-review/TerminalAxioms.lean` and its output is in the terminal tool result for this audit. This fresh local closure rebuild did not rebuild Mathlib or other pinned production dependencies.

**Verdict:** source semantics, floor-depth indexing, constants, and transitive axiom closure are consistent for the stated deterministic scope. This does not establish the subsequent probability/event assembly or the complete finite-horizon theorem.

Production integration: the actual production module matches the independently reviewed source body, with qualified imports. The full project check compiled the exports and audited 2,406 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
