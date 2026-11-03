# Independent review: β/N wrapper for finite-horizon Lemma 9

Reviewed staged `.local/FiniteHorizonLemmaNine.lean`, SHA-256 `fbe84272b28ce3fe197e5372eeee97d3459ac492c2711932ed03c601744d8746`. The reviewed staged dependencies were:

- `FiniteHorizonAuxiliaryTerminal.lean`: `3683cd311fa674715e00d95dda59d1fca0f5314cedb14c8a620d43da49a6aefa`
- `FiniteHorizonAuxiliaryResidualRecursion.lean`: `a0d565123dd0458b4db4ce10c2234f50de77c338eaa89ccf5100dd8f494ecc09`
- `FiniteHorizonAuxiliaryGrowth.lean`: `9df2d4d8bbeaf8ca5f9c47d66e6e06c85d161a90fb65082530b8eccb5a9bd1c3`

## Source review

The weak-threshold wrapper assumes `12 H β ≤ N`, with `H>0`, `N>0`, and `β≥0`. These imply `12 H β/N≤1`; squaring the nonnegative product `sqrt(β/N) sqrt(3H)` gives `3Hβ/N≤1/4`, hence the exact contraction `sqrt(β/N) sqrt(3H)≤1/2`. The weak inequality is appropriate for this deterministic implication. The companion source-domain wrapper assumes the strict threshold `12 H β<N`, derives `N>0` rather than adding it as a premise, and passes the weak consequence to the first wrapper. Thus the strict source threshold and the weak auxiliary threshold are distinguished correctly.

The coefficients specialize exactly: `a=sqrt(β/N)` and `b=β/N=a²`. The final square-root identity normalizes `a sqrt(3H)` to `sqrt(3 β H/N)`, preserving the source bound `6 H sqrt(3 β H/N)`. It is valid at `β=0` because the wrapper separately carries `N>0` (or derives it from the strict threshold) and does not divide by β.

Natural depth remains `Nat.log 2 H`; the residual hypothesis in the natural-level wrappers is explicit for every `l≤Nat.log 2 H`. In particular, at `H=1` this depth is zero and the terminal residual at `l=0` is still required and consumed. The source-log wrapper assumes the premise for every natural `l` with `(l:ℝ)≤Real.logb 2 H`, and `Real.natLog_le_logb H 2` supplies the needed floor-depth premise. It adds no residual level above the source's real-log domain.

The suffix result quantifies over every start stage `h`. It applies the prefix-to-suffix lemma to `pairs.drop h` and shifted policy `k ↦ f (h+k)`, so each suffix inherits the same residual premise for every level through the same depth. This is a deterministic all-suffix result; it does not assert a new probability event, suffix independence, or fitted-policy independence. The theorem remains conditional on the explicit full-list residual premise.

## Independent compile and axioms

Using the previously fresh-built exact terminal dependency chain, I compiled the exact wrapper source to `.local/finite-auxiliary-lemma-nine-review/FiniteHorizonLemmaNine.olean`; it succeeded with no diagnostics. An import-only probe queried all six exported theorems: `auxiliaryResidualCondition_drop`, `auxiliary_sample_contraction`, both `auxiliaryErrorNorm_le_lemmaNine` variants, and both suffix/source-log variants. Every `#print axioms` result contained exactly `propext`, `Classical.choice`, and `Quot.sound`.

The builder handoff was not present in `docs/` at review time. Compilation used Lean 4.27.0-rc1, existing pinned production dependencies, and the separately reviewed fresh terminal output; no Mathlib or production dependency rebuild was performed in this wrapper audit.

**Verdict:** the source constants, strict/weak sample-size domains, β/N specialization, natural floor-depth endpoint, source real-log premise, and all-suffix transport are consistent with the stated deterministic Lemma 9 wrapper. This does not discharge the residual assumptions probabilistically or establish the end-to-end finite-horizon theorem.

Production integration: the actual production module matches the independently reviewed source body, with qualified imports. The full project check compiled the exports and audited 2,406 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
