# Independent source review: Bernstein event to recursive residuals

Reviewed `.local/FiniteHorizonBernsteinResidualBridge.lean`, SHA-256 `fba67cbbaf80a7c8148924a7f6cd5309d26910904265192d4bc91c0fdcb4482a`, and `docs/builder-finite-horizon-bernstein-residual-bridge.md`. This is source-only; the builder handoff reports a successful compile and standard-only axiom probe, which I did not reproduce because compiler slots were occupied.

## Coefficients and indexed residual conversion

The event radius at confidence `η` and family size one has square-root coefficient `sqrt(2 log(4/η)/N)` and linear coefficient `2 log(4/η)/(3N)`. `allLevelBeta` is defined as exactly `2 log(4/η)`, so its square-root coefficient is `sqrt(β/N)`. The residual inequality needs linear coefficient `β/N`; `bernsteinRadius_le_residual_coefficients` weakens the actual `β/(3N)` coefficient by a factor of three using `log(4/η)≥0` and `‖V‖≥0`. It does not change the variance, norm, or event. `allLevelConfidence_bounds` proves `0<η<1` from `H>0`, `0<δ<1`, and nonempty state/action/stage types; therefore the logarithm has the needed sign and the preceding Bernstein event's domain holds.

`auxiliaryResidualCondition_of_indexed` consumes a pointwise row inequality for every `i : Fin pairs.length` and every state. Its induction matches the head residual at stage zero and shifts the policy by one while dropping one pair for every later stage. `trueAuxiliaryValueAt_cons_succ` proves the matching continuation suffix/shift identity, so the residual uses the same true auxiliary continuation and policy as the source recursive condition. It concludes the recursive condition from indexed inequalities; it does not assume that conclusion.

## Both policy branches and same-data semantics

`sourceAuxiliaryPolicy` selects either the supplied fixed policy (`b=true`) or the causal backward-greedy policy computed from `empiricalStages E N hN data` (`b=false`). `sourceAuxiliaryContinuation_eq_valueAt` identifies the event vector with the true auxiliary value at stage `h+1` under that exact policy. The residual application constructs `pairedEmpiricalStages E N hN data` and uses the same `data` to define the fitted policy and the comparison stages. The paired-stage map lemmas identify its first projection with `List.ofFn E` and its second with those same empirical stages. There is no cross-sample or separately selected policy substituted in the bridge.

For the fitted branch, the earlier all-level event source proof establishes strict-future factorization and action-uniformity. The current action `f i s` is selected only after using the common event at every action; no independence from the current row is claimed. The fixed branch is valid for any fixed policy function, with the true-optimal deterministic policy available as the intended source instantiation. The theorem quantifies `fixed` outside the data variable and does not provide uniformity over data-selected fixed policies.

## Levels, dimensions, and remaining scope

The event's level index is `Fin (Nat.log 2 H + 1)`, which supplies each natural level `l≤Nat.log 2 H` exactly once. Given that premise, `⟨l, by omega⟩` selects the event coordinate, so the residual theorem adds no level beyond the natural floor depth. The bridge requires `H>0` (so a stage exists), `N>0` (actual empirical rows), and `0<δ<1` (valid confidence). State and action nonemptiness follow from the actual environment and the explicit fallback action; they are not hidden extra statistical assumptions. Zero variance is permitted. The coefficient keeps the conservative `β=2log(8K HSA/δ)` implied by the event and does not claim the paper's smaller literal logarithm.

The handoff correctly limits this result to the event-to-residual bridge. It does not consume the level-zero trajectory identities, apply the conditional Lemma 9 theorem, perform logarithm absorption, compare the fitted policy to the true optimum, or prove the final sample theorem.

**Verdict:** the coefficient conversion, both policy branches, same-data stage pairing, and full natural-level range are source-consistent. The selected current action is covered by event uniformity over actions, not by an independence assertion. No hidden variance/norm or residual premise is introduced beyond the actual indexed event.

## Independent fresh-source compile and axiom audit

I rechecked the exact eight staged source hashes recorded in `scripts/finite-horizon-bernstein-bridge-sources.sha256`; all matched. `bash scripts/audit-finite-horizon-bernstein-bridge-fresh.sh` completed with exit code 0, compiling the eight modules in dependency order into `.local/finite-horizon-bernstein-bridge-fresh-audit/` and running the export probe. The probe contains 85 declarations from the closure, including the bridge's public exports. All 85 report only `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or other nonstandard axiom was found. The final bridge export `allLevelBernsteinEvent_implies_residual` has the same standard-only axiom list. This is an isolated staged-source compile; it does not claim the production integration or final monograph theorem is complete.

Production integration: production bodies match the independently reviewed sources, with qualified imports. The full project export compiled and audited 2,565 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
