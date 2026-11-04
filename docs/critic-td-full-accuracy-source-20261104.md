# Independent source audit: TD full-accuracy theorem

Date: 2026-11-04
Scope: independent source and statement review only. No Lean process was run,
and no Lean source was edited. This note does not certify the theorem: the
integrated build and transitive axiom audit are still pending.

## Pinned source and export

The source is `source/upstream/tex/chapters/generative_model_model_free.tex`,
label `thm:policy-evaluation-TD`, lines 179–224 (file SHA-256
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`). The
audited intermediate export is
`StatisticalRL.TemporalDifference.tdSource_policyEvaluation_accuracy_exists_universal_constants`
in `Formalization/ModelFree/TDSourceFullAccuracyUniversal.lean` (current
SHA-256 `1bcc96d2b7dd6af07196a404e30ba9169df2227ae754c317b9ff4880bce4f6d5`).
The exact-T source-facing wrapper is
`StatisticalRL.TemporalDifference.tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants`
in `Formalization/ModelFree/TDSourceAccuracyExactSamples.lean` (SHA-256
`7afd0996fff921fdc91f22e53aad673e6485aa8dfffd472faf8d6b687e67f375`);
Chapter 4's `Thm4_1_holds` now consumes that wrapper.

The source schedule is equation `eq:thm:eta-TD` at lines 179–187. It constrains
only `1 ≤ t ≤ T`:

\[
\frac1{1+c_1(1-\gamma)T/\log^2T}\leq\eta_t\leq
\frac1{1+c_2(1-\gamma)t/\log^2T},\qquad c_1\geq c_2>0.
\]

Theorem lines 205–224 assumes `δ∈(0,1)`,
`ε∈(0,1/(1−γ)]`, `γ∈[1/2,1)`, that schedule for sufficiently small
universal `c₁≥c₂>0`, `T≥2`, the budget
\[
T\geq \frac{c_3\log^3(T)\log(ST/\delta)}
{(1-\gamma)^3\varepsilon^2}
\]
for a sufficiently large universal `c₃>0`, and `V₀∈[0,1/(1−γ)]`.
It concludes, with probability at least `1−δ`, that every state has
`|V_T(s)−V^π(s)|≤ε`.

## Source-facing binder audit

| Lean binder/input | Source classification and review |
|---|---|
| `∃ c₁ c₂ c₃ : ℝ` before the model parameters | SOURCE: the paper first chooses universal constants. The proof witnesses `c₁=c₂=1/4` and `c₃=max(4096, exp(4)/log(2)^4)`, independent of `State`, `Action`, `M`, `π`, `η`, `δ`, `ε`, `T`, or `V₀`. This is a concrete witness for the source's qualitative “small enough/sufficiently large” constants. |
| `0<c₂`, `c₂≤c₁`, `c₁≤1`, `0<c₃` | `c₂>0` and `c₂≤c₁` are SOURCE. `c₁≤1` is a witness-level convenience restriction, not a premise on a source parameter; the fixed witness `1/4` meets it. The construction proves `c₃>0`. |
| `State : Type*`, `Action : Type*`, `[Fintype State]`, `[Fintype Action]` | SOURCE/TYPING: finite state and action carriers, generalized over Lean universes. `DiscountedMDP` carries nonemptiness, rewards in `[0,1]`, normalized transition rows, and `0≤γ<1`. |
| `M`, `π : StationaryPolicy State Action` | SOURCE/STANDING: the fixed MDP and fixed stationary policy being evaluated. The Lean policy type permits randomized stationary policies, and its induced row is exactly `M.policyTransition π`; no data-dependent policy is introduced. |
| `η : ℕ→ℝ`, `δ`, `ε`, `T` | SOURCE: the finite schedule, confidence, accuracy, and iteration count. |
| `1/2≤M.discount`, `2≤T`, `0<δ`, `δ<1`, `0<ε`, `ε≤M.effectiveHorizon` | SOURCE: these are the theorem's ranges, with `effectiveHorizon=1/(1−γ)`. The model structure supplies the remaining upper discount bound. |
| `tdSourceRateSchedule M.discount c₁ c₂ T η` | SOURCE: after unfolding, it is exactly the pair of displayed schedule inequalities for each `1≤i≤T`. No premise on `η₀` or on rates after `T` is added to the source-facing theorem. |
| `V₀` and `∀s, 0≤V₀ s ∧ V₀ s≤M.effectiveHorizon` | SOURCE: the initial-value range stated immediately before the conclusion. |
| `c₃ log³(T) log(card(State)·T/δ)/((1−γ)³ε²)≤T` | SOURCE: this is the printed sample-budget inequality, with `S` represented by `Fintype.card State`. |
| Probability event and `tdErrorValue` | The target is the source terminal event `∀s, |V_T(s)−V^π(s)|≤ε`. `tdErrorValue` unfolds to the actual TD iterate minus `M.trajectoryExpectedValue π`; it is not a Bellman surrogate. The probability-law carrier caveat is described below. |

The theorem’s constant witness is chosen before any MDP or sample parameters.
The local `c₁≤1` witness condition and the proof's other numerical
requirements (`c₁c₃≥4`, `c₁c₂≤1/8`, `c₃≥384`, `c₁c₃ log²(2)≥1`, and
`c₃≥3168`) are proved from that choice; they are not left as final theorem
premises.

## Actual TD law, update, and terminal value

The source's synchronous algorithm draws, at each update `t=1,…,T`, an
independent `s_t(s)∼P_π(·|s)` for every state and updates
\[
V_t(s)=(1-\eta_t)V_{t-1}(s)+\eta_t(r_\pi(s)+\gamma V_{t-1}(s_t(s)))
\]
(`generative_model_model_free.tex:114–130`, algorithm lines 154–163). The Lean
`tdIterate` uses this update and `tdErrorValue` subtracts the actual infinite
trajectory value `M.trajectoryExpectedValue π`. `StationaryPolicy` is fixed
throughout, and the sample row is its true policy-induced transition row.

The intermediate concentration proof uses `tdSamplingLaw M π T`, the product
law with `T+1` draws indexed by `State × Fin (T+1)`; coordinate zero is unused
by the update. This carrier difference is now bridged in the exact-T
source-facing wrapper. `TDSourceSamplingProjection.lean` (SHA-256
`75b995e0bb0afd5520d6f8e31d2ecc8f2a184d24ed38d0fb6c2c682f770d3a99`)
proves `tdUsedSampleProjection_map_law`, which pushes the padded product law
to the product law of exactly `T` draws, and
`tdSampledIterate_eq_sourceSampledIterate`, which proves pathwise equality of
the terminal outputs after dropping coordinate zero. The wrapper in
`TDSourceAccuracyExactSamples.lean` consumes both: it identifies the exact-T
event probability with the padded-law preimage probability and transfers the
accuracy event by pathwise iterate equality. The conclusion is therefore
stated under the source's exact-T experiment. This bridge is present in the
current source tree, subject to the integrated build and axiom audit still in
progress. The intermediate `tdSource_policyEvaluation_accuracy_exists_universal_constants`
alone remains stated on the padded carrier.

The exact-T carrier and update are defined in
`TDSourceSamplingDefinitions.lean` (current SHA-256
`c7a55219c10f2e4f76b317a199aead2115fd24dd1d80c3ee5b4a76e9cc136a63`): its
array is `State × Fin T`, and update `k` reads coordinate `k−1` for
`1≤k≤T`. Thus each state has exactly the source's `T` row draws; there is no
extra time-zero draw in the public endpoint.

The rate schedule is finite and positive-indexed as in the paper. The
zero-tail extension used inside the variance proof preserves each rate through
`T`, and the update/error-unrolling code uses only `η₁,…,η_T`; `η₀` is not
silently constrained. The extension is an internal proof device, not a change
to the source-facing schedule.

## Helper-premise consumption in the 11-module assembly

The following exact file snapshot is the new assembly reviewed. The current
export applies the helper theorems rather than placing their conclusions in
the final theorem's hypotheses.

| Module | Role and helper hypotheses consumed by the final wrapper |
|---|---|
| `TDSourceFullAccuracyUniversal.lean` (`1bcc96d2…`) | Intermediate proof: chooses universal constants, derives final-time eligibility and all numeric side conditions, obtains the first-Freedman event, joint variance event, and deterministic initial-error bound, then calls the final accuracy composition. It states probability on the padded carrier. |
| `TDSourceAccuracyExactSamples.lean` (`7afd0996…`) | Exact-T source-facing wrapper: preserves the same constants and source premises; applies the intermediate result, rewrites probability using the projection pushforward, and transports the error event by pointwise iterate equality. It adds no hypothesis. |
| `TDSourceFinalAccuracyComposition.lean` (`3b764f48…`) | `tdSource_final_terminal_eligible_of_budget` derives `T/(c₂ log T)≤T` from the printed budget and the selected constant relation. `tdSource_final_accuracy_of_events` still has explicit internal event premises `hFirst`, `hVariance`, and `hInitial`; the outer theorem supplies each. It uses the actual error-unrolling identity and combines failures `δ/(2T)+δ/(2T)=δ/T≤δ`. |
| `TDSourceFirstFreedmanAssembly.lean` (`15dd0b64…`) | Its explicit `4≤c₁c₃`, `c₁c₂≤1/8`, `c₃≥384`, source ranges, budget, finite schedule, and eligible-time conditions are all supplied by the outer witness and `tdSource_final_terminal_eligible_of_budget`. Crucially, it derives the large-time condition `log²T≤c₁(1−γ)T` from the actual sample budget; it does not assume the omitted C5 premise. |
| `TDSourceFirstFreedmanComparisons.lean` (`a29ae10b…`) | Derives the rate-weight, increment, variance-floor, dyadic cutoff, and logarithm comparisons from the finite schedule, budget-derived large-time condition, `t≤T`, and source eligible-time bound, then feeds the resulting caps into the event theorem. |
| `TDSourceFreedmanScheduleCaps.lean` (`5ceea08b…`) | Derives the all-update weight envelope and source-scale increment/variance caps. Its extra `hlarge` premise is the one proved by the first-Freedman budget assembly. |
| `TDSourceFirstFreedmanUnion.lean` (`223457e5…`) | Takes per-update caps and logarithm comparisons from the comparisons module, applies the fixed-terminal scalar Freedman result, and unions over the finite state set with confidence `δ/(2ST)`, yielding the all-state event at `1−δ/(2T)`. No pointwise/a.e. upgrade is assumed without the underlying event construction. |
| `TDSourceVarianceProxyLemma.lean` (`not in the 11-file change list; imported helper`) | The budget-fed variance theorem supplies both source bounds simultaneously. The outer wrapper specializes it at `t=T` and converts the vector norm bound to the coordinatewise upper event. The proof's actual-law common-event and variance-sum producers remain dependencies, not assumptions of the source theorem. |
| `TDVarianceLemmaComposition.lean` (`48a16fd5…`) | Internally combines the fixed-terminal proxy event, a per-state a.e. early/late split, and the scalar comparison into one simultaneous event. In the source consumer, the proxy event and early/late split come from their budget-fed producers, and the scalar bound is proved from the source schedule. |
| `TDInitialErrorContraction.lean` (`2a95be09…`) | Derives `‖propagate₀ᵀ(V₀−V^π)‖≤H/T²` from the source budget, finite schedule, and terminal eligibility by controlling the `k=0` propagated weight. Its proof never uses or constrains `η₀`. The outer wrapper supplies every premise. |
| `TDSourceFinalScalarBudgetBridge.lean` (`b10542da…`) | Converts the printed budget to the normalized scalar `X≤ε²/c₃`; the consumer supplies positive denominators, `T>0`, and the exact source budget. |
| `TDSourceFinalScalarArithmetic.lean` (`7e58e659…`) | Proves root and linear absorptions from the budget-derived scalar bound and source ε/discount ranges. The outer consumer provides `c₃≥3168` from its fixed universal witness. |
| `TDSourceFinalScalarBudgetConsumer.lean` (`dfe035f3…`) | Connects the pure scalar lemmas to the final Freedman radius and initial term. Its helper inequalities are derived from the source budget; none are exposed in the final theorem. |

The variance helper line above is an existing dependency in the direct target
closure, not one of these 11 newly added modules. It is named to make clear
where the common-event, actual-law variance claims enter. The assembly also
depends on the existing actual TD sampling, conditional-moment, weighted
variance, Freedman, iterate, and error-unrolling modules; these provide the
mathematical estimates used by the 11 wrappers.

## C5 distinction and verdict

The standalone source lemma `lemma:TD-step-size` at
`generative_model_model_free.tex:317–327` has a documented gap: its appendix
argument uses an additional gamma-dependent large-`T` condition and a finite
time scope not stated in that standalone lemma. The already-recorded C5
counterexample applies to that standalone claim. It does not by itself refute
`thm:policy-evaluation-TD`: the main theorem supplies the sample budget, and
the current budget-fed proof stack derives the required large-`T` inequality
from that budget and the selected universal constants before applying the
early-weight estimate. No C5 premise is smuggled into the final theorem.

**Independent binder verdict:** the exact-T wrapper's source parameters,
quantifier order, uniform constant dependence, finite positive-index schedule,
discount/accuracy/confidence/horizon domains, initial-value range, and actual
terminal trajectory-value conclusion match the cited theorem. No mathematical
counterexample or additional source-domain assumption was found in the
budget-fed helper composition. The exact-T projection and pathwise iterate
bridge are present and consumed by the wrapper. The full integrated build and
axiom audit are unverified here. Therefore this note is not a theorem-completion
certificate.
