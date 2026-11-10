# CRITIC a1: A=1 policy-evaluation lower bound (independent review, 2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/Generative/PolicyEvalLowerBoundA1.lean` and the entry `Thm3_7_policyEvaluation_A1_restricted`. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT-WITH-FIXES; findings 1-3 applied (COVERAGE rows for the model-based and model-free A = 1 comparisons rewritten, SOURCE-ISSUES "Candidate repair of Theorem 3.7" names the entry, the entry docstring now says randomized estimators are in the printed domain but not covered). The entry is PASS-DISCLOSED (deterministic estimators only).

Targets: `Formalization/Generative/PolicyEvalLowerBoundA1.lean`
(`StatisticalRL.GenerativeLowerBound.policyEvaluation_lowerBound_singleAction`, c_N = 1/32768);
entry `Thm3_7_policyEvaluation_A1_restricted` (Formalization/Statements/Ch3.lean:337) and
`_holds` (Ch3Proofs.lean:92).
Source read: `theorem:azar`, generative_model_model_based.tex:1443–1464; comparisons
:1468–1474 and generative_model_model_free.tex:240–251 (claim at 248–249);
SOURCE-ISSUES.md C1 (l.7), C2 (l.39), "Candidate repair of Theorem 3.7" (l.70).

## Verdict: ACCEPT-WITH-FIXES (Lean and entry accepted; fixes are docs-only)

## Compilation and axioms (run by critic, scripts/lean-local.sh, one Lean at a time)
- PolicyEvalLowerBoundA1.lean: no errors/warnings. Ch3.lean: only 3 pre-existing unused-variable
  warnings (line 186). Ch3Proofs.lean: clean. Oleans present and newer than sources.
- <local probe>: both the library theorem and `_holds` depend on
  [propext, Classical.choice, Quot.sound] only. No sorry/admit/axiom in the new file.

## Independent reconstruction (printed Thm 3.7(ii) at A = 1)
∃ c_N > 0 (universal) such that ∀ γ ∈ [2/3,1), 0 < ε < 1/(32(1−γ)), S·1 ≥ 16, N ≤ c_N log(S)/((1−γ)³ε²)
(N i.i.d. generative draws per (s,a) = per state), ∀ Q-estimator Q̂ ("any", not qualified as
deterministic, unlike part (i)), ∃ γ-discounted MDP with S states, 1 action: P_M(‖Q̂ − Q⋆‖∞ > ε) ≥ 1/4.
At A = 1: Q⋆(s,0) = V^{π₀}(s), π₀ the unique policy, and the generative experiment is the
policy-evaluation experiment of Thm 3.1/TD.

## Reduction soundness (check 1): sound
- QHat(r,γ,data) := VHat(r,γ, projectPolicySamples N (const 0) data) is a deterministic Q-estimator of
  exactly the type `Thm3_7_corrected` (ii) quantifies over; witness M obtained after QHat (hence after VHat).
- `samplingLaw_projectPolicySamples`: pushforward of the learning product law under the projection is
  `ModelBasedPolicyEvaluation.samplingLaw M (pointMass ∘ f) N` (Measure.pi of policy rows). Measurability
  trivial (⊤ σ-algebra on finite carriers). Event pulled back pointwise.
- Q⋆ identification: `optimalGreedyPolicy = π₀` by Subsingleton (Fin 1), then
  `trajectoryExpectedValue_eq_policyAverageQ` + pointMass expectation; sup-norm of the constant lift
  equals ‖h‖ (`norm_singleAction_lift`, both directions proved).
- Sampling model matches the book's: `Thm3_1` uses the same `ModelBasedPolicyEvaluation.samplingLaw`,
  and `tdSourceSamplingLaw M π T` is definitionally `ModelBasedPolicyEvaluation.samplingLaw M π T`
  (TDSourceSamplingDefinitions.lean:15–17). TD's output uses only M.reward, M.discount and data
  (tdIterate; padding coordinates unused for 1 ≤ k ≤ T), so TD with fixed η, V₀ is itself an
  admissible VHat. The estimator also sees the known reward table and discount (book convention;
  only strengthens the lower bound).

## Five-bin binder table
| binder | Lean type | bin | citation |
|---|---|---|---|
| c_N, 0 < c_N (∃, outermost) | ℝ | SOURCE | :1449–1451 "universal constant c_N>0" |
| S | ℕ, carrier Fin S | TYPING | "S states" |
| A = 1 (fixed, Fin 1) | — | SOURCE (specialization named by the comparisons) | :1470 "A=1"; MF:248 "setting A=1" |
| N | ℕ (N = 0 allowed) | SOURCE | :1447 |
| γ, ε | ℝ | SOURCE | :1445 |
| 16 ≤ S | = SA ≥ 16 at A = 1 | SOURCE | :1445 |
| 2/3 ≤ γ, γ < 1 | | SOURCE | :1445 |
| 0 < ε, ε < 1/(32(1−γ)) | | SOURCE | :1445 |
| N ≤ c_N log S/((1−γ)³ε²) | log(S·1) = log S | SOURCE | :1448 |
| ∀ VHat : rewards → discount → PE samples → (Fin S → ℝ) | deterministic | DISCLOSED | Candidate repair of Thm 3.7 (l.70: "Each estimator is a deterministic map ..."); entry name `_restricted` + docstring |
| ∃ M : DiscountedMDP (Fin S) (Fin 1), M.discount = γ | | SOURCE | :1457–1458 |
| conclusion 1/4 ≤ P(ε < ‖VHat − V^{π₀}‖) | strict event, `.real` of probability measure | SOURCE (Q⋆ = V^{π₀} at A=1) | :1458 |
Counts: SOURCE 10, TYPING 1, DISCLOSED 1, EXCESS 0. Entry verdict: PASS-DISCLOSED.

Other checks: quantifier order correct (c_N first, then S,N,γ,ε, then VHat, then M). No junk:
log S > 0 (S ≥ 16), denominator > 0, measure is a probability measure. Hypotheses satisfiable
(builder probe S=16, γ=2/3, ε=1/64, N=1; budget ≈ 9.4 ≥ 1). Self-contained Prop; Ch3.lean imports
definitions only; `_holds` is a one-line application of the library theorem. `_restricted` (not
`_corrected`) is right: A = 1 is the instance the comparisons use; C1 (part (i)) and C2 (S = 1) are
vacuous here; the only deviation is deterministic-only estimators.

## Findings
1. (docs, minor) COVERAGE rows 217–218 are already partly stale independently of this work: row 218 says
   "`Thm3_7_corrected` needs A ≥ 2 ([C1]) so no A = 1 lower bound is formalized", but
   `Thm3_7_corrected` requires A ≥ 2 only in part (i); part (ii) holds at A = 1 on learning samples
   (SOURCE-ISSUES l.70 says so). The new entry's real contribution is the policy-evaluation form
   (estimator sees exactly Thm 3.1/TD's experiment; error against V^{π₀}).
2. (docs, required) SOURCE-ISSUES "Candidate repair of Theorem 3.7" should name the new entry so the
   DISCLOSED bin has an explicit matching entry (proposed text below).
3. (docs, minor) Entry docstring is accurate. Optional: say "randomized estimators (printed part (ii):
   'any Q-function estimator')" to make clear that randomization is in the printed domain.
4. (info) Randomized lower bounds exist only for S,A ≥ 2 (GenerativeLowerBoundQMixtureFinalRandomized,
   c_N = 1/512); none at A = 1. Deterministic → randomized does not follow (witness M depends on the
   estimator), so this stays open.
5. (info) Formalization.lean reaches the new module only transitively via Ch3Proofs; adequate for the
   audit.

## Proposed COVERAGE wording
Row 217 (model-based 1468–1474), status cell:
**Implied by `Thm3_1`, `Thm3_2_positiveN`, `Thm3_7_corrected` and `Thm3_7_policyEvaluation_A1_restricted`,
in the lower-bound regime only.** Policy learning: Theorem 3.2's upper bound against the corrected
Theorem 3.7 (S ≥ 2, SA ≥ 16, γ ≥ 2/3, A ≥ 2 for part (i); [C1], [C2]). Policy evaluation (A = 1):
Theorem 3.1's upper bound against `Thm3_7_policyEvaluation_A1_restricted` (S ≥ 16, γ ∈ [2/3,1),
0 < ε < 1/(32(1−γ)), N ≤ (1/32768) log S/((1−γ)³ε²) draws per state from Theorem 3.1's own sampling law,
deterministic value estimators seeing the known rewards and discount); both match up to logarithmic
factors. The Õ comparison is not formalized as a separate Prop (decision F1, 2026-11-09).
**Not implied, open:** "across the entire range of precision levels": accuracies
1/(32(1−γ)) ≤ ε ≤ 1/(1−γ) (no lower bound is stated or proved there), γ < 2/3, and randomized
estimators (printed part (ii) quantifies over any estimator).

Row 218 (model-free 240–251), replace the "Not implied, open" sentence with:
**Implied, in the lower-bound regime only:** the minimax-optimality claim (lines 248–249) against
Theorem 3.7 at A = 1 is `Thm3_7_policyEvaluation_A1_restricted`, stated on TD's own experiment
(`tdSourceSamplingLaw` is `ModelBasedPolicyEvaluation.samplingLaw`, T draws per state; TD with fixed
rates and V₀ is an admissible estimator): S·T ≳ S log S/((1−γ)³ε²) samples are necessary, matching
`Thm4_1`'s Õ(S/((1−γ)³ε²)) up to log factors, for S ≥ 16, γ ∈ [2/3,1), ε < 1/(32(1−γ)).
**Not implied, open:** "the full accuracy range ε ∈ (0, 1/(1−γ)]" for ε ≥ 1/(32(1−γ)), γ ∈ [1/2, 2/3)
(covered by `Thm4_1` but not by the lower bound), and randomized estimators.

## Proposed SOURCE-ISSUES note (append to "Candidate repair of Theorem 3.7")
**A = 1 policy-evaluation form (2026-11-10).** `Thm3_7_policyEvaluation_A1_restricted` specializes
corrected part (ii) to one action and restates it on the policy-evaluation experiment of Theorem 3.1 and
TD learning (estimator: deterministic map of the known rewards, discount and N draws per state; error
‖V̂ − V^{π₀}‖∞, equal to ‖Q̂ − Q⋆‖∞ at A = 1), with c_N = 1/32768 and the printed γ, ε, SA ≥ 16 (= S ≥ 16)
domain. C1 and C2 are vacuous here; the only deviation from the print is deterministic estimators.
It closes the A = 1 comparisons (model-based :1468–1474, model-free :248–249) only for
ε < 1/(32(1−γ)) and γ ≥ 2/3.
