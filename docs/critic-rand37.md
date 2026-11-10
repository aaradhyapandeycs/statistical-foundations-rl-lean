# Critic report: randomized Theorem 3.7(ii), A = 1 policy evaluation and two-point display (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/Generative/RandomizedQLowerBound.lean` and the drafted randomized statement entries `Thm3_7_corrected` (part (ii)), `Thm3_7_policyEvaluation_A1` and `Eq_P_Mi_Q_inaccurate_lower_generative`. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT-WITH-FIXES; all findings applied. The three entries were strengthened in place to kernel-form randomized estimators (no `_rand` suffix); `Thm3_7_policyEvaluation_A1_restricted` was renamed `Thm3_7_policyEvaluation_A1` (no remaining deviation); the docstrings state the Borel σ-algebra and a guard `example` in `Statements/Ch3.lean` checks that the local `⊤` instances are not selected (finding 2); the Dirac case recovers deterministic estimators; the wrappers in `Statements/Ch3Proofs.lean` apply the library exports; `Formalization.Generative.RandomizedQLowerBound` is imported from `Formalization.lean`; COVERAGE rows 114, 156, 157, 216, 217, SOURCE-ISSUES (Candidate repair of Theorem 3.7, C4), ERRATA item 15, `named-result-status.json` and the statement-audit README were updated. Remaining deviations of `Thm3_7_corrected`: `S ≥ 2` (C2), `A ≥ 2` in part (i) (C1), deterministic part (i).


Critic: independent (did not build). Date 2026-11-10. Read-only except this file and
<local probe>.

Target: `Formalization/Generative/RandomizedQLowerBound.lean` (492 lines); builder probe
<local probe>.
Source read: `generative_model_model_based.tex:1440–1474` (theorem:azar + comparison),
`:1536–1560` (eq:N-UB-test-lower-Q-generative-overall, eq:P-Mi-Q-inaccurate-lower-generative),
`generative_model_model_free.tex:244–252`. Existing entries `Statements/Ch3.lean:283–355, 463–488`,
wrappers `Ch3Proofs.lean:89–123`, SOURCE-ISSUES C1, C2, C4, "Candidate repair of Theorem 3.7",
COVERAGE rows 114, 156, 157, 216, 217.

## Verdict: ACCEPT-WITH-FIXES (fixes are entry/docs wording; the library file is accepted as is)

## Evidence (commands actually run)

- `bash scripts/lean-local.sh Formalization/Generative/RandomizedQLowerBound.lean`: rc 0, 7.5 s,
  only two `unnecessarySeqFocus` linter warnings (lines 103, 468). No sorry/admit/axiom in file.
- `bash scripts/lean-local.sh <local probe>`: rc 0. `#synth`
  under the Ch3.lean local instances: `MeasurableSpace (Fin 3 → Fin 2 → ℝ)` = `MeasurableSpace.pi`,
  `MeasurableSpace ℝ` = `Real.measurableSpace` (Borel), not the generic local `⊤` instance.
  `#print axioms` for the three draft `_holds`, `theorem37_Q_fin_randomized_seed`,
  `qMixtureSource_randomized_Q_risk_of_pos`: `[propext, Classical.choice, Quot.sound]`.
- Own check <local probe> (rc 0): the draft randomized
  `Thm3_7_corrected_rand` implies the current deterministic part (ii) of `Thm3_7_corrected` by
  Dirac kernels (`dirac_real_eq` + `integral_indicator_one`). So the randomized model contains the
  deterministic one, machine-checked.

## Findings

1. **Estimator model is faithful.** QHat is a probability measure on Q-tables for each (known
   reward, known discount, data); the data space is finite, so no measurability in the data is
   needed and `∫ data, (κ data).real E ∂samplingLaw` is exactly the joint data/estimate probability
   (`finiteDataRandomOutputLaw_real_event_eq_integral`). Deterministic estimators are Dirac kernels
   (checked, item above). Seed form (`theorem37_Q_fin_randomized_seed`: arbitrary seed space Ξ,
   probability ν, measurable in the seed) is derived from the kernel form by pushforward; the kernel
   form is the more general one and should be the indexed form.
2. **Measurability does not make anything vacuous.** The library is generic in the σ-algebra on
   estimates with only "open error balls measurable" (`hE`) or `OpensMeasurableSpace`. In the entries
   the instance resolves to Borel (`MeasurableSpace.pi`, `Real.measurableSpace`), where the error sets
   are open hence measurable, so `.real` is a genuine probability, not outer measure. Borel is fully
   general: any law on a finer σ-algebra restricts to a Borel law with the same error probabilities.
   Hazard (minor): `Ch3.lean` has a generic local instance `statementStateMeasurable (State) := ⊤`;
   had it been selected, the entries would cover only laws defined on all subsets (a real
   restriction, e.g. no Lebesgue-continuous output noise under CH). It is not selected today
   (#synth), but the choice is fragile. Fix: say "Borel σ-algebra" in each docstring and add a guard
   (e.g. a static-gate or test `example : (inferInstance : MeasurableSpace (Fin 3 → Fin 2 → ℝ)) =
   MeasurableSpace.pi := rfl` compiled under the same local instances), or write the measure type
   with an explicit `@Measure _ MeasurableSpace.pi`.
   The two-point library lemma takes an arbitrary `mR` and uses outer measure (degenerate for
   coarse `mR`, e.g. `⊥`, where it is trivially true); harmless for the library, and the entry uses
   Borel, so fine.
3. **Proof structure checked.** Mixture argument: baseline vs uniform mixture over `Fin m × Fin A`
   alternatives, chi-square ≤ 1 from `N·d ≤ log(mA+1)`, overlap ≥ 1/2, risk selection
   `finiteRandomOutput_mixture_risk_selection`, transfer to actual sampling laws via
   `qMixtureSamplingLaw_eq_reconstructed_product` + `finiteDataRandomOutputLaw_map_event`.
   Relabel `Option (Fin m) ≃ Fin (m+1)` with σ-algebra pulled back (`MeasurableSpace.map g`) and the
   sup norm preserved (`norm_comp_equiv_sub`). Known reward: all family members share `r₀`, so QHat
   is evaluated at one reward table (wrapper closes by `congr`, compiles). A=1 PE: QHat :=
   (VHat ∘ projectPolicySamples).map lift and `samplingLaw_projectPolicySamples` push the Q-sampling
   law onto the policy-evaluation law in the correct direction; `Q⋆(s,0) = V^{π₀}(s)` by
   `singleAction_trajectoryExpectedQ_eq`. Two-point: covering `1 ≤ f₀ + f₁` pointwise (separation
   `2ε < v₁ − v₀`), overlap > 1/5 via KL ≤ 9/10 Pinsker/exp branch (strict, C4 route).
4. **hA removal is correct.** In `qMixtureSource_randomized_Q_risk` `2 ≤ A` was used only for the
   cardinality/log step; it is replaced by `qMixture_log_card_lower_of_pos`
   (`log((m+1)A) ≤ 2 log(mA+1)` for m, A ≥ 1, from `(m+1)A ≤ (mA+1)²`). Budget chain
   `32768·NΔ ≤ log(SA)` ⇒ `512·NΔ ≤ log((m+1)A)` ⇒ `N·d ≤ 256·NΔ ≤ log(mA+1)`. The old `hsize` premise
   is also gone (not needed). `hA : 1 ≤ A` in `theorem37_Q_fin_randomized` is derived from SA ≥ 16.
5. **Consequence for C1/C2.** Part (ii) now holds for randomized Q-estimators on the whole domain
   S ≥ 2, SA ≥ 16 (every A ≥ 1; with A = 1 this is S ≥ 16), same as the deterministic part (ii)
   already did. C1 concerns part (i) only and is unaffected. C2 (S = 1) still applies to part (ii):
   `S ≥ 2` remains a disclosed correction. Remaining deviations of `Thm3_7_corrected`: S ≥ 2 (both
   parts, C2); A ≥ 2 in part (i) (C1); part (i) estimators are deterministic maps returning
   deterministic policies. Printed part (i) says "(deterministic) policy estimator"; if read as
   "deterministic estimator" this is the print, otherwise a restriction; keep it disclosed. (A library
   randomized-policy result on S, A ≥ 2, the exact part-(i) domain, exists in
   `sourcePolicyAndQ_risk_quarter_with_common_constant` on `Option (Fin m)` carriers; lifting it to
   `Fin S` would close this too. Optional follow-up.)
6. **Constants unchanged.** c_N witness 1/32768 (both Thm3_7 entries, as deterministic entries),
   probability ≥ 1/4, strict `> ε`, sup norm; display: N ≤ 0.003/((1−γ)³ε²) (library 9/2560 looser,
   wrapper derives), `> 0.1` strict, M₀, M₁ chosen before N and QHat. Printed theorem has an
   unspecified universal c_N, chosen first in all entries.
7. **Wrappers only apply library theorems** (Thm3_7: `theorem37_corrected_fin_carriers` part (i) +
   `theorem37_Q_fin_randomized_sampleBound`; A1: library + openness of balls; display: same budget
   arithmetic as current wrapper + library). No restated proof of substance.
8. **Naming.** Do not introduce a `_rand` suffix (not a disclosed-deviation suffix under AGENTS.md).
   Strengthen in place: `Thm3_7_corrected` (part (ii) randomized); rename
   `Thm3_7_policyEvaluation_A1_restricted` → `Thm3_7_policyEvaluation_A1` (no remaining deviation);
   keep `Eq_P_Mi_Q_inaccurate_lower_generative` and drop "restricted" from its docstring/COVERAGE.
   The deterministic versions are implied (finding Dirac check), so nothing is lost. Update all
   references (COVERAGE rows 114, 156, 157, 216, 217, `named-result-status.json`, site, gate lists).
9. Cosmetic: two `<;>` linter warnings (lines 103, 468).

## Five-bin of the drafted Props (probe definitions)

### Thm3_7_corrected (randomized part (ii)) — PASS-DISCLOSED
| binder | bin | note |
|---|---|---|
| ∃ c_N, 0 < c_N (first) | SOURCE | "small universal constant" |
| S A N : ℕ | TYPING | |
| γ ε : ℝ | SOURCE | |
| 2 ≤ S | DISCLOSED | C2 |
| 16 ≤ S*A | SOURCE | |
| 2/3 ≤ γ, γ < 1, 0 < ε, ε < 1/(32(1−γ)) | SOURCE | |
| N ≤ c_N log(SA)/((1−γ)³ε²) | SOURCE | |
| 2 ≤ A → (part i) | DISCLOSED | C1 |
| piHat : (r, γ, data) → Fin S → Fin A | STANDING + DISCLOSED | known reward/discount (`:31`, `prelim.tex:42`); deterministic estimator (see finding 5) |
| QHat : (r, γ, data) → Measure (Borel) | SOURCE/STANDING | "any Q-function estimator", randomized included |
| ∀ r g data, IsProbabilityMeasure | TYPING | |
| ∃ M on Fin S × Fin A, M.discount = γ | SOURCE | |
| 1/4 ≤ P(‖·‖∞ > ε), Q⋆ = trajectory Q of optimal greedy | SOURCE | |
Counts: SOURCE 11, STANDING 1(+), TYPING 2, DISCLOSED 3 (C1, C2, part-(i) determinism), EXCESS 0.

### Thm3_7_policyEvaluation_A1 (was `_restricted`) — PASS
Binders: c_N first (SOURCE); S N (TYPING); 16 ≤ S (SOURCE: SA ≥ 16 at A = 1); γ, ε ranges (SOURCE);
N ≤ c_N log S/(…) (SOURCE, log(S·1)); VHat : (r : Fin S → Fin 1 → ℝ, γ, PE samples) → Borel prob.
measure (STANDING: known reward/discount; at A = 1 the per-state policy samples are the per-pair
generative samples; randomized included); hV (TYPING); ∃ M Fin S × Fin 1, discount γ (SOURCE);
`‖V − V^{π₀}‖ > ε` with V^{π₀} = Q⋆(·,0) (SOURCE, equivalent form proved in library). EXCESS 0,
DISCLOSED 0. C1/C2 vacuous here.

### Eq_P_Mi_Q_inaccurate_lower_generative (randomized) — PASS
γ, ε ranges (SOURCE); ∃ M₀ M₁ on Bool × Unit, discount γ, common reward (SOURCE: two states one
action; STANDING: known reward); ∀ N ≤ 0.003/(…) (SOURCE); QHat : data → Borel prob. measure on ℝ
(SOURCE "any estimator"); hQ (TYPING); strict > 0.1 for some i, s₁ = true (SOURCE). EXCESS 0.
C4 remains a proof-step (strictness) note only, not a statement deviation.

## Drafted Props (as in probe, renames applied; all compiled under Ch3.lean instances)

`Thm3_7_corrected`: the probe's `Thm3_7_corrected_rand` body verbatim.
`Thm3_7_policyEvaluation_A1`: the probe's `Thm3_7_policyEvaluation_A1_rand` body verbatim.
`Eq_P_Mi_Q_inaccurate_lower_generative`: the probe's `..._rand` body verbatim.
Wrappers: the probe's three `_holds` proofs verbatim.

## Proposed wording

COVERAGE row 156 (Thm3_7_corrected), replace the "Further restriction" sentence:
"Part (ii) covers every Q-function estimator, randomized included: a probability law on Q-tables
(Borel σ-algebra) for each value of the known reward, discount and sample array, with failure
probability under the joint data/estimate law (`theorem37_Q_fin_randomized_sampleBound`;
deterministic estimators are the Dirac case). Part (i) remains restricted to deterministic
estimators returning deterministic policies."
Row 157: "**Proved** (`Thm3_7_policyEvaluation_A1`) … every value estimator, randomized included
(probability law on value vectors given the known rewards, discount and the Theorem 3.1 sample
array) … C1 and C2 are vacuous here; no deviation from printed part (ii) at A = 1."
Row 114: "**Proved** (`Eq_P_Mi_Q_inaccurate_lower_generative`) … every estimator, randomized
included (probability law on ℝ, Borel, given the full sample array) … strict > 0.1 via the Pinsker
branch (C4)." Rows 216/217: drop "randomized estimators" from the "Not implied, open" lists.
SOURCE-ISSUES "Candidate repair" (line 83): replace "Each estimator is a deterministic map … (project
decision 2026-11-10)" by "Part (ii) quantifies over randomized Q-estimators (Borel probability laws
given the known reward, discount and sample array); part (i) over deterministic estimators returning
deterministic policies. Part (ii) is proved for every A ≥ 1 (randomized `2 ≤ A` premise removed via
`qMixture_log_card_lower_of_pos`)." Line 116: note the 1/512, S, A ≥ 2 randomized Q result is now
superseded by `theorem37_Q_fin_randomized` (S ≥ 2, SA ≥ 16, 1/32768). C4 (line 181–182): replace the
"restricted variant … not indexed" sentences with "The entry covers randomized estimators
(`sourceHardMDP_randomized_Q_estimation_lower`)."
