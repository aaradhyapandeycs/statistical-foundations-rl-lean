# Critic report: calibrated oracle confidence regions (eq:convex.Cdelta, C47(2)/(3)) — 2026-11-10

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of the exact `1 − α` Gaussian levels for the corrected, oracle-covariance ellipsoid and rectangle (`Formalization/TDInference/Confidence/Calibration.lean`, export `exists_confRegion_oracle_calibrated`), with drafted statement entries `Eq_convex_Cdelta_ellipsoid_corrected_oracle_calibrated` and `Eq_convex_Cdelta_rectangle_corrected_oracle_calibrated`. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT; findings 5–7 applied (entries use the printed range `0 < η₀ < 1/4`; module imported from `Formalization.lean`; the `_corrected_oracle` docstrings point to the new `_calibrated` entries; COVERAGE and SOURCE-ISSUES C47 updated). The entries landed as drafted below.

Reviewed file sha256 7dfe670804822bfb93e477c850e7244595c20c946db848ecec88e76224c0f2bb (248 lines).
Source: chapters/inference.tex:196-213; docs/SOURCE-ISSUES.md C47(2)/(3).

## Verdict: ACCEPT (with minor integration fixes)

## Commands run (read-only; no lake, no git, no -o)
- `bash scripts/lean-local.sh Formalization/TDInference/Confidence/Calibration.lean` -> exit 0, no output (no errors/warnings).
- <local probe>: #print axioms of the 4 exports -> [propext, Classical.choice, Quot.sound];
  #check of the calibrated export; deliberate `1 = 2 := rfl` correctly reported as error (probe is live).
- <local probe> (copy of the builder probe): g_calibrated and g_ellipsoid_95
  on instance G (S=2, Gamma_true=(25/128,1/128), eta0=1/8) compile; axioms standard. All hypotheses are discharged
  on G, so they are jointly satisfiable. The conclusion `N(...).real = 1 - alpha` itself rules out a degenerate
  (zero/junk) measure.

## Findings
1. (OK) No-atom argument. `confCalib_mem_frontier_of_smul`: if x in C and t.x notin C for all t>1, then x not in
   interior (t.x -> x as t -> 1+); correct. For q>0, {g=q} subset {g<=q}, and strict growth g(t.x)>g(x) for
   g(x)>0 puts it in frontier of the convex set {g<=q}, null by tdGaussCov_frontier_convex_eq_zero. For q<=0,
   {g=q} subset {g<=0} = {0} via g>=0 and g=0 => x=0. Ellipsoid: g=0 => A x = 0 (via quadForm_trueLambda_inv,
   Gamma_true>0) => x=0 by invertibility of A (tdA_isUnit); sup norm: norm_eq_zero. {0} null as a convex set
   with empty interior (S>=1 needed, provided by Nonempty State). Scaling: t^2 and t factors; correct.
2. (OK) Cdf/IVT: cdf of the image law nu.map g; continuity via Stieltjes measure of singletons = 0 and
   leftLim = rightLim; cdf(0) = nu{g<=0} = 0; tends to 1 at top, so p in [0,1) attained on [0,Q]. Correct.
3. (OK) Quantifier order: exists K0 > 0, forall alpha in (0,1), exists q,r >= 0 (no T), forall T >= 1. K0 is
   legitimately alpha-independent: it comes from exists_confRegion_oracle_bounds, whose bound is uniform in all
   q, r (and all convex K) and fixed before alpha. q, r are chosen before T. Matches the intended reading.
4. (OK) Docstrings are honest: oracle Lambda "unknown in practice"; threshold q not R^2 and sqrt T once (C47(2)/(3));
   chi^2(S) identification, plug-in Lambda_hat_T and rate without log(2T) explicitly not proved; "instance constant".
5. (Minor) Export assumes eta0 <= 1 (source: 0 < eta0 < 1/4, :133); weaker hypothesis, fine. Statement entries should
   use the printed range, as the existing _corrected_oracle entries do.
6. (Minor, integration) File is not imported from Formalization.lean, so the public axiom audit does not yet cover it;
   add the import (and any g2 gate list) when integrating.
7. (Minor, docs) The existing entries Eq_convex_Cdelta_{ellipsoid,rectangle}_corrected_oracle say "existence of an
   exact 1 - alpha threshold/level is not part of this entry"; when calibrated entries land, add a pointer to them
   and update C47(2)/(3) evidence notes and COVERAGE. Do not mutate the existing entries; add new ones.

## Recommendation: add two statement entries in Formalization/Statements/Ch7.lean (section EqConvexCdelta)
Lambda written out as in the existing entries. Docstrings: same differences as the _corrected_oracle siblings, plus
"q_alpha, r_alpha exist with exact Gaussian mass 1 - alpha; the chi^2(S) identification of q_alpha is not proved;
K0 does not depend on alpha".

```lean
def Eq_convex_Cdelta_ellipsoid_corrected_oracle_calibrated : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ α : ℝ, 0 < α → α < 1 → ∃ q : ℝ, 0 ≤ q ∧
      (gaussCov (tdA M π μ) (trueGamma M π μ)).real
          {x | ∑ s, ∑ s', x s * x s' *
            ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ)⁻¹ s s' ≤ q} = 1 - α ∧
      ∀ T : ℕ, 1 ≤ T →
        |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
              (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                  ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ)⁻¹ s s' ≤
                q}.indicator 1 ω) - (1 - α)| ≤
          K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T))

def Eq_convex_Cdelta_rectangle_corrected_oracle_calibrated : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ α : ℝ, 0 < α → α < 1 → ∃ r : ℝ, 0 ≤ r ∧
      (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r} = 1 - α ∧
      ∀ T : ℕ, 1 ≤ T →
        |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
                M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}.indicator 1 ω) -
          (1 - α)| ≤
          K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T))
```
Proofs (Ch7Proofs.lean): obtain ⟨K₀,hK₀,hb⟩ := exists_confRegion_oracle_calibrated M π μ hμ h0 (by linarith) V₀ hΓ;
refine ⟨K₀,hK₀,fun α a0 a1 ↦ ?_⟩; take the q (resp. r) component and `.1`/`.2` of the T-conjunction. trueLambda
unfolds definitionally to the written-out Lambda (TDInference711Defs.lean:230-232), as in the existing wrappers.
An entry is warranted: this is a genuine strengthening (exact-level calibrated coverage), not a restatement.
