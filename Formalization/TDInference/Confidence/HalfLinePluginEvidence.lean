import Formalization.TDInference.Confidence.PrintedRectangleEvidence

/-!
# C47(1) refutation with the printed plug-in covariance `Λ̂_T`

Source: `chapters/inference.tex:187–196`: the rule `eq:convex.Cdelta` (display :191–193) says it
suffices to choose *any* convex set `C_α` with at least `1 − α` mass under `N(V̄_T, Λ̂_T/T)`, with
`Λ̂_T = Ā_T⁻¹Γ̂_TĀ_T⁻ᵀ` (`eq:defn-hat-Lambda`, :180–182), and that "such sets serve as approximate
confidence regions" (:196). SOURCE-ISSUES C47(1).

**Instance O (one state).** As in `TDInference/Confidence/HalfLineEvidence.lean`: `State = Unit`, two actions
with rewards `0, 1`, `γ = 1/2`, uniform `π` and `μ`; `V^π = 1`, `Γ_true = 1/4`, `A = 1/2`, oracle
`Λ = 1`. Every step size `0 < η₀ ≤ 1` (containing the printed range `0 < η₀ < 1/4`) and every
initialisation `V₀` is allowed.

**Selection rule.** For a level `z ≥ 0` (`α = 1 − Φ(z) ∈ (0, 1/2]`), on each path `ω` take the
half-line `signSel (z√(Λ̂_T(ω)/T)) (V̄_T(ω))`, i.e. `[V̄_T − z√(Λ̂_T/T), ∞)` if `V̄_T ≥ 1` and
`(−∞, V̄_T + z√(Λ̂_T/T)]` otherwise. It is a function of the data only (through `V̄_T`, `Λ̂_T`);
its fixed threshold `1` equals `V^π` of instance O, which is legitimate because the printed claim
is universal over such sets (one instance and one rule refute it).

**Result** (`C47_convex_dataSelected_undercovers_plugin`, proved by
`c47_convex_dataSelected_undercovers_plugin`). Each selected set is convex; on every path its
mass under the printed Gaussian `N(V̄_T, Λ̂_T/T)` is at least `Φ(z) = 1 − α`, and exactly `Φ(z)`
whenever `Λ̂_T(ω) > 0` (on paths with `Λ̂_T(ω) = 0`, where in this instance `Λ̂_T ≥ 0`, the Gaussian `N(v, 0)` is the
point mass at `V̄_T`, which the half-line contains, mass `1`). Yet its coverage
`P(V^π ∈ C_α)` tends to `2Φ(z) − 1 = 1 − 2α` and is eventually at most
`Φ(z) − (1 − Φ(z))/2`, which is strictly below `1 − α = Φ(z)`. Hence the printed rule
`eq:convex.Cdelta`, with the printed plug-in `Λ̂_T`, does not yield approximate confidence regions
for data-selected convex sets. The limit is the plug-in two-sided limit
`oneState_tendsto_twoSided_plugin` (consistency of `Λ̂_T`, no rate; qualitative only).

Scope: this refutes the printed rule for data-selected convex sets. Corrections for convex shapes
fixed before the data are the separate statement-index entries (`Eq_convex_Cdelta_corrected_*`).
Library refutation Prop; no statement-index entry. Oracle-covariance variant:
`oneState_signSel_coverage_eventually_lt`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped BigOperators NNReal

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Probability.Stein

/-- For a positive variance `d`, the half-line `signSel (z√d) v` has mass exactly `Φ(z)` under
`N(v, d)`. -/
theorem gaussianReal_signSel_of_pos (v z : ℝ) {d : ℝ} (hd : 0 < d) :
    (gaussianReal v d.toNNReal).real (signSel (z * Real.sqrt d) v) =
      (gaussianReal 0 1).real (Set.Iic z) := by
  set σ := Real.sqrt d with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hd
  have hσ2 : σ ^ 2 = (d.toNNReal : ℝ) := by
    rw [hσdef, Real.sq_sqrt hd.le, Real.coe_toNNReal _ hd.le]
  unfold signSel
  split_ifs with hv
  · rw [gaussianReal_eq_map_mul_add v (-σ) _ (by rw [neg_sq]; exact hσ2),
      map_measureReal_apply (by fun_prop) measurableSet_Ici]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
    constructor <;> intro h <;> nlinarith
  · rw [gaussianReal_eq_map_mul_add v σ _ hσ2,
      map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> nlinarith

/-- For every real `d` (read through `toNNReal`) and `z ≥ 0`, the half-line `signSel (z√d) v` has
mass at least `Φ(z)` under `N(v, d)`. -/
theorem le_gaussianReal_signSel (v : ℝ) {z : ℝ} (hz : 0 ≤ z) (d : ℝ) :
    (gaussianReal 0 1).real (Set.Iic z) ≤
      (gaussianReal v d.toNNReal).real (signSel (z * Real.sqrt d) v) := by
  rcases lt_or_ge 0 d with hd | hd
  · exact (gaussianReal_signSel_of_pos v z hd).ge
  · have hmem : v ∈ signSel (z * Real.sqrt d) v := by
      unfold signSel
      split_ifs
      · exact Set.mem_Ici.2 (by linarith [mul_nonneg hz (Real.sqrt_nonneg d)])
      · exact Set.mem_Iic.2 (by linarith [mul_nonneg hz (Real.sqrt_nonneg d)])
    have h1 : (Measure.dirac v).real (signSel (z * Real.sqrt d) v) = 1 := by
      rw [measureReal_def, Measure.dirac_apply_of_mem hmem, ENNReal.toReal_one]
    rw [Real.toNNReal_of_nonpos hd, gaussianReal_zero_var, h1, gaussianReal_real_Iic]
    exact stdCDF_le_one z

open OneState

/-- **C47(1), data-selected convex sets, printed plug-in covariance (library refutation Prop, not a
statement-index entry).** On instance O (`inference.tex:187–196`), for every `0 < η₀ ≤ 1`, every
`V₀` and every `z ≥ 0` (`α = 1 − Φ(z)`), the sign-selected half-lines
`C_T(ω) = signSel (z√(Λ̂_T(ω)/T)) (V̄_T(ω))`
1. are convex,
2. have mass at least `Φ(z)` under `N(V̄_T(ω), Λ̂_T(ω)/T)` on every path, with equality when
   `Λ̂_T(ω) > 0` (so they satisfy the printed condition `eq:convex.Cdelta`),
3. have coverage `P(V^π ∈ C_T)` tending to `2Φ(z) − 1`,
4. eventually have coverage at most `Φ(z) − (1 − Φ(z))/2`,
5. and `Φ(z) − (1 − Φ(z))/2 < Φ(z) = 1 − α`.
Here `Φ(z) = (gaussianReal 0 1).real (Set.Iic z)` and coverage is the path-law probability. -/
def C47_convex_dataSelected_undercovers_plugin : Prop :=
  ∀ η₀ : ℝ, 0 < η₀ → η₀ ≤ 1 → ∀ V₀ : Unit → ℝ, ∀ z : ℝ, 0 ≤ z →
    (∀ T : ℕ, ∀ ω : Fin T → Tuple Unit (Fin 2),
      Convex ℝ (signSel (z * Real.sqrt (lambdaHat oMDP η₀ V₀ ω () () / T))
        (prAverage oMDP η₀ V₀ ω ()))) ∧
    (∀ T : ℕ, 1 ≤ T → ∀ ω : Fin T → Tuple Unit (Fin 2),
      (gaussianReal 0 1).real (Set.Iic z) ≤
        (gaussianReal (prAverage oMDP η₀ V₀ ω ())
          (Real.toNNReal (lambdaHat oMDP η₀ V₀ ω () () / T))).real
          (signSel (z * Real.sqrt (lambdaHat oMDP η₀ V₀ ω () () / T))
            (prAverage oMDP η₀ V₀ ω ())) ∧
      (0 < lambdaHat oMDP η₀ V₀ ω () () →
        (gaussianReal (prAverage oMDP η₀ V₀ ω ())
          (Real.toNNReal (lambdaHat oMDP η₀ V₀ ω () () / T))).real
          (signSel (z * Real.sqrt (lambdaHat oMDP η₀ V₀ ω () () / T))
            (prAverage oMDP η₀ V₀ ω ())) = (gaussianReal 0 1).real (Set.Iic z))) ∧
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
        {ω' : Fin T → Tuple Unit (Fin 2) | oMDP.valueFixedPoint oPolicy () ∈
          signSel (z * Real.sqrt (lambdaHat oMDP η₀ V₀ ω' () () / T))
            (prAverage oMDP η₀ V₀ ω' ())}.indicator 1 ω) atTop
      (𝓝 (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)) ∧
    (∀ᶠ T : ℕ in atTop,
      (∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
          {ω' : Fin T → Tuple Unit (Fin 2) | oMDP.valueFixedPoint oPolicy () ∈
            signSel (z * Real.sqrt (lambdaHat oMDP η₀ V₀ ω' () () / T))
              (prAverage oMDP η₀ V₀ ω' ())}.indicator 1 ω) ≤
        (gaussianReal 0 1).real (Set.Iic z) -
          (1 - (gaussianReal 0 1).real (Set.Iic z)) / 2) ∧
    (gaussianReal 0 1).real (Set.Iic z) - (1 - (gaussianReal 0 1).real (Set.Iic z)) / 2 <
      (gaussianReal 0 1).real (Set.Iic z)

/-- **C47(1) with `Λ̂_T`: the printed rule fails for data-selected convex sets.** -/
theorem c47_convex_dataSelected_undercovers_plugin :
    C47_convex_dataSelected_undercovers_plugin := by
  intro η₀ h0 h1 V₀ z hz
  set Φz := (gaussianReal 0 1).real (Set.Iic z) with hΦz
  have hgap : 0 < 1 - Φz := sub_pos.2 (gaussianReal_real_Iic_lt_one z)
  -- the coverage set is the two-sided plug-in interval
  have hset : ∀ T : ℕ, {ω' : Fin T → Tuple Unit (Fin 2) | oMDP.valueFixedPoint oPolicy () ∈
        signSel (z * Real.sqrt (lambdaHat oMDP η₀ V₀ ω' () () / T))
          (prAverage oMDP η₀ V₀ ω' ())} =
      {ω' | |prAverage oMDP η₀ V₀ ω' () - oMDP.valueFixedPoint oPolicy ()| ≤
          z * Real.sqrt (lambdaHat oMDP η₀ V₀ ω' () () / T)} := by
    intro T
    ext ω'
    simp only [Set.mem_setOf_eq, oneState_valueFixedPoint, one_mem_signSel_iff]
  have hlim : Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple Unit (Fin 2),
      pathWeight oMDP oPolicy oMu ω *
        {ω' : Fin T → Tuple Unit (Fin 2) | oMDP.valueFixedPoint oPolicy () ∈
          signSel (z * Real.sqrt (lambdaHat oMDP η₀ V₀ ω' () () / T))
            (prAverage oMDP η₀ V₀ ω' ())}.indicator 1 ω) atTop (𝓝 (2 * Φz - 1)) := by
    simp only [hset]
    rw [hΦz, gaussianReal_real_Iic]
    exact oneState_tendsto_twoSided_plugin h0 h1 V₀ hz
  refine ⟨fun T ω ↦ convex_signSel _ _, fun T _ ω ↦ ⟨?_, fun hL ↦ ?_⟩, hlim, ?_, by linarith⟩
  · exact le_gaussianReal_signSel _ hz _
  · have hT : (0 : ℝ) < T := by exact_mod_cast ‹1 ≤ T›
    exact gaussianReal_signSel_of_pos _ z (div_pos hL hT)
  · exact (hlim.eventually (gt_mem_nhds (by linarith : 2 * Φz - 1 < Φz - (1 - Φz) / 2))).mono
      fun T hT ↦ hT.le

end StatisticalRL.Ch7Rest.TDInference
