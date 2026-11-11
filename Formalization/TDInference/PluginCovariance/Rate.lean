import Formalization.Analysis.MatrixInversePerturbation
import Formalization.TDInference.PluginCovariance.CorrectedConsistency
import Formalization.TDInference.Confidence.Regions

/-!
# Quantitative consistency of `Λ̂_T` and `Λ̂_T⁻¹` (rate `C/(ε²T)`)

Source: `chapters/inference.tex:165–184` (`Ā_T`, `Γ̂_T` :166–168, weights :175–177,
`eq:defn-hat-Lambda` :180–182). Infrastructure for finite-`T` rates of the plug-in confidence rules
(`eq:convex.Cdelta`, :187–213); the target is the corrected `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`
(`trueLambda`, SOURCE-ISSUES C43).

* `exists_pathProb_lambdaHat_sub_gt_le`: for full-support `μ`, `0 < η₀ ≤ 1` and every `V₀`
  (no `Γ_true ≻ 0`), there is an instance constant `C > 0` with
  `P(∃ s s', ε < |Λ̂_T(s,s') − Λ(s,s')|) ≤ C/(ε²T)` for all `T ≥ 1` and `0 < ε ≤ 1`.
* `exists_pathProb_lambdaHat_inv_sub_gt_le`: under `Γ_true ≻ 0` in addition, the same bound for
  `Λ̂_T⁻¹` against `Λ⁻¹`.

Proof. The continuity step `exists_delta_lambda` of `TDInference/PluginCovariance/CorrectedConsistency.lean` is replaced
by the explicit perturbation bound `abs_inv_mul_mul_inv_transpose_sub_le`
(`Formalization/Analysis/MatrixInversePerturbation.lean`, `ℓ∞` operator norm): with
`a = ‖A⁻¹‖`, `g = ∑_s |Γ_true(s)|`, `L = 6a³S(g+1) + 2a²`, `K = 2L + 2aS + 2` and `δ = ε/K`,
entrywise `δ`-closeness of `(Ā_T, Γ̂_T)` to `(A, diag Γ_true)` forces every entry of
`Λ̂_T − Λ` within `Lδ ≤ ε`. The bad event is the union of `∃ i j, δ < |Ā_T(i,j) − A(i,j)|`
(`≤ S²/(δ²T)`), the substitution events `δ/2 < |Γ̂_T(i,i) − Γ̂^{or}_T(i)|` and the oracle events
`δ/2 < |Γ̂^{or}_T(i) − Γ_true(i)|` (Chebyshev from the second-moment bounds). Hence
`C = K²(S² + S(4|C'| + 8B⁴)) + 1`, with `C'` the (existential) substitution constant of
`exists_sum_pathWeight_mul_sq_gammaHat_sub_oracle_le` and `B = tdNoiseBound`.

Junk value: on the event that some state is unsampled, `Ā_T` is singular (C47(4)) and Lean's
`Matrix.inv` returns `0`. That event lies inside the bad event: off it, `S‖A⁻¹‖δ ≤ 1/2` and
entrywise `δ`-closeness force `Ā_T` invertible (`isUnit_det_of_abs_sub_le`). So the bound is
charged quantitatively and does not depend on the junk convention. The same holds for `Λ̂_T⁻¹`:
off the bad event `Λ̂_T` is entrywise close to the invertible `Λ`, hence invertible.
-/

open Finset
open scoped BigOperators Matrix

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability
open StatisticalRL.Analysis.MatrixInversePerturbation

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- **Quantitative consistency of `Λ̂_T`** for the corrected target `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`:
for full-support `μ`, `0 < η₀ ≤ 1` and every `V₀` there is `C > 0` such that for all `T ≥ 1` and
`0 < ε ≤ 1`, `P(∃ s s', ε < |Λ̂_T(s,s') − Λ(s,s')|) ≤ C/(ε²T)`. No `Γ_true ≻ 0` is assumed. -/
theorem exists_pathProb_lambdaHat_sub_gt_le [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s)
    {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      pathProb M π μ T {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|}
        ≤ C / (ε ^ 2 * T) := by
  have hμmin0 : 0 < diagMin μ.prob := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, diagMin μ.prob ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (Finset.mem_univ s)
  have hAu : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  obtain ⟨Csub, hCsub⟩ :=
    exists_sum_pathWeight_mul_sq_gammaHat_sub_oracle_le M π μ hμ h0 h1 V₀
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Fintype.card State := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ‖(tdA M π μ)⁻¹‖ := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = ∑ i, |trueGamma M π μ i| := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = tdNoiseBound M π := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hS ▸ Nat.cast_nonneg _
  have ha0 : 0 ≤ a := ha ▸ norm_nonneg _
  have hg0 : 0 ≤ g := hg ▸ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 6 * a ^ 3 * S * (g + 1) + 2 * a ^ 2 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hL ▸ by positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * L + 2 * a * S + 2 := ⟨_, rfl⟩
  have hK2 : 2 ≤ K := by rw [hK]; nlinarith [mul_nonneg ha0 hS0]
  have hKpos : 0 < K := by linarith
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = S ^ 2 + S * (4 * |Csub| + 8 * B ^ 4) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ add_nonneg (sq_nonneg _) (mul_nonneg hS0 (by positivity))
  refine ⟨K ^ 2 * D + 1, by positivity, fun T hT ε hε hε1 ↦ ?_⟩
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / K := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδ ▸ div_pos hε hKpos
  have hδK : δ * K = ε := by rw [hδ, div_mul_cancel₀ _ hKpos.ne']
  have hδ1 : δ ≤ 1 := by nlinarith
  have hδ2 : 0 < δ / 2 := by positivity
  -- the deterministic step
  have hsmall : Fintype.card State * ‖(tdA M π μ)⁻¹‖ * δ ≤ 1 / 2 := by
    rw [← hS, ← ha]
    have : 2 * a * S * δ ≤ K * δ :=
      mul_le_mul_of_nonneg_right (by rw [hK]; linarith) hδ0.le
    nlinarith
  have hGb : ∀ i j, |Matrix.diagonal (trueGamma M π μ) i j| ≤ g := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hg]
      exact Finset.single_le_sum (f := fun i ↦ |trueGamma M π μ i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
    · rw [Matrix.diagonal_apply_ne _ hij, abs_zero]; exact hg0
  have hdet : ∀ {n : ℕ} (ω : Fin n → Tuple State Action),
      (∀ i j, |aBar M ω i j - tdA M π μ i j| ≤ δ) →
      (∀ i, |gammaHat M η₀ V₀ ω i i - oracleGammaHat M π ω i| ≤ δ / 2) →
      (∀ i, |oracleGammaHat M π ω i - trueGamma M π μ i| ≤ δ / 2) →
      ∀ s s', |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'| ≤ ε := by
    intro n ω hX hS' hO s s'
    have hY : ∀ i j, |gammaHat M η₀ V₀ ω i j - Matrix.diagonal (trueGamma M π μ) i j| ≤ δ := by
      intro i j
      by_cases hij : i = j
      · subst hij
        have htri := abs_sub_le (gammaHat M η₀ V₀ ω i i) (oracleGammaHat M π ω i)
          (trueGamma M π μ i)
        rw [Matrix.diagonal_apply_eq]
        linarith [hS' i, hO i]
      · rw [gammaHat_eq_gammaHatAt, gammaHatAt_apply, if_neg hij,
          Matrix.diagonal_apply_ne _ hij, sub_zero, abs_zero]
        exact hδ0.le
    have hb := abs_inv_mul_mul_inv_transpose_sub_le hAu hGb hX hY hsmall s s'
    rw [← hS, ← ha] at hb
    have e1 : 6 * a ^ 3 * S * (g + δ) * δ ≤ 6 * a ^ 3 * S * (g + 1) * δ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hδ0.le
    have e2 : L * δ ≤ K * δ :=
      mul_le_mul_of_nonneg_right (by rw [hK]; linarith [mul_nonneg ha0 hS0]) hδ0.le
    have e3 : L * δ = 6 * a ^ 3 * S * (g + 1) * δ + 2 * a ^ 2 * δ := by rw [hL]; ring
    simp only [lambdaHat, trueLambda]
    linarith
  -- the bad events
  let EA : Set (Fin T → Tuple State Action) := {ω | ∃ i j, δ < |aBar M ω i j - tdA M π μ i j|}
  let ES : State → Set (Fin T → Tuple State Action) := fun i ↦
    {ω | δ / 2 < |gammaHat M η₀ V₀ ω i i - oracleGammaHat M π ω i|}
  let EO : State → Set (Fin T → Tuple State Action) := fun i ↦
    {ω | δ / 2 < |oracleGammaHat M π ω i - trueGamma M π μ i|}
  have hsub : {ω : Fin T → Tuple State Action |
      ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|} ⊆
        EA ∪ {ω | ∃ i, ω ∈ ES i ∪ EO i} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_lt, EA, ES, EO] at hnot
    obtain ⟨hA', hG'⟩ := hnot
    obtain ⟨s, s', hss⟩ := hω
    exact absurd hss (not_lt.2 (hdet ω hA' (fun i ↦ (hG' i).1) (fun i ↦ (hG' i).2) s s'))
  have pA : pathProb M π μ T EA ≤ S ^ 2 / (δ ^ 2 * T) := by
    rw [hS]; exact pathProb_exists_abs_aBar_sub_gt_le M π μ hT hδ0
  have pS : ∀ i, pathProb M π μ T (ES i) ≤ (|Csub| / (δ / 2) ^ 2) / T := fun i ↦
    (pathProb_lt_abs_le_div M π μ _ hδ2 (hCsub T hT i)).trans
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))
        hT0.le)
  have pO : ∀ i, pathProb M π μ T (EO i) ≤ (2 * B ^ 4 / (δ / 2) ^ 2) / T := fun i ↦ by
    rw [hB]
    exact pathProb_lt_abs_le_div M π μ _ hδ2
      (sum_pathWeight_mul_sq_oracleGammaHat_sub_le M π μ hT i)
  have htot : pathProb M π μ T {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' -
      trueLambda M π μ s s'|} ≤ D / (δ ^ 2 * T) := by
    calc _ ≤ pathProb M π μ T (EA ∪ {ω | ∃ i, ω ∈ ES i ∪ EO i}) := pathProb_mono M π μ T hsub
      _ ≤ pathProb M π μ T EA + pathProb M π μ T {ω | ∃ i, ω ∈ ES i ∪ EO i} :=
          pathProb_union_le M π μ T _ _
      _ ≤ pathProb M π μ T EA + ∑ i, (pathProb M π μ T (ES i) + pathProb M π μ T (EO i)) := by
          gcongr
          refine (pathProb_exists_le M π μ T _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
          exact pathProb_union_le M π μ T _ _
      _ ≤ S ^ 2 / (δ ^ 2 * T) +
            ∑ _i : State, ((|Csub| / (δ / 2) ^ 2) / T + (2 * B ^ 4 / (δ / 2) ^ 2) / T) := by
          gcongr with i
          · exact pS i
          · exact pO i
      _ = D / (δ ^ 2 * T) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hS, hD]
          field_simp
          ring
  have hfin : D / (δ ^ 2 * T) ≤ (K ^ 2 * D + 1) / (ε ^ 2 * T) := by
    have hδε : δ ^ 2 * T = ε ^ 2 * T / K ^ 2 := by
      rw [← hδK]; field_simp
    rw [hδε, div_div_eq_mul_div, mul_comm D]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  exact htot.trans hfin

/-- **Quantitative consistency of `Λ̂_T⁻¹`** for `Λ⁻¹`, `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`: for
full-support `μ`, `0 < η₀ ≤ 1`, every `V₀` and `Γ_true ≻ 0`, there is `C > 0` such that for all
`T ≥ 1` and `0 < ε ≤ 1`, `P(∃ s s', ε < |Λ̂_T⁻¹(s,s') − Λ⁻¹(s,s')|) ≤ C/(ε²T)`. Here `Λ̂_T⁻¹` is
Lean's `Matrix.inv` (junk `0` on a singular `Λ̂_T`; that event lies inside the bad event). -/
theorem exists_pathProb_lambdaHat_inv_sub_gt_le [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s)
    {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      pathProb M π μ T
          {ω | ∃ s s', ε < |(lambdaHat M η₀ V₀ ω)⁻¹ s s' - (trueLambda M π μ)⁻¹ s s'|}
        ≤ C / (ε ^ 2 * T) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_pathProb_lambdaHat_sub_gt_le M π μ hμ h0 h1 V₀
  have hΛu : IsUnit (trueLambda M π μ).det :=
    Matrix.isUnit_det_of_left_inverse (trueLambda_inv_mul M π μ hμ hΓ)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Fintype.card State := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ‖(trueLambda M π μ)⁻¹‖ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hS ▸ Nat.cast_nonneg _
  have ha0 : 0 ≤ a := ha ▸ norm_nonneg _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * a ^ 2 * S + 2 * a * S + 2 := ⟨_, rfl⟩
  have hK2 : 2 ≤ K := by rw [hK]; nlinarith [mul_nonneg ha0 hS0, mul_nonneg (sq_nonneg a) hS0]
  have hKpos : 0 < K := by linarith
  refine ⟨C₁ * K ^ 2, by positivity, fun T hT ε hε hε1 ↦ ?_⟩
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / K := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδ ▸ div_pos hε hKpos
  have hδK : δ * K = ε := by rw [hδ, div_mul_cancel₀ _ hKpos.ne']
  have hδ1 : δ ≤ 1 := by nlinarith
  have hsmall : Fintype.card State * ‖(trueLambda M π μ)⁻¹‖ * δ ≤ 1 / 2 := by
    rw [← hS, ← ha]
    have : 2 * a * S * δ ≤ K * δ :=
      mul_le_mul_of_nonneg_right (by rw [hK]; nlinarith [mul_nonneg (sq_nonneg a) hS0]) hδ0.le
    nlinarith
  have hsub : {ω : Fin T → Tuple State Action |
      ∃ s s', ε < |(lambdaHat M η₀ V₀ ω)⁻¹ s s' - (trueLambda M π μ)⁻¹ s s'|} ⊆
      {ω | ∃ s s', δ < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_setOf_eq, not_exists, not_lt] at hnot
    obtain ⟨s, s', hss⟩ := hω
    have hb := abs_inv_sub_inv_apply_le hΛu hnot hsmall s s'
    rw [← hS, ← ha] at hb
    have e : 2 * a ^ 2 * S * δ ≤ K * δ :=
      mul_le_mul_of_nonneg_right (by rw [hK]; nlinarith [mul_nonneg ha0 hS0]) hδ0.le
    linarith
  calc _ ≤ _ := pathProb_mono M π μ T hsub
    _ ≤ C₁ / (δ ^ 2 * T) := h₁ T hT δ hδ0 hδ1
    _ = C₁ * K ^ 2 / (ε ^ 2 * T) := by
        rw [← hδK]; field_simp

end StatisticalRL.Ch7Rest.TDInference
