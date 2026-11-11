import Formalization.TDInference.PluginCovariance.Consistency
import Formalization.TDInference.PolyakRuppertRemainder
import Mathlib.Algebra.Order.Chebyshev

/-!
# `Λ̂_T` is consistent for the corrected `Λ = A⁻¹Γ_trueA⁻ᵀ` (C3(c)–(e))

Source: `chapters/inference.tex:165–184` (`Ā_T`, `Γ̂_T` :166–168, weights :175–177,
`eq:defn-hat-Lambda` :180–182, "the final estimator of `Λ⋆`" :184). The printed target `Λ⋆`
(with `r(s) = r_π(s)`) is refuted in `TDInference/PluginCovariance/PrintedLambdaRefutation.lean` (SOURCE-ISSUES C43). Here the
corrected target `trueLambda = A⁻¹ diag(Γ_true) A⁻ᵀ` is proved: for full-support `μ`,
`0 < η₀ ≤ 1` (wider than the printed `(0, 1/4)`), every `V₀`, and **without** `Γ_true ≻ 0`,
`P(∃ s s', ε < |Λ̂_T(s,s') − Λ(s,s')|) → 0` for every `ε > 0` (`eq_defn_hat_Lambda_corrected`).

Steps.
* (c) `E(V̄_T(u) − V^π(u))² ≤ C/T` (`exists_sum_pathWeight_mul_sq_prAverage_sub_le`), from the
  Polyak–Ruppert `L²` remainder (`weightedL2_scaledError_sub_prGaussPart_le_rpow`) and the exact
  second moment `E W_T(u)² = Λ(u,u)` (`sum_pathWeight_mul_prGaussPart_mul`). Pathwise
  `|V̄_T(u) − V^π(u)| ≤ D` (`abs_tdIter_sub_le`). Then
  `|Γ̂_T(i,i) − Γ̂^{or}_T(i)| ≤ 4(B+D) ∑_u |V̄_T(u) − V^π(u)|` (`abs_gammaHat_sub_oracle_le`), so
  `E(Γ̂_T(i,i) − Γ̂^{or}_T(i))² ≤ C'/T`.
* (d) Inverse perturbation, qualitatively: `X ↦ X⁻¹` is continuous at the invertible `A`
  (`continuousAt_matrix_inv`), so `(X, Y) ↦ (X⁻¹YX⁻ᵀ)(s,s')` is continuous at `(A, diag Γ_true)`;
  this yields `δ > 0` such that entrywise `δ`-closeness of `(Ā_T, Γ̂_T)` forces
  `|Λ̂_T(s,s') − Λ(s,s')| < ε` (`exists_delta_lambda`). `δ` comes from continuity, at `A`, of the
  map built from Lean's actual `Matrix.inv` (which agrees with the true inverse near `A`). So the
  closeness implication holds pathwise whatever value `Matrix.inv` takes, and the singular event
  needs no separate term.
* (e) Union bound over the `Ā` entries (C3(a)), the substitution term (c) and the oracle term
  (C3(b)); every piece is `O(1/T)`.

Rate caveat: the result is convergence in probability. Each piece is `O(1/T)`, but `δ` comes from
continuity and is not explicit, so no explicit rate in `ε` is claimed.

Norms are entrywise absolute values throughout (no matrix norm instance is used).

Junk value: on the event that some state is unsampled, `Ā_T` is singular and the printed `Λ̂_T` is
undefined (C47(4)); Lean's `Matrix.inv` returns 0 there, so `lambdaHat = 0` on that event, whose
probability is charged in the bound. The conclusion does not depend on the junk convention, since
`P(Ā_T singular) ≤ ∑_s (1 − μ(s))^T → 0` (`pathProb_aBar_singular_le`).

Restricted variant (`eq_defn_hat_Lambda_restricted`, `TDInference/PluginCovariance/PrintedLambdaRefutation.lean`): when
`r(s,·)` is constant on the support of `π(·|s)` for every `s` (state-only rewards or deterministic
`π`), `Γ_true = Γ_printed`, so `Λ̂_T` is consistent for the printed `Λ⋆` (SOURCE-ISSUES C43 scope).
-/

open Filter Topology
open scoped BigOperators Matrix
open Finset

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-! ## Bridge to the operator form -/

/-- The plug-in matrix `A_t` acts as the operator `sampleA` of `TDInference/Operator.lean`. -/
theorem sampleAMat_mulVec (M : DiscountedMDP State Action) (x : Tuple State Action)
    (v : State → ℝ) : (sampleAMat M x).mulVec v = sampleA M x v := by
  funext i
  rw [sampleA_apply]
  simp only [Matrix.mulVec, dotProduct, sampleAMat_apply]
  by_cases hi : i = x.1
  · subst hi
    simp only [if_true]
    rw [Finset.sum_congr rfl fun j _ ↦ by rw [sub_mul, mul_assoc]]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq', ite_mul]
  · simp [hi]

/-! ## Generic helpers -/

omit [DecidableEq State] in
theorem pathProb_union_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) (E F : Set (Fin T → Tuple State Action)) :
    pathProb M π μ T (E ∪ F) ≤ pathProb M π μ T E + pathProb M π μ T F := by
  simp only [pathProb, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ ↦ ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
  have hE := Set.indicator_nonneg (s := E) (fun _ _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)) ω
  have hF := Set.indicator_nonneg (s := F) (fun _ _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)) ω
  by_cases h : ω ∈ E ∪ F
  · rw [Set.indicator_of_mem h]
    rcases h with h | h
    · rw [Set.indicator_of_mem h]; linarith
    · rw [Set.indicator_of_mem (s := F) h]; linarith
  · rw [Set.indicator_of_notMem h]; linarith

/-- A nonnegative sequence bounded by `c/T` for `T ≥ 1` tends to `0`. -/
theorem tendsto_zero_of_le_div {f : ℕ → ℝ} (c : ℝ) (hf0 : ∀ T, 0 ≤ f T)
    (hf : ∀ T, 1 ≤ T → f T ≤ c / T) : Tendsto f atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall hf0)
    (by filter_upwards [eventually_ge_atTop 1] with T hT; exact hf T hT)
    (tendsto_const_div_atTop_nhds_zero_nat c)

omit [DecidableEq State] in
/-- Chebyshev turned into a `c/T` bound. -/
theorem pathProb_lt_abs_le_div (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (g : (Fin T → Tuple State Action) → ℝ) {η c : ℝ} (hη : 0 < η)
    (hg : ∑ ω, pathWeight M π μ ω * g ω ^ 2 ≤ c / T) :
    pathProb M π μ T {ω | η < |g ω|} ≤ (c / η ^ 2) / T := by
  refine (pathProb_lt_abs_le M π μ T g hη).trans ?_
  rw [div_div, mul_comm (η ^ 2), ← div_div]
  exact div_le_div_of_nonneg_right hg (by positivity)

/-! ## (c) Second moment of `V̄_T − V^π` and the substitution step -/

theorem prAverage_sub_apply (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) (ω : Fin T → Tuple State Action) (u : State) :
    prAverage M η₀ V₀ ω u - M.valueFixedPoint π u =
      (T : ℝ)⁻¹ * ∑ t ∈ range T, (tdIter M η₀ V₀ ω (t + 1) u - M.valueFixedPoint π u) := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hT)
  simp only [prAverage, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- Pathwise `|V̄_T(u) − V^π(u)| ≤ D` (`D = tdPathBound`). -/
theorem abs_prAverage_sub_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T)
    (ω : Fin T → Tuple State Action) (u : State) :
    |prAverage M η₀ V₀ ω u - M.valueFixedPoint π u| ≤ tdPathBound M π V₀ := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  rw [prAverage_sub_apply M π η₀ V₀ hT, abs_mul, abs_of_pos (inv_pos.2 hT0)]
  calc (T : ℝ)⁻¹ * |∑ t ∈ range T, (tdIter M η₀ V₀ ω (t + 1) u - M.valueFixedPoint π u)|
      ≤ (T : ℝ)⁻¹ * ∑ t ∈ range T, tdPathBound M π V₀ := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ ↦ ?_)
        exact abs_tdIter_sub_le M π h0 h1 V₀ ω (t + 1) u
    _ = tdPathBound M π V₀ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

/-- `E(V̄_T(u) − V^π(u))² ≤ C/T` for every `T ≥ 1`, any `V₀`, `0 < η₀ ≤ 1`, full-support `μ`. -/
theorem exists_sum_pathWeight_mul_sq_prAverage_sub_le [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, 1 ≤ T → ∀ u : State,
      ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (prAverage M η₀ V₀ ω u - M.valueFixedPoint π u) ^ 2 ≤ C / T := by
  set μmin := diagMin μ.prob
  have hμmin0 : 0 < μmin := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, μmin ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (Finset.mem_univ s)
  set K := Fintype.card State * prRemainderConst M π V₀ μmin η₀ / ((1 - M.discount) * μmin)
  let c : State → ℝ := fun u ↦ (|K| + Real.sqrt (trueLambda M π μ u u)) ^ 2
  refine ⟨∑ u, c u, Finset.sum_nonneg fun u _ ↦ sq_nonneg _, fun T hT u ↦ ?_⟩
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hw := pathWeight_nonneg M π μ (T := T)
  -- the `L²` norm of `√T Δ̄_T(u)`
  have hsplit : (fun ω : Fin T → Tuple State Action ↦ scaledError M π η₀ V₀ ω u) =
      (fun ω ↦ scaledError M π η₀ V₀ ω u - prGaussPart M π μ ω u) +
        fun ω ↦ prGaussPart M π μ ω u := by
    funext ω; simp
  have hW : weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
      prGaussPart M π μ ω u) = Real.sqrt (trueLambda M π μ u u) := by
    unfold weightedL2
    congr 1
    rw [trueLambda, ← sum_pathWeight_mul_prGaussPart_mul M π μ hT u u]
    exact Finset.sum_congr rfl fun ω _ ↦ by ring
  have hrem := weightedL2_scaledError_sub_prGaussPart_le_rpow M π μ h0 h1 V₀ hμmin0 hμmin hT u
  have hpow : (T : ℝ) ^ (-(1 / 6 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (by norm_num)
  have hpow0 : 0 ≤ (T : ℝ) ^ (-(1 / 6 : ℝ)) := by positivity
  have hrem' : weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
      scaledError M π η₀ V₀ ω u - prGaussPart M π μ ω u) ≤ |K| := by
    refine hrem.trans ?_
    calc K * (T : ℝ) ^ (-(1 / 6 : ℝ)) ≤ |K| * (T : ℝ) ^ (-(1 / 6 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) hpow0
      _ ≤ |K| * 1 := mul_le_mul_of_nonneg_left hpow (abs_nonneg K)
      _ = |K| := mul_one _
  have hL : weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
      scaledError M π η₀ V₀ ω u) ≤ |K| + Real.sqrt (trueLambda M π μ u u) := by
    rw [hsplit]
    refine (weightedL2_add_le hw _ _).trans ?_
    rw [hW]; linarith
  have hsq : ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
      scaledError M π η₀ V₀ ω u ^ 2 ≤ c u := by
    rw [← sq_weightedL2 hw]
    exact pow_le_pow_left₀ (weightedL2_nonneg _ _) hL 2
  have hrel : ∀ ω : Fin T → Tuple State Action,
      (prAverage M η₀ V₀ ω u - M.valueFixedPoint π u) ^ 2 =
        scaledError M π η₀ V₀ ω u ^ 2 / T := by
    intro ω
    simp only [scaledError, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_pow,
      Real.sq_sqrt hT0.le]
    field_simp
  simp_rw [hrel, mul_div_assoc', ← Finset.sum_div]
  refine div_le_div_of_nonneg_right (hsq.trans ?_) hT0.le
  exact Finset.single_le_sum (f := c) (fun v _ ↦ sq_nonneg _) (Finset.mem_univ u)

/-- **Substitution, pathwise.** `|Γ̂_T(i,i) − Γ̂^{or}_T(i)| ≤ 4(B+D) ∑_u |V̄_T(u) − V^π(u)|`. -/
theorem abs_gammaHat_sub_oracle_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {T : ℕ} (hT : 1 ≤ T) (ω : Fin T → Tuple State Action) (i : State) :
    |gammaHat M η₀ V₀ ω i i - oracleGammaHat M π ω i| ≤
      4 * (tdNoiseBound M π + tdPathBound M π V₀) *
        ∑ u, |prAverage M η₀ V₀ ω u - M.valueFixedPoint π u| := by
  set V := M.valueFixedPoint π
  set Vb := prAverage M η₀ V₀ ω
  set B := tdNoiseBound M π
  set D := tdPathBound M π V₀
  set m := ∑ u, |Vb u - V u|
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hB := tdNoiseBound_pos M π
  have hD := tdPathBound_nonneg M π V₀
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun u _ ↦ abs_nonneg _
  have hmu : ∀ u, |Vb u - V u| ≤ m := fun u ↦
    Finset.single_le_sum (f := fun u ↦ |Vb u - V u|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ u)
  have hDu : ∀ u, |Vb u - V u| ≤ D := fun u ↦ abs_prAverage_sub_le M π h0 h1 V₀ hT ω u
  rw [gammaHat_eq_gammaHatAt, gammaHatAt_apply, if_pos rfl, oracleGammaHat,
    ← Finset.sum_sub_distrib]
  have hterm : ∀ t : Fin T, |pluginWeight T t * (if (ω t).1 = i then
      (Vb i - M.discount * Vb (ω t).2.2 - M.reward (ω t).1 (ω t).2.1) ^ 2 else 0) -
      pluginWeight T t * (if i = (ω t).1 then tdNoise M π (ω t) ^ 2 else 0)| ≤
      pluginWeight T t * (4 * (B + D) * m) := by
    intro t
    have hw := pluginWeight_nonneg T t
    rw [← mul_sub, abs_mul, abs_of_nonneg hw]
    refine mul_le_mul_of_nonneg_left ?_ hw
    by_cases h : (ω t).1 = i
    · rw [if_pos h, if_pos h.symm]
      set x := ω t
      set ξ := tdNoise M π x
      set d := (Vb i - V i) - M.discount * (Vb x.2.2 - V x.2.2)
      have hξ : |ξ| ≤ B := abs_tdNoise_le M π x
      have hrep : Vb i - M.discount * Vb x.2.2 - M.reward x.1 x.2.1 = ξ + d := by
        simp only [ξ, d, tdNoise, h]; ring
      have hd : |d| ≤ 2 * m := by
        have h2 : |M.discount * (Vb x.2.2 - V x.2.2)| ≤ m := by
          rw [abs_mul, abs_of_nonneg hγ0]
          calc M.discount * |Vb x.2.2 - V x.2.2| ≤ 1 * |Vb x.2.2 - V x.2.2| :=
                mul_le_mul_of_nonneg_right hγ1.le (abs_nonneg _)
            _ ≤ m := by rw [one_mul]; exact hmu _
        calc |d| ≤ |Vb i - V i| + |M.discount * (Vb x.2.2 - V x.2.2)| := abs_sub _ _
          _ ≤ m + m := add_le_add (hmu i) h2
          _ = 2 * m := by ring
      have hdD : |d| ≤ 2 * D := by
        have h2 : |M.discount * (Vb x.2.2 - V x.2.2)| ≤ D := by
          rw [abs_mul, abs_of_nonneg hγ0]
          calc M.discount * |Vb x.2.2 - V x.2.2| ≤ 1 * |Vb x.2.2 - V x.2.2| :=
                mul_le_mul_of_nonneg_right hγ1.le (abs_nonneg _)
            _ ≤ D := by rw [one_mul]; exact hDu _
        calc |d| ≤ |Vb i - V i| + |M.discount * (Vb x.2.2 - V x.2.2)| := abs_sub _ _
          _ ≤ D + D := add_le_add (hDu i) h2
          _ = 2 * D := by ring
      rw [hrep, show (ξ + d) ^ 2 - ξ ^ 2 = d * (2 * ξ + d) by ring, abs_mul]
      have h2 : |2 * ξ + d| ≤ 2 * B + 2 * D := by
        calc |2 * ξ + d| ≤ |2 * ξ| + |d| := abs_add_le _ _
          _ = 2 * |ξ| + |d| := by rw [abs_mul, abs_two]
          _ ≤ 2 * B + 2 * D := by linarith
      calc |d| * |2 * ξ + d| ≤ (2 * m) * (2 * B + 2 * D) :=
            mul_le_mul hd h2 (abs_nonneg _) (by positivity)
        _ = 4 * (B + D) * m := by ring
    · rw [if_neg h, if_neg (Ne.symm h), sub_zero, abs_zero]
      positivity
  calc |∑ t, (pluginWeight T t * (if (ω t).1 = i then
          (Vb i - M.discount * Vb (ω t).2.2 - M.reward (ω t).1 (ω t).2.1) ^ 2 else 0) -
        pluginWeight T t * (if i = (ω t).1 then tdNoise M π (ω t) ^ 2 else 0))|
      ≤ ∑ t, pluginWeight T t * (4 * (B + D) * m) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ ↦ hterm t)
    _ = 4 * (B + D) * m := by rw [← Finset.sum_mul, sum_pluginWeight hT, one_mul]

/-- **Substitution, second moment.** `E(Γ̂_T(i,i) − Γ̂^{or}_T(i))² ≤ C'/T`. -/
theorem exists_sum_pathWeight_mul_sq_gammaHat_sub_oracle_le [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) :
    ∃ C : ℝ, ∀ T : ℕ, 1 ≤ T → ∀ i : State,
      ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (gammaHat M η₀ V₀ ω i i - oracleGammaHat M π ω i) ^ 2 ≤ C / T := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_pathWeight_mul_sq_prAverage_sub_le M π μ hμ h0 h1 V₀
  set L := 4 * (tdNoiseBound M π + tdPathBound M π V₀)
  set S : ℝ := (Fintype.card State : ℝ)
  refine ⟨L ^ 2 * (S * (S * C)), fun T hT i ↦ ?_⟩
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hpt : ∀ ω : Fin T → Tuple State Action,
      (gammaHat M η₀ V₀ ω i i - oracleGammaHat M π ω i) ^ 2 ≤
        L ^ 2 * (S * ∑ u, (prAverage M η₀ V₀ ω u - M.valueFixedPoint π u) ^ 2) := by
    intro ω
    have h := abs_gammaHat_sub_oracle_le M π h0.le h1 V₀ hT ω i
    have hm0 : 0 ≤ ∑ u, |prAverage M η₀ V₀ ω u - M.valueFixedPoint π u| :=
      Finset.sum_nonneg fun u _ ↦ abs_nonneg _
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun u ↦ |prAverage M η₀ V₀ ω u - M.valueFixedPoint π u|)
    simp only [sq_abs, Finset.card_univ] at hcs
    calc (gammaHat M η₀ V₀ ω i i - oracleGammaHat M π ω i) ^ 2
        = |gammaHat M η₀ V₀ ω i i - oracleGammaHat M π ω i| ^ 2 := (sq_abs _).symm
      _ ≤ (L * ∑ u, |prAverage M η₀ V₀ ω u - M.valueFixedPoint π u|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = L ^ 2 * (∑ u, |prAverage M η₀ V₀ ω u - M.valueFixedPoint π u|) ^ 2 := by ring
      _ ≤ L ^ 2 * (S * ∑ u, (prAverage M η₀ V₀ ω u - M.valueFixedPoint π u) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
  calc ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (gammaHat M η₀ V₀ ω i i - oracleGammaHat M π ω i) ^ 2
      ≤ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          (L ^ 2 * (S * ∑ u, (prAverage M η₀ V₀ ω u - M.valueFixedPoint π u) ^ 2)) :=
        Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hpt ω) (pathWeight_nonneg M π μ ω)
    _ = L ^ 2 * (S * ∑ u, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          (prAverage M η₀ V₀ ω u - M.valueFixedPoint π u) ^ 2) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
    _ ≤ L ^ 2 * (S * ∑ _u : State, C / T) := by
        gcongr with u
        exact hC T hT u
    _ = L ^ 2 * (S * (S * C)) / T := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ## (d) Continuity of `(X, Y) ↦ X⁻¹YX⁻ᵀ` at an invertible `X` -/

omit [Fintype Action] in
/-- If `A` is invertible, entrywise `δ`-closeness of `(X, Y)` to `(A, G)` forces the `(s,s')`
entry of `X⁻¹YX⁻ᵀ` within `ε` of that of `A⁻¹GA⁻ᵀ`. -/
theorem exists_delta_lambda (A G : Matrix State State ℝ) (hA : A.det ≠ 0) (s s' : State)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ X Y : Matrix State State ℝ, (∀ i j, |X i j - A i j| < δ) →
      (∀ i j, |Y i j - G i j| < δ) →
        |(X⁻¹ * Y * X⁻¹ᵀ) s s' - (A⁻¹ * G * A⁻¹ᵀ) s s'| < ε := by
  let P := (State → State → ℝ) × (State → State → ℝ)
  let H : Matrix State State ℝ × Matrix State State ℝ → ℝ := fun q ↦ (q.1⁻¹ * q.2 * q.1⁻¹ᵀ) s s'
  let F : P → ℝ := fun p ↦ H (Matrix.of p.1, Matrix.of p.2)
  have hRing : ContinuousAt Ring.inverse A.det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hA
  have hinv : ContinuousAt (fun q : Matrix State State ℝ × Matrix State State ℝ ↦ q.1⁻¹) (A, G) :=
    (continuousAt_matrix_inv A hRing).comp continuous_fst.continuousAt
  have hmul : Continuous fun q : Matrix State State ℝ × Matrix State State ℝ ×
      Matrix State State ℝ ↦ (q.1 * q.2.1 * q.2.2) s s' :=
    ((continuous_fst.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      (continuous_snd.comp continuous_snd)).matrix_elem s s'
  have hin : ContinuousAt (fun q : Matrix State State ℝ × Matrix State State ℝ ↦
      (q.1⁻¹, q.2, q.1⁻¹ᵀ)) (A, G) :=
    hinv.prodMk (continuous_snd.continuousAt.prodMk
      (continuous_id.matrix_transpose.continuousAt.comp hinv))
  have hH : ContinuousAt H (A, G) := by
    simpa only [Function.comp_def] using hmul.continuousAt.comp hin
  have hof : Continuous fun x : State → State → ℝ ↦ Matrix.of x :=
    continuous_matrix fun i j ↦ by
      simpa only [Matrix.of_apply] using (continuous_apply j).comp (continuous_apply i)
  have hφ : Continuous fun p : P ↦ (Matrix.of p.1, Matrix.of p.2) :=
    (hof.comp continuous_fst).prodMk (hof.comp continuous_snd)
  have hF : ContinuousAt F ((A : State → State → ℝ), (G : State → State → ℝ)) :=
    hH.comp_of_eq hφ.continuousAt rfl
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hF ε hε
  refine ⟨δ, hδ, fun X Y hX hY ↦ ?_⟩
  have hd : dist (((X : State → State → ℝ), (Y : State → State → ℝ)) : P)
      ((A : State → State → ℝ), (G : State → State → ℝ)) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · refine (dist_pi_lt_iff hδ).2 fun i ↦ (dist_pi_lt_iff hδ).2 fun j ↦ ?_
      rw [Real.dist_eq]; exact hX i j
    · refine (dist_pi_lt_iff hδ).2 fun i ↦ (dist_pi_lt_iff hδ).2 fun j ↦ ?_
      rw [Real.dist_eq]; exact hY i j
  have := h hd
  rw [Real.dist_eq] at this
  exact this

/-! ## (e) Assembly -/

/-- One entry: `P(ε < |Λ̂_T(s,s') − Λ(s,s')|) → 0`. -/
theorem tendsto_pathProb_lambdaHat_entry [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s)
    {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (s s' : State) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun T : ℕ ↦ pathProb M π μ T
      {ω | ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|}) atTop (𝓝 0) := by
  set A := tdA M π μ
  set G := Matrix.diagonal (trueGamma M π μ)
  have hμmin0 : 0 < diagMin μ.prob := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, diagMin μ.prob ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (Finset.mem_univ s)
  have hA : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)).ne_zero
  obtain ⟨δ, hδ, hcont⟩ := exists_delta_lambda A G hA s s' hε
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ4 : 0 < δ / 4 := by positivity
  obtain ⟨Csub, hCsub⟩ :=
    exists_sum_pathWeight_mul_sq_gammaHat_sub_oracle_le M π μ hμ h0 h1 V₀
  -- the three families of bad events
  let EA : (T : ℕ) → Set (Fin T → Tuple State Action) := fun T ↦
    {ω | ∃ i j, δ / 2 < |aBar M ω i j - A i j|}
  let ES : (T : ℕ) → State → Set (Fin T → Tuple State Action) := fun T i ↦
    {ω | δ / 4 < |gammaHat M η₀ V₀ ω i i - oracleGammaHat M π ω i|}
  let EO : (T : ℕ) → State → Set (Fin T → Tuple State Action) := fun T i ↦
    {ω | δ / 4 < |oracleGammaHat M π ω i - trueGamma M π μ i|}
  -- inclusion
  have hsub : ∀ T : ℕ, {ω : Fin T → Tuple State Action |
      ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|} ⊆
        EA T ∪ {ω | ∃ i, ω ∈ ES T i ∪ EO T i} := by
    intro T ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_lt, EA, ES, EO] at hnot
    obtain ⟨hA', hG'⟩ := hnot
    have hX : ∀ i j, |aBar M ω i j - A i j| < δ := fun i j ↦ by linarith [hA' i j]
    have hY : ∀ i j, |gammaHat M η₀ V₀ ω i j - G i j| < δ := by
      intro i j
      by_cases hij : i = j
      · subst hij
        have h1' := (hG' i).1
        have h2' := (hG' i).2
        have htri := abs_sub_le (gammaHat M η₀ V₀ ω i i) (oracleGammaHat M π ω i)
          (trueGamma M π μ i)
        simp only [G, Matrix.diagonal_apply_eq]
        linarith
      · rw [gammaHat_eq_gammaHatAt, gammaHatAt_apply, if_neg hij]
        simp only [G, Matrix.diagonal_apply_ne _ hij, sub_zero, abs_zero]
        exact hδ
    have := hcont (aBar M ω) (gammaHat M η₀ V₀ ω) hX hY
    simp only [Set.mem_setOf_eq] at hω
    exact absurd hω (not_lt.2 (le_of_lt this))
  -- each family tends to zero
  have tA : Tendsto (fun T : ℕ ↦ pathProb M π μ T (EA T)) atTop (𝓝 0) :=
    tendsto_zero_of_le_div ((Fintype.card State : ℝ) ^ 2 / (δ / 2) ^ 2)
      (fun T ↦ pathProb_nonneg M π μ T _) fun T hT ↦ by
        refine (pathProb_exists_abs_aBar_sub_gt_le M π μ hT hδ2).trans (le_of_eq ?_)
        rw [div_div]
  have tS : ∀ i, Tendsto (fun T : ℕ ↦ pathProb M π μ T (ES T i)) atTop (𝓝 0) := fun i ↦
    tendsto_zero_of_le_div (Csub / (δ / 4) ^ 2) (fun T ↦ pathProb_nonneg M π μ T _)
      fun T hT ↦ pathProb_lt_abs_le_div M π μ _ hδ4 (hCsub T hT i)
  have tO : ∀ i, Tendsto (fun T : ℕ ↦ pathProb M π μ T (EO T i)) atTop (𝓝 0) := fun i ↦
    tendsto_zero_of_le_div (2 * tdNoiseBound M π ^ 4 / (δ / 4) ^ 2)
      (fun T ↦ pathProb_nonneg M π μ T _) fun T hT ↦
        pathProb_lt_abs_le_div M π μ _ hδ4
          (sum_pathWeight_mul_sq_oracleGammaHat_sub_le M π μ hT i)
  have tsum : Tendsto (fun T : ℕ ↦ pathProb M π μ T (EA T) +
      ∑ i, (pathProb M π μ T (ES T i) + pathProb M π μ T (EO T i))) atTop (𝓝 0) := by
    have := tA.add (tendsto_finset_sum (Finset.univ : Finset State)
      fun i _ ↦ (tS i).add (tO i))
    simpa using this
  refine squeeze_zero (fun T ↦ pathProb_nonneg M π μ T _) (fun T ↦ ?_) tsum
  calc pathProb M π μ T {ω | ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|}
      ≤ pathProb M π μ T (EA T ∪ {ω | ∃ i, ω ∈ ES T i ∪ EO T i}) :=
        pathProb_mono M π μ T (hsub T)
    _ ≤ pathProb M π μ T (EA T) + pathProb M π μ T {ω | ∃ i, ω ∈ ES T i ∪ EO T i} :=
        pathProb_union_le M π μ T _ _
    _ ≤ pathProb M π μ T (EA T) + ∑ i, (pathProb M π μ T (ES T i) + pathProb M π μ T (EO T i)) := by
        gcongr
        refine (pathProb_exists_le M π μ T _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        exact pathProb_union_le M π μ T _ _

/-- **Corrected consistency of the plug-in estimator** (`eq:defn-hat-Lambda`,
`chapters/inference.tex:180–182`, "the final estimator of `Λ⋆`" :184), with the corrected target
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (SOURCE-ISSUES C43) in place of the printed `Λ⋆`: for every instance with
full-support `μ`, every `η₀ ∈ (0,1]` (containing the printed `(0, 1/4)`), every `V₀` and every
`ε > 0`, `P(∃ s s', ε < |Λ̂_T(s,s') − Λ(s,s')|) → 0`. No `Γ_true ≻ 0` is assumed. Convergence in
probability only; no explicit rate. Junk value: on the event that some state is unsampled, `Ā_T`
is singular and the printed `Λ̂_T` is undefined (C47(4)); Lean's `Matrix.inv` returns 0 there, so
`lambdaHat = 0` on that event, whose probability is charged in the bound. The conclusion does not
depend on the junk convention, since `P(Ā_T singular) ≤ ∑_s (1 − μ(s))^T → 0`
(`pathProb_aBar_singular_le`). -/
def Eq_defn_hat_Lambda_corrected : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ ≤ 1 →
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun T : ℕ ↦ pathProb M π μ T
        {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|}) atTop (𝓝 0)

omit [Fintype State] [Fintype Action] [DecidableEq State] in
theorem eq_defn_hat_Lambda_corrected : Eq_defn_hat_Lambda_corrected := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 ε hε
  have tall := tendsto_finset_sum (Finset.univ : Finset (State × State)) fun p _ ↦
    tendsto_pathProb_lambdaHat_entry M π μ hμ h0 h1 V₀ p.1 p.2 hε
  simp only [Finset.sum_const_zero] at tall
  refine squeeze_zero (fun T ↦ pathProb_nonneg M π μ T _) (fun T ↦ ?_) tall
  have hset : {ω : Fin T → Tuple State Action |
      ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|} =
      {ω | ∃ p : State × State, ω ∈ {ω : Fin T → Tuple State Action |
        ε < |lambdaHat M η₀ V₀ ω p.1 p.2 - trueLambda M π μ p.1 p.2|}} := by
    ext ω; simp
  rw [hset]
  exact pathProb_exists_le M π μ T _

end StatisticalRL.Ch7Rest.TDInference
