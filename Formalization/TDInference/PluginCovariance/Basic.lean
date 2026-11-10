import Formalization.TDInference.Definitions

/-!
# The plug-in covariance estimator `Λ̂_T` (`eq:defn-hat-Lambda`): basic facts

Source: `chapters/inference.tex:156–185` (paragraph "Covariance matrix estimation"): `Ā_T`, `A_t`
:166, `Γ̂_T`, `b_t` :168 (align* block :165–169), weights `w_{t,T}` :175–177, `eq:defn-hat-Lambda` :180–182 ("the final
estimator of `Λ⋆`"), online claim :185. Source issues: SOURCE-ISSUES C43 (the printed `Γ` omits
the action-reward variance; `Γ̂_T` estimates the true noise covariance `trueGamma`) and C47(4)
(`Ā_T` is singular when a state is unsampled).

The definitions below live in `TDInference/Definitions.lean` (same names, so that the statement index
can use them); this module holds their basic lemmas and the printed consistency reading.

Objects (path level, `ω : Fin T → Tuple`, the sample `ω t` is the `(t+1)`-st tuple
`(s_{t+1}, a_{t+1}, s'_{t+1})`):
* `sampleAMat M x = e_s (e_s − γ e_{s'})ᵀ` and `sampleB M x = r(s,a) e_s` for `x = (s,a,s')` (:166, :168).
* `aBar M ω = T⁻¹ ∑_t A_t` (:166).
* `pluginWeight T t = (t+1) / ∑_{u=1}^T u`, the printed `w_{t+1,T}` (:175–177);
  `pluginWeight_eq` is the printed closed form `2(t+1)/(T(T+1))` and `sum_pluginWeight` is `∑ w = 1`.
* `gammaHat M η₀ V₀ ω = ∑_t w_{t,T} (A_t V̄_T − b_t)(A_t V̄_T − b_t)ᵀ` with `V̄_T = prAverage` (:168);
  `gammaHatAt M V ω` is the same formula at an arbitrary `V`, and `gammaHat = gammaHatAt (prAverage …)`.
* `lambdaHat M η₀ V₀ ω = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ` (`eq:defn-hat-Lambda`, :180–182).

**Junk value (C47(4)).** On the event that some state is unsampled, `Ā_T` is singular and the
printed `Λ̂_T` is undefined; Lean's `Matrix.inv` returns `0` there, so `lambdaHat = 0` on that
event (`lambdaHat_eq_zero_of_det_eq_zero`). That event has probability `≤ ∑_s (1 − μ(s))^T → 0`
(`pathProb_aBar_singular_le`, `TDInference/PluginCovariance/Singular.lean`); the corrected consistency
theorem holds pathwise whatever value `Matrix.inv` takes there (`TDInference/PluginCovariance/CorrectedConsistency.lean`).

The targets: `printedLambda = A⁻¹ diag(Γ_printed) A⁻ᵀ` (the printed `Λ⋆`, :99–117, with
`r(s) = r_π(s)`) and `trueLambda = A⁻¹ diag(Γ_true) A⁻ᵀ` (the C43 correction).
`pathProb` is the probability of an arbitrary event of the sample path under the i.i.d. law.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Matrix

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action]

variable [DecidableEq State]

/-- Real-valued visit count `n_s = #{t : s_t = s}`. -/
noncomputable def pluginVisitCount {T : ℕ} (ω : Fin T → Tuple State Action) (s : State) : ℝ :=
  ∑ t, if (ω t).1 = s then 1 else 0

/-- Real-valued transition count `m_{sj} = #{t : s_t = s, s'_t = j}`. -/
noncomputable def pluginTransCount {T : ℕ} (ω : Fin T → Tuple State Action) (s j : State) : ℝ :=
  ∑ t, if (ω t).1 = s ∧ (ω t).2.2 = j then 1 else 0

/-- "`Λ̂_T` is an estimator of `Λ⋆`" read as consistency for the printed `Λ⋆`
(`eq:defn-hat-Lambda`, `inference.tex:180–182`, "final estimator of `Λ⋆`" :184; `r(s) = r_π(s)`,
SOURCE-ISSUES C43): for every instance with full-support `μ`, `Γ_printed ≻ 0`, every `η₀` in the
printed range `(0, 1/4)` (`inference.tex:134`) and every `V₀`, entrywise convergence in
probability. The source never states consistency in words; this is a reading of :184. The
full-support and `Γ_printed ≻ 0` hypotheses only weaken the claim. Refuted by
`not_eq_defn_hat_Lambda_printed_consistent` (`TDInference/PluginCovariance/PrintedLambdaRefutation.lean`).

Reading caveat (C43): the refutation uses action-dependent rewards with `r(s) = r_π(s)`. With
state-only rewards, or deterministic `π`, `printedGamma = trueGamma`
(`trueGamma_eq_printedGamma_of_reward_const_on_support`), so `printedLambda = trueLambda`, and that
reading is proved (`eq_defn_hat_Lambda_restricted`, from `eq_defn_hat_Lambda_corrected`).

Junk value: on the event that some state is unsampled, `Ā_T` is singular and the printed `Λ̂_T`
is undefined (C47(4)); Lean's `Matrix.inv` returns 0 there, so `lambdaHat = 0` on that event, whose
probability is at most `∑_s (1 − μ(s))^T → 0` (`pathProb_aBar_singular_le`); the refutation does not
depend on that value (`ZeroNoise.pathProb_far_nonsingular_ge`). -/
def Eq_defn_hat_Lambda_printed_consistent : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < printedGamma M π μ s) →
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun T : ℕ ↦ pathProb M π μ T
        {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - printedLambda M π μ s s'|}) atTop (𝓝 0)

/-! ## Basic facts -/

omit [DecidableEq State] in
theorem pathProb_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) (E : Set (Fin T → Tuple State Action)) :
    0 ≤ pathProb M π μ T E :=
  Finset.sum_nonneg fun ω _ ↦ mul_nonneg (pathWeight_nonneg M π μ ω)
    (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)

omit [DecidableEq State] in
theorem pathProb_mono (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) {E F : Set (Fin T → Tuple State Action)}
    (h : E ⊆ F) : pathProb M π μ T E ≤ pathProb M π μ T F :=
  Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left
    (Set.indicator_le_indicator_of_subset h (fun _ ↦ zero_le_one) ω) (pathWeight_nonneg M π μ ω)

omit [DecidableEq State] in
theorem pathProb_univ (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) : pathProb M π μ T Set.univ = 1 := by
  simp only [pathProb, Set.indicator_univ, mul_one]
  exact sum_pathWeight M π μ T

omit [DecidableEq State] in
/-- An event containing every positive-weight path has probability one. -/
theorem pathProb_eq_one_of_forall (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ)
    {E : Set (Fin T → Tuple State Action)} (h : ∀ ω, pathWeight M π μ ω ≠ 0 → ω ∈ E) :
    pathProb M π μ T E = 1 := by
  rw [← sum_pathWeight M π μ T, pathProb]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  by_cases hω : pathWeight M π μ ω = 0
  · rw [hω, zero_mul]
  · rw [Set.indicator_of_mem (h ω hω), mul_one]

/-- `∑_{u=1}^T u = T(T+1)/2`. -/
theorem sum_fin_add_one (T : ℕ) : ∑ u : Fin T, ((u : ℝ) + 1) = (T : ℝ) * (T + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun u ↦ (u : ℝ) + 1)]
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The printed closed form `w_{t,T} = 2t/(T(T+1))` (`inference.tex:175–177`, 1-based `t+1`). -/
theorem pluginWeight_eq (T : ℕ) (t : Fin T) :
    pluginWeight T t = 2 * ((t : ℝ) + 1) / ((T : ℝ) * (T + 1)) := by
  rw [pluginWeight, sum_fin_add_one]
  field_simp

theorem pluginWeight_nonneg (T : ℕ) (t : Fin T) : 0 ≤ pluginWeight T t := by
  rw [pluginWeight_eq]; positivity

/-- The weights sum to one: `∑_t w_{t,T} = 1` (`inference.tex:175–177`). -/
theorem sum_pluginWeight {T : ℕ} (hT : 1 ≤ T) : ∑ t : Fin T, pluginWeight T t = 1 := by
  have hpos : (0 : ℝ) < ∑ u : Fin T, ((u : ℝ) + 1) := by
    rw [sum_fin_add_one]
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    positivity
  simp only [pluginWeight, ← Finset.sum_div]
  exact div_self hpos.ne'

/-- Entries of `A_t`. -/
theorem sampleAMat_apply (M : DiscountedMDP State Action) (x : Tuple State Action) (i j : State) :
    sampleAMat M x i j = if i = x.1 then
      ((if j = x.1 then 1 else 0) - M.discount * (if j = x.2.2 then 1 else 0)) else 0 := by
  simp only [sampleAMat, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  split_ifs <;> ring

/-- Entries of `Ā_T` through the counts: `Ā_T(s,j) = T⁻¹(1[j=s] n_s − γ m_{sj})`. -/
theorem aBar_apply (M : DiscountedMDP State Action) {T : ℕ} (ω : Fin T → Tuple State Action)
    (s j : State) :
    aBar M ω s j =
      (T : ℝ)⁻¹ * ((if j = s then pluginVisitCount ω s else 0) - M.discount * pluginTransCount ω s j) := by
  simp only [aBar, Matrix.smul_apply, Matrix.sum_apply, sampleAMat_apply, smul_eq_mul]
  congr 1
  have h : ∀ t : Fin T, (if s = (ω t).1 then
      ((if j = (ω t).1 then (1 : ℝ) else 0) - M.discount * (if j = (ω t).2.2 then 1 else 0))
        else 0) =
      (if j = s then (if (ω t).1 = s then 1 else 0) else 0) -
        M.discount * (if (ω t).1 = s ∧ (ω t).2.2 = j then 1 else 0) := by
    intro t
    by_cases h1 : (ω t).1 = s
    · subst h1
      by_cases h2 : (ω t).2.2 = j
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · simp [h1, Ne.symm h1]
  rw [Finset.sum_congr rfl fun t _ ↦ h t, Finset.sum_sub_distrib, ← Finset.mul_sum, pluginVisitCount,
    pluginTransCount]
  split_ifs <;> simp

/-- The residual is supported on `s_t`: `A_t V − b_t = (V(s) − γV(s') − r(s,a)) e_s`. -/
theorem pluginResidual_eq (M : DiscountedMDP State Action) (V : State → ℝ) (x : Tuple State Action) :
    pluginResidual M V x =
      Pi.single x.1 (V x.1 - M.discount * V x.2.2 - M.reward x.1 x.2.1) := by
  funext i
  simp only [pluginResidual, Pi.sub_apply, Matrix.mulVec, dotProduct, sampleAMat_apply, sampleB,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hi : i = x.1
  · subst hi
    simp only [if_true, mul_one]
    rw [Finset.sum_congr rfl fun j _ ↦ by rw [sub_mul, mul_assoc]]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq', ite_mul]
  · simp [hi]

/-- `Γ̂_T` is diagonal: `Γ̂_T(s,s') = 1[s=s'] ∑_t w_{t,T} 1[s_t=s](V̄(s) − γV̄(s'_t) − r_t)²`. -/
theorem gammaHat_apply (M : DiscountedMDP State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) (s s' : State) :
    gammaHat M η₀ V₀ ω s s' = if s = s' then
      ∑ t, pluginWeight T t * (if (ω t).1 = s then
        (prAverage M η₀ V₀ ω s - M.discount * prAverage M η₀ V₀ ω (ω t).2.2 -
          M.reward (ω t).1 (ω t).2.1) ^ 2 else 0) else 0 := by
  simp only [gammaHat, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    pluginResidual_eq, Pi.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    by_cases ht : s = (ω t).1
    · subst ht; simp [sq]
    · simp [ht, Ne.symm ht]
  · refine Finset.sum_eq_zero fun t _ ↦ ?_
    by_cases ht : s = (ω t).1
    · subst ht; simp [Ne.symm h]
    · simp [ht]

/-- `Γ̂_T` is the `Γ̂` formula at `V̄_T`. -/
theorem gammaHat_eq_gammaHatAt (M : DiscountedMDP State Action) (η₀ : ℝ) (V₀ : State → ℝ)
    {T : ℕ} (ω : Fin T → Tuple State Action) :
    gammaHat M η₀ V₀ ω = gammaHatAt M (prAverage M η₀ V₀ ω) ω := rfl

/-- `Γ̂(V)` is diagonal: `Γ̂(V)(s,s') = 1[s=s'] ∑_t w_{t,T} 1[s_t=s](V(s) − γV(s'_t) − r_t)²`. -/
theorem gammaHatAt_apply (M : DiscountedMDP State Action) (V : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) (s s' : State) :
    gammaHatAt M V ω s s' = if s = s' then
      ∑ t, pluginWeight T t * (if (ω t).1 = s then
        (V s - M.discount * V (ω t).2.2 - M.reward (ω t).1 (ω t).2.1) ^ 2 else 0) else 0 := by
  simp only [gammaHatAt, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    pluginResidual_eq, Pi.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    by_cases ht : s = (ω t).1
    · subst ht; simp [sq]
    · simp [ht, Ne.symm ht]
  · refine Finset.sum_eq_zero fun t _ ↦ ?_
    by_cases ht : s = (ω t).1
    · subst ht; simp [Ne.symm h]
    · simp [ht]

/-- **Junk value.** If `Ā_T` is singular then Lean's `lambdaHat` is `0` (C47(4)). -/
theorem lambdaHat_eq_zero_of_det_eq_zero (M : DiscountedMDP State Action) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} {ω : Fin T → Tuple State Action} (h : (aBar M ω).det = 0) :
    lambdaHat M η₀ V₀ ω = 0 := by
  have hinv : (aBar M ω)⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by rw [h]; exact not_isUnit_zero)
  simp [lambdaHat, hinv]

end StatisticalRL.Ch7Rest.TDInference
