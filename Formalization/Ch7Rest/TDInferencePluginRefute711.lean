import Formalization.Ch7Rest.TDInferencePluginSingular711
import Formalization.Ch7Rest.TDInferenceZeroNoise711
import Formalization.Ch7Rest.TDInferencePluginCorrected711
import Formalization.Ch7Rest.TDInferenceCLT711

/-!
# `Λ̂_T` is not a consistent estimator of the printed `Λ⋆` (SOURCE-ISSUES C43, C47(4))

Source: `chapters/inference.tex:180–182` (`eq:defn-hat-Lambda`, "the final estimator of `Λ⋆`"),
`Λ⋆ = A⁻¹ΓA⁻ᵀ` :99–117 with `r(s) = r_π(s)` (`prelim.tex:414–419`).

Instance Z (`TDInferenceZeroNoise711.lean`): two states, two actions, `γ = 1/2`, uniform `μ, π`,
action `a` moves to state `a`, and `r(s,a) + γV^π(a) = V^π(s)` for every `(s,a)`. Started from
`V₀ = V^π`, every positive-weight path keeps `V_t = V̄_T = V^π`, every residual
`A_tV̄_T − b_t = (V̄(s_t) − γV̄(s'_t) − r_t)e_{s_t}` vanishes, so `Γ̂_T = 0` and `Λ̂_T = 0` surely
for every `T ≥ 1` and every `η₀` (`lambdaHat_zero`). The printed `Λ⋆` has `Λ⋆(0,0) = 5/64`
(`zPrintedLambda_00`), so `P(|Λ̂_T(0,0) − Λ⋆(0,0)| > 1/64) = 1` for every `T ≥ 1`
(`pathProb_lambdaHat_far_eq_one`): the consistency reading
`Eq_defn_hat_Lambda_printed_consistent` is false (`not_eq_defn_hat_Lambda_printed_consistent`).
By contrast the corrected target is `trueLambda = 0` here (`zTrueLambda`), consistent with C43.

Scope: `not_eq_defn_hat_Lambda_printed_consistent` refutes the every-`V₀` reading (it uses
`V₀ = V^π`). The some-`V₀` reading is refuted too: from **every** `V₀` and every `η₀ ∈ (0,1]`,
`P(∃ s s', 1/64 < |Λ̂_T(s,s') − Λ⋆(s,s')|) → 1` in instance Z
(`ZeroNoise.tendsto_pathProb_lambdaHat_far_printed_one`), a corollary of the corrected consistency
theorem `eq_defn_hat_Lambda_corrected` since `trueLambda = 0` while `Λ⋆(0,0) = 5/64`; hence
`not_eq_defn_hat_Lambda_printed_consistent_someInit`.

Restricted variant (`eq_defn_hat_Lambda_restricted`): when `r(s,·)` is constant on the support of
`π(·|s)` (state-only rewards or deterministic `π`), `printedLambda = trueLambda` and `Λ̂_T` is
consistent for the printed `Λ⋆`.

Also the concrete C47(4) witness: in instance Z, `P(Ā_T singular) ≥ 2^{-T} > 0` for every `T`
(`zAbar_singular_ge`), and Lean's `lambdaHat` is the junk `0` there.
-/

open Filter Topology
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

namespace ZeroNoise

/-- `A⁻¹ = [[3, 1], [1, 3]]` for instance Z. -/
noncomputable def zAinv : Matrix (Fin 2) (Fin 2) ℝ := !![3, 1; 1, 3]

theorem zA_mul_zAinv : tdA zMDP zPolicy zMu * zAinv = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, zA_apply, zA_apply]
  fin_cases i <;> fin_cases j <;> norm_num [zAinv, Matrix.one_apply]

theorem zA_inv_eq : (tdA zMDP zPolicy zMu)⁻¹ = zAinv := Matrix.inv_eq_right_inv zA_mul_zAinv

/-- The printed `Λ⋆(0,0) = (1/128)(3² + 1²) = 5/64`. -/
theorem zPrintedLambda_00 : printedLambda zMDP zPolicy zMu 0 0 = 5 / 64 := by
  have hΓ : printedGamma zMDP zPolicy zMu = fun _ ↦ 1 / 128 := funext zPrintedGamma
  rw [printedLambda, zA_inv_eq, hΓ]
  simp [Matrix.mul_apply, Fin.sum_univ_two, zAinv]
  norm_num

/-- The true noise covariance vanishes in instance Z. -/
theorem zTrueGamma (s : Fin 2) : trueGamma zMDP zPolicy zMu s = 0 := by
  simp only [trueGamma, FiniteDistribution.expectation, Fin.sum_univ_two, zValueFixedPoint,
    zTransition_prob, zPolicy, uniformRow_two_prob]
  fin_cases s <;> norm_num [zMDP, zV]

/-- The corrected target `A⁻¹Γ_trueA⁻ᵀ` is `0` in instance Z. -/
theorem zTrueLambda : trueLambda zMDP zPolicy zMu = 0 := by
  have hΓ : trueGamma zMDP zPolicy zMu = fun _ ↦ 0 := funext zTrueGamma
  rw [trueLambda, hΓ]
  simp

theorem prAverage_zV (η₀ : ℝ) {T : ℕ} (hT : 1 ≤ T) {ω : Fin T → Tuple (Fin 2) (Fin 2)}
    (hω : pathWeight zMDP zPolicy zMu ω ≠ 0) : prAverage zMDP η₀ zV ω = zV := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hT)
  rw [prAverage]
  simp only [tdIter_zV η₀ hω, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hT', one_smul]

/-- From `V₀ = V^π`, every positive-weight path has `Γ̂_T = 0`. -/
theorem gammaHat_zero (η₀ : ℝ) {T : ℕ} (hT : 1 ≤ T) {ω : Fin T → Tuple (Fin 2) (Fin 2)}
    (hω : pathWeight zMDP zPolicy zMu ω ≠ 0) :
    gammaHat zMDP η₀ (zMDP.valueFixedPoint zPolicy) ω = 0 := by
  rw [zValueFixedPoint, gammaHat, prAverage_zV η₀ hT hω]
  refine Finset.sum_eq_zero fun t _ ↦ ?_
  have hx := Finset.prod_ne_zero_iff.mp hω t (Finset.mem_univ t)
  have hres : pluginResidual zMDP zV (ω t) = 0 := by
    rw [pluginResidual_eq, next_eq_of_tupleProb_ne_zero hx]
    have hb := zReward_bellman (ω t).1 (ω t).2.1
    rw [show zV (ω t).1 - zMDP.discount * zV (ω t).2.1 - zMDP.reward (ω t).1 (ω t).2.1 = 0 by
      linarith]
    exact Pi.single_zero _
  rw [hres]
  ext i j
  simp

/-- From `V₀ = V^π`, every positive-weight path has `Λ̂_T = 0`, for every `η₀` and `T ≥ 1`. -/
theorem lambdaHat_zero (η₀ : ℝ) {T : ℕ} (hT : 1 ≤ T) {ω : Fin T → Tuple (Fin 2) (Fin 2)}
    (hω : pathWeight zMDP zPolicy zMu ω ≠ 0) :
    lambdaHat zMDP η₀ (zMDP.valueFixedPoint zPolicy) ω = 0 := by
  rw [lambdaHat, gammaHat_zero η₀ hT hω]
  simp

/-- `P(|Λ̂_T(0,0) − Λ⋆(0,0)| > 1/64) = 1` for every `T ≥ 1` and every `η₀`. -/
theorem pathProb_lambdaHat_far_eq_one (η₀ : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pathProb zMDP zPolicy zMu T {ω | ∃ s s', 1 / 64 <
      |lambdaHat zMDP η₀ (zMDP.valueFixedPoint zPolicy) ω s s' -
        printedLambda zMDP zPolicy zMu s s'|} = 1 := by
  refine pathProb_eq_one_of_forall _ _ _ _ fun ω hω ↦ ⟨0, 0, ?_⟩
  rw [lambdaHat_zero η₀ hT hω, zPrintedLambda_00, Matrix.zero_apply]
  norm_num

/-- Junk-independence (critic R1): the far event *intersected with the nonsingular event* (where
`Λ̂_T` is the genuine printed value) has probability `≥ 1 − ∑_s (1 − μ(s))^T = 1 − 2·2^{-T}`. -/
theorem pathProb_far_nonsingular_ge (η₀ : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    1 - 2 * (1 / 2 : ℝ) ^ T ≤ pathProb zMDP zPolicy zMu T {ω | (aBar zMDP ω).det ≠ 0 ∧
      ∃ s s', 1 / 64 < |lambdaHat zMDP η₀ (zMDP.valueFixedPoint zPolicy) ω s s' -
        printedLambda zMDP zPolicy zMu s s'|} := by
  set F := {ω : Fin T → Tuple (Fin 2) (Fin 2) | ∃ s s', 1 / 64 <
      |lambdaHat zMDP η₀ (zMDP.valueFixedPoint zPolicy) ω s s' -
        printedLambda zMDP zPolicy zMu s s'|}
  set S := {ω : Fin T → Tuple (Fin 2) (Fin 2) | (aBar zMDP ω).det = 0}
  have hF := pathProb_lambdaHat_far_eq_one η₀ hT
  have hS := pathProb_aBar_singular_le zMDP zPolicy zMu T
  have hsum : ∑ s, (1 - zMu.prob s) ^ T = 2 * (1 / 2 : ℝ) ^ T := by
    rw [Fin.sum_univ_two, zMu, uniformRow_two_prob, uniformRow_two_prob]; norm_num; ring
  rw [hsum] at hS
  have hsplit : pathProb zMDP zPolicy zMu T F ≤
      pathProb zMDP zPolicy zMu T {ω | (aBar zMDP ω).det ≠ 0 ∧ ω ∈ F} +
        pathProb zMDP zPolicy zMu T S := by
    simp only [pathProb, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ ↦ ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg _ _ _ ω)
    by_cases hd : (aBar zMDP ω).det = 0
    · rw [Set.indicator_of_mem (show ω ∈ S from hd)]
      have := Set.indicator_le_self' (s := F) (fun _ _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)) ω
      have h0 := Set.indicator_nonneg (s := {ω | (aBar zMDP ω).det ≠ 0 ∧ ω ∈ F})
        (fun _ _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)) ω
      linarith
    · rw [Set.indicator_of_notMem (show ω ∉ S from hd), add_zero]
      by_cases hω : ω ∈ F
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem
          (show ω ∈ {ω | (aBar zMDP ω).det ≠ 0 ∧ ω ∈ F} from ⟨hd, hω⟩)]
      · rw [Set.indicator_of_notMem hω]
        exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ω
  have : pathProb zMDP zPolicy zMu T {ω | (aBar zMDP ω).det ≠ 0 ∧ ω ∈ F} =
      pathProb zMDP zPolicy zMu T {ω | (aBar zMDP ω).det ≠ 0 ∧
        ∃ s s', 1 / 64 < |lambdaHat zMDP η₀ (zMDP.valueFixedPoint zPolicy) ω s s' -
          printedLambda zMDP zPolicy zMu s s'|} := rfl
  linarith

/-- Concrete C47(4) witness: `P(Ā_T singular) ≥ 2^{-T} > 0` for every `T` in instance Z. -/
theorem zAbar_singular_ge (T : ℕ) :
    (1 / 2 : ℝ) ^ T ≤ pathProb zMDP zPolicy zMu T {ω | (aBar zMDP ω).det = 0} := by
  have h := pathProb_aBar_singular_ge zMDP zPolicy zMu T 0
  rwa [zMu, uniformRow_two_prob, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h

end ZeroNoise

open ZeroNoise in
/-- **`Λ̂_T` is not consistent for the printed `Λ⋆`** (`eq:defn-hat-Lambda`,
`inference.tex:180–182`; SOURCE-ISSUES C43, every-`V₀` reading, `r(s) = r_π(s)`): instance Z with
`V₀ = V^π`, `η₀ = 1/8` (in the printed range `(0, 1/4)`), `ε = 1/64`.

Reading caveat: this needs action-dependent rewards with `r(s) = r_π(s)`. With state-only rewards
or deterministic `π`, `printedGamma = trueGamma`, so `printedLambda = trueLambda`; that reading is
proved (`eq_defn_hat_Lambda_restricted`). The some-`V₀` reading is refuted as well
(`not_eq_defn_hat_Lambda_printed_consistent_someInit`). Junk value: on the event that some state is unsampled, `Ā_T` is
singular and the printed `Λ̂_T` is undefined (C47(4)); Lean's `Matrix.inv` returns 0 there. The
refutation does not depend on that value: on the nonsingular event `Λ̂_T = Ā⁻¹ · 0 · Ā⁻ᵀ = 0` is
the genuine printed value, and that event has probability `≥ 1 − 2·2^{-T}`
(`pathProb_far_nonsingular_ge`). -/
theorem not_eq_defn_hat_Lambda_printed_consistent : ¬ Eq_defn_hat_Lambda_printed_consistent := by
  intro h
  have hlim := h (Fin 2) (Fin 2) zMDP zPolicy zMu (1 / 8) (zMDP.valueFixedPoint zPolicy) zMu_pos
    (by norm_num) (by norm_num) zPrintedGamma_pos (1 / 64) (by norm_num)
  have h1 : Tendsto (fun T : ℕ ↦ pathProb zMDP zPolicy zMu T {ω | ∃ s s', 1 / 64 <
      |lambdaHat zMDP (1 / 8) (zMDP.valueFixedPoint zPolicy) ω s s' -
        printedLambda zMDP zPolicy zMu s s'|}) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with T hT
      exact (pathProb_lambdaHat_far_eq_one (1 / 8) hT).symm)
  exact absurd (tendsto_nhds_unique hlim h1) (by norm_num)

namespace ZeroNoise

/-- **Some-`V₀` refutation (critic R4).** In instance Z, from **every** initialization `V₀` and
every `η₀ ∈ (0,1]` (containing the printed `(0, 1/4)`),
`P(∃ s s', 1/64 < |Λ̂_T(s,s') − Λ⋆(s,s')|) → 1`, where `Λ⋆ = printedLambda`. Proof: the corrected
target is `trueLambda = 0` (`zTrueLambda`) while `Λ⋆(0,0) = 5/64` (`zPrintedLambda_00`), so every
path is far from `Λ` or far from `Λ⋆`, and `eq_defn_hat_Lambda_corrected` sends the first
probability to `0`. -/
theorem tendsto_pathProb_lambdaHat_far_printed_one {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1)
    (V₀ : Fin 2 → ℝ) :
    Tendsto (fun T : ℕ ↦ pathProb zMDP zPolicy zMu T {ω | ∃ s s', 1 / 64 <
      |lambdaHat zMDP η₀ V₀ ω s s' - printedLambda zMDP zPolicy zMu s s'|}) atTop (𝓝 1) := by
  have hc := eq_defn_hat_Lambda_corrected (Fin 2) (Fin 2) zMDP zPolicy zMu η₀ V₀ zMu_pos
    h0 h1 (1 / 64) (by norm_num)
  have hle : ∀ T : ℕ, 1 - pathProb zMDP zPolicy zMu T {ω | ∃ s s', 1 / 64 <
      |lambdaHat zMDP η₀ V₀ ω s s' - trueLambda zMDP zPolicy zMu s s'|} ≤
      pathProb zMDP zPolicy zMu T {ω | ∃ s s', 1 / 64 <
      |lambdaHat zMDP η₀ V₀ ω s s' - printedLambda zMDP zPolicy zMu s s'|} := by
    intro T
    have hu := pathProb_union_le zMDP zPolicy zMu T
      {ω | ∃ s s', 1 / 64 < |lambdaHat zMDP η₀ V₀ ω s s' - trueLambda zMDP zPolicy zMu s s'|}
      {ω | ∃ s s', 1 / 64 < |lambdaHat zMDP η₀ V₀ ω s s' - printedLambda zMDP zPolicy zMu s s'|}
    have hcov : {ω : Fin T → Tuple (Fin 2) (Fin 2) | ∃ s s', 1 / 64 <
        |lambdaHat zMDP η₀ V₀ ω s s' - trueLambda zMDP zPolicy zMu s s'|} ∪
        {ω | ∃ s s', 1 / 64 < |lambdaHat zMDP η₀ V₀ ω s s' -
          printedLambda zMDP zPolicy zMu s s'|} = Set.univ := by
      ext ω
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      by_contra h
      push_neg at h
      have h1 := h.1 0 0
      have h2 := h.2 0 0
      rw [zTrueLambda, Matrix.zero_apply, sub_zero] at h1
      rw [zPrintedLambda_00] at h2
      have := abs_sub_abs_le_abs_sub (lambdaHat zMDP η₀ V₀ ω 0 0) (5 / 64)
      rw [abs_sub_comm] at h2
      have h5 : |(5 / 64 : ℝ)| = 5 / 64 := abs_of_pos (by norm_num)
      have := abs_sub_abs_le_abs_sub (5 / 64 : ℝ) (lambdaHat zMDP η₀ V₀ ω 0 0)
      linarith
    rw [hcov, pathProb_univ] at hu
    linarith
  have hlow : Tendsto (fun T : ℕ ↦ 1 - pathProb zMDP zPolicy zMu T {ω | ∃ s s', 1 / 64 <
      |lambdaHat zMDP η₀ V₀ ω s s' - trueLambda zMDP zPolicy zMu s s'|}) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hc
  have hup : ∀ T : ℕ, pathProb zMDP zPolicy zMu T {ω | ∃ s s', 1 / 64 <
      |lambdaHat zMDP η₀ V₀ ω s s' - printedLambda zMDP zPolicy zMu s s'|} ≤ 1 := fun T ↦
    (pathProb_mono _ _ _ T (Set.subset_univ _)).trans (le_of_eq (pathProb_univ _ _ _ T))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hle hup

end ZeroNoise

/-- The some-`V₀` consistency reading of `eq:defn-hat-Lambda` for the printed `Λ⋆`
(`inference.tex:180–182`, "the final estimator of `Λ⋆`" :184; `r(s) = r_π(s)`, SOURCE-ISSUES C43):
for every instance with full-support `μ`, `Γ_printed ≻ 0` and every `η₀` in the printed range
`(0, 1/4)`, **some** initialization `V₀` makes `Λ̂_T` entrywise consistent for `Λ⋆`. Weaker than
`Eq_defn_hat_Lambda_printed_consistent`; refuted by
`not_eq_defn_hat_Lambda_printed_consistent_someInit`. -/
def Eq_defn_hat_Lambda_printed_consistent_someInit : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < printedGamma M π μ s) →
    ∃ V₀ : State → ℝ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun T : ℕ ↦ pathProb M π μ T
        {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - printedLambda M π μ s s'|}) atTop (𝓝 0)

open ZeroNoise in
/-- **`Λ̂_T` is not consistent for the printed `Λ⋆` from any initialization** (SOURCE-ISSUES C43):
instance Z, `η₀ = 1/8`, `ε = 1/64`; for every `V₀` the far probability tends to `1`
(`tendsto_pathProb_lambdaHat_far_printed_one`). -/
theorem not_eq_defn_hat_Lambda_printed_consistent_someInit :
    ¬ Eq_defn_hat_Lambda_printed_consistent_someInit := by
  intro h
  obtain ⟨V₀, hV⟩ := h (Fin 2) (Fin 2) zMDP zPolicy zMu (1 / 8) zMu_pos (by norm_num) (by norm_num)
    zPrintedGamma_pos
  exact absurd (tendsto_nhds_unique (hV (1 / 64) (by norm_num))
    (tendsto_pathProb_lambdaHat_far_printed_one (by norm_num) (by norm_num) V₀)) (by norm_num)

/-- **Restricted variant: the printed `Λ⋆`** (`eq:defn-hat-Lambda`, `chapters/inference.tex:180–182`,
"the final estimator of `Λ⋆`" :184; `Λ⋆` :99–117 with `r(s) = r_π(s)`). When `r(s,·)` is constant
on the support of `π(·|s)` for every `s` (state-only rewards or deterministic `π`),
`Γ_printed = Γ_true` (`trueGamma_eq_printedGamma_of_reward_const_on_support`), so for full-support
`μ`, every `η₀ ∈ (0,1]`, every `V₀` and every `ε > 0`,
`P(∃ s s', ε < |Λ̂_T(s,s') − Λ⋆(s,s')|) → 0` (SOURCE-ISSUES C43 scope). No `Γ ≻ 0` is assumed;
convergence in probability only, no rate. -/
theorem eq_defn_hat_Lambda_restricted {State Action : Type} [Fintype State] [DecidableEq State]
    [Nonempty State] [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ)
    (hr : ∀ s a a', 0 < (π s).prob a → 0 < (π s).prob a' → M.reward s a = M.reward s a')
    (hμ : ∀ s, 0 < μ.prob s) (h0 : 0 < η₀) (h1 : η₀ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℕ ↦ pathProb M π μ T
      {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - printedLambda M π μ s s'|}) atTop (𝓝 0) := by
  have h := eq_defn_hat_Lambda_corrected State Action M π μ η₀ V₀ hμ h0 h1 ε hε
  have he : trueLambda M π μ = printedLambda M π μ := by
    rw [trueLambda, printedLambda, trueGamma_eq_printedGamma_of_reward_const_on_support M π μ hr]
  rwa [he] at h

end StatisticalRL.Ch7Rest.TDInference
