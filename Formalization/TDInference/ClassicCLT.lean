import Formalization.TDInference.SmoothApproximation
import Formalization.Probability.WeakConvergenceSmoothTest

/-!
# The classic CLT display `eqn:classic-clt` for Polyak–Ruppert-averaged TD

Source: `chapters/inference.tex:98–103` (display `eqn:classic-clt`, prose :98), `Λ⋆ = A⁻¹ΓA⁻ᵀ`,
`A`, `Γ` :104–117, i.i.d. sampling :51–66, TD update :70–75, Polyak–Ruppert average and `Δ̄_T`
:80–88.

Exports:
* `lawMeasure` (the law of `√T Δ̄_T`, a finite weighted Dirac sum), its probability instance,
  and `integral_lawMeasure`;
* `tendsto_sum_pathWeight_smooth_gaussCov` (convergence for `C^∞` compactly supported tests);
* `tendsto_sum_pathWeight_bcf_gaussCov`: for every finite instance with full-support `μ`, every
  `η₀ ∈ (0, 1]` (step sizes `η_t = η₀ t^{-2/3}`), every `V₀` and every bounded continuous `g`,
  `E g(√T Δ̄_T) → ∫ g dN(0, A⁻¹ diag(Γ_true) A⁻ᵀ)`; that is, `√T Δ̄_T →d N(0, A⁻¹Γ_trueA⁻ᵀ)` with
  the **corrected** covariance (`docs/SOURCE-ISSUES.md#C43`). No `Γ_true ≻ 0` hypothesis: the
  Gaussian may be degenerate;
* `tendsto_lawProbabilityMeasure`: the same as convergence in `ProbabilityMeasure (State → ℝ)`;
* `trueGamma_eq_printedGamma_of_reward_const_on_support`: when `r(s,·)` is constant on the
  support of `π(·|s)` for every `s` (state-only rewards, or deterministic `π`), the printed `Γ`
  (with `r(s) := r_π(s)`) equals `Γ_true`;
* `tendsto_sum_pathWeight_bcf_gaussCov_printed_of_reward_const`: under that restriction the
  printed display holds with the printed `Γ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.TemporalDifference (policyReward)
open StatisticalRL.Probability

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- The law of `√T Δ̄_T` under the i.i.d. sampling law (`inference.tex:54–61`):
`∑_ω pathWeight(ω) δ_{scaledError(ω)}`. -/
noncomputable def lawMeasure [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) : Measure (State → ℝ) :=
  ∑ ω : Fin T → Tuple State Action,
    ENNReal.ofReal (pathWeight M π μ ω) • Measure.dirac (scaledError M π η₀ V₀ ω)

theorem integral_lawMeasure [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) (g : (State → ℝ) → ℝ) :
    ∫ x, g x ∂(lawMeasure M π μ η₀ V₀ T) =
      ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * g (scaledError M π η₀ V₀ ω) := by
  rw [lawMeasure, integral_finset_sum_measure fun ω _ ↦
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (pathWeight_nonneg M π μ ω),
    smul_eq_mul]

instance lawMeasure_isProbabilityMeasure [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) : IsProbabilityMeasure (lawMeasure M π μ η₀ V₀ T) := by
  constructor
  simp only [lawMeasure, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ ↦ pathWeight_nonneg M π μ ω, sum_pathWeight,
    ENNReal.ofReal_one]

/-- `μmin = min_s μ(s)` is positive under full support. -/
theorem diagMin_prob_pos [Nonempty State] (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) : 0 < diagMin μ.prob :=
  (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s

theorem diagMin_prob_le [Nonempty State] (μ : FiniteDistribution State) (s : State) :
    diagMin μ.prob ≤ μ.prob s :=
  Finset.inf'_le _ (Finset.mem_univ s)

/-- Convergence of `E f(√T Δ̄_T)` for every `C^∞` compactly supported test `f`, from the smooth
Gaussian-approximation bound `scaledError_smooth_gaussian_le`. -/
theorem tendsto_sum_pathWeight_smooth_gaussCov [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {f : (State → ℝ) → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcs : HasCompactSupport f) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action,
        pathWeight M π μ ω * f (scaledError M π η₀ V₀ ω)) atTop
      (𝓝 (∫ x, f x ∂(gaussCov (tdA M π μ) (trueGamma M π μ)))) := by
  obtain ⟨hf2, ⟨L₁, hL₁⟩, ⟨L₂, hL₂⟩⟩ := exists_smooth_test_bounds hf hcs
  set K := smoothRemainderConst M π V₀ (diagMin μ.prob) η₀
  set C := smoothLindebergConst M π μ (diagMin μ.prob)
  have hb : Tendsto (fun T : ℕ ↦ L₁ * K * (T : ℝ) ^ (-(1 / 6 : ℝ)) +
      L₂ * C * (T : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    have h6 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
    have := (h6.const_mul (L₁ * K)).add (h2.const_mul (L₂ * C))
    rw [mul_zero, mul_zero, add_zero] at this
    exact this
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
    ?_ hb)
  rw [eventually_atTop]
  refine ⟨1, fun T hT ↦ ?_⟩
  rw [Real.dist_eq]
  have := scaledError_smooth_gaussian_le M π μ h0 h1 V₀ (diagMin_prob_pos μ hμ)
    (diagMin_prob_le μ) hT hf2 hL₁ hL₂
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Classic CLT, corrected covariance.** For every finite instance with full-support `μ`,
every `η₀ ∈ (0, 1]` (step sizes `η_t = η₀ t^{-2/3}`), every `V₀` and every bounded continuous
`g`, `E g(√T Δ̄_T) → ∫ g dN(0, A⁻¹ diag(Γ_true) A⁻ᵀ)` as `T → ∞`. -/
theorem tendsto_sum_pathWeight_bcf_gaussCov [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (g : BoundedContinuousFunction (State → ℝ) ℝ) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action,
        pathWeight M π μ ω * g (scaledError M π η₀ V₀ ω)) atTop
      (𝓝 (∫ x, g x ∂(gaussCov (tdA M π μ) (trueGamma M π μ)))) := by
  simp_rw [← integral_lawMeasure M π μ η₀ V₀]
  refine tendsto_integral_bcf_of_tendsto_integral_smooth (fun f hf hcs ↦ ?_) g
  simp_rw [integral_lawMeasure M π μ η₀ V₀]
  exact tendsto_sum_pathWeight_smooth_gaussCov M π μ hμ h0 h1 V₀ hf hcs

/-- The law of `√T Δ̄_T` as a probability measure. -/
noncomputable def lawProbabilityMeasure [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) : ProbabilityMeasure (State → ℝ) :=
  ⟨lawMeasure M π μ η₀ V₀ T, inferInstance⟩

/-- `N(0, A⁻¹ diag(Γ) A⁻ᵀ)` as a probability measure. -/
noncomputable def gaussCovPM [DecidableEq State] (A : Matrix State State ℝ) (Γ : State → ℝ) :
    ProbabilityMeasure (State → ℝ) :=
  ⟨gaussCov A Γ, inferInstance⟩

/-- Weak convergence `√T Δ̄_T →d N(0, A⁻¹Γ_trueA⁻ᵀ)` in `ProbabilityMeasure (State → ℝ)`. -/
theorem tendsto_lawProbabilityMeasure [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) :
    Tendsto (fun T : ℕ ↦ lawProbabilityMeasure M π μ η₀ V₀ T) atTop
      (𝓝 (gaussCovPM (tdA M π μ) (trueGamma M π μ))) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun g ↦ ?_
  change Tendsto (fun T : ℕ ↦ ∫ x, g x ∂(lawMeasure M π μ η₀ V₀ T)) atTop
    (𝓝 (∫ x, g x ∂(gaussCov (tdA M π μ) (trueGamma M π μ))))
  simp_rw [integral_lawMeasure M π μ η₀ V₀]
  exact tendsto_sum_pathWeight_bcf_gaussCov M π μ hμ h0 h1 V₀ g

/-! ## Printed `Γ` under rewards constant on the support of the policy -/

/-- If `r(s,·)` is constant on the support of `π(·|s)` for every `s`, then for every supported
action `r(s,a) = r_π(s)`. -/
theorem reward_eq_policyReward_of_const_on_support (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action)
    (hr : ∀ s a a', 0 < (π s).prob a → 0 < (π s).prob a' → M.reward s a = M.reward s a')
    (s : State) (a : Action) (ha : 0 < (π s).prob a) : M.reward s a = policyReward M π s := by
  have h : ∀ a', (π s).prob a' * M.reward s a' = (π s).prob a' * M.reward s a := by
    intro a'
    rcases ((π s).prob_nonneg a').eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul]
    · rw [hr s a' a h ha]
  simp only [policyReward, DiscountedMDP.policyExpectedReward, FiniteDistribution.expectation, h, ← Finset.sum_mul, (π s).sum_prob,
    one_mul]

/-- **Printed `Γ` = true `Γ` when `r(s,·)` is constant on the support of `π(·|s)`** (covers
state-only rewards and deterministic policies). -/
theorem trueGamma_eq_printedGamma_of_reward_const_on_support (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hr : ∀ s a a', 0 < (π s).prob a → 0 < (π s).prob a' → M.reward s a = M.reward s a') :
    trueGamma M π μ = printedGamma M π μ := by
  funext s
  have hterm : ∀ a, (π s).prob a * ∑ s', (M.transition s a).prob s' *
        (M.valueFixedPoint π s - M.reward s a - M.discount * M.valueFixedPoint π s') ^ 2 =
      (π s).prob a * ∑ s', (M.transition s a).prob s' *
        (M.valueFixedPoint π s -
          (policyReward M π s + M.discount * M.valueFixedPoint π s')) ^ 2 := by
    intro a
    rcases ((π s).prob_nonneg a).eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul]
    · rw [reward_eq_policyReward_of_const_on_support M π hr s a h]
      congr 1
      refine Finset.sum_congr rfl fun s' _ ↦ by ring
  simp only [trueGamma, printedGamma, FiniteDistribution.expectation]
  congr 1
  rw [Finset.sum_congr rfl fun a _ ↦ hterm a]
  simp only [DiscountedMDP.policyTransition_prob, FiniteDistribution.expectation, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s' _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring

/-- **Classic CLT with the printed `Γ`, restricted** to instances where `r(s,·)` is constant on
the support of `π(·|s)` (then `Γ_printed = Γ_true`). -/
theorem tendsto_sum_pathWeight_bcf_gaussCov_printed_of_reward_const [DecidableEq State]
    [Nonempty State] (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State)
    (hr : ∀ s a a', 0 < (π s).prob a → 0 < (π s).prob a' → M.reward s a = M.reward s a')
    (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (g : BoundedContinuousFunction (State → ℝ) ℝ) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action,
        pathWeight M π μ ω * g (scaledError M π η₀ V₀ ω)) atTop
      (𝓝 (∫ x, g x ∂(gaussCov (tdA M π μ) (printedGamma M π μ)))) := by
  rw [← trueGamma_eq_printedGamma_of_reward_const_on_support M π μ hr]
  exact tendsto_sum_pathWeight_bcf_gaussCov M π μ hμ h0 h1 V₀ g

end StatisticalRL.Ch7Rest.TDInference
