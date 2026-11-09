import Formalization.Ch7Rest.TDInferenceCLT711
import Formalization.Ch7Rest.TDInferenceAnyInit711

/-!
# The classic CLT display `eqn:classic-clt` with the printed `Γ`: refutation

Source: `chapters/inference.tex:98–103` (display, prose :98), `Λ⋆`, `A`, `Γ` :104–117; issue
`docs/SOURCE-ISSUES.md#C43` (the printed `Γ` omits the action-reward variance and cross term).

`Eq_classic_clt_printed` reads the display with the printed `Γ` (`r(s) := r_π(s)`), the printed
step-size family `η_t = η₀ t^{-2/3}` with `η₀ ∈ (0, 1/4)`, every `V₀`, full-support `μ`, and weak
convergence as convergence of `E g` for every bounded continuous `g`.
`Eq_classic_clt_printed_someInit` asks only for **some** `η₀ ∈ (0, 1]` and **some** `V₀` per
instance. Both are false (`not_eq_classic_clt_printed_someInit`, `not_eq_classic_clt_printed`).
Within the family, `η₀ ∈ (0, 1]` exhausts the source-admissible step sizes: the source requires
`0 < η_t < 1` (`inference.tex:75`), which at `t = 1` means `η₀ ∈ (0, 1)`.

Scope of the refutation. The display is existential in the schedule ("with an appropriate choice
of the learning rate schedule"); `tdIter` fixes `η_t = η₀ t^{-2/3}`, so these theorems refute the
display for the printed step-size family only (`η₀ ∈ (0, 1/4)` for every `V₀`; `η₀ ∈ (0, 1]` and
some `V₀` for `_someInit`). For `V₀ = V^π` the same zero-noise argument refutes it for every
schedule (paper argument, not Lean-checked, since `tdIter` fixes the schedule). The reading
"some schedule and some `V₀`" over arbitrary schedules is not refuted.

Witness: instance Z (`TDInferenceZeroNoise711`), where the TD noise vanishes. With the bounded
continuous test `g(x) = min(1, |x 0|)`: `E g(√TΔ̄_T) ≤ E|√TΔ̄_T(0)| = O(T^{-1/2}) → 0`
(`zScaledError_expect_le`), while `∫ g dN(0, Λ⋆_printed) ≥ (1/20)·(3/4)` (`zGauss_slab_le`).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace StatisticalRL.Ch7Rest.TDInference

/-- `eqn:classic-clt` as printed (`inference.tex:98–103`, `Γ` :111–117 with `r(s) := r_π(s)`),
for the step-size family `η_t = η₀ t^{-2/3}`, `η₀ ∈ (0, 1/4)`, every `V₀`. Refuted by
`not_eq_classic_clt_printed`. -/
def Eq_classic_clt_printed : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    ∀ g : BoundedContinuousFunction (State → ℝ) ℝ,
      Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action,
          pathWeight M π μ ω * g (scaledError M π η₀ V₀ ω)) atTop
        (𝓝 (∫ x, g x ∂(gaussCov (tdA M π μ) (printedGamma M π μ))))

/-- Weakest reading within the printed step-size family: some `η₀ ∈ (0, 1]` and some `V₀` per
instance. Refuted by `not_eq_classic_clt_printed_someInit`. -/
def Eq_classic_clt_printed_someInit : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State),
    (∀ s, 0 < μ.prob s) → ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ ∃ V₀ : State → ℝ,
    ∀ g : BoundedContinuousFunction (State → ℝ) ℝ,
      Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action,
          pathWeight M π μ ω * g (scaledError M π η₀ V₀ ω)) atTop
        (𝓝 (∫ x, g x ∂(gaussCov (tdA M π μ) (printedGamma M π μ))))

namespace ZeroNoise

/-- The bounded continuous test `g(x) = min(1, |x 0|)`. -/
noncomputable def zTest : BoundedContinuousFunction (Fin 2 → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ min 1 |x 0|)
    (continuous_const.min (continuous_abs.comp (continuous_apply 0))) 1 fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (abs_nonneg _))]
      exact min_le_left _ _

theorem zTest_apply (x : Fin 2 → ℝ) : zTest x = min 1 |x 0| := rfl

/-- Under the data law, `E g(√TΔ̄_T) → 0` for every `η₀ ∈ (0, 1]` and every `V₀`. -/
theorem tendsto_zTest_law {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : Fin 2 → ℝ) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple (Fin 2) (Fin 2),
        pathWeight zMDP zPolicy zMu ω * zTest (scaledError zMDP zPolicy η₀ V₀ ω)) atTop
      (𝓝 0) := by
  set D := (zLyap V₀ + 1) / 2 * (1440 / (3 * η₀ / 16) ^ 6)
  have hup : Tendsto (fun T : ℕ ↦ D * (T : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    have h2 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul D
    rw [mul_zero] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun T ↦ Finset.sum_nonneg fun ω _ ↦
      mul_nonneg (pathWeight_nonneg _ _ _ ω) (le_min zero_le_one (abs_nonneg _))) ?_
  rw [eventually_atTop]
  refine ⟨1, fun T hT ↦ ?_⟩
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hsq : (Real.sqrt T)⁻¹ = (T : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hT0]
  calc _ ≤ ∑ ω : Fin T → Tuple (Fin 2) (Fin 2),
        pathWeight zMDP zPolicy zMu ω * |scaledError zMDP zPolicy η₀ V₀ ω 0| :=
        Finset.sum_le_sum fun ω _ ↦
          mul_le_mul_of_nonneg_left (min_le_right _ _) (pathWeight_nonneg _ _ _ ω)
    _ ≤ (Real.sqrt T)⁻¹ * D := zScaledError_expect_le h0 h1 V₀ hT
    _ = D * (T : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hsq, mul_comm]

/-- Under the printed Gaussian, `∫ g ≥ (1/20)·(3/4) > 0`. -/
theorem zTest_gauss_pos :
    0 < ∫ x, zTest x ∂(gaussCov (tdA zMDP zPolicy zMu) (printedGamma zMDP zPolicy zMu)) := by
  set N := gaussCov (tdA zMDP zPolicy zMu) (printedGamma zMDP zPolicy zMu)
  have hmeas : MeasurableSet (zSlab (1 / 20))ᶜ := (zSlab_isClosed _).measurableSet.compl
  have hpt : ∀ x, (zSlab (1 / 20))ᶜ.indicator (fun _ ↦ (1 / 20 : ℝ)) x ≤ zTest x := by
    intro x
    rw [zTest_apply]
    by_cases hx : x ∈ (zSlab (1 / 20))ᶜ
    · rw [Set.indicator_of_mem hx]
      simp only [zSlab, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
      exact le_min (by norm_num) hx.le
    · rw [Set.indicator_of_notMem hx]
      exact le_min zero_le_one (abs_nonneg _)
  have hI : ∫ x, (zSlab (1 / 20))ᶜ.indicator (fun _ ↦ (1 / 20 : ℝ)) x ∂N ≤ ∫ x, zTest x ∂N :=
    integral_mono ((integrable_const _).indicator hmeas) (zTest.integrable N) hpt
  rw [integral_indicator_const _ hmeas, probReal_compl_eq_one_sub (zSlab_isClosed _).measurableSet,
    smul_eq_mul] at hI
  have hG := zGauss_slab_le
  have : 0 < (1 - N.real (zSlab (1 / 20))) * (1 / 20 : ℝ) := by
    apply mul_pos _ (by norm_num)
    change (gaussCov (tdA zMDP zPolicy zMu) (printedGamma zMDP zPolicy zMu)).real
      (zSlab (1 / 20)) ≤ 1 / 4 at hG
    linarith
  linarith

end ZeroNoise

open ZeroNoise in
/-- **The classic CLT display with the printed `Γ` is false, even for some `η₀ ∈ (0, 1]` and some
`V₀` per instance** (`eqn:classic-clt`, `inference.tex:98–103`; SOURCE-ISSUES C43), under
`r(s) = r_π(s)` with action-dependent rewards. Refutes the display for the printed step-size
family `η_t = η₀ t^{-2/3}` only; the display is existential in the schedule, and the reading
"some schedule and some `V₀`" over arbitrary schedules is not refuted. -/
theorem not_eq_classic_clt_printed_someInit : ¬ Eq_classic_clt_printed_someInit := by
  intro h
  obtain ⟨η₀, h0, h1, V₀, hconv⟩ := h (Fin 2) (Fin 2) zMDP zPolicy zMu zMu_pos
  have hlim := tendsto_nhds_unique (hconv zTest) (tendsto_zTest_law h0 h1 V₀)
  exact absurd hlim (ne_of_gt zTest_gauss_pos)

/-- **The classic CLT display with the printed `Γ` is false** for every `η₀ ∈ (0, 1/4)` and
every `V₀` (`eqn:classic-clt`, `inference.tex:98–103`; SOURCE-ISSUES C43), under `r(s) = r_π(s)`
with action-dependent rewards; derived from `not_eq_classic_clt_printed_someInit` with
`η₀ = 1/8`, `V₀ = 0`. Same schedule scope. -/
theorem not_eq_classic_clt_printed : ¬ Eq_classic_clt_printed := fun h ↦
  not_eq_classic_clt_printed_someInit fun S A _ _ _ _ _ M π μ hμ ↦
    ⟨1 / 8, by norm_num, by norm_num, 0, h S A M π μ (1 / 8) 0 hμ (by norm_num) (by norm_num)⟩

end StatisticalRL.Ch7Rest.TDInference
