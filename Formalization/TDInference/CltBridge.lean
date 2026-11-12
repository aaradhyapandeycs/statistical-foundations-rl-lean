import Formalization.TDInference.ClassicCLT
import Formalization.TDInference.Operator

/-!
# Canonicity bridges for the TD classic CLT (Theorem 7.11 / `eqn:classic-clt`)

Source: `chapters/inference.tex:98–117`.

* `tdA_isUnit_of_forall_pos`: under full support of `μ` (the only hypothesis the CLT, plug-in and
  confidence-set statements carry on `μ`), the matrix `A = diag(μ)(I − γP_π)` is invertible, so
  `gaussCov (tdA M π μ) Γ` uses a genuine inverse and not Lean's junk value `0` of `Matrix.inv`
  on singular matrices.
* `tendsto_lawProbabilityMeasure_iff_forall_bcf`: the library's formulation of convergence in
  distribution (convergence of `E g(√T Δ̄_T)` for every bounded continuous `g`, as in the
  statement index entries `Eq_classic_clt_corrected` and `Eq_classic_clt_restricted`) is Mathlib's
  weak convergence of `ProbabilityMeasure`, via
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.
-/

open MeasureTheory Filter Topology

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- **`A = diag(μ)(I − γP_π)` is invertible under full support** of `μ` (`inference.tex:110`):
every hypothesis `∀ s, 0 < μ.prob s` carried by the CLT and confidence statements suffices. -/
theorem tdA_isUnit_of_forall_pos [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) : IsUnit (tdA M π μ) :=
  tdA_isUnit M π μ (diagMin_prob_pos μ hμ) (diagMin_prob_le μ)

/-- Under full support of `μ`, the determinant of `A` is a unit, so `A⁻¹` is a true two-sided
inverse. -/
theorem isUnit_det_tdA_of_forall_pos [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) : IsUnit (tdA M π μ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit_of_forall_pos M π μ hμ)

/-- Under full support of `μ`, `A * A⁻¹ = 1`, so the Gaussian limit `gaussCov (tdA M π μ) Γ` is
`N(0, A⁻¹ diag(Γ) A⁻ᵀ)` with an honest inverse. -/
theorem tdA_mul_inv_of_forall_pos [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) :
    tdA M π μ * (tdA M π μ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_tdA_of_forall_pos M π μ hμ)

/-- **Weak convergence bridge.** Convergence of the law of `√T Δ̄_T` to `N(0, A⁻¹ diag(Γ) A⁻ᵀ)`
in Mathlib's topology on `ProbabilityMeasure (State → ℝ)` is equivalent to the formulation used in
the statement index: `E g(√T Δ̄_T) → ∫ g d gaussCov A Γ` for every bounded continuous `g`. -/
theorem tendsto_lawProbabilityMeasure_iff_forall_bcf [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ)
    (A : Matrix State State ℝ) (Γ : State → ℝ) :
    Tendsto (fun T : ℕ ↦ lawProbabilityMeasure M π μ η₀ V₀ T) atTop (𝓝 (gaussCovPM A Γ)) ↔
      ∀ g : BoundedContinuousFunction (State → ℝ) ℝ,
        Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action,
            pathWeight M π μ ω * g (scaledError M π η₀ V₀ ω)) atTop
          (𝓝 (∫ x, g x ∂(gaussCov A Γ))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine forall_congr' fun g ↦ ?_
  change Tendsto (fun T : ℕ ↦ ∫ x, g x ∂(lawMeasure M π μ η₀ V₀ T)) atTop
    (𝓝 (∫ x, g x ∂(gaussCov A Γ))) ↔ _
  simp_rw [integral_lawMeasure M π μ η₀ V₀]

end StatisticalRL.Ch7Rest.TDInference
