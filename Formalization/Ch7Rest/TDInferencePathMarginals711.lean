import Formalization.Ch7Rest.TDInference711Defs
import Formalization.Probability.GaussianAntiConcentration

/-!
# Theorem 7.11 support: prefix marginals of the i.i.d. TD path law, and slab bounds for `gaussCov`

General facts (any finite MDP, policy, sampling law) about the M1 objects of
`TDInference711Defs.lean` (source `chapters/inference.tex:47–117`):

* `StatisticalRL.Fintype.sum_fin_succ_snoc`: a sum over `Fin (n+1) → X` splits as a sum over
  the first `n` coordinates and the last one (`Fin.snoc`).
* `tdIter_snoc_of_le`, `tdIter_snoc_last`, `pathWeight_snoc`: appending a sample changes neither
  the earlier iterates nor their weights, and the last iterate is one more TD step.
* `sum_pathWeight_mul_tdIter_of_le`: the expectation of any function of the `t`-th iterate is the
  same under the length-`T` path law for every `T ≥ t` (prefix marginalization).
* `sum_pathWeight_mul_tdIter_succ`: the one-step (tower-property) identity on exact-length paths.
* `gaussCov_slab_le`: `N(0, A⁻¹ diag(Γ) A⁻ᵀ){x : |x_{s₀} - b| ≤ δ} ≤ 2δ/(|(A⁻¹)_{s₀ j}√Γ_j| √(2π))`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Fintype

/-- Split a sum over `Fin (n+1) → X` into the first `n` coordinates and the last one. -/
theorem sum_fin_succ_snoc {X : Type*} [Fintype X] {n : ℕ} {β : Type*} [AddCommMonoid β]
    (F : (Fin (n + 1) → X) → β) :
    ∑ ω, F ω = ∑ ω : Fin n → X, ∑ x : X, F (Fin.snoc ω x) := by
  rw [← (Fin.snocEquiv fun _ ↦ X).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

end StatisticalRL.Fintype

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action]

theorem tdIter_snoc_of_le [DecidableEq State] (M : DiscountedMDP State Action) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (ω : Fin T → Tuple State Action) (x : Tuple State Action) :
    ∀ {t : ℕ}, t ≤ T →
      tdIter M η₀ V₀ (Fin.snoc ω x : Fin (T + 1) → Tuple State Action) t = tdIter M η₀ V₀ ω t
  | 0, _ => rfl
  | t + 1, ht => by
    have h' : t < T := ht
    have h1 : t < T + 1 := by omega
    rw [tdIter, tdIter, dif_pos h1, dif_pos h', tdIter_snoc_of_le M η₀ V₀ ω x h'.le]
    congr 1
    simp [Fin.snoc, h']

theorem tdIter_snoc_last [DecidableEq State] (M : DiscountedMDP State Action) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (ω : Fin T → Tuple State Action) (x : Tuple State Action) :
    tdIter M η₀ V₀ (Fin.snoc ω x : Fin (T + 1) → Tuple State Action) (T + 1) =
      tdStep M (stepSize η₀ (T + 1)) (tdIter M η₀ V₀ ω T) x := by
  rw [tdIter, dif_pos (Nat.lt_succ_self T), tdIter_snoc_of_le M η₀ V₀ ω x le_rfl]
  congr 1
  simp [Fin.snoc]

theorem pathWeight_snoc (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {T : ℕ} (ω : Fin T → Tuple State Action)
    (x : Tuple State Action) :
    pathWeight M π μ (Fin.snoc ω x : Fin (T + 1) → Tuple State Action) =
      pathWeight M π μ ω * tupleProb M π μ x := by
  simp [pathWeight, Fin.prod_univ_castSucc]

/-- Prefix marginalization: for `t ≤ T`, the expectation of any function of `V_t` under the
length-`T` i.i.d. path law equals that under the length-`t` law. -/
theorem sum_pathWeight_mul_tdIter_of_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (f : (State → ℝ) → ℝ) {t T : ℕ} (htT : t ≤ T) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * f (tdIter M η₀ V₀ ω t) =
      ∑ ω : Fin t → Tuple State Action, pathWeight M π μ ω * f (tdIter M η₀ V₀ ω t) := by
  induction T, htT using Nat.le_induction with
  | base => rfl
  | succ T hT ih =>
    rw [Fintype.sum_fin_succ_snoc, ← ih]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    simp_rw [pathWeight_snoc, tdIter_snoc_of_le M η₀ V₀ ω _ hT, mul_assoc, ← Finset.mul_sum]
    rw [← Finset.sum_mul, sum_tupleProb, one_mul]

/-- One-step identity on exact-length paths: `E f(V_{t+1}) = E ∑ₓ p(x) f(TDstep(V_t, x))`. -/
theorem sum_pathWeight_mul_tdIter_succ [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (f : (State → ℝ) → ℝ) (t : ℕ) :
    ∑ ω : Fin (t + 1) → Tuple State Action, pathWeight M π μ ω * f (tdIter M η₀ V₀ ω (t + 1)) =
      ∑ ω : Fin t → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x * f (tdStep M (stepSize η₀ (t + 1)) (tdIter M η₀ V₀ ω t) x) := by
  rw [Fintype.sum_fin_succ_snoc]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  simp_rw [pathWeight_snoc, tdIter_snoc_last, Finset.mul_sum, mul_assoc]

/-- Slab anti-concentration of the printed-form Gaussian `N(0, A⁻¹ diag(Γ) A⁻ᵀ)`. -/
theorem gaussCov_slab_le [DecidableEq State] (A : Matrix State State ℝ) (Γ : State → ℝ)
    (s₀ j : State) (hj : A⁻¹ s₀ j * Real.sqrt (Γ j) ≠ 0) (b δ : ℝ) :
    gaussCov A Γ {x | |x s₀ - b| ≤ δ} ≤
      ENNReal.ofReal (2 * δ / (|A⁻¹ s₀ j * Real.sqrt (Γ j)| * Real.sqrt (2 * Real.pi))) := by
  have hmeas : MeasurableSet {x : State → ℝ | |x s₀ - b| ≤ δ} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [gaussCov, Measure.map_apply (measurable_gaussMap A Γ) hmeas]
  have hset : gaussMap A Γ ⁻¹' {x : State → ℝ | |x s₀ - b| ≤ δ} =
      {z | |∑ i, (A⁻¹ s₀ i * Real.sqrt (Γ i)) * z i - b| ≤ δ} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, gaussMap, Matrix.mulVec, dotProduct, mul_assoc]
  rw [hset]
  exact StatisticalRL.Probability.stdGaussianPi_abs_linear_le (ι := State)
    (fun i ↦ A⁻¹ s₀ i * Real.sqrt (Γ i)) hj b δ

end StatisticalRL.Ch7Rest.TDInference
