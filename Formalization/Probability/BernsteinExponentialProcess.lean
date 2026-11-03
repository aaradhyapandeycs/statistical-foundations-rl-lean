import Formalization.Probability.ConditionalBernsteinSharpMGF
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! The genuine exponential supermartingale from the sharp conditional Bernstein MGF bound. No tail inequality is asserted. -/
open MeasureTheory
open scoped BigOperators
namespace StatisticalRL

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-- Sharp bounded-increment Bernstein compensator coefficient. -/
noncomputable def bernsteinCoefficient (B t : ℝ) : ℝ := t ^ 2 / (2 * (1 - |t| * B / 3))

theorem bernsteinCoefficient_nonneg (B t : ℝ) (ht : |t| * B < 3) :
    0 ≤ bernsteinCoefficient B t := by
  unfold bernsteinCoefficient
  apply div_nonneg (sq_nonneg t)
  linarith

/-- Recursive exponential process with the actual predictable conditional
second moment, indexed with X n revealed at filtration time n+1. -/
noncomputable def bernsteinExponentialProcess (μ : Measure Ω)
    (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (B t : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ ↦ 1
  | n + 1 => fun ω ↦ bernsteinExponentialProcess μ ℱ X B t n ω *
      Real.exp (t * X n ω - bernsteinCoefficient B t * μ[fun ω' ↦ X n ω' ^ 2 | ℱ n] ω)

/-- The recursive process is literally the exponential of the actual
increment sum minus its cumulative predictable second-moment compensation. -/
theorem bernsteinExponentialProcess_eq_exp_sum (μ : Measure Ω)
    (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (B t : ℝ) (n : ℕ) (ω : Ω) :
    bernsteinExponentialProcess μ ℱ X B t n ω =
      Real.exp (t * (∑ k ∈ Finset.range n, X k ω) -
        bernsteinCoefficient B t * (∑ k ∈ Finset.range n, μ[fun ω' ↦ X k ω' ^ 2 | ℱ k] ω)) := by
  induction n with
  | zero => simp [bernsteinExponentialProcess]
  | succ n ih =>
    change bernsteinExponentialProcess μ ℱ X B t n ω *
      Real.exp (t * X n ω - bernsteinCoefficient B t * μ[fun ω' ↦ X n ω' ^ 2 | ℱ n] ω) = _
    rw [ih, ← Real.exp_add]
    congr 1
    simp only [Finset.sum_range_succ]
    ring

/-- The process is positive at every outcome, not merely almost everywhere. -/
theorem bernsteinExponentialProcess_pos (μ : Measure Ω)
    (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (B t : ℝ) (n : ℕ) (ω : Ω) :
    0 < bernsteinExponentialProcess μ ℱ X B t n ω := by
  induction n with
  | zero => simp [bernsteinExponentialProcess]
  | succ n ih => exact mul_pos ih (Real.exp_pos _)

/-- Actual filtration adaptedness follows from measurability of each newly
revealed increment and the predictable conditional variance. -/
theorem bernsteinExponentialProcess_adapted (μ : Measure Ω)
    (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (B t : ℝ)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n)) :
    Adapted ℱ (bernsteinExponentialProcess μ ℱ X B t) := by
  intro n
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
    have hp := ih.measurable.mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have hx := (hX n).measurable
    have hv := (stronglyMeasurable_condExp (μ := μ)
      (m := ℱ n) (f := fun ω ↦ X n ω ^ 2)).measurable.mono
        (ℱ.mono (Nat.le_succ n)) le_rfl
    change StronglyMeasurable[ℱ (n + 1)] (fun ω ↦
      bernsteinExponentialProcess μ ℱ X B t n ω *
        Real.exp (t * X n ω - bernsteinCoefficient B t * μ[fun ω' ↦ X n ω' ^ 2 | ℱ n] ω))
    exact (hp.mul ((measurable_const.mul hx).sub (measurable_const.mul hv)).exp).stronglyMeasurable

/-- A finite-time deterministic upper envelope gives integrability; it is
not an assumed bound on a tail or on a desired performance estimate. -/
theorem bernsteinExponentialProcess_bound (μ : Measure Ω)
    (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (B t : ℝ)
    (_hB : 0 ≤ B) (ht : |t| * B < 3) (hbound : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B) (n : ℕ) :
    ∀ᵐ ω ∂μ, bernsteinExponentialProcess μ ℱ X B t n ω ≤
      Real.exp (n * (|t| * B)) := by
  induction n with
  | zero => simp [bernsteinExponentialProcess]
  | succ n ih =>
    have hv : 0 ≤ᵐ[μ] μ[fun ω ↦ X n ω ^ 2 | ℱ n] :=
      condExp_nonneg (Filter.Eventually.of_forall fun ω ↦ sq_nonneg _)
    filter_upwards [ih, hbound n, hv] with ω hi hx hv
    have hex : t * X n ω - bernsteinCoefficient B t * μ[fun ω' ↦ X n ω' ^ 2 | ℱ n] ω ≤ |t| * B := by
      have hb := (mul_le_mul_of_nonneg_left hx (abs_nonneg t))
      have ha := le_abs_self (t * X n ω)
      rw [abs_mul] at ha
      nlinarith [mul_nonneg (bernsteinCoefficient_nonneg B t ht) hv]
    calc
      _ ≤ Real.exp (n * (|t| * B)) * Real.exp (|t| * B) :=
        mul_le_mul hi (Real.exp_le_exp.mpr hex) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp ((n + 1 : ℕ) * (|t| * B)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

/-- Under actual bounded martingale-difference assumptions the constructed
process is a supermartingale. Constants correspond to the sharp Bernstein compensator and |t|B<3 domain. -/
theorem bernsteinExponentialProcess_supermartingale
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B t : ℝ) (hB : 0 ≤ B)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hbound : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B) (ht : |t| * B < 3)
    (hmean : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) :
    Supermartingale (bernsteinExponentialProcess μ ℱ X B t) ℱ μ := by
  let Z := bernsteinExponentialProcess μ ℱ X B t
  have had := bernsteinExponentialProcess_adapted μ ℱ X B t hX
  have hint (n : ℕ) : Integrable (Z n) μ := by
    apply Integrable.of_bound ((had n).mono (ℱ.le n)).aestronglyMeasurable
      (Real.exp (n * (|t| * B)))
    filter_upwards [bernsteinExponentialProcess_bound μ ℱ X B t hB ht hbound n] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_pos (bernsteinExponentialProcess_pos μ ℱ X B t n ω)] using hω
  apply supermartingale_nat had hint
  intro n
  let V := μ[fun ω ↦ X n ω ^ 2 | ℱ n]
  let A := fun ω ↦ Z n ω * Real.exp (-(bernsteinCoefficient B t * V ω))
  let E := fun ω ↦ Real.exp (t * X n ω)
  have hx := (hX n).measurable.mono (ℱ.le (n + 1)) le_rfl
  have hsmall : ∀ᵐ ω ∂μ, |t * X n ω| ≤ |t| * B := by
    filter_upwards [hbound n] with ω hω
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hω (abs_nonneg t)
  have hei : Integrable E μ := by
    apply Integrable.of_bound (by dsimp [E]; fun_prop) (Real.exp (|t| * B))
    filter_upwards [hsmall] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hω)
  have hA : StronglyMeasurable[ℱ n] A := by
    have hz := (had n).measurable
    have hv := (stronglyMeasurable_condExp (μ := μ)
      (m := ℱ n) (f := fun ω ↦ X n ω ^ 2)).measurable
    exact (hz.mul (measurable_const.mul hv).neg.exp).stronglyMeasurable
  have hprod : A * E = Z (n + 1) := by
    funext ω
    dsimp [A, E, Z, V, bernsteinExponentialProcess]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hpull := condExp_mul_of_stronglyMeasurable_left hA
    (hprod.symm ▸ hint (n + 1)) hei
  have hmgf := conditional_mgf_le_exp_bernstein_secondMoment μ (ℱ n) (ℱ.le n)
    (X n) hx B t (hbound n) ht (hmean n)
  rw [hprod] at hpull
  filter_upwards [hpull, hmgf] with ω hp hm
  change μ[Z (n + 1) | ℱ n] ω = A ω * μ[E | ℱ n] ω at hp
  rw [hp]
  calc
    _ ≤ A ω * Real.exp (bernsteinCoefficient B t * V ω) := mul_le_mul_of_nonneg_left hm
      (mul_nonneg (bernsteinExponentialProcess_pos μ ℱ X B t n ω).le (Real.exp_pos _).le)
    _ = Z n ω := by
      dsimp [A]
      rw [mul_assoc, ← Real.exp_add]
      simp

end StatisticalRL
