import Formalization.ModelFree.QLearningPrefixFiltration
import Formalization.ModelFree.QLearningIndicatorCondExp
import Formalization.Probability.EmpiricalRow
import Mathlib.Probability.Independence.Integration

/-!
# Product-law tools for the Q-learning lower bound

Generic facts about the genuine product sampling law `qSamplingLaw M N`: a function of the strict
past layers is independent of a function of the current layer; single-coordinate integrals are row
expectations; distinct coordinates are independent; draws lie in the row support almost surely;
and second-moment comparisons.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qLbProductStateMeasurable : MeasurableSpace State := ⊤
local instance qLbProductActionMeasurable : MeasurableSpace Action := ⊤

/-- Completion of a single layer to a full sample array. -/
noncomputable def qLbLayerComplete (M : DiscountedMDP State Action) (N n : ℕ)
    (code : (i : qLayerIndices (State := State) (Action := Action) N n) → State) :
    QSamples State Action N := by
  classical
  exact fun i ↦
    if h : i ∈ qLayerIndices (State := State) (Action := Action) N n then code ⟨i, h⟩
    else Classical.choice M.state_nonempty

/-- A function of the strict past layers `< n` and a function of layer `n` are uncorrelated
under the product law. -/
theorem qLb_integral_mul_past_layer (M : DiscountedMDP State Action) (N n : ℕ)
    (F G : QSamples State Action N → ℝ)
    (hF : ∀ d d' : QSamples State Action N,
      (∀ i : (State × Action) × Fin N, i.2.val < n → d i = d' i) → F d = F d')
    (hG : ∀ d d' : QSamples State Action N,
      (∀ i : (State × Action) × Fin N, i.2.val = n → d i = d' i) → G d = G d') :
    ∫ d, F d * G d ∂qSamplingLaw M N =
      (∫ d, F d ∂qSamplingLaw M N) * ∫ d, G d ∂qSamplingLaw M N := by
  classical
  let f := fun code ↦ F (qCompletePast M N n code)
  let g := fun code ↦ G (qLbLayerComplete M N n code)
  have hFf : F = f ∘ qPastData N n := by
    funext d
    apply hF
    intro i hi
    have hmem : i ∈ qPastIndices (State := State) (Action := Action) N n := by
      simp [qPastIndices, hi]
    simp [qCompletePast, qPastData, hmem]
  have hGg : G = g ∘ qLayerData N n := by
    funext d
    apply hG
    intro i hi
    have hmem : i ∈ qLayerIndices (State := State) (Action := Action) N n := by
      simp [qLayerIndices, hi]
    simp [qLbLayerComplete, qLayerData, hmem]
  have hind := (qPast_indep_layer M N n).comp (measurable_of_countable f)
    (measurable_of_countable g)
  rw [hFf, hGg]
  exact ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hind
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- A single coordinate integrates as its row expectation. -/
theorem qLb_integral_coord (M : DiscountedMDP State Action) (N : ℕ)
    (i : (State × Action) × Fin N) (g : State → ℝ) :
    ∫ d, g (d i) ∂qSamplingLaw M N = ∑ x, (M.transition i.1.1 i.1.2).prob x * g x := by
  have hmap := qSamplingLaw_marginal M N i.1.1 i.1.2 i.2
  have hv : Integrable g ((qSamplingLaw M N).map
      (fun d : QSamples State Action N ↦ d ((i.1.1, i.1.2), i.2))) := Integrable.of_finite
  have h := integral_map (μ := qSamplingLaw M N)
    (measurable_pi_apply ((i.1.1, i.1.2), i.2)).aemeasurable hv.aestronglyMeasurable
  rw [hmap, FiniteDistribution.rowMeasure_integral] at h
  simpa [FiniteDistribution.expectation] using h.symm

/-- Two distinct coordinates are independent. -/
theorem qLb_integral_two_coords (M : DiscountedMDP State Action) (N : ℕ)
    (i j : (State × Action) × Fin N) (hij : i ≠ j) (f g : State → ℝ) :
    ∫ d, f (d i) * g (d j) ∂qSamplingLaw M N =
      (∫ d, f (d i) ∂qSamplingLaw M N) * ∫ d, g (d j) ∂qSamplingLaw M N := by
  have hind := ((qSamplingLaw_independent M N).indepFun hij).comp
    (measurable_of_countable f) (measurable_of_countable g)
  exact ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hind
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- Almost surely every draw lies in the support of its row. -/
theorem qLb_support_ae (M : DiscountedMDP State Action) (N : ℕ) :
    ∀ᵐ d ∂qSamplingLaw M N, ∀ i : (State × Action) × Fin N,
      (M.transition i.1.1 i.1.2).prob (d i) ≠ 0 := by
  classical
  rw [ae_all_iff]
  intro i
  let h : QSamples State Action N → ℝ :=
    fun d ↦ if (M.transition i.1.1 i.1.2).prob (d i) = 0 then 1 else 0
  have hint : ∫ d, h d ∂qSamplingLaw M N = 0 := by
    have := qLb_integral_coord M N i
      (fun x ↦ if (M.transition i.1.1 i.1.2).prob x = 0 then 1 else 0)
    rw [this]
    apply Finset.sum_eq_zero
    intro x _
    split <;> simp_all
  have hnn : 0 ≤ᵐ[qSamplingLaw M N] h :=
    Filter.Eventually.of_forall fun d ↦ by simp only [h]; split <;> norm_num
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn (qSampling_integrable M N h)).mp hint
  filter_upwards [hz] with d hd
  intro h0
  have : h d = 1 := by simp [h, h0]
  rw [this] at hd
  norm_num at hd

/-- Jensen for squares: `(E f - c)² ≤ E (f - c)²`, and the variance is the least mean square
deviation: `E (f - E f)² ≤ E (f - c)²`. -/
theorem qLb_sq_dev (M : DiscountedMDP State Action) (N : ℕ)
    (f : QSamples State Action N → ℝ) (c : ℝ) :
    ∫ d, (f d - c) ^ 2 ∂qSamplingLaw M N =
      ∫ d, (f d - ∫ e, f e ∂qSamplingLaw M N) ^ 2 ∂qSamplingLaw M N +
        (∫ e, f e ∂qSamplingLaw M N - c) ^ 2 := by
  set m := ∫ e, f e ∂qSamplingLaw M N
  have hexp : (fun d ↦ (f d - c) ^ 2) = fun d ↦
      ((f d - m) ^ 2 + 2 * (m - c) * (f d - m)) + (m - c) ^ 2 := by
    funext d; ring
  rw [hexp, integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_const_mul, integral_sub (qSampling_integrable M N _) (qSampling_integrable M N _)]
  simp [m]

theorem qLb_sq_integral_le (M : DiscountedMDP State Action) (N : ℕ)
    (f : QSamples State Action N → ℝ) (c : ℝ) :
    (∫ d, f d ∂qSamplingLaw M N - c) ^ 2 ≤ ∫ d, (f d - c) ^ 2 ∂qSamplingLaw M N := by
  rw [qLb_sq_dev M N f c]
  have : 0 ≤ ∫ d, (f d - ∫ e, f e ∂qSamplingLaw M N) ^ 2 ∂qSamplingLaw M N :=
    integral_nonneg fun d ↦ sq_nonneg _
  linarith

theorem qLb_variance_le (M : DiscountedMDP State Action) (N : ℕ)
    (f : QSamples State Action N → ℝ) (c : ℝ) :
    ∫ d, (f d - ∫ e, f e ∂qSamplingLaw M N) ^ 2 ∂qSamplingLaw M N ≤
      ∫ d, (f d - c) ^ 2 ∂qSamplingLaw M N := by
  rw [qLb_sq_dev M N f c]
  nlinarith [sq_nonneg (∫ e, f e ∂qSamplingLaw M N - c)]

/-- Sample-stream agreement from agreement of the strict past layers. -/
theorem qSamplesExtend_agree_past (M : DiscountedMDP State Action) (N n : ℕ)
    (d d' : QSamples State Action N)
    (h : ∀ i : (State × Action) × Fin N, i.2.val < n → d i = d' i)
    (k : ℕ) (hk : k ≤ n) (s : State) (a : Action) :
    qSamplesExtend M N d k s a = qSamplesExtend M N d' k s a := by
  unfold qSamplesExtend
  split
  · rename_i hk'
    exact h _ (by simp; omega)
  · rfl

/-- Sample-stream agreement at the source time `n+1` from agreement of layer `n`. -/
theorem qSamplesExtend_agree_layer (M : DiscountedMDP State Action) (N n : ℕ)
    (d d' : QSamples State Action N)
    (h : ∀ i : (State × Action) × Fin N, i.2.val = n → d i = d' i) (s : State) (a : Action) :
    qSamplesExtend M N d (n + 1) s a = qSamplesExtend M N d' (n + 1) s a := by
  unfold qSamplesExtend
  split
  · exact h _ (by simp)
  · rfl

/-- For `1 ≤ k ≤ N` the stream entry is the zero-based coordinate `k-1`. -/
theorem qSamplesExtend_coord (M : DiscountedMDP State Action) (N k : ℕ) (hk1 : 1 ≤ k)
    (hkN : k ≤ N) (d : QSamples State Action N) (s : State) (a : Action) :
    qSamplesExtend M N d k s a = d ((s, a), ⟨k - 1, by omega⟩) := by
  unfold qSamplesExtend
  rw [dif_pos ⟨by omega, hkN⟩]

end StatisticalRL.QLearning
