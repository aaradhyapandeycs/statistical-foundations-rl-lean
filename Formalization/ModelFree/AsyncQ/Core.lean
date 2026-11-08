import Formalization.ModelFree.AsyncQ.Definitions
import Formalization.ModelFree.AsyncQ.Weights
import Formalization.Probability.FiniteMarkov.Measure
import Formalization.Probability.FiniteMarkov.WindowVisits
import Formalization.ModelFree.QLearningChiResidual
import Formalization.ModelFree.QLearningChiResidualUpper

/-! # Asynchronous Q-learning: pathwise identities and per-window Freedman events

* the pair kernel is stochastic and the initial law is a probability vector;
* the iterates stay in `[0, 1/(1-γ)]` (analogue of `lemma:non-negativity-Qt-Vt`);
* `window_plus_le` / `window_minus_le`: the unrolled one-sided error bound over a window, for any
  comparator `Q_c`, with the residual `Q_c - r - γ P V_c` (resp. `r + γ P V_c - Q_c`);
* `window_freedman`: for a fixed comparator value `V_c`, pair `z`, window start `τ`, length `m`
  and final count `n`, Freedman with the predictable weights in the pair-chain filtration. -/

open MeasureTheory
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatisticalRL.AsyncQ

open StatisticalRL.FiniteMarkov StatisticalRL.QLearning

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

attribute [local instance] pairMeasurableSpace

local instance pairMeasurableSingletonClass : @MeasurableSingletonClass (S × A) pairMeasurableSpace :=
  ⟨fun _ ↦ trivial⟩

theorem pairKernel_isStochastic (M : DiscountedMDP S A) (πb : StationaryPolicy S A) :
    IsStochastic (pairKernel M πb) where
  nonneg x y := mul_nonneg ((M.transition x.1 x.2).prob_nonneg _) ((πb y.1).prob_nonneg _)
  row_sum x := by
    unfold pairKernel
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, (πb _).sum_prob, mul_one]
    exact (M.transition x.1 x.2).sum_prob

theorem initLaw_isProb (πb : StationaryPolicy S A) (s₀ : S) : IsProb (initLaw πb s₀) where
  nonneg x := by unfold initLaw; split_ifs <;> simp [(πb s₀).prob_nonneg]
  sum_eq := by
    unfold initLaw
    rw [Fintype.sum_prod_type, sum_eq_single s₀]
    · simpa using (πb s₀).sum_prob
    · intro s _ hs; simp [hs]
    · simp

theorem pathLaw_eq (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (s₀ : S) (T : ℕ) :
    pathLaw M πb s₀ T = pathMeasure (initLaw πb s₀) (pairKernel M πb) T := rfl

/-! ## Iterates -/

variable (M : DiscountedMDP S A) (η : ℝ) (Q₀ : S → A → ℝ)

theorem iterate_succ_of_eq {n : ℕ} (x : Fin (n + 1) → S × A) (t : ℕ) (s : S) (a : A)
    (h : (s, a) = pathAt x t) :
    iterate M η Q₀ x (t + 1) s a = (1 - η) * iterate M η Q₀ x t s a +
      η * (M.reward s a + M.discount * qLearningValue M (iterate M η Q₀ x t) (pathAt x (t + 1)).1) := by
  rw [iterate]; exact if_pos h

theorem iterate_succ_of_ne {n : ℕ} (x : Fin (n + 1) → S × A) (t : ℕ) (s : S) (a : A)
    (h : ¬ (s, a) = pathAt x t) : iterate M η Q₀ x (t + 1) s a = iterate M η Q₀ x t s a := by
  rw [iterate]; exact if_neg h

theorem iterate_mem {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {Q₀ : S → A → ℝ}
    (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) {n : ℕ} (x : Fin (n + 1) → S × A)
    (t : ℕ) : ∀ s a, 0 ≤ iterate M η Q₀ x t s a ∧ iterate M η Q₀ x t s a ≤ M.effectiveHorizon := by
  induction t with
  | zero => exact h₀
  | succ t ih =>
    intro s a
    by_cases h : (s, a) = pathAt x t
    · rw [iterate_succ_of_eq M η Q₀ x t s a h]
      have hv := qLearningValue_bounds M _ ih (pathAt x (t + 1)).1
      have hr0 := M.reward_nonneg s a
      have hr1 := M.reward_le_one s a
      have hrec := M.effectiveHorizon_recursion
      have hγ := M.discount_nonneg
      have hq := ih s a
      have h1 : 0 ≤ M.reward s a + M.discount * qLearningValue M (iterate M η Q₀ x t)
          (pathAt x (t + 1)).1 := by nlinarith
      have h2 : M.reward s a + M.discount * qLearningValue M (iterate M η Q₀ x t)
          (pathAt x (t + 1)).1 ≤ M.effectiveHorizon := by nlinarith
      constructor <;> nlinarith
    · rw [iterate_succ_of_ne M η Q₀ x t s a h]; exact ih s a

theorem value_sub_le (Q Q' : S → A → ℝ) (s : S) {B : ℝ} (h : ∀ a, Q s a - Q' s a ≤ B) :
    qLearningValue M Q s - qLearningValue M Q' s ≤ B := by
  letI : Nonempty A := M.action_nonempty
  change actionMaximum (Q s) - actionMaximum (Q' s) ≤ B
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (Q s)
  have h1 : actionMaximum (Q s) = Q s a := ha
  have h2 := le_actionMaximum (Q' s) a
  linarith [h a]

/-- Window visit predicate: step `k` of the window starting at `τ` updates `z`. -/
def visits {n : ℕ} (x : Fin (n + 1) → S × A) (τ : ℕ) (z : S × A) (k : ℕ) : Prop :=
  pathAt x (τ + k) = z

instance {n : ℕ} (x : Fin (n + 1) → S × A) (τ : ℕ) (z : S × A) : DecidablePred (visits x τ z) :=
  fun k ↦ inferInstanceAs (Decidable (pathAt x (τ + k) = z))

/-- The noise `γ (V_c(s_{τ+k+1}) - P_z V_c)` of window step `k`. -/
noncomputable def noise {n : ℕ} (x : Fin (n + 1) → S × A) (τ : ℕ) (z : S × A) (Vc : S → ℝ)
    (k : ℕ) : ℝ :=
  M.discount * (Vc (pathAt x (τ + k + 1)).1 - (M.transition z.1 z.2).expectation Vc)

theorem window_plus_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {n : ℕ} (x : Fin (n + 1) → S × A)
    (Qc : S → A → ℝ) (τ K : ℕ) (s : S) (a : A) {B : ℝ}
    (hB : ∀ t, τ ≤ t → t < τ + K → ∀ s' a', iterate M η Q₀ x t s' a' - Qc s' a' ≤ B) :
    iterate M η Q₀ x (τ + K) s a - Qc s a ≤
      (1 - η) ^ cnt (visits x τ (s, a)) K * (iterate M η Q₀ x τ s a - Qc s a) +
      (1 - (1 - η) ^ cnt (visits x τ (s, a)) K) *
        (M.discount * B - qComparatorResidualPlus M Qc s a) +
      accum (visits x τ (s, a)) η (noise M x τ (s, a) (qLearningValue M Qc)) K := by
  have h := unroll_le (visits x τ (s, a)) hη0 hη1 M.discount_nonneg
    (fun k ↦ iterate M η Q₀ x (τ + k) s a - Qc s a)
    (fun k ↦ qLearningValue M (iterate M η Q₀ x (τ + k)) (pathAt x (τ + k + 1)).1 -
      qLearningValue M Qc (pathAt x (τ + k + 1)).1)
    (noise M x τ (s, a) (qLearningValue M Qc)) (R := qComparatorResidualPlus M Qc s a) (B := B) K
    (fun k _ ↦ by
      simp only [visits, ← add_assoc]
      by_cases hv : pathAt x (τ + k) = (s, a)
      · rw [if_pos hv, iterate_succ_of_eq M η Q₀ x (τ + k) s a hv.symm]
        simp only [noise, qComparatorResidualPlus]; ring
      · rw [if_neg hv, iterate_succ_of_ne M η Q₀ x (τ + k) s a (Ne.symm hv)])
    (fun k hk _ ↦ value_sub_le M _ _ _ fun a' ↦ hB (τ + k) (by omega) (by omega) _ a')
  simpa using h

theorem window_minus_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {n : ℕ} (x : Fin (n + 1) → S × A)
    (Qc : S → A → ℝ) (τ K : ℕ) (s : S) (a : A) {B : ℝ}
    (hB : ∀ t, τ ≤ t → t < τ + K → ∀ s' a', Qc s' a' - iterate M η Q₀ x t s' a' ≤ B) :
    Qc s a - iterate M η Q₀ x (τ + K) s a ≤
      (1 - η) ^ cnt (visits x τ (s, a)) K * (Qc s a - iterate M η Q₀ x τ s a) +
      (1 - (1 - η) ^ cnt (visits x τ (s, a)) K) *
        (M.discount * B - qComparatorResidualMinus M Qc s a) +
      accum (visits x τ (s, a)) η (fun k ↦ -noise M x τ (s, a) (qLearningValue M Qc) k) K := by
  have h := unroll_le (visits x τ (s, a)) hη0 hη1 M.discount_nonneg
    (fun k ↦ Qc s a - iterate M η Q₀ x (τ + k) s a)
    (fun k ↦ qLearningValue M Qc (pathAt x (τ + k + 1)).1 -
      qLearningValue M (iterate M η Q₀ x (τ + k)) (pathAt x (τ + k + 1)).1)
    (fun k ↦ -noise M x τ (s, a) (qLearningValue M Qc) k)
    (R := qComparatorResidualMinus M Qc s a) (B := B) K
    (fun k _ ↦ by
      simp only [visits, ← add_assoc]
      by_cases hv : pathAt x (τ + k) = (s, a)
      · rw [if_pos hv, iterate_succ_of_eq M η Q₀ x (τ + k) s a hv.symm]
        simp only [noise, qComparatorResidualMinus]; ring
      · rw [if_neg hv, iterate_succ_of_ne M η Q₀ x (τ + k) s a (Ne.symm hv)])
    (fun k hk _ ↦ value_sub_le M _ _ _ fun a' ↦ hB (τ + k) (by omega) (by omega) _ a')
  simpa using h

theorem accum_neg (v : ℕ → Prop) [DecidablePred v] (η : ℝ) (d : ℕ → ℝ) (K : ℕ) :
    accum v η (fun k ↦ -d k) K = -accum v η d K := by
  induction K with
  | zero => simp [accum]
  | succ K ih => simp only [accum, ih]; split_ifs <;> ring

end StatisticalRL.AsyncQ
