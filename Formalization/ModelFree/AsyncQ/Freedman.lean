import Formalization.ModelFree.AsyncQ.Core

/-! # Per-window Freedman events for asynchronous Q-learning

For a fixed comparator value `V_c` with span at most `1/(1-γ)`, a pair `z`, a window start `τ`,
a length `m` and a final visit count `n`, the predictable-weight sum
`∑_{j<m} weight_n(j) · γ (V_c(s_{τ+j+1}) - P_z V_c)` is a martingale in the pair-chain filtration
`σ(X₀..X_{τ+j})` (plan §3.3–3.4), with predictable variance at most `γ² η Var_{P_z} V_c`. Freedman
(`K₀ = 1`) gives the radius `γ √(ρ Var) + γ ρ H / 6` with `ρ = 8 η log(2/δ₁)`. -/

open MeasureTheory
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatisticalRL.AsyncQ

open StatisticalRL.FiniteMarkov StatisticalRL.QLearning

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

attribute [local instance] pairMeasurableSpace

local instance pairMeasurableSingletonClass' : @MeasurableSingletonClass (S × A) pairMeasurableSpace :=
  ⟨fun _ ↦ trivial⟩

theorem weight_congr (v v' : ℕ → Prop) [DecidablePred v] [DecidablePred v'] (η : ℝ) (n j : ℕ)
    (h : ∀ i ≤ j, (v i ↔ v' i)) : weight v η n j = weight v' η n j := by
  have hc : cnt v (j + 1) = cnt v' (j + 1) := by
    unfold cnt; congr 1
    exact Finset.filter_congr fun i hi ↦ h i (by have := mem_range.mp hi; omega)
  unfold weight
  rw [hc]
  by_cases h1 : v j ∧ cnt v' (j + 1) ≤ n
  · rw [if_pos h1, if_pos ⟨(h j le_rfl).1 h1.1, h1.2⟩]
  · rw [if_neg h1, if_neg (fun h2 ↦ h1 ⟨(h j le_rfl).2 h2.1, h2.2⟩)]

theorem pairKernel_sum_fst (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (u : S × A)
    (f : S → ℝ) : ∑ y, pairKernel M πb u y * f y.1 = (M.transition u.1 u.2).expectation f := by
  unfold pairKernel FiniteDistribution.expectation
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun s' _ ↦ ?_
  have : ∑ a', (M.transition u.1 u.2).prob s' * (πb s').prob a' * f s' =
      (M.transition u.1 u.2).prob s' * f s' * ∑ a', (πb s').prob a' := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ ↦ by ring
  simp only [this, (πb s').sum_prob, mul_one]

theorem window_freedman (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (s₀ : S) {T : ℕ}
    (Vc : S → ℝ) (hspan : ∀ s₁ s₂, |Vc s₁ - Vc s₂| ≤ M.effectiveHorizon) (z : S × A) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (τ m n : ℕ) (hm : τ + m ≤ T) (δ₁ : ℝ) (hδ : 0 < δ₁)
    (hδ1 : δ₁ < 1) :
    1 - δ₁ ≤ (pathLaw M πb s₀ T).real {x | |∑ j ∈ range m,
      weight (visits x τ z) η n j * noise M x τ z Vc j| ≤
        M.discount * Real.sqrt (8 * η * Real.log (2 / δ₁) * (M.transition z.1 z.2).variance Vc) +
          M.discount * (8 * η * Real.log (2 / δ₁)) * M.effectiveHorizon / 6} := by
  set γ := M.discount
  set H := M.effectiveHorizon
  set p := M.transition z.1 z.2
  set Var := p.variance Vc
  set E := p.expectation Vc
  have hγ := M.discount_nonneg
  have hH := M.effectiveHorizon_nonneg
  have hVar : 0 ≤ Var := p.variance_nonneg Vc
  have hK := pairKernel_isStochastic M πb
  have hν := initLaw_isProb πb s₀
  let C : ℕ → (Fin (T + 1) → S × A) → ℝ := fun j x ↦ weight (visits x τ z) η n j
  let hf : S × A → S × A → ℝ := fun u y ↦ if u = z then γ * (Vc y.1 - E) else 0
  have hC : ∀ j, DependsUpTo (τ + j) (C j) := fun j x x' hx ↦
    weight_congr _ _ η n j fun i hi ↦ by
      simp only [visits]; rw [hx (τ + i) (by omega)]
  have hcent : ∀ u, ∑ y, pairKernel M πb u y * hf u y = 0 := fun u ↦ by
    by_cases hu : u = z
    · subst hu
      simp only [hf, if_true]
      rw [pairKernel_sum_fst M πb u (fun s ↦ γ * (Vc s - E)), FiniteDistribution.expectation_mul,
        FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const]
      simp [E, p]
    · simp [hf, hu]
  have hHb : ∀ u y, |hf u y| ≤ γ * H := fun u y ↦ by
    simp only [hf]
    split_ifs
    · rw [abs_mul, abs_of_nonneg hγ]
      exact mul_le_mul_of_nonneg_left (qChi_abs_centered_le_of_pairwise p Vc H hspan _) hγ
    · simpa using mul_nonneg hγ hH
  have hq : ∀ u, ∑ y, pairKernel M πb u y * hf u y ^ 2 ≤ γ ^ 2 * Var := fun u ↦ by
    by_cases hu : u = z
    · subst hu
      simp only [hf, if_true]
      rw [pairKernel_sum_fst M πb u (fun s ↦ (γ * (Vc s - E)) ^ 2)]
      have : (fun s ↦ (γ * (Vc s - E)) ^ 2) = fun s ↦ γ ^ 2 * (Vc s - E) ^ 2 := by
        funext s; ring
      rw [this, FiniteDistribution.expectation_mul, ← p.variance_eq_expectation_centered_sq]
    · simp [hf, hu]; positivity
  have hσ : ∀ x : Fin (T + 1) → S × A, ∑ j ∈ range m, C j x ^ 2 *
      ∑ y, pairKernel M πb (pathAt x (τ + j)) y * hf (pathAt x (τ + j)) y ^ 2 ≤ γ ^ 2 * η * Var :=
    fun x ↦ by
      calc ∑ j ∈ range m, C j x ^ 2 *
            ∑ y, pairKernel M πb (pathAt x (τ + j)) y * hf (pathAt x (τ + j)) y ^ 2
          ≤ ∑ j ∈ range m, C j x ^ 2 * (γ ^ 2 * Var) :=
            sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hq _) (sq_nonneg _)
        _ = (∑ j ∈ range m, weight (visits x τ z) η n j ^ 2) * (γ ^ 2 * Var) := by rw [sum_mul]
        _ ≤ η * (γ ^ 2 * Var) :=
            mul_le_mul_of_nonneg_right (sum_weight_sq_le _ hη0 hη1 n m) (by positivity)
        _ = γ ^ 2 * η * Var := by ring
  have key := markov_freedman hK hν hm C hC hη0.le
    (fun j x ↦ abs_weight_le _ hη0.le hη1 n j) hf hcent (mul_nonneg hγ hH) hHb
    (by positivity) hσ δ₁ hδ hδ1
  haveI := pathMeasure_isProb hK hν T
  refine key.trans (measureReal_mono (fun x hx ↦ ?_) (measure_ne_top _ _))
  simp only [Set.mem_setOf_eq] at hx ⊢
  have hsum : ∑ j ∈ range m, C j x * hf (pathAt x (τ + j)) (pathAt x (τ + j + 1)) =
      ∑ j ∈ range m, weight (visits x τ z) η n j * noise M x τ z Vc j :=
    sum_congr rfl fun j _ ↦ by
      by_cases hv : pathAt x (τ + j) = z
      · simp [hf, hv, noise, C, E, p, γ]
      · have : weight (visits x τ z) η n j = 0 := by
          unfold weight; rw [if_neg (fun h ↦ hv h.1)]
        simp [C, this]
  have hrad : Real.sqrt (8 * (γ ^ 2 * η * Var) * Real.log (2 / δ₁)) +
      4 / 3 * (η * (γ * H)) * Real.log (2 / δ₁) =
      γ * Real.sqrt (8 * η * Real.log (2 / δ₁) * Var) + γ * (8 * η * Real.log (2 / δ₁)) * H / 6 := by
    rw [show 8 * (γ ^ 2 * η * Var) * Real.log (2 / δ₁) =
        γ ^ 2 * (8 * η * Real.log (2 / δ₁) * Var) by ring, Real.sqrt_mul (sq_nonneg γ),
      Real.sqrt_sq hγ]
    ring
  rw [hsum, hrad] at hx
  exact hx

end StatisticalRL.AsyncQ
