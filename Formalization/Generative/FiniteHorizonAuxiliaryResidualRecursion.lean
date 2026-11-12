import Formalization.Generative.FiniteHorizonAuxiliaryGrowth
import Formalization.Generative.PolicyEvaluationRecursiveUnroll

/-! Deterministic auxiliary error propagation for Li et al., Appendix C.1.
The rowwise Bernstein-shaped condition is explicit. No probability event is assumed
proved, and no data-dependent-policy independence is used. -/
open scoped BigOperators
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The literal source residual condition at every remaining stage for one level.
It is an explicit deterministic premise; subsequent concentration must discharge it. -/
noncomputable def auxiliaryResidualCondition :
    List (EnvironmentStage State Action × EnvironmentStage State Action) →
    (ℕ → State → Action) → ℕ → ℝ → ℝ → Prop
  | [], _, _, _, _ => True
  | (E,F) :: tail, f, l, a, b =>
      (∀ s, |policyRowResidual E F (trueAuxiliaryValue (tail.map Prod.fst) (fun k ↦ f (k + 1)) l)
          s (f 0 s)| ≤
        a * auxiliaryPolicyReward (E :: tail.map Prod.fst) f (l + 1) s +
        b * ‖trueAuxiliaryValue (tail.map Prod.fst) (fun k ↦ f (k + 1)) l‖) ∧
      auxiliaryResidualCondition tail (fun k ↦ f (k + 1)) l a b

/-- Shared forcing cancels exactly; comparison transitions propagate the error. -/
theorem auxiliary_difference_cons (E F : EnvironmentStage State Action)
    (tail : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) (s : State) :
    comparisonAuxiliaryValue ((E,F) :: tail) f l s -
      trueAuxiliaryValue (E :: tail.map Prod.fst) f l s =
    policyRowResidual E F (trueAuxiliaryValue (tail.map Prod.fst) (fun k ↦ f (k + 1)) l) s (f 0 s) +
      (F.transition s (f 0 s)).expectation (fun t ↦
        comparisonAuxiliaryValue tail (fun k ↦ f (k + 1)) l t -
          trueAuxiliaryValue (tail.map Prod.fst) (fun k ↦ f (k + 1)) l t) := by
  rw [comparisonAuxiliaryValue_bellman, trueAuxiliaryValue_bellman]
  simp only [policyRowResidual, FiniteDistribution.expectation_sub]
  ring

/-- A uniform envelope derived from Lemma 12, not an extra source assumption. -/
theorem norm_trueAuxiliaryValue_le_source_growth (H l : ℕ)
    (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action)
    (hlen : es.length ≤ H) :
    ‖trueAuxiliaryValue es f l‖ ≤ (H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (Real.sqrt_nonneg _) _))).2
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (trueAuxiliaryValue_nonneg _ _ _ _)]
  exact trueAuxiliaryValue_le_source_growth H l es f hlen s

/-- Source (113): Bernstein-shaped row residuals bound the level-l error by
its actual comparison level-(l+1) value and the explicit accumulated linear term. -/
theorem auxiliary_error_le_comparison_successor
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H l : ℕ) (a b : ℝ)
    (hb : 0 ≤ b) (hlen : pairs.length ≤ H)
    (hres : auxiliaryResidualCondition pairs f l a b) (s : State) :
    |comparisonAuxiliaryValue pairs f l s - trueAuxiliaryValue (pairs.map Prod.fst) f l s| ≤
      a * comparisonAuxiliaryValue pairs f (l + 1) s +
      b * pairs.length * ((H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l) := by
  induction pairs generalizing f s with
  | nil => simp [comparisonAuxiliaryValue, trueAuxiliaryValue]
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    have ht : tail.length ≤ H := by simp only [List.length_cons] at hlen; omega
    have hhead := hres.1 s
    have htail := hres.2
    let d := F.transition s (f 0 s)
    let delta : State → ℝ := fun t ↦ comparisonAuxiliaryValue tail (fun k ↦ f (k + 1)) l t -
      trueAuxiliaryValue (tail.map Prod.fst) (fun k ↦ f (k + 1)) l t
    have hnorm := norm_trueAuxiliaryValue_le_source_growth H l (tail.map Prod.fst)
      (fun k ↦ f (k + 1)) (by simpa only [List.length_map] using ht)
    have hrow : |policyRowResidual E F
        (trueAuxiliaryValue (tail.map Prod.fst) (fun k ↦ f (k + 1)) l) s (f 0 s)| ≤
        a * auxiliaryPolicyReward (E :: tail.map Prod.fst) f (l + 1) s +
        b * ((H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l) := by
      exact hhead.trans (add_le_add_right (mul_le_mul_of_nonneg_left hnorm hb) _)
    have hI := d.expectation_mono (fun t ↦ ih (fun k ↦ f (k + 1)) ht htail t)
    have habs : |d.expectation delta| ≤ d.expectation (fun t ↦ |delta t|) := by
      unfold FiniteDistribution.expectation
      calc
        |∑ t, d.prob t * delta t| ≤ ∑ t, |d.prob t * delta t| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg (d.prob_nonneg _)]
    rw [List.map_cons, auxiliary_difference_cons]
    have htri := abs_add_le
      (policyRowResidual E F (trueAuxiliaryValue (tail.map Prod.fst) (fun k ↦ f (k + 1)) l) s (f 0 s))
      (d.expectation delta)
    change d.expectation (fun t ↦ |delta t|) ≤ d.expectation (fun t ↦
      a * comparisonAuxiliaryValue tail (fun k ↦ f (k + 1)) (l + 1) t +
      b * tail.length * ((H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l)) at hI
    rw [d.expectation_add, d.expectation_mul, d.expectation_const] at hI
    rw [comparisonAuxiliaryValue_bellman]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    change |policyRowResidual E F _ s (f 0 s) + d.expectation delta| ≤ _
    nlinarith

/-- The actual supremum-norm evaluation error at an auxiliary level. -/
noncomputable def auxiliaryErrorNorm
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) : ℝ :=
  ‖comparisonAuxiliaryValue pairs f l - trueAuxiliaryValue (pairs.map Prod.fst) f l‖

/-- The concrete level recursion underlying (115)--(117). All value-growth terms
are proved from the actual true model; the only conditional premise is the
explicit rowwise residual condition at this level. -/
theorem auxiliaryErrorNorm_level_recursion
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H l : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlen : pairs.length ≤ H)
    (hres : auxiliaryResidualCondition pairs f l a b) :
    auxiliaryErrorNorm pairs f l ≤ a * auxiliaryErrorNorm pairs f (l + 1) +
      a * ((H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ (l + 1)) +
      b * H * ((H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l) := by
  have hM : 0 ≤ (H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l := by positivity
  have hMnext : 0 ≤ (H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ (l + 1) := by positivity
  have hD : 0 ≤ auxiliaryErrorNorm pairs f (l + 1) := norm_nonneg _
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro s
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hfirst := auxiliary_error_le_comparison_successor pairs f H l a b hb hlen hres s
  have htrue := trueAuxiliaryValue_le_source_growth H (l + 1) (pairs.map Prod.fst) f
    (by simpa only [List.length_map] using hlen) s
  have he : |comparisonAuxiliaryValue pairs f (l + 1) s -
      trueAuxiliaryValue (pairs.map Prod.fst) f (l + 1) s| ≤ auxiliaryErrorNorm pairs f (l + 1) := by
    exact norm_le_pi_norm (comparisonAuxiliaryValue pairs f (l + 1) -
      trueAuxiliaryValue (pairs.map Prod.fst) f (l + 1)) s
  have hc : comparisonAuxiliaryValue pairs f (l + 1) s ≤ auxiliaryErrorNorm pairs f (l + 1) +
      (H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ (l + 1) := by
    have hh := le_abs_self (comparisonAuxiliaryValue pairs f (l + 1) s -
      trueAuxiliaryValue (pairs.map Prod.fst) f (l + 1) s)
    linarith
  have hca := mul_le_mul_of_nonneg_left hc ha
  have hlenR : (pairs.length : ℝ) ≤ H := Nat.cast_le.mpr hlen
  have hlinear := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlenR hb) hM
  nlinarith

/-- Finite recursive unrolling on the actual error sequence. The terminal error
is retained explicitly; no terminal estimate or logarithmic depth is assumed. -/
theorem auxiliaryErrorNorm_unroll
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H m : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlen : pairs.length ≤ H)
    (hres : ∀ l < m, auxiliaryResidualCondition pairs f l a b) :
    auxiliaryErrorNorm pairs f 0 ≤ a ^ m * auxiliaryErrorNorm pairs f m +
      (a * H * Real.sqrt (3 * (H : ℝ)) + b * (H : ℝ) ^ 2) *
        ∑ l ∈ Finset.range m, (a * Real.sqrt (3 * (H : ℝ))) ^ l := by
  let c : ℝ := Real.sqrt (3 * (H : ℝ))
  let C : ℝ := a * H * c + b * (H : ℝ) ^ 2
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hh := ModelBasedPolicyEvaluation.auxiliary_error_recursion_unroll
    (auxiliaryErrorNorm pairs f) (fun l ↦ c ^ l) a C c m ha hC
    (by
      intro l hl
      have h := auxiliaryErrorNorm_level_recursion pairs f H l a b ha hb hlen (hres l hl)
      calc
        auxiliaryErrorNorm pairs f l ≤ a * auxiliaryErrorNorm pairs f (l + 1) +
          a * ((H : ℝ) * c ^ (l + 1)) + b * H * ((H : ℝ) * c ^ l) := h
        _ = a * auxiliaryErrorNorm pairs f (l + 1) + C * c ^ l := by dsimp [C]; ring)
    (by intro l hl; simp)
  simpa only [pow_zero, mul_one] using hh

end StatisticalRL.FiniteHorizonGenerative
