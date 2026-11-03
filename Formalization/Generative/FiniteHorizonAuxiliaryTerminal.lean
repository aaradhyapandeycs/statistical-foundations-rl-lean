import Formalization.Generative.FiniteHorizonAuxiliaryResidualRecursion
import Formalization.Generative.PolicyLearningVarianceTransfer
import Mathlib.Data.Nat.Log

/-! Deterministic terminal estimate and natural-depth arithmetic for Li et al.
Lemma 9. No concentration event or sharp sample theorem is asserted here. -/
open scoped BigOperators
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- True standard-deviation forcing is bounded by the proved preceding-level
value envelope, without imposing normalized rewards on auxiliary levels. -/
theorem auxiliaryPolicyReward_succ_le_growth (H l : ℕ)
    (E : EnvironmentStage State Action) (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (hlen : es.length ≤ H) (s : State) :
    auxiliaryPolicyReward (E :: es) f (l + 1) s ≤
      (H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l := by
  exact ((E.transition s (f 0 s)).sqrt_variance_le_norm _).trans
    (norm_trueAuxiliaryValue_le_source_growth H l es (fun k ↦ f (k + 1)) hlen)

/-- Even under comparison transitions, the same true-derived forcing has the
proved envelope at every stage. -/
theorem comparisonAuxiliaryValue_succ_le_growth
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H l : ℕ) (hlen : pairs.length ≤ H) (s : State) :
    comparisonAuxiliaryValue pairs f (l + 1) s ≤
      pairs.length * ((H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l) := by
  induction pairs generalizing f s with
  | nil => simp [comparisonAuxiliaryValue]
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    have ht : tail.length ≤ H := by simp only [List.length_cons] at hlen; omega
    have hr := auxiliaryPolicyReward_succ_le_growth H l E (tail.map Prod.fst) f
      (by simpa only [List.length_map] using ht) s
    have hi := (F.transition s (f 0 s)).expectation_le_const
      (fun t ↦ ih (fun k ↦ f (k + 1)) ht t)
    rw [comparisonAuxiliaryValue_bellman]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The terminal auxiliary error estimate is derived from its own residual
condition, not introduced as an extra premise of the final unrolling. -/
theorem auxiliaryErrorNorm_terminal_le
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H l : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlen : pairs.length ≤ H)
    (hres : auxiliaryResidualCondition pairs f l a b) :
    auxiliaryErrorNorm pairs f l ≤
      (H : ℝ) * (a + b) * ((H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l) := by
  have hM : 0 ≤ (H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l := by positivity
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro s
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hh := auxiliary_error_le_comparison_successor pairs f H l a b hb hlen hres s
  have hc := comparisonAuxiliaryValue_succ_le_growth pairs f H l hlen s
  have hca := mul_le_mul_of_nonneg_left hc ha
  have hlenR : (pairs.length : ℝ) ≤ H := Nat.cast_le.mpr hlen
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hlenR (add_nonneg ha hb)) hM
  nlinarith

/-- Natural floor depth never asks for a level beyond the source's real log₂H.
This exact power characterization is the part needed for contraction. -/
theorem auxiliary_floor_depth_power (H : ℕ) : H < 2 ^ (Nat.log 2 H + 1) := by
  exact Nat.lt_pow_succ_log_self (by decide) H

/-- A floor-depth contraction estimate retaining the factor two lost by rounding. -/
theorem auxiliary_floor_depth_contraction (H : ℕ) (q : ℝ)
    (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2) :
    (H : ℝ) * q ^ Nat.log 2 H ≤ 2 := by
  have hp : (H : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 H + 1) := by
    exact_mod_cast (Nat.le_of_lt (auxiliary_floor_depth_power H))
  have hqp : q ^ Nat.log 2 H ≤ (1 / 2 : ℝ) ^ Nat.log 2 H :=
    pow_le_pow_left₀ hq hhalf _
  have hh := mul_le_mul_of_nonneg_right hp (pow_nonneg hq (Nat.log 2 H))
  have hj := mul_le_mul_of_nonneg_left hqp (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.log 2 H + 1))
  have he : (2 : ℝ) ^ (Nat.log 2 H + 1) * (1 / 2 : ℝ) ^ Nat.log 2 H = 2 := by
    rw [pow_succ]
    calc
      (2 : ℝ) ^ Nat.log 2 H * 2 * (1 / 2 : ℝ) ^ Nat.log 2 H =
          2 * ((2 : ℝ) ^ Nat.log 2 H * (1 / 2 : ℝ) ^ Nat.log 2 H) := by ring
      _ = 2 := by rw [← mul_pow]; norm_num
  nlinarith

/-- The source constant six survives floor-log rounding: its spare numerical
slack absorbs the factor two in the terminal contraction. -/
theorem auxiliary_six_constant (H a : ℝ) (hH : 1 ≤ H) (ha : 0 ≤ a)
    (hhalf : a * Real.sqrt (3 * H) ≤ 1 / 2) :
    2 * H * (a + a ^ 2) + 2 * (a * H * Real.sqrt (3 * H) + a ^ 2 * H ^ 2) ≤
      6 * H * (a * Real.sqrt (3 * H)) := by
  let c := Real.sqrt (3 * H)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = 3 * H := Real.sq_sqrt (by linarith)
  have hcmin : 3 / 2 ≤ c := by nlinarith
  have hap : a * c ≤ 1 / 2 := hhalf
  have hamax : a ≤ 1 / 3 := by nlinarith [mul_nonneg ha (sub_nonneg.mpr hcmin)]
  have hsmall : a + a ^ 2 ≤ a * c := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hcmin)]
  have hq : 0 ≤ a * c := mul_nonneg ha hc
  have heq : (a * c) ^ 2 = 3 * a ^ 2 * H := by rw [mul_pow, hc2]; ring
  have hlinear : a ^ 2 * H ≤ a * c := by nlinarith
  have hs := mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ H)
  have hl := mul_le_mul_of_nonneg_left hlinear (by linarith : 0 ≤ H)
  change 2 * H * (a + a ^ 2) + 2 * (a * H * c + a ^ 2 * H ^ 2) ≤ 6 * H * (a * c)
  nlinarith

/-- Deterministic conclusion of Lemma 9 with an explicit natural floor depth.
All source residual conditions, including the terminal level, remain explicit. -/
theorem auxiliaryErrorNorm_le_six
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H : ℕ) (a : ℝ)
    (hH : 0 < H) (ha : 0 ≤ a) (hlen : pairs.length ≤ H)
    (hhalf : a * Real.sqrt (3 * (H : ℝ)) ≤ 1 / 2)
    (hres : ∀ l ≤ Nat.log 2 H, auxiliaryResidualCondition pairs f l a (a ^ 2)) :
    auxiliaryErrorNorm pairs f 0 ≤ 6 * H * (a * Real.sqrt (3 * (H : ℝ))) := by
  let m := Nat.log 2 H
  let c : ℝ := Real.sqrt (3 * (H : ℝ))
  let q := a * c
  let C : ℝ := a * H * c + a ^ 2 * (H : ℝ) ^ 2
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hq : 0 ≤ q := mul_nonneg ha hc
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hU := auxiliaryErrorNorm_unroll pairs f H m a (a ^ 2) ha (sq_nonneg _) hlen
    (fun l hl ↦ hres l (Nat.le_of_lt hl))
  have hT := auxiliaryErrorNorm_terminal_le pairs f H m a (a ^ 2) ha (sq_nonneg _) hlen (hres m le_rfl)
  have hTP := mul_le_mul_of_nonneg_left hT (pow_nonneg ha m)
  have he : a ^ m * ((H : ℝ) * (a + a ^ 2) * ((H : ℝ) * c ^ m)) =
      (H : ℝ) * (a + a ^ 2) * ((H : ℝ) * q ^ m) := by dsimp [q]; rw [mul_pow]; ring
  change a ^ m * auxiliaryErrorNorm pairs f m ≤ a ^ m *
    ((H : ℝ) * (a + a ^ 2) * ((H : ℝ) * c ^ m)) at hTP
  rw [he] at hTP
  have hcontract := auxiliary_floor_depth_contraction H q hq hhalf
  have hterminal := mul_le_mul_of_nonneg_left hcontract
    (mul_nonneg (Nat.cast_nonneg H) (add_nonneg ha (sq_nonneg a)))
  have hgeom := ModelBasedPolicyEvaluation.auxiliary_geometric_sum_le_two q m hq hhalf
  have hseries := mul_le_mul_of_nonneg_left hgeom hC
  have hraw : auxiliaryErrorNorm pairs f 0 ≤ 2 * H * (a + a ^ 2) + 2 * C := by
    change auxiliaryErrorNorm pairs f 0 ≤ a ^ m * auxiliaryErrorNorm pairs f m +
      C * (∑ l ∈ Finset.range m, q ^ l) at hU
    change (H : ℝ) * (a + a ^ 2) * ((H : ℝ) * q ^ m) ≤ (H : ℝ) * (a + a ^ 2) * 2 at hterminal
    nlinarith
  exact hraw.trans (auxiliary_six_constant H a (by exact_mod_cast hH) ha hhalf)

end StatisticalRL.FiniteHorizonGenerative
