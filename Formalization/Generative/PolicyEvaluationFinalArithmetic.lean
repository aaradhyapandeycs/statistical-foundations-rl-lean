import Formalization.Generative.PolicyEvaluationRecursiveUnroll
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Deterministic arithmetic for the source's final evaluation bound.
This file is conditional on previously established recursion, growth, and
terminal inequalities; it makes no probability or sample-theorem claim. -/

namespace StatisticalRL.ModelBasedPolicyEvaluation

/-- Finite unrolling with an explicit terminal estimate and a geometric tail. -/
theorem auxiliary_unroll_with_terminal (E V : ℕ → ℝ) (b₁ b₂ b₃ c B h : ℝ)
    (m : ℕ) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hc : 0 ≤ c) (hV0 : 0 ≤ V 0) (hVB : V 0 ≤ B)
    (hqhalf : b₁ * b₃ ≤ 1 / 2) (hqtail : (b₁ * b₃) ^ m ≤ h)
    (hstep : ∀ l < m, E l ≤ b₁ * E (l + 1) + b₂ * V l)
    (hvalue : ∀ l ≤ m, V l ≤ b₃ ^ l * V 0)
    (hterminal : E m ≤ c * V m) :
    E 0 ≤ (h * c + 2 * b₂) * B := by
  have hq : 0 ≤ b₁ * b₃ := mul_nonneg hb₁ hb₃
  have hu := auxiliary_error_recursion_unroll_half E V b₁ b₂ b₃ m hb₁ hb₂ hV0
    hq hqhalf hstep (fun l hl ↦ hvalue l (Nat.le_of_lt hl))
  have hb1pow : 0 ≤ b₁ ^ m := pow_nonneg hb₁ _
  have hb3pow : 0 ≤ b₃ ^ m := pow_nonneg hb₃ _
  have ht : E m ≤ c * (b₃ ^ m * V 0) :=
    hterminal.trans (mul_le_mul_of_nonneg_left (hvalue m le_rfl) hc)
  have hpow := mul_le_mul_of_nonneg_left ht hb1pow
  have hqB := mul_le_mul_of_nonneg_right hqtail (mul_nonneg hc hV0)
  have hr : b₁ ^ m * E m ≤ h * c * V 0 := by
    rw [mul_pow] at hqB
    nlinarith
  have hcoeff : 0 ≤ h * c + 2 * b₂ := by
    have : 0 ≤ h := (pow_nonneg hq m).trans hqtail
    positivity
  calc
    E 0 ≤ b₁ ^ m * E m + 2 * b₂ * V 0 := hu
    _ ≤ (h * c + 2 * b₂) * V 0 := by nlinarith
    _ ≤ (h * c + 2 * b₂) * B := mul_le_mul_of_nonneg_left hVB hcoeff

/-- The source's logarithmic depth makes any ratio at most e⁻¹ have tail ≤ h. -/
theorem auxiliary_geometric_tail_of_log_depth (q h : ℝ) (m : ℕ)
    (hq : 0 ≤ q) (hqexp : q ≤ Real.exp (-1)) (hh : 0 < h)
    (hm : -Real.log h ≤ (m : ℝ)) : q ^ m ≤ h := by
  calc
    q ^ m ≤ (Real.exp (-1)) ^ m := pow_le_pow_left₀ hq hqexp m
    _ = Real.exp (-(m : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (Real.log h) := Real.exp_le_exp.mpr (by linarith)
    _ = h := Real.exp_log hh

/-- The numerical constants in the source's final high-sample estimate.
Here `t=√h`, `k=√2`, and `a=√(β/N)`; the high-sample condition
`N≥64β/h` entails `a≤t/8`. -/
theorem auxiliary_source_coefficient_bound (h t k γ a : ℝ)
    (hh : 0 < h) (ht : 0 < t) (htsq : t ^ 2 = h) (ht1 : t ≤ 1)
    (hk : 1 ≤ k) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (ha : 0 ≤ a) (hasmall : a ≤ t / 8) :
    (h * (γ / h * (a + a ^ 2)) + 2 * (k * a / t + a ^ 2 / h)) * (1 / h) ≤
      6 * k * a / (h * t) := by
  have ha1 : a ≤ 1 := by linarith
  have hat : a ≤ k * t := by nlinarith
  have hx : a / t ≤ k := (div_le_iff₀ ht).2 hat
  have hx0 : 0 ≤ a / t := div_nonneg ha ht.le
  have hsq : a ^ 2 / h ≤ k * a / t := by
    calc
      _ = (a / t) ^ 2 := by rw [← htsq, div_pow]
      _ ≤ k * (a / t) := by nlinarith [mul_le_mul_of_nonneg_left hx hx0]
      _ = _ := by ring
  have hsum : a + a ^ 2 ≤ 2 * a := by nlinarith
  have hsum0 : 0 ≤ a + a ^ 2 := by positivity
  have hγsum : γ * (a + a ^ 2) ≤ 2 * a := by
    calc
      _ ≤ 1 * (a + a ^ 2) := mul_le_mul_of_nonneg_right hγ1 hsum0
      _ ≤ _ := by linarith
  have hatk : t ≤ k := le_trans ht1 hk
  have h2 : 2 * a ≤ 2 * k * a / t := by
    apply (le_div_iff₀ ht).2
    nlinarith [mul_le_mul_of_nonneg_left hatk ha]
  have hmain : γ * (a + a ^ 2) ≤ 2 * k * a / t := hγsum.trans h2
  have hminor : 2 * (k * a / t + a ^ 2 / h) ≤ 4 * k * a / t := by
    calc
      _ ≤ 2 * (k * a / t + k * a / t) := by gcongr
      _ = _ := by ring
  have hres := add_le_add hmain hminor
  have hres' := div_le_div_of_nonneg_right hres hh.le
  calc
    _ = (γ * (a + a ^ 2) + 2 * (k * a / t + a ^ 2 / h)) / h := by field_simp
    _ ≤ (2 * k * a / t + 4 * k * a / t) / h := hres'
    _ = _ := by ring

/-- Conditional source-coefficient estimate after finite unrolling. The terminal
inequality is the explicit intermediate bound from the source's Step 4, not a
high-probability hypothesis or the final evaluation guarantee. -/
theorem auxiliary_source_high_sample_arithmetic
    (E V : ℕ → ℝ) (γ h a : ℝ) (m : ℕ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (ha : 0 ≤ a) (hasmall : a ≤ Real.sqrt h / 8)
    (hm : -Real.log h ≤ (m : ℝ))
    (hV0 : 0 ≤ V 0) (hVB : V 0 ≤ 1 / h)
    (hstep : ∀ l < m, E l ≤ γ * a * E (l + 1) +
      (Real.sqrt 2 * a / Real.sqrt h + a ^ 2 / h) * V l)
    (hvalue : ∀ l ≤ m, V l ≤
      (Real.sqrt 2 / (γ * Real.sqrt h)) ^ l * V 0)
    (hterminal : E m ≤ γ / h * (a + a ^ 2) * V m) :
    E 0 ≤ 6 * Real.sqrt 2 * a / (h * Real.sqrt h) := by
  let t := Real.sqrt h
  let k := Real.sqrt 2
  let b₁ := γ * a
  let b₂ := k * a / t + a ^ 2 / h
  let b₃ := k / (γ * t)
  let c := γ / h * (a + a ^ 2)
  have ht : 0 < t := Real.sqrt_pos.2 hh
  have htsq : t ^ 2 = h := Real.sq_sqrt hh.le
  have ht1 : t ≤ 1 := Real.sqrt_le_one.mpr hh1
  have hk : 1 ≤ k := Real.one_le_sqrt.mpr (by norm_num)
  have hk2 : k ≤ 2 := by
    dsimp [k]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hb₁ : 0 ≤ b₁ := mul_nonneg hγ.le ha
  have hb₂ : 0 ≤ b₂ := by dsimp [b₂]; positivity
  have hb₃ : 0 ≤ b₃ := by dsimp [b₃]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hq : 0 ≤ b₁ * b₃ := mul_nonneg hb₁ hb₃
  have hqhalf : b₁ * b₃ ≤ 1 / 2 := by
    have heq : b₁ * b₃ = k * a / t := by dsimp [b₁, b₃]; field_simp
    rw [heq]
    apply (div_le_iff₀ ht).2
    have hhsmall : a ≤ t / 8 := hasmall
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hk2)]
  have hqquarter : b₁ * b₃ ≤ 1 / 4 := by
    have heq : b₁ * b₃ = k * a / t := by dsimp [b₁, b₃]; field_simp
    rw [heq]
    apply (div_le_iff₀ ht).2
    have hhsmall : a ≤ t / 8 := hasmall
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hk2)]
  have hqexp : b₁ * b₃ ≤ Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div]
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.le.trans (by norm_num))
    nlinarith [mul_nonneg hq (sub_nonneg.mpr he)]
  have hqtail : (b₁ * b₃) ^ m ≤ h :=
    auxiliary_geometric_tail_of_log_depth _ _ _ hq hqexp hh hm
  have hu := auxiliary_unroll_with_terminal E V b₁ b₂ b₃ c (1 / h) h m
    hb₁ hb₂ hb₃ hc hV0 hVB hqhalf hqtail hstep hvalue hterminal
  have hcoef := auxiliary_source_coefficient_bound h t k γ a hh ht htsq ht1 hk
    hγ.le hγ1 ha hasmall
  exact hu.trans hcoef

/-- The source's high-sample condition implies the square-root coefficient bound. -/
theorem auxiliary_sample_coefficient_bound (h β N : ℝ)
    (hh : 0 < h) (hN : 0 < N)
    (hNbound : 64 * β / h ≤ N) :
    Real.sqrt (β / N) ≤ Real.sqrt h / 8 := by
  have hprod : 64 * β ≤ N * h := (div_le_iff₀ hh).mp hNbound
  have hsq : β / N ≤ (Real.sqrt h / 8) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hh.le]
    apply (div_le_iff₀ hN).2
    nlinarith
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩

/-- The coefficient expression is exactly the source's displayed radius. -/
theorem auxiliary_source_radius_eq (h β N : ℝ)
    (hh : 0 < h) (hβ : 0 ≤ β) (hN : 0 < N) :
    6 * Real.sqrt 2 * Real.sqrt (β / N) / (h * Real.sqrt h) =
      3 * Real.sqrt (8 * β / (h ^ 3 * N)) := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hs2 := Real.sq_sqrt hh.le
  have ha : 0 ≤ β / N := div_nonneg hβ hN.le
  have hb : 0 ≤ 8 * β / (h ^ 3 * N) := by positivity
  have hsqa := Real.sq_sqrt ha
  have hsqb := Real.sq_sqrt hb
  have hs2' := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hleft : 0 ≤ 6 * Real.sqrt 2 * Real.sqrt (β / N) / (h * Real.sqrt h) := by positivity
  have hright : 0 ≤ 3 * Real.sqrt (8 * β / (h ^ 3 * N)) := by positivity
  apply (sq_eq_sq₀ hleft hright).mp
  simp only [div_pow, mul_pow, hs2', hsqa, hs2, hsqb]
  field_simp
  ring

/-- Conditional deterministic closure at the source's high-sample threshold
and exactly the displayed final radius. The recursion, value-growth and
terminal estimates remain explicit previously established inputs. -/
theorem auxiliary_source_high_sample_radius
    (E V : ℕ → ℝ) (γ h β N : ℝ) (m : ℕ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hβ : 0 ≤ β) (hN : 0 < N) (hNbound : 64 * β / h ≤ N)
    (hm : -Real.log h ≤ (m : ℝ))
    (hV0 : 0 ≤ V 0) (hVB : V 0 ≤ 1 / h)
    (hstep : ∀ l < m, E l ≤ γ * Real.sqrt (β / N) * E (l + 1) +
      (Real.sqrt 2 * Real.sqrt (β / N) / Real.sqrt h + (β / N) / h) * V l)
    (hvalue : ∀ l ≤ m, V l ≤
      (Real.sqrt 2 / (γ * Real.sqrt h)) ^ l * V 0)
    (hterminal : E m ≤ γ / h * (Real.sqrt (β / N) + β / N) * V m) :
    E 0 ≤ 3 * Real.sqrt (8 * β / (h ^ 3 * N)) := by
  let a := Real.sqrt (β / N)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hasmall : a ≤ Real.sqrt h / 8 := auxiliary_sample_coefficient_bound h β N hh hN hNbound
  have ha2 : a ^ 2 = β / N := Real.sq_sqrt (div_nonneg hβ hN.le)
  have hstep' : ∀ l < m, E l ≤ γ * a * E (l + 1) +
      (Real.sqrt 2 * a / Real.sqrt h + a ^ 2 / h) * V l := by
    simpa only [ha2] using hstep
  have hterminal' : E m ≤ γ / h * (a + a ^ 2) * V m := by
    simpa only [ha2] using hterminal
  have hresult := auxiliary_source_high_sample_arithmetic E V γ h a m hγ hγ1 hh hh1
    ha hasmall hm hV0 hVB hstep' hvalue hterminal'
  change E 0 ≤ 6 * Real.sqrt 2 * Real.sqrt (β / N) / (h * Real.sqrt h) at hresult
  rw [auxiliary_source_radius_eq h β N hh hβ hN] at hresult
  exact hresult

/-- The exact source-selected ceiling satisfies the depth required by the
conditional high-sample arithmetic. -/
theorem auxiliary_source_ceiling_depth (h : ℝ) (hh : 0 < h) :
    -Real.log h ≤ (⌈Real.log (Real.exp 1 / h)⌉₊ : ℝ) := by
  have hc := Nat.le_ceil (Real.log (Real.exp 1 / h))
  rw [Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hh), Real.log_exp] at hc ⊢
  linarith

end StatisticalRL.ModelBasedPolicyEvaluation
