import Formalization.Online.Bandit.UCBDefinitions
import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Exponential supermartingale bound for predictable Gaussian sums

Generic infrastructure for Theorem 5.1 (`thm:bandit-pure-ucb`): on the round-indexed table of
independent standard Gaussian noise vectors, the exponential of a predictably weighted sum of one
coordinate per round, compensated by half the sum of squared weights, has expectation at most one.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

noncomputable section

namespace StatisticalRL.Bandit

/-- Sequential product bound on a finite product space: if each factor depends only on the
coordinates up to its own index and integrates to at most one in its own coordinate, then the
product integrates to at most one. -/
theorem lintegral_prod_predictable_le_one {T : ℕ} {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (g : Fin T → (Fin T → X) → ℝ≥0∞) (hmeas : ∀ t, Measurable (g t))
    (hdep : ∀ t (x y : Fin T → X), (∀ s, s ≤ t → x s = y s) → g t x = g t y)
    (hstep : ∀ t (x : Fin T → X), ∫⁻ y, g t (Function.update x t y) ∂ν ≤ 1) :
    ∫⁻ z, ∏ t, g t z ∂(Measure.pi fun _ : Fin T => ν) ≤ 1 := by
  classical
  set F : (Fin T → X) → ℝ≥0∞ := fun z => ∏ t, g t z with hF
  have hFm : Measurable F := Finset.measurable_prod _ (fun t _ => hmeas t)
  -- coordinates with index at least `k`
  let S : ℕ → Finset (Fin T) := fun k => univ.filter (fun t => k ≤ t.val)
  let P : ℕ → (Fin T → X) → ℝ≥0∞ := fun k x => ∏ t ∈ univ.filter (fun t => t.val < k), g t x
  have key : ∀ j, j ≤ T → ∀ x, (∫⋯∫⁻_(S (T - j)), F ∂(fun _ => ν)) x ≤ P (T - j) x := by
    intro j
    induction j with
    | zero =>
      intro _ x
      have hS : S (T - 0) = ∅ := by
        ext t; simp [S]
      have hP : P (T - 0) x = F x := by
        simp only [P, F, Nat.sub_zero]
        congr 1
        ext t; simp
      rw [hS, lmarginal_empty, hP]
    | succ j ih =>
      intro hj x
      have hk : T - (j + 1) < T := by omega
      set k := T - (j + 1) with hkdef
      have hk1 : T - j = k + 1 := by omega
      let i : Fin T := ⟨k, hk⟩
      have hSi : S k = insert i (S (k + 1)) := by
        ext t
        simp only [S, mem_filter, mem_univ, true_and, mem_insert, i]
        constructor
        · intro h
          rcases Nat.eq_or_lt_of_le h with h' | h'
          · left; exact Fin.ext h'.symm
          · right; omega
        · rintro (h | h)
          · rw [h]
          · omega
      have hnot : i ∉ S (k + 1) := by simp [S, i]
      rw [hSi, lmarginal_insert _ hFm hnot]
      have ih' := ih (by omega)
      rw [hk1] at ih'
      calc ∫⁻ xi, (∫⋯∫⁻_(S (k + 1)), F ∂(fun _ => ν)) (Function.update x i xi) ∂ν
          ≤ ∫⁻ xi, P (k + 1) (Function.update x i xi) ∂ν := lintegral_mono (fun xi => ih' _)
        _ = ∫⁻ xi, P k x * g i (Function.update x i xi) ∂ν := by
            congr 1
            ext xi
            have hfil : univ.filter (fun t : Fin T => t.val < k + 1)
                = insert i (univ.filter (fun t : Fin T => t.val < k)) := by
              ext t
              simp only [mem_filter, mem_univ, true_and, mem_insert, i]
              constructor
              · intro h
                rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
                · right; exact h'
                · left; exact Fin.ext h'
              · rintro (h | h)
                · rw [h]; exact Nat.lt_succ_self k
                · omega
            have hni : i ∉ univ.filter (fun t : Fin T => t.val < k) := by simp [i]
            simp only [P]
            rw [hfil, prod_insert hni, mul_comm]
            congr 1
            apply prod_congr rfl
            intro t ht
            simp only [mem_filter, mem_univ, true_and] at ht
            apply hdep
            intro s hs
            have hsi : s ≠ i := by
              intro h; rw [h] at hs; exact absurd (Fin.le_def.mp hs) (by simp [i]; omega)
            simp [Function.update_of_ne hsi]
        _ = P k x * ∫⁻ xi, g i (Function.update x i xi) ∂ν := by
            rw [lintegral_const_mul]
            exact (hmeas i).comp (measurable_update x)
        _ ≤ P k x * 1 := by gcongr; exact hstep i x
        _ = P k x := mul_one _
  rcases isEmpty_or_nonempty (Fin T → X) with hE | ⟨⟨x⟩⟩
  · simp [lintegral_of_isEmpty]
  have h0 := key T le_rfl x
  rw [Nat.sub_self] at h0
  have hS0 : S 0 = univ := by ext t; simp [S]
  have hP0 : P 0 x = 1 := by simp [P]
  rw [hS0, hP0, lmarginal_univ] at h0
  exact h0

/-- One Gaussian step: the compensated exponential of a fixed multiple of one coordinate of a
standard Gaussian vector integrates to one. -/
theorem lintegral_exp_gaussian_coord {A : ℕ} (b : Fin A) (u : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (u * y b - u ^ 2 / 2))
      ∂(Measure.pi fun _ : Fin A => gaussianReal 0 1) = 1 := by
  have hmp := measurePreserving_eval (μ := fun _ : Fin A => gaussianReal 0 1) b
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (u * x - u ^ 2 / 2)) := by
    fun_prop
  rw [hmp.lintegral_comp hm]
  have hint : Integrable (fun x : ℝ => Real.exp (u * x - u ^ 2 / 2)) (gaussianReal 0 1) := by
    have := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) u).mul_const
      (Real.exp (-(u ^ 2 / 2)))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.exp_add]; ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  have hmgf := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) u
  simp only [mgf, id] at hmgf
  have : ∫ x, Real.exp (u * x - u ^ 2 / 2) ∂gaussianReal 0 1
      = (∫ x, Real.exp (u * x) ∂gaussianReal 0 1) * Real.exp (-(u ^ 2 / 2)) := by
    rw [← integral_mul_const]
    congr 1; ext x; rw [← Real.exp_add]; ring_nf
  rw [this, hmgf, ← Real.exp_add]
  simp

/-- Exponential supermartingale bound for a predictably weighted Gaussian sum along one arm. -/
theorem lintegral_exp_predictable_gaussian_le_one {T A : ℕ} (b : Fin A) (lam : ℝ)
    (c : Fin T → (Fin T → Fin A → ℝ) → ℝ) (hc : ∀ t, Measurable (c t))
    (hpast : ∀ t (x y : Fin T → Fin A → ℝ), (∀ s, s < t → x s = y s) → c t x = c t y) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (lam * ∑ t, c t z * z t b - lam ^ 2 / 2 * ∑ t, c t z ^ 2))
      ∂gaussianNoiseTable T A ≤ 1 := by
  classical
  let g : Fin T → (Fin T → Fin A → ℝ) → ℝ≥0∞ := fun t z =>
    ENNReal.ofReal (Real.exp (lam * (c t z * z t b) - lam ^ 2 / 2 * c t z ^ 2))
  have hprod : ∀ z, ENNReal.ofReal (Real.exp (lam * ∑ t, c t z * z t b
      - lam ^ 2 / 2 * ∑ t, c t z ^ 2)) = ∏ t, g t z := by
    intro z
    rw [← ENNReal.ofReal_prod_of_nonneg (fun t _ => (Real.exp_pos _).le), ← Real.exp_sum]
    congr 2
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
  simp_rw [hprod]
  apply lintegral_prod_predictable_le_one
  · intro t
    have h1 : Measurable fun z : Fin T → Fin A → ℝ => z t b :=
      (measurable_pi_apply b).comp (measurable_pi_apply t)
    have h2 := hc t
    fun_prop
  · intro t x y hxy
    simp only [g]
    rw [hpast t x y (fun s hs => hxy s hs.le), hxy t le_rfl]
  · intro t x
    simp only [g]
    have hc' : ∀ y, c t (Function.update x t y) = c t x := fun y =>
      hpast t _ _ (fun s hs => Function.update_of_ne hs.ne _ _)
    simp_rw [hc', Function.update_self]
    have := lintegral_exp_gaussian_coord b (lam * c t x)
    refine le_of_eq ?_
    rw [← this]
    congr 1; ext y; congr 2; ring

end StatisticalRL.Bandit
