import Formalization.Online.Bandit.GaussianPredictableExp
import Formalization.Online.Bandit.UCBMeasurability

/-!
# UCB: adaptive fixed-count Gaussian tail

Repair of Step 1 of the proof of Theorem 5.1 (`chapters/bandits.tex:400–429`): the source applies
the fixed-`n` Gaussian tail (`:188–199`) at the random count `N_t(a)` via the identity
`r̄_t(a) - r(a) ~ N(0, 1/N_t(a))` (`:180`), which fails under adaptive sampling. Instead, for each
fixed `k`, the sum of the first `k` noises of an arm obeys the Chernoff tail
`P(k ≤ N_T(b), σ·(first-k noise sum) ≥ k √(2θ/k)) ≤ exp(-θ)` by the exponential supermartingale
of `GaussianPredictableExp`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

noncomputable section

namespace StatisticalRL.Bandit

variable {A : ℕ} (tie : ℕ → Finset (Fin A) → Fin A) (L : ℝ) (r : Fin A → ℝ)

theorem extendNoise_congr {T : ℕ} (t : Fin T) (x y : Fin T → Fin A → ℝ)
    (h : ∀ s, s < t → x s = y s) : ∀ s, s < t.val → extendNoise x s = extendNoise y s := by
  intro s hs
  have hsT : s < T := lt_trans hs t.isLt
  simp only [extendNoise, hsT, dite_true]
  exact h ⟨s, hsT⟩ (Fin.lt_def.mpr hs)

/-- Adaptive fixed-count Chernoff tail for the first-`k` noise sum of arm `b`. -/
theorem ucb_first_noise_tail {T : ℕ} (b : Fin A) (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : σ ^ 2 = 1)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (gaussianNoiseTable T A).real {z | k ≤ ucbCount tie L r (extendNoise z) T b ∧
        (k : ℝ) * Real.sqrt (2 * θ / k) ≤ σ * ucbNoiseSum tie L r (extendNoise z) T k b}
      ≤ Real.exp (-θ) := by
  classical
  set μ := gaussianNoiseTable T A
  have hζ : ∀ t, Measurable fun z : Fin T → Fin A → ℝ => extendNoise z t :=
    fun t => measurable_extendNoise t
  let ind : Fin T → (Fin T → Fin A → ℝ) → ℝ := fun t z =>
    if ucbArm tie L r (extendNoise z) t.val = b ∧
      ucbCount tie L r (extendNoise z) t.val b < k then 1 else 0
  let c : Fin T → (Fin T → Fin A → ℝ) → ℝ := fun t z => σ * ind t z
  have hind : ∀ t, Measurable (ind t) := by
    intro t
    apply Measurable.ite _ measurable_const measurable_const
    have h1 : MeasurableSet {z : Fin T → Fin A → ℝ | ucbArm tie L r (extendNoise z) t.val = b} :=
      measurable_ucbArm tie L r (fun z => extendNoise z) hζ t.val (measurableSet_singleton b)
    have h2 : MeasurableSet {z : Fin T → Fin A → ℝ |
        ucbCount tie L r (extendNoise z) t.val b < k} :=
      measurable_ucbCount tie L r (fun z => extendNoise z) hζ t.val b
        (MeasurableSet.of_discrete (s := {n : ℕ | n < k}))
    exact h1.inter h2
  have hc : ∀ t, Measurable (c t) := fun t => (hind t).const_mul σ
  have hpast : ∀ t (x y : Fin T → Fin A → ℝ), (∀ s, s < t → x s = y s) → c t x = c t y := by
    intro t x y h
    have h' := extendNoise_congr t x y h
    simp only [c, ind]
    rw [ucbArm_congr tie L r (extendNoise x) t.val h',
      show ucbCount tie L r (extendNoise x) t.val b = ucbCount tie L r (extendNoise y) t.val b by
        simp only [ucbCount]; rw [ucbState_congr tie L r (extendNoise x) t.val h']]
  set lam := Real.sqrt (2 * θ / k) with hlam
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hlam2 : lam ^ 2 = 2 * θ / k := Real.sq_sqrt (by positivity)
  have hlam0 : 0 ≤ lam := Real.sqrt_nonneg _
  have hsum1 : ∀ z : Fin T → Fin A → ℝ, ∑ t, c t z * z t b
      = σ * ucbNoiseSum tie L r (extendNoise z) T k b := by
    intro z
    unfold ucbNoiseSum
    rw [mul_sum]
    rw [← Fin.sum_univ_eq_sum_range (fun s => σ * (if ucbArm tie L r (extendNoise z) s = b ∧
      ucbCount tie L r (extendNoise z) s b < k then extendNoise z s b else 0)) T]
    apply sum_congr rfl
    intro t _
    have hz : z t b = extendNoise z t.val b := by simp [extendNoise, t.isLt]
    simp only [c, ind]
    split_ifs <;> simp [hz]
  have hsum2 : ∀ z : Fin T → Fin A → ℝ, ∑ t, c t z ^ 2
      = (min k (ucbCount tie L r (extendNoise z) T b) : ℕ) := by
    intro z
    rw [← sum_pull_below_real]
    rw [← Fin.sum_univ_eq_sum_range (fun s => if ucbArm tie L r (extendNoise z) s = b ∧
      ucbCount tie L r (extendNoise z) s b < k then (1 : ℝ) else 0) T]
    apply sum_congr rfl
    intro t _
    simp only [c, ind]
    split_ifs <;> simp [hσ]
  let f : (Fin T → Fin A → ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (lam * ∑ t, c t z * z t b - lam ^ 2 / 2 * ∑ t, c t z ^ 2))
  have hf : Measurable f := by
    have hS1 : Measurable fun z : Fin T → Fin A → ℝ => ∑ t, c t z * z t b :=
      Finset.measurable_sum _ (fun t _ =>
        (hc t).mul ((measurable_pi_apply b).comp (measurable_pi_apply t)))
    have hS2 : Measurable fun z : Fin T → Fin A → ℝ => ∑ t, c t z ^ 2 :=
      Finset.measurable_sum _ (fun t _ => (hc t).pow_const 2)
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hS1.const_mul lam).sub (hS2.const_mul _)))
  have hint : ∫⁻ z, f z ∂μ ≤ 1 :=
    lintegral_exp_predictable_gaussian_le_one b lam c hc hpast
  set E := {z : Fin T → Fin A → ℝ | k ≤ ucbCount tie L r (extendNoise z) T b ∧
        (k : ℝ) * Real.sqrt (2 * θ / k) ≤ σ * ucbNoiseSum tie L r (extendNoise z) T k b}
  have hsub : E ⊆ {z | ENNReal.ofReal (Real.exp θ) ≤ f z} := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Set.mem_setOf_eq, f]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [hsum1, hsum2, min_eq_left hz1]
    have h3 : lam * ((k : ℝ) * lam) ≤ lam * (σ * ucbNoiseSum tie L r (extendNoise z) T k b) :=
      mul_le_mul_of_nonneg_left hz2 hlam0
    have h4 : lam * ((k : ℝ) * lam) = 2 * θ := by
      rw [show lam * ((k : ℝ) * lam) = k * lam ^ 2 by ring, hlam2]
      field_simp
    have h5 : lam ^ 2 / 2 * (k : ℝ) = θ := by
      rw [hlam2]; field_simp
    linarith
  have hmark := mul_meas_ge_le_lintegral₀ hf.aemeasurable (μ := μ) (ENNReal.ofReal (Real.exp θ))
  have hE : ENNReal.ofReal (Real.exp θ) * μ E ≤ 1 :=
    le_trans (by gcongr) (hmark.trans hint)
  have hμE : μ E ≤ ENNReal.ofReal (Real.exp (-θ)) := by
    have hone : ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp θ) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
    calc μ E = ENNReal.ofReal (Real.exp (-θ)) * (ENNReal.ofReal (Real.exp θ) * μ E) := by
          rw [← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (-θ)) * 1 := by gcongr
      _ = ENNReal.ofReal (Real.exp (-θ)) := mul_one _
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hμE

end StatisticalRL.Bandit
