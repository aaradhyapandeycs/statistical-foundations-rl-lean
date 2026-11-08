import Formalization.Online.LowerBound.GaussianBanditKL
import Formalization.Probability.Fano.ReverseTest

/-!
# Minimax lower bound for Gaussian bandits (Remark 5.12)

For `2 ≤ A ≤ T` and the hard family `hardMean ε` with `ε = ½√(A/T)`, every learner has expected
pseudo-regret at least `(1/16)√(AT)` on some member. Proof: per-round reverse Fano against the
reference instance `0`, with the adapted Gaussian tilt of `KL.lean` (KL budget `ε²T/2`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

noncomputable section

namespace StatisticalRL.GaussianBanditLB

open StatisticalRL.Bandit

variable {A : ℕ}

theorem hardMean_mem_Icc {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (i a : Fin A) :
    hardMean ε i a ∈ Set.Icc (0 : ℝ) 1 := by
  unfold hardMean
  split_ifs <;> constructor <;> linarith

/-- In instance `j`, every arm other than `j` has gap at least `ε/2`. -/
theorem hardMean_gap {ε : ℝ} (h0 : 0 ≤ ε) (j b : Fin A) :
    ε / 2 * (if b ≠ j then (1 : ℝ) else 0) ≤ hardMean ε j j - hardMean ε j b := by
  by_cases hb : b = j
  · subst hb; simp
  · have hbj : ¬ (b = j ∧ j.val ≠ 0) := fun h => hb h.1
    unfold hardMean
    rw [if_neg hbj, if_pos hb]
    by_cases hj : j.val = 0
    · have hjj : ¬ (j = j ∧ j.val ≠ 0) := fun h => h.2 hj
      have hb0 : b.val ≠ 0 := fun h => hb (Fin.ext (h.trans hj.symm))
      rw [if_neg hjj, if_pos hj, if_neg hb0]
      linarith
    · rw [if_pos ⟨rfl, hj⟩]
      split_ifs <;> linarith

theorem hardMean_succ_sub {M : ℕ} (ε : ℝ) (j : Fin M) (b : Fin (M + 1)) :
    hardMean ε j.succ b - hardMean ε 0 b = if b = j.succ then ε else 0 := by
  unfold hardMean
  by_cases h : b = j.succ
  · subst h; simp [Fin.succ_ne_zero]
  · simp [h]

theorem sum_sq_hardMean_succ_sub_le {M : ℕ} (ε : ℝ) (b : Fin (M + 1)) :
    ∑ j : Fin M, (hardMean ε j.succ b - hardMean ε 0 b) ^ 2 / 2 ≤ ε ^ 2 / 2 := by
  simp_rw [hardMean_succ_sub]
  have h1 : ∀ j : Fin M, (if b = j.succ then ε else 0) ^ 2 / 2 =
      if b = j.succ then ε ^ 2 / 2 else 0 := fun j => by split_ifs <;> simp
  simp_rw [h1]
  have h2 := Fin.sum_univ_succ (fun k : Fin (M + 1) => if b = k then ε ^ 2 / 2 else (0 : ℝ))
  rw [Finset.sum_ite_eq] at h2
  simp only [mem_univ, if_true] at h2
  have h3 : (0 : ℝ) ≤ if b = 0 then ε ^ 2 / 2 else 0 := by split_ifs <;> positivity
  linarith

/-- Scalar step of the reverse-Fano bound: with budget `B ≤ (M+1)/8` the average error is at
least `1/4`. -/
theorem fano_quarter (M : ℕ) (hM : 1 ≤ M) (B : ℝ) (hB : B ≤ ((M : ℝ) + 1) / 8) :
    (1 : ℝ) / 4 ≤ 1 - 1 / ((M : ℝ) + 1) - Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2)) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpos : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  have hfrac : (M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (M : ℝ) * B ≤ M * (((M : ℝ) + 1) / 8) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    nlinarith
  have hsq : Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2)) ≤ 1 / 4 := by
    calc Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2)) ≤ Real.sqrt (1 / 16) :=
          Real.sqrt_le_sqrt hfrac
      _ = 1 / 4 := by
          rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hinv : 1 / ((M : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]; linarith
  linarith

section learner

variable {Seed : Type*} [MeasurableSpace Seed]
  {arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A}
  (harm : ∀ t, Measurable (Function.uncurry (arm t)))
  (ν : Measure Seed) [IsProbabilityMeasure ν] (T : ℕ)

omit [MeasurableSpace Seed] in
/-- Pointwise: the regret in instance `j` is at least `ε/2` times the number of rounds whose arm
is not `j`. -/
theorem regret_ge_count {ε : ℝ} (h0 : 0 ≤ ε) (j : Fin A) (σ : Seed)
    (z : Fin T → Fin A → ℝ) :
    ε / 2 * ∑ s : Fin T,
        (if armAt arm (hardMean ε j) σ (extendNoise z) s ≠ j then (1 : ℝ) else 0) ≤
      regret arm (hardMean ε j) T σ z := by
  unfold regret
  have hsplit : (T : ℝ) * (⨆ a, hardMean ε j a) -
      ∑ s : Fin T, hardMean ε j (armAt arm (hardMean ε j) σ (extendNoise z) s) =
      ∑ s : Fin T, ((⨆ a, hardMean ε j a) -
        hardMean ε j (armAt arm (hardMean ε j) σ (extendNoise z) s)) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [hsplit, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have hsup : hardMean ε j j ≤ ⨆ a, hardMean ε j a :=
    le_ciSup (Set.finite_range _).bddAbove j
  have := hardMean_gap h0 j (armAt arm (hardMean ε j) σ (extendNoise z) s)
  linarith

include harm in
/-- Expected regret in instance `j` is at least `ε/2` times the summed error probabilities. -/
theorem integral_regret_ge {ε : ℝ} (h0 : 0 ≤ ε) (j : Fin A) :
    ε / 2 * ∑ s : Fin T, (ν.prod (gaussianNoiseTable T A)).real
        {ω | armAt arm (hardMean ε j) ω.1 (extendNoise ω.2) s ≠ j} ≤
      ∫ ω, regret arm (hardMean ε j) T ω.1 ω.2 ∂(ν.prod (gaussianNoiseTable T A)) := by
  set P := ν.prod (gaussianNoiseTable T A)
  have hS : ∀ s : Fin T,
      MeasurableSet {ω : Seed × (Fin T → Fin A → ℝ) |
        armAt arm (hardMean ε j) ω.1 (extendNoise ω.2) s ≠ j} :=
    fun s => (measurable_armAt_joint harm (hardMean ε j) T s) (measurableSet_singleton j).compl
  have hI : ∀ s ∈ (univ : Finset (Fin T)), Integrable
      ({ω : Seed × (Fin T → Fin A → ℝ) |
        armAt arm (hardMean ε j) ω.1 (extendNoise ω.2) s ≠ j}.indicator 1) P :=
    fun s _ => (integrable_const (1 : ℝ)).indicator (hS s)
  calc ε / 2 * ∑ s : Fin T, P.real {ω | armAt arm (hardMean ε j) ω.1 (extendNoise ω.2) s ≠ j}
      = ∫ ω, ε / 2 * ∑ s : Fin T, ({ω : Seed × (Fin T → Fin A → ℝ) |
          armAt arm (hardMean ε j) ω.1 (extendNoise ω.2) s ≠ j}.indicator 1 ω) ∂P := by
        rw [integral_const_mul, integral_finset_sum _ hI]
        congr 1
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [integral_indicator_one (hS s)]
    _ ≤ ∫ ω, regret arm (hardMean ε j) T ω.1 ω.2 ∂P := by
        refine integral_mono ((integrable_finset_sum _ hI).const_mul _)
          (integrable_regret (hardMean ε j) harm T P) fun ω => ?_
        have := regret_ge_count T h0 j ω.1 ω.2 (arm := arm)
        simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
        exact this

end learner

/-- The Gaussian-bandit minimax lower bound (Remark 5.12, lower-bound part). -/
theorem minimax_lower_bound (A T : ℕ) (hA : 2 ≤ A) (hAT : A ≤ T) :
    ∃ μ : Fin A → Fin A → ℝ, (∀ i a, μ i a ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A),
        (∀ t, Measurable (Function.uncurry (arm t))) →
        ∃ i : Fin A,
          Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) => regret arm (μ i) T ω.1 ω.2)
            (ν.prod (gaussianNoiseTable T A)) ∧
          (1 / 16 : ℝ) * Real.sqrt ((A : ℝ) * T) ≤
            ∫ ω, regret arm (μ i) T ω.1 ω.2 ∂(ν.prod (gaussianNoiseTable T A)) := by
  obtain ⟨M, rfl⟩ : ∃ M, A = M + 1 := ⟨A - 1, by omega⟩
  have hM : 1 ≤ M := by omega
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hAT' : ((M : ℝ) + 1) ≤ T := by exact_mod_cast hAT
  set ε : ℝ := 1 / 2 * Real.sqrt (((M : ℝ) + 1) / T) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hratio : ((M : ℝ) + 1) / T ≤ 1 := (div_le_one hTpos).2 hAT'
  have hε1 : ε ≤ 1 := by
    have := Real.sqrt_le_one.mpr hratio
    rw [hε]; linarith
  have hεsq : ε ^ 2 = ((M : ℝ) + 1) / T / 4 := by
    rw [hε, mul_pow, Real.sq_sqrt (by positivity)]; ring
  refine ⟨hardMean ε, fun i a => hardMean_mem_Icc hε0 hε1 i a, ?_⟩
  intro Seed _ ν _ arm harm
  set P := ν.prod (gaussianNoiseTable T (M + 1)) with hP
  let c : Fin (M + 1) → Fin (M + 1) → ℝ := fun j a => hardMean ε j a - hardMean ε 0 a
  have hmeans : ∀ j, (fun a => hardMean ε 0 a + c j a) = hardMean ε j :=
    fun j => funext fun a => by simp only [c]; ring
  let Q : Fin (M + 1) → Measure (Seed × (Fin T → Fin (M + 1) → ℝ)) :=
    fun j => tiltQ (arm := arm) (hardMean ε 0) (c j) ν T
  haveI : ∀ j, IsProbabilityMeasure (Q j) := fun j => isProbabilityMeasure_tiltQ harm _ _ ν T
  -- the reference measure
  have hQ0 : Q 0 = P := by
    have hf : (fun ω : Seed × (Fin T → Fin (M + 1) → ℝ) =>
        logDensity arm (hardMean ε 0) (c 0) T ω.1 ω.2) = 0 := by
      funext ω; simp [logDensity, c]
    simp only [Q, tiltQ_def, hf, tilted_zero]
    exact hP.symm
  -- KL budget
  set B : ℝ := ε ^ 2 * T / 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hKL : (∑ j : Fin M, InformationTheory.klDiv (Q 0) (Q j.succ)) ≤ ENNReal.ofReal B := by
    rw [hQ0, hP]
    simp only [Q, klDiv_tiltQ harm _ _ ν T]
    rw [← hP]
    have hint : ∀ j ∈ (univ : Finset (Fin M)), Integrable
        (fun ω : Seed × (Fin T → Fin (M + 1) → ℝ) => ∑ s : Fin T,
          c j.succ (armAt arm (hardMean ε 0) ω.1 (extendNoise ω.2) s) ^ 2 / 2) P :=
      fun j _ => integrable_finset_sum _ fun s _ =>
        integrable_fin_valued P (measurable_armAt_joint harm (hardMean ε 0) T s)
          fun b => c j.succ b ^ 2 / 2
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ =>
      integral_nonneg fun ω => Finset.sum_nonneg fun s _ => by positivity]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← integral_finset_sum _ hint]
    calc ∫ ω, ∑ j : Fin M, ∑ s : Fin T,
          c j.succ (armAt arm (hardMean ε 0) ω.1 (extendNoise ω.2) s) ^ 2 / 2 ∂P
        ≤ ∫ _ω, B ∂P := by
          refine integral_mono (integrable_finset_sum _ hint) (integrable_const B) fun ω => ?_
          simp only
          rw [Finset.sum_comm]
          calc ∑ s : Fin T, ∑ j : Fin M,
                c j.succ (armAt arm (hardMean ε 0) ω.1 (extendNoise ω.2) s) ^ 2 / 2
              ≤ ∑ _s : Fin T, ε ^ 2 / 2 := Finset.sum_le_sum fun s _ =>
                sum_sq_hardMean_succ_sub_le ε _
            _ = B := by simp [hB]; ring
      _ = B := by simp
  -- per-round reverse Fano
  have hRF : ∀ s : Fin T, ((M : ℝ) + 1) / 4 ≤ ∑ j : Fin (M + 1),
      P.real {ω | armAt arm (hardMean ε j) ω.1 (extendNoise ω.2) s ≠ j} := by
    intro s
    have hψ : Measurable fun ω : Seed × (Fin T → Fin (M + 1) → ℝ) =>
        armAt arm (hardMean ε 0) ω.1 (extendNoise ω.2) s :=
      measurable_armAt_joint harm (hardMean ε 0) T s
    have h := PrelimFano.reverseFano_test_error_lower M Q _ hψ B hB0 hKL
    have hq := fano_quarter M hM B (by rw [hB, hεsq]; field_simp; linarith)
    have heq : ∀ j : Fin (M + 1),
        (Q j).real {ω | armAt arm (hardMean ε 0) ω.1 (extendNoise ω.2) s ≠ j} =
          P.real {ω | armAt arm (hardMean ε j) ω.1 (extendNoise ω.2) s ≠ j} := by
      intro j
      simp only [Measure.real, Q]
      rw [tiltQ_arm_ne harm (hardMean ε 0) (c j) ν T s s.isLt.le j, hmeans j]
    simp_rw [heq] at h
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have h2 := hq.trans h
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos] at h2
    linarith
  -- average over instances
  have havg : ∑ _j : Fin (M + 1), ε * T / 8 ≤
      ∑ j : Fin (M + 1), ∫ ω, regret arm (hardMean ε j) T ω.1 ω.2 ∂P := by
    calc ∑ _j : Fin (M + 1), ε * T / 8 = ε / 2 * ∑ _s : Fin T, ((M : ℝ) + 1) / 4 := by
          simp; ring
      _ ≤ ε / 2 * ∑ s : Fin T, ∑ j : Fin (M + 1),
            P.real {ω | armAt arm (hardMean ε j) ω.1 (extendNoise ω.2) s ≠ j} :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => hRF s) (by positivity)
      _ = ∑ j : Fin (M + 1), ε / 2 * ∑ s : Fin T,
            P.real {ω | armAt arm (hardMean ε j) ω.1 (extendNoise ω.2) s ≠ j} := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun j _ => integral_regret_ge harm ν T hε0 j
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le univ_nonempty havg
  refine ⟨j, integrable_regret _ harm T _, ?_⟩
  have hsqrt : Real.sqrt (((M + 1 : ℕ) : ℝ) * T) = Real.sqrt (((M : ℝ) + 1) / T) * T := by
    rw [show (((M + 1 : ℕ) : ℝ) * T) = ((M : ℝ) + 1) / T * T ^ 2 by
        push_cast; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hTpos.le]
  rw [hsqrt]
  calc (1 / 16 : ℝ) * (Real.sqrt (((M : ℝ) + 1) / T) * T) = ε * T / 8 := by rw [hε]; ring
    _ ≤ _ := hj

end StatisticalRL.GaussianBanditLB
