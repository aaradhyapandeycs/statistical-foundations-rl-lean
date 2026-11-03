import Formalization.Generative.GenerativeLowerBoundFamilyKL

/-! Exact sparse two-row change of measure for actual indexed MDP samples. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance familySparseStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance familySparseFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- One specified row contributes its constant exactly N times. -/
theorem family_sum_row_indicator {m n N : ℕ} (j : Fin m) (a : Fin (n + 1)) (c : ℝ) :
    (∑ z : FamilyActiveCoordinates m n N,
      if z.1.1 = j ∧ z.1.2 = a then c else 0) = N * c := by
  classical
  simp [Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq']
  have h (x : Fin (n + 1)) : (∑ _t : Fin N, if x = a then c else 0) =
      if x = a then N * c else 0 := by
    by_cases hx : x = a <;> simp [hx]
  simp_rw [h]
  simp

/-- Coordinatewise divergence for an alternative relative to baseline is
zero except at its two genuinely swapped rows. -/
theorem alternative_coordinate_kl_sparse {m n N : ℕ} (j : Fin m) (k : Fin n)
    (p q : ℝ≥0) (hpq : p ≤ q) (hq : q < 1) (z : FamilyActiveCoordinates m n N) :
    (InformationTheory.klDiv
      (PMF.bernoulli (familyBernoulliParameter (some (j,k)) p q z)
        (familyBernoulliParameter_le_one (some (j,k)) p q (le_trans hpq hq.le) hq.le z)).toMeasure
      (PMF.bernoulli (familyBernoulliParameter none p q z)
        (familyBernoulliParameter_le_one none p q (le_trans hpq hq.le) hq.le z)).toMeasure).toReal =
    (if z.1.1 = j ∧ z.1.2 = k.succ then
      (InformationTheory.klDiv (PMF.bernoulli q hq.le).toMeasure
        (PMF.bernoulli p (le_trans hpq hq.le)).toMeasure).toReal else 0) +
    (if z.1.1 = j ∧ z.1.2 = 0 then
      (InformationTheory.klDiv (PMF.bernoulli p (le_trans hpq hq.le)).toMeasure
        (PMF.bernoulli q hq.le).toMeasure).toReal else 0) := by
  classical
  rcases z with ⟨⟨s,a⟩,t⟩
  by_cases hs : s = j
  · subst s
    by_cases hk : a = k.succ
    · simp [familyBernoulliParameter, hardPolicySignature, hk, Fin.succ_ne_zero]
    · by_cases hzero : a = 0
      · simp [familyBernoulliParameter, hardPolicySignature, hk, hzero, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero k)]
      · simp [familyBernoulliParameter, hardPolicySignature, hk, hzero, InformationTheory.klDiv_self]
  · simp [familyBernoulliParameter, hardPolicySignature, hs, InformationTheory.klDiv_self]

/-- The actual full-array KL of an alternative relative to baseline is the
sum of the two swapped-row divergences, each repeated N times. -/
theorem familyAlternative_fullKL_exact {m n : ℕ} (j : Fin m) (k : Fin n)
    (γ : ℝ) (p q : ℝ≥0) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let M₁ := familyMDP (some (j,k)) γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    let M₀ := familyMDP none γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    (InformationTheory.klDiv (samplingLaw M₁ N) (samplingLaw M₀ N)).toReal =
      N * ((InformationTheory.klDiv (PMF.bernoulli q hq.le).toMeasure
          (PMF.bernoulli p (le_trans hpq hq.le)).toMeasure).toReal +
        (InformationTheory.klDiv (PMF.bernoulli p (le_trans hpq hq.le)).toMeasure
          (PMF.bernoulli q hq.le).toMeasure).toReal) := by
  classical
  dsimp only
  rw [familySamplingLaw_klDiv_eq_coordinate_sum _ _ _ _ _ hγ hγ1 hp hpq hq N]
  simp_rw [alternative_coordinate_kl_sparse j k p q hpq hq]
  rw [Finset.sum_add_distrib, family_sum_row_indicator, family_sum_row_indicator]
  ring

/-- The actual full-array alternative-versus-baseline KL satisfies the
source's two-row quadratic bound. -/
theorem familyAlternative_fullKL_le_source {m n : ℕ} (j : Fin m) (k : Fin n)
    (γ : ℝ) (p q : ℝ≥0) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : (1 : ℝ≥0) / 2 ≤ p) (hpq : p < q) (hq : q < 1)
    (hhalf : 2 * ((q : ℝ) - (p : ℝ)) ≤ 1 - (p : ℝ)) (N : ℕ) :
    let M₁ := familyMDP (some (j,k)) γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq.le) (by exact_mod_cast hq)
    let M₀ := familyMDP none γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq.le) (by exact_mod_cast hq)
    (InformationTheory.klDiv (samplingLaw M₁ N) (samplingLaw M₀ N)).toReal ≤
      8 * N * ((q : ℝ) - (p : ℝ)) ^ 2 / (1 - (p : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hq0 : 0 < q := lt_trans hp0 hpq
  have hb := twoRowSwapLaw_klDiv_le_source N p q hp hpq hq hhalf
  rw [twoRowSwapLaw_toReal_klDiv N p q hp0 (lt_trans hpq hq) hq0 hq] at hb
  dsimp only
  rw [familyAlternative_fullKL_exact j k γ p q hγ hγ1 hp0 hpq.le hq N]
  exact hb

/-- Under the source γ,ε parameter choices, every actual nonbaseline model's
full-array KL to the baseline is at most 1024 N (1−γ)³ ε². -/
theorem sourceFamilyAlternative_fullKL_le {m n : ℕ} (j : Fin m) (k : Fin n)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ) :
    let M₁ := sourceFamilyMDP (some (j,k)) γ ε hγ hγ1 hε hεmax
    let M₀ := sourceFamilyMDP none γ ε hγ hγ1 hε hεmax
    (InformationTheory.klDiv (samplingLaw M₁ N) (samplingLaw M₀ N)).toReal ≤
      1024 * N * (1 - γ) ^ 3 * ε ^ 2 := by
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  let p : ℝ≥0 := ⟨baseProbability γ, by linarith [ha.1]⟩
  let q : ℝ≥0 := ⟨baseProbability γ + probabilityIncrement γ ε, by linarith [ha.1, ha.2.1]⟩
  have hp : (1 : ℝ≥0) / 2 ≤ p := by exact_mod_cast ha.1
  have hpq : p < q := by exact_mod_cast ha.2.1
  have hq : q < 1 := by exact_mod_cast ha.2.2.1
  have hhalf : 2 * ((q : ℝ) - (p : ℝ)) ≤ 1 - (p : ℝ) := by
    change 2 * (baseProbability γ + probabilityIncrement γ ε - baseProbability γ) ≤
      1 - baseProbability γ
    linarith [ha.2.2.2]
  have hb := familyAlternative_fullKL_le_source j k γ p q (by linarith) hγ1 hp hpq hq hhalf N
  have hr := (source_parameters_squared_ratio γ ε hγ hγ1 hε).2
  have hn : (0 : ℝ) ≤ N := by positivity
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 8 * (N : ℝ) by positivity)
  dsimp only [sourceFamilyMDP] at ⊢
  change (InformationTheory.klDiv
    (samplingLaw (familyMDP (some (j,k)) γ (p : ℝ) (q : ℝ) _ _ _ _ _) N)
    (samplingLaw (familyMDP none γ (p : ℝ) (q : ℝ) _ _ _ _ _) N)).toReal ≤ _
  apply hb.trans
  change 8 * (N : ℝ) * (baseProbability γ + probabilityIncrement γ ε - baseProbability γ) ^ 2 /
      (1 - baseProbability γ) ≤ 1024 * N * (1 - γ) ^ 3 * ε ^ 2
  have heq : baseProbability γ + probabilityIncrement γ ε - baseProbability γ =
      probabilityIncrement γ ε := by ring
  rw [heq]
  convert hm using 1 <;> ring

end StatisticalRL.GenerativeLowerBound
