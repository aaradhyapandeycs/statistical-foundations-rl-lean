import Formalization.Probability.BernsteinFixedTimeTail
import Formalization.Probability.FreedmanVariancePeeling

/-! Source Freedman constants from actual bounded martingale differences,
sharp Bernstein tails and deterministic dyadic variance coverage. -/
open MeasureTheory
open scoped BigOperators
namespace StatisticalRL
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-- Negation preserves the actual predictable second-moment process. -/
theorem predictableSecondMomentSum_neg (μ : Measure Ω) (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (n : ℕ) :
    predictableSecondMomentSum μ ℱ (fun k ω ↦ -X k ω) n =
      predictableSecondMomentSum μ ℱ X n := by
  funext ω
  simp [predictableSecondMomentSum]

/-- Actual predictable second-moment sums are nonnegative almost everywhere. -/
theorem predictableSecondMomentSum_nonneg (μ : Measure Ω) (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (n : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ predictableSecondMomentSum μ ℱ X n ω := by
  induction n with
  | zero => simp [predictableSecondMomentSum]
  | succ n ih =>
    have hv : 0 ≤ᵐ[μ] μ[fun ω ↦ X n ω ^ 2 | ℱ n] :=
      condExp_nonneg (Filter.Eventually.of_forall fun ω ↦ sq_nonneg _)
    filter_upwards [ih, hv] with ω hi hv
    simpa only [predictableSecondMomentSum, Finset.sum_range_succ] using add_nonneg hi hv

/-- Lower-tail transfer uses negated genuine increments and unchanged actual
conditional variances, rather than a symmetry assumption on their law. -/
theorem bernstein_variance_restricted_lower_chernoff
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B t : ℝ) (hB : 0 ≤ B) (ht0 : 0 ≤ t)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B) (ht : |t| * B < 3)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ) (x v : ℝ) :
    μ.real {ω | x ≤ -incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤
      Real.exp (bernsteinCoefficient B t * v - t * x) := by
  have hn (k : ℕ) : μ[(fun ω ↦ -X k ω) | ℱ k] =ᵐ[μ] fun _ ↦ 0 := by
    filter_upwards [condExp_neg (μ := μ) (X k) (ℱ k), hc k] with ω hneg hz
    simpa only [Pi.neg_apply, hz, neg_zero] using hneg
  have hbound (k : ℕ) : ∀ᵐ ω ∂μ, |(-X k ω)| ≤ B := by simpa only [abs_neg] using hb k
  have hp := bernstein_variance_restricted_chernoff μ ℱ (fun k ω ↦ -X k ω) B t hB ht0
    (fun k ↦ (hX k).neg) hbound ht hn n x v
  simpa only [predictableSecondMomentSum_neg, incrementSum, Finset.sum_neg_distrib] using hp

/-- A two-sided fixed-bin tail with the source linear coefficient. -/
theorem bernstein_abs_variance_restricted_source_radius
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ)
    (v L : ℝ) (hv : 0 < v) (hL : 0 < L) :
    μ.real {ω | 2 * Real.sqrt (v * L) + (4 / 3) * B * L ≤ |incrementSum X n ω| ∧
      predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤ 2 * Real.exp (-L) := by
  let x := 2 * Real.sqrt (v * L) + (4 / 3) * B * L
  have hu := bernstein_variance_restricted_source_radius μ ℱ X B hB hX hb hc n v L hv hL
  have hn (k : ℕ) : μ[(fun ω ↦ -X k ω) | ℱ k] =ᵐ[μ] fun _ ↦ 0 := by
    filter_upwards [condExp_neg (μ := μ) (X k) (ℱ k), hc k] with ω hneg hz
    simpa only [Pi.neg_apply, hz, neg_zero] using hneg
  have hbound (k : ℕ) : ∀ᵐ ω ∂μ, |(-X k ω)| ≤ B := by simpa only [abs_neg] using hb k
  have hl := bernstein_variance_restricted_source_radius μ ℱ (fun k ω ↦ -X k ω)
    B hB (fun k ↦ (hX k).neg) hbound hn n v L hv hL
  simp only [predictableSecondMomentSum_neg, incrementSum, Finset.sum_neg_distrib] at hl
  let U := {ω | x ≤ incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v}
  let D := {ω | x ≤ -incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v}
  have hsub : {ω | x ≤ |incrementSum X n ω| ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ⊆ U ∪ D := by
    intro ω hω
    rcases le_max_iff.mp (by simpa only [abs_eq_max_neg] using hω.1) with hy | hy
    · exact Or.inl ⟨hy, hω.2⟩
    · exact Or.inr ⟨hy, hω.2⟩
  have hm := measureReal_mono hsub (measure_ne_top μ _)
  have huni := measureReal_union_le (μ := μ) U D
  change μ.real {ω | x ≤ |incrementSum X n ω| ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤ _
  change μ.real U ≤ _ at hu
  change μ.real D ≤ _ at hl
  linarith

/-- Both signs of the generic fixed-time Chernoff bound. -/
theorem bernstein_abs_variance_restricted_chernoff
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B t : ℝ) (hB : 0 ≤ B) (ht0 : 0 ≤ t)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B) (ht : |t| * B < 3)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ) (x v : ℝ) :
    μ.real {ω | x ≤ |incrementSum X n ω| ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤
      2 * Real.exp (bernsteinCoefficient B t * v - t * x) := by
  have hu := bernstein_variance_restricted_chernoff μ ℱ X B t hB ht0 hX hb ht hc n x v
  have hl := bernstein_variance_restricted_lower_chernoff μ ℱ X B t hB ht0 hX hb ht hc n x v
  let U := {ω | x ≤ incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v}
  let D := {ω | x ≤ -incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v}
  have hsub : {ω | x ≤ |incrementSum X n ω| ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ⊆ U ∪ D := by
    intro ω hω
    rcases le_max_iff.mp (by simpa only [abs_eq_max_neg] using hω.1) with hy | hy
    · exact Or.inl ⟨hy, hω.2⟩
    · exact Or.inr ⟨hy, hω.2⟩
  have hm := measureReal_mono hsub (measure_ne_top μ _)
  have huni := measureReal_union_le (μ := μ) U D
  change μ.real U ≤ _ at hu
  change μ.real D ≤ _ at hl
  linarith

/-- Zero variance ceiling is handled by a legal positive tuning, with no
inverse variance or limiting argument. -/
theorem bernstein_abs_zero_variance_radius
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B : ℝ) (hB : 0 < B)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ)
    (L : ℝ) (hL : 0 < L) :
    μ.real {ω | (4 / 3) * B * L ≤ |incrementSum X n ω| ∧
      predictableSecondMomentSum μ ℱ X n ω ≤ 0} ≤ 2 * Real.exp (-L) := by
  have ht : 0 ≤ (1 : ℝ) / B := by positivity
  have hlegal : |(1 : ℝ) / B| * B < 3 := by
    rw [abs_of_nonneg ht, div_mul_cancel₀ _ hB.ne']
    norm_num
  have hp := bernstein_abs_variance_restricted_chernoff μ ℱ X B (1 / B)
    hB.le ht hX hb hlegal hc n ((4 / 3) * B * L) 0
  have he : bernsteinCoefficient B (1 / B) * 0 - (1 / B) * ((4 / 3) * B * L) ≤ -L := by
    have hid : (1 / B) * ((4 / 3) * B * L) = (4 / 3) * L := by field_simp
    rw [mul_zero, zero_sub, hid]
    linarith
  exact hp.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num))

/-- B=0 implies actual zero increment sums almost everywhere. -/
theorem incrementSum_eq_zero_of_zero_bound (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ 0) (n : ℕ) :
    incrementSum X n =ᵐ[μ] fun _ ↦ 0 := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun ω ↦ by simp [incrementSum]
  | succ n ih =>
    filter_upwards [ih, hb n] with ω hi hx
    have he : X n ω = 0 := abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))
    change (∑ k ∈ Finset.range (n + 1), X k ω) = 0
    rw [Finset.sum_range_succ, he, add_zero]
    exact hi

/-- The exact source Freedman random-variance failure bound, including zero
increment and zero global variance scales. -/
theorem freedman_source_failure_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B σ₂ : ℝ) (hB : 0 ≤ B) (hσ : 0 ≤ σ₂)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n K : ℕ) (hK : 0 < K)
    (hcap : ∀ᵐ ω ∂μ, predictableSecondMomentSum μ ℱ X n ω ≤ σ₂)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | Real.sqrt (8 * max (predictableSecondMomentSum μ ℱ X n ω)
      (σ₂ / (2 : ℝ) ^ K) * Real.log (2 * K / δ)) +
      (4 / 3) * B * Real.log (2 * K / δ) < |incrementSum X n ω|} ≤ δ := by
  let L := Real.log (2 * K / δ)
  let W := predictableSecondMomentSum μ ℱ X n
  let R := fun ω ↦ Real.sqrt (8 * max (W ω) (σ₂ / (2 : ℝ) ^ K) * L) + (4 / 3) * B * L
  let bad := {ω | R ω < |incrementSum X n ω|}
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hδ).2 (by linarith))
  have he : Real.exp (-L) = δ / (2 * K) := by
    dsimp [L]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have htwo : 2 * Real.exp (-L) ≤ δ := by
    rw [he]
    have hid : 2 * (δ / (2 * (K : ℝ))) = δ / K := by field_simp
    rw [hid]
    exact (div_le_iff₀ hKpos).2 (by nlinarith)
  by_cases hB0 : B = 0
  · subst B
    have hz := incrementSum_eq_zero_of_zero_bound μ X hb n
    have hnull : bad =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hz] with ω hω
      have hn : ¬ R ω < |incrementSum X n ω| := by
        dsimp [R]
        rw [hω]
        simp only [abs_zero, mul_zero, zero_mul, add_zero]
        exact not_lt.mpr (Real.sqrt_nonneg _)
      exact propext (iff_false_intro hn)
    change μ.real bad ≤ δ
    rw [measureReal_congr hnull]
    simpa using hδ.le
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  by_cases hσ0 : σ₂ = 0
  · subst σ₂
    let E := {ω | (4 / 3) * B * L ≤ |incrementSum X n ω| ∧ W ω ≤ 0}
    have hp : μ.real E ≤ 2 * Real.exp (-L) := bernstein_abs_zero_variance_radius μ ℱ X B hBp hX hb hc n L hL
    have hsub : bad ≤ᵐ[μ] E := by
      filter_upwards [hcap, predictableSecondMomentSum_nonneg μ ℱ X n] with ω hw hn
      intro hbad
      have hw0 : W ω = 0 := by dsimp [W]; linarith
      refine ⟨?_, hw⟩
      change R ω < |incrementSum X n ω| at hbad
      dsimp [R] at hbad
      rw [hw0] at hbad
      simp only [zero_div, max_self, mul_zero, zero_mul, Real.sqrt_zero, zero_add] at hbad
      exact hbad.le
    change μ.real bad ≤ δ
    exact (ENNReal.toReal_mono (measure_ne_top μ E) (measure_mono_ae hsub)).trans (hp.trans htwo)
  have hσp : 0 < σ₂ := lt_of_le_of_ne hσ (Ne.symm hσ0)
  let E : Fin K → Set Ω := fun j ↦ {ω |
    2 * Real.sqrt ((σ₂ / (2 : ℝ) ^ (j : ℕ)) * L) + (4 / 3) * B * L ≤
      |incrementSum X n ω| ∧ W ω ≤ σ₂ / (2 : ℝ) ^ (j : ℕ)}
  have hbin (j : Fin K) : μ.real (E j) ≤ 2 * Real.exp (-L) :=
    bernstein_abs_variance_restricted_source_radius μ ℱ X B hB hX hb hc n _ L (by positivity) hL
  have hsub : bad ≤ᵐ[μ] ⋃ j : Fin K, E j := by
    filter_upwards [hcap, predictableSecondMomentSum_nonneg μ ℱ X n] with ω hw hn
    intro hbad
    obtain ⟨j, hj, hwj, hrad⟩ := dyadic_variance_radius_cover K hK σ₂ (W ω) L hσ hn hw hL.le
    apply Set.mem_iUnion.mpr
    refine ⟨⟨j, hj⟩, ?_, hwj⟩
    have hid : Real.sqrt (4 * (σ₂ / (2 : ℝ) ^ j) * L) =
        2 * Real.sqrt ((σ₂ / (2 : ℝ) ^ j) * L) := by
      rw [show 4 * (σ₂ / (2 : ℝ) ^ j) * L = 4 * ((σ₂ / (2 : ℝ) ^ j) * L) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [hid] at hrad
    change R ω < |incrementSum X n ω| at hbad
    dsimp [R] at hbad
    change _ ≤ _
    linarith
  change μ.real bad ≤ δ
  calc
    _ ≤ μ.real (⋃ j : Fin K, E j) := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    _ ≤ ∑ j : Fin K, μ.real (E j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin K, 2 * Real.exp (-L) := Finset.sum_le_sum fun j _ ↦ hbin j
    _ = δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [he]
      field_simp

/-- Source Freedman random-variance confidence event with its exact constants.
The variance scale is nonnegative and all zero endpoints are included. -/
theorem freedman_source_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B σ₂ : ℝ) (hB : 0 ≤ B) (hσ : 0 ≤ σ₂)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n K : ℕ) (hK : 0 < K)
    (hcap : ∀ᵐ ω ∂μ, predictableSecondMomentSum μ ℱ X n ω ≤ σ₂)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {ω | |incrementSum X n ω| ≤
      Real.sqrt (8 * max (predictableSecondMomentSum μ ℱ X n ω)
        (σ₂ / (2 : ℝ) ^ K) * Real.log (2 * K / δ)) +
        (4 / 3) * B * Real.log (2 * K / δ)} := by
  let R := fun ω ↦ Real.sqrt (8 * max (predictableSecondMomentSum μ ℱ X n ω)
    (σ₂ / (2 : ℝ) ^ K) * Real.log (2 * K / δ)) + (4 / 3) * B * Real.log (2 * K / δ)
  have hy : Measurable (incrementSum X n) := by
    unfold incrementSum
    apply Finset.measurable_fun_sum
    intro k hk
    exact (hX k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have hw : Measurable (predictableSecondMomentSum μ ℱ X n) := by
    unfold predictableSecondMomentSum
    apply Finset.measurable_fun_sum
    intro k hk
    exact (stronglyMeasurable_condExp (μ := μ) (m := ℱ k)
      (f := fun ω ↦ X k ω ^ 2)).measurable.mono (ℱ.le k) le_rfl
  have hr : Measurable R := by dsimp [R]; fun_prop
  have hbad := freedman_source_failure_bound μ ℱ X B σ₂ hB hσ hX hb hc n K hK hcap δ hδ hδ1
  have heq : {ω | |incrementSum X n ω| ≤ R ω} = {ω | R ω < |incrementSum X n ω|}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  have hp := measureReal_compl (μ := μ) (measurableSet_lt hr (continuous_abs.measurable.comp hy))
  change μ.real {ω | R ω < |incrementSum X n ω|}ᶜ =
    μ.real Set.univ - μ.real {ω | R ω < |incrementSum X n ω|} at hp
  rw [probReal_univ, ← heq] at hp
  change μ.real {ω | R ω < |incrementSum X n ω|} ≤ δ at hbad
  change 1 - δ ≤ μ.real {ω | |incrementSum X n ω| ≤ R ω}
  linarith

end StatisticalRL
