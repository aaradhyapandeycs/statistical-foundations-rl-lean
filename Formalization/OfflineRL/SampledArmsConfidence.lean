import Formalization.OfflineRL.FixedMaskGaussianMean
import Formalization.OfflineRL.BanditDefinitions
import Mathlib.MeasureTheory.Measure.Prod

/-! All-sampled-arms Gaussian confidence event under the actual joint law.

Source: `chapters/offlineRL.tex:243–260, 322–334, 400–403, 427–443, 524–556`.
The action vector and independent Gaussian noise have their actual product law.
The proof conditions on each fixed action-vector section, derives the random-count
bound without assuming independence of the count and its summands, and then takes
the union over arms. The event makes no assertion at zero count.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatisticalRL.OfflineRL

variable {Arm : Type*} [Fintype Arm] [DecidableEq Arm]

theorem empiricalArmMean_sub {N : ℕ} (r : Arm → ℝ) (a : Fin N → Arm) (z : Fin N → ℝ) (b : Arm)
    (hb : 0 < armCount a b) :
    empiricalArmMean r a z b - r b =
      (∑ i ∈ Finset.univ.filter (fun i => a i = b), z i) / armCount a b := by
  unfold empiricalArmMean
  set s := Finset.univ.filter (fun i => a i = b) with hs
  have hk : (armCount a b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have h1 : ∑ i ∈ s, r (a i) = ∑ i ∈ s, r b :=
    Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
  have hcard : (s.card : ℝ) = armCount a b := rfl
  rw [Finset.sum_add_distrib, h1, Finset.sum_const, nsmul_eq_mul, hcard]
  field_simp
  ring

/-- The bad event has probability at most `δ/2` under the actual joint law. -/
theorem allSampledArms_bad_le [MeasurableSpace Arm] [MeasurableSingletonClass Arm]
    (d : Measure Arm) [IsProbabilityMeasure d] (r : Arm → ℝ) (N : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin N => d).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1))
      {ω : (Fin N → Arm) × (Fin N → ℝ) | ∀ b, 0 < armCount ω.1 b →
        |empiricalArmMean r ω.1 ω.2 b - r b| ≤
          armRadius (Fintype.card Arm) δ (armCount ω.1 b)}ᶜ ≤ ENNReal.ofReal (δ / 2) := by
  classical
  set S := Measure.pi fun _ : Fin N => d with hS
  set G := Measure.pi fun _ : Fin N => gaussianReal 0 1 with hG
  set A := Fintype.card Arm with hA
  set c : ℝ := δ / (2 * A) with hc
  let T : (Fin N → Arm) → Arm → Set (Fin N → ℝ) := fun a b =>
    {z | 0 < armCount a b ∧
      Real.sqrt (2 * Real.log (4 * Fintype.card Arm / δ) /
          (Finset.univ.filter (fun i => a i = b)).card) <
        |(∑ i ∈ Finset.univ.filter (fun i => a i = b), z i) /
          (Finset.univ.filter (fun i => a i = b)).card|}
  have hT : ∀ a b, G (T a b) ≤ ENNReal.ofReal c := by
    intro a b
    by_cases hb : 0 < armCount a b
    · have h50 := fixedMask_gaussianMean_tail_pi N a b hb δ hδ hδ1
      have hset : T a b = {z : Fin N → ℝ | Real.sqrt (2 * Real.log (4 * Fintype.card Arm / δ) /
          (Finset.univ.filter (fun i => a i = b)).card) <
        |(∑ i ∈ Finset.univ.filter (fun i => a i = b), z i) /
          (Finset.univ.filter (fun i => a i = b)).card|} := by
        ext z
        simp only [T, Set.mem_setOf_eq, hb, true_and]
      rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top G _)]
      exact ENNReal.ofReal_le_ofReal (by simpa only [measureReal_def] using h50)
    · have hempty : T a b = ∅ := by
        ext z
        simp only [T, Set.mem_setOf_eq, hb, false_and, Set.mem_empty_iff_false]
      rw [hempty, measure_empty]
      exact zero_le _
  have hsub : {ω : (Fin N → Arm) × (Fin N → ℝ) | ∀ b, 0 < armCount ω.1 b →
        |empiricalArmMean r ω.1 ω.2 b - r b| ≤ armRadius A δ (armCount ω.1 b)}ᶜ ⊆
      ⋃ b ∈ (Finset.univ : Finset Arm), ⋃ a ∈ (Finset.univ : Finset (Fin N → Arm)),
        ({a} : Set (Fin N → Arm)) ×ˢ T a b := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hω
    obtain ⟨b, hb, hlt⟩ := hω
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_prod,
      Set.mem_singleton_iff]
    refine ⟨b, ω.1, rfl, hb, ?_⟩
    rw [empiricalArmMean_sub r ω.1 ω.2 b hb] at hlt
    simpa only [armRadius, armCount, hA] using hlt
  have hsum : ∀ b : Arm, ∑ a : Fin N → Arm, S {a} * G (T a b) ≤ ENNReal.ofReal c := by
    intro b
    calc ∑ a : Fin N → Arm, S {a} * G (T a b)
        ≤ ∑ a : Fin N → Arm, S {a} * ENNReal.ofReal c :=
          Finset.sum_le_sum fun a _ => mul_le_mul_left' (hT a b) _
      _ = (∑ a : Fin N → Arm, S {a}) * ENNReal.ofReal c := by rw [Finset.sum_mul]
      _ = ENNReal.ofReal c := by
          rw [sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]
  have hfinal : (A : ℝ≥0∞) * ENNReal.ofReal c ≤ ENNReal.ofReal (δ / 2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rcases Nat.eq_zero_or_pos A with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, zero_mul]; positivity
    · have hApos : (0 : ℝ) < A := by exact_mod_cast hpos
      rw [hc]
      apply le_of_eq
      field_simp
  calc _ ≤ (S.prod G) (⋃ b ∈ (Finset.univ : Finset Arm),
          ⋃ a ∈ (Finset.univ : Finset (Fin N → Arm)), ({a} : Set (Fin N → Arm)) ×ˢ T a b) :=
        measure_mono hsub
    _ ≤ ∑ b : Arm, (S.prod G) (⋃ a ∈ (Finset.univ : Finset (Fin N → Arm)),
          ({a} : Set (Fin N → Arm)) ×ˢ T a b) := measure_biUnion_finset_le _ _
    _ ≤ ∑ b : Arm, ∑ a : Fin N → Arm, (S.prod G) (({a} : Set (Fin N → Arm)) ×ˢ T a b) :=
        Finset.sum_le_sum fun b _ => measure_biUnion_finset_le _ _
    _ = ∑ b : Arm, ∑ a : Fin N → Arm, S {a} * G (T a b) := by
        simp only [Measure.prod_prod]
    _ ≤ ∑ _b : Arm, ENNReal.ofReal c := Finset.sum_le_sum fun b _ => hsum b
    _ = (A : ℝ≥0∞) * ENNReal.ofReal c := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (δ / 2) := hfinal

/-- All-sampled-arms confidence under the actual product law
`(⊗ d) ⊗ (⊗ N(0,1))`: with probability at least `1 − δ/2`, every arm with
`n_b > 0` satisfies `|μ̂_b − r(b)| ≤ √(2 log(4A/δ)/n_b)`. -/
theorem allSampledArms_confidence [MeasurableSpace Arm] [MeasurableSingletonClass Arm]
    (d : Measure Arm) [IsProbabilityMeasure d] (r : Arm → ℝ) (N : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 ≤
      ((Measure.pi fun _ : Fin N => d).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)).real
        {ω : (Fin N → Arm) × (Fin N → ℝ) | ∀ b, 0 < armCount ω.1 b →
          |empiricalArmMean r ω.1 ω.2 b - r b| ≤
            armRadius (Fintype.card Arm) δ (armCount ω.1 b)} := by
  set μ := (Measure.pi fun _ : Fin N => d).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)
  set Good := {ω : (Fin N → Arm) × (Fin N → ℝ) | ∀ b, 0 < armCount ω.1 b →
          |empiricalArmMean r ω.1 ω.2 b - r b| ≤
            armRadius (Fintype.card Arm) δ (armCount ω.1 b)}
  have hbad := allSampledArms_bad_le d r N δ hδ hδ1
  have hbadR : μ.real Goodᶜ ≤ δ / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
  have hu := measureReal_union_le (μ := μ) Good Goodᶜ
  rw [Set.union_compl_self, probReal_univ] at hu
  linarith

/-- The same event on any probability space carrying the exact joint law of
(action vector, noise vector). -/
theorem allSampledArms_confidence_of_hasLaw [MeasurableSpace Arm] [MeasurableSingletonClass Arm]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : Measure Arm) [IsProbabilityMeasure d] (r : Arm → ℝ) (N : ℕ)
    (act : Ω → Fin N → Arm) (noise : Ω → Fin N → ℝ)
    (hlaw : HasLaw (fun ω => (act ω, noise ω))
      ((Measure.pi fun _ : Fin N => d).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)) P)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 ≤ P.real {ω | ∀ b, 0 < armCount (act ω) b →
          |empiricalArmMean r (act ω) (noise ω) b - r b| ≤
            armRadius (Fintype.card Arm) δ (armCount (act ω) b)} := by
  set Good := {ω : (Fin N → Arm) × (Fin N → ℝ) | ∀ b, 0 < armCount ω.1 b →
          |empiricalArmMean r ω.1 ω.2 b - r b| ≤
            armRadius (Fintype.card Arm) δ (armCount ω.1 b)}
  have hpre : {ω | ∀ b, 0 < armCount (act ω) b →
          |empiricalArmMean r (act ω) (noise ω) b - r b| ≤
            armRadius (Fintype.card Arm) δ (armCount (act ω) b)} =
      (fun ω => (act ω, noise ω)) ⁻¹' Good := rfl
  have hbad := allSampledArms_bad_le d r N δ hδ hδ1
  have hle : P ((fun ω => (act ω, noise ω)) ⁻¹' Goodᶜ) ≤ ENNReal.ofReal (δ / 2) := by
    calc _ ≤ P.map (fun ω => (act ω, noise ω)) Goodᶜ := Measure.le_map_apply hlaw.aemeasurable _
      _ = _ := by rw [hlaw.map_eq]
      _ ≤ _ := hbad
  have hbadR : P.real ((fun ω => (act ω, noise ω)) ⁻¹' Good)ᶜ ≤ δ / 2 := by
    rw [← Set.preimage_compl]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle
  have hu := measureReal_union_le (μ := P) ((fun ω => (act ω, noise ω)) ⁻¹' Good)
    ((fun ω => (act ω, noise ω)) ⁻¹' Good)ᶜ
  rw [Set.union_compl_self, probReal_univ] at hu
  rw [hpre]
  linarith

end StatisticalRL.OfflineRL
