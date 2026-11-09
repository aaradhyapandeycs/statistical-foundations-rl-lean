import Formalization.OfflineRL.BanditDefinitions
import Formalization.OfflineRL.FixedMaskGaussianMean
import Formalization.Probability.GaussianTailLower

/-!
# The two-armed offline bandit example (Example 6.1, Remarks 6.4 and 6.5)

Source: `chapters/offlineRL.tex:348–379` (Example 6.1 and its proof), `:357–359` (Remark 6.4),
`:400–415` (penalty and Remark 6.5). Arms `Fin 2` (source arm 1 is `0`, arm 2 is `1`),
`r = (1, 0)`, deterministic design `aᵢ = 0` for `i < N − 1` and `a_{N−1} = 1`, noise
`z ∼ N(0,1)^{⊗N}`, rewards `r(aᵢ) + zᵢ`.

* `exampleDesign_armCount_zero/one`: the counts are `N − 1` and `1`;
* `exampleDesign_cstar`, `tendsto_div_sub_one`: Remark 6.4 (`C⋆ = N/(N−1) → 1`);
* `exampleDesign_lcb_selects_optimal`: Remark 6.5 (LCB selects arm 1 w.p. `≥ 1 − δ`);
* `exampleDesign_empiricalBest_regret`: Example 6.1 (`E[r⋆ − r_{a^emp}] ≥ 0.075` for every
  empirical-best selector, as a lower Lebesgue integral).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatisticalRL.OfflineRL

/-- The deterministic design of Example 6.1: arm `0` for `i < N − 1`, arm `1` at `i = N − 1`. -/
def exampleDesign (N : ℕ) : Fin N → Fin 2 := fun i ↦ if i.val < N - 1 then 0 else 1

theorem fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem exampleDesign_eq_zero_iff {N : ℕ} (i : Fin N) : exampleDesign N i = 0 ↔ i.val < N - 1 := by
  unfold exampleDesign; split_ifs with h <;> simp [h]

theorem exampleDesign_eq_one_iff {N : ℕ} (i : Fin N) : exampleDesign N i = 1 ↔ i.val = N - 1 := by
  unfold exampleDesign
  have := i.isLt
  split_ifs with h
  · simp; omega
  · simp; omega

/-- The last index `N − 1`. -/
def exampleLast (N : ℕ) (hN : 1 ≤ N) : Fin N := ⟨N - 1, by omega⟩

theorem exampleDesign_filter_one {N : ℕ} (hN : 1 ≤ N) :
    Finset.univ.filter (fun i ↦ exampleDesign N i = 1) = {exampleLast N hN} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [exampleDesign_eq_one_iff, Fin.ext_iff]
  rfl

theorem exampleDesign_armCount_one {N : ℕ} (hN : 1 ≤ N) : armCount (exampleDesign N) 1 = 1 := by
  unfold armCount; rw [exampleDesign_filter_one hN]; rfl

theorem exampleDesign_armCount_zero {N : ℕ} (hN : 1 ≤ N) :
    armCount (exampleDesign N) 0 = N - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin N ↦ exampleDesign N i = 0)
  have hneg : Finset.univ.filter (fun i ↦ ¬ exampleDesign N i = 0) =
      Finset.univ.filter (fun i ↦ exampleDesign N i = 1) := by
    refine Finset.filter_congr fun i _ ↦ ?_
    rcases fin_two_cases (exampleDesign N i) with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [hneg, exampleDesign_filter_one hN, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin] at h
  unfold armCount
  omega

theorem exampleLast_notMem {N : ℕ} (hN : 1 ≤ N) :
    exampleLast N hN ∉ Finset.univ.filter (fun i ↦ exampleDesign N i = 0) := by
  simp [exampleDesign_eq_zero_iff, exampleLast]

/-- Empirical mean of arm `1`: the single observation `z_{N−1}`. -/
theorem exampleDesign_mean_one {N : ℕ} (hN : 1 ≤ N) (z : Fin N → ℝ) :
    empiricalArmMean ![(1 : ℝ), 0] (exampleDesign N) z 1 = z (exampleLast N hN) := by
  unfold empiricalArmMean
  rw [exampleDesign_armCount_one hN, exampleDesign_filter_one hN, Finset.sum_singleton]
  have : exampleDesign N (exampleLast N hN) = 1 := by
    rw [exampleDesign_eq_one_iff]; rfl
  rw [this]
  simp

/-- Empirical mean of arm `0`: `1 + (∑_{i<N−1} zᵢ)/(N−1)`. -/
theorem exampleDesign_mean_zero {N : ℕ} (hN : 2 ≤ N) (z : Fin N → ℝ) :
    empiricalArmMean ![(1 : ℝ), 0] (exampleDesign N) z 0 =
      1 + (∑ i ∈ Finset.univ.filter (fun i ↦ exampleDesign N i = 0), z i) / ((N : ℝ) - 1) := by
  unfold empiricalArmMean
  have hc := exampleDesign_armCount_zero (N := N) (by omega)
  have hcard : ((Finset.univ.filter (fun i ↦ exampleDesign N i = 0)).card : ℝ) = (N : ℝ) - 1 := by
    have : (Finset.univ.filter (fun i ↦ exampleDesign N i = 0)).card = N - 1 := hc
    rw [this, Nat.cast_sub (by omega), Nat.cast_one]
  have hpos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [Finset.sum_congr rfl (fun i hi ↦ by
      rw [(Finset.mem_filter.1 hi).2] : ∀ i ∈ Finset.univ.filter (fun i ↦ exampleDesign N i = 0),
        ![(1 : ℝ), 0] (exampleDesign N i) + z i = ![(1 : ℝ), 0] 0 + z i)]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  unfold armCount
  rw [hcard]
  simp only [Matrix.cons_val_zero, mul_one]
  field_simp

/-! ## Remark 6.4 -/

/-- Remark 6.4: with `d^b` the design frequency, `max_b d⋆(b)/d^b(b) = N/(N−1)`. -/
theorem exampleDesign_cstar {N : ℕ} (hN : 2 ≤ N) :
    (⨆ b : Fin 2, ENNReal.ofReal (if b = 0 then 1 else 0) /
        ENNReal.ofReal ((armCount (exampleDesign N) b : ℝ) / N)) =
      ENNReal.ofReal ((N : ℝ) / ((N : ℝ) - 1)) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : ((armCount (exampleDesign N) 0 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [exampleDesign_armCount_zero (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have hval : ENNReal.ofReal (if (0 : Fin 2) = 0 then 1 else 0) /
      ENNReal.ofReal ((armCount (exampleDesign N) 0 : ℝ) / N) =
      ENNReal.ofReal ((N : ℝ) / ((N : ℝ) - 1)) := by
    rw [if_pos rfl, h0, ← ENNReal.ofReal_div_of_pos (div_pos (by linarith) (by linarith))]
    congr 1
    field_simp
  apply le_antisymm
  · refine iSup_le fun b ↦ ?_
    rcases fin_two_cases b with rfl | rfl
    · rw [hval]
    · simp
  · rw [← hval]
    exact le_iSup (fun b : Fin 2 ↦ ENNReal.ofReal (if b = 0 then 1 else 0) /
      ENNReal.ofReal ((armCount (exampleDesign N) b : ℝ) / N)) 0

/-- `N/(N−1) → 1`. -/
theorem tendsto_div_sub_one :
    Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) / ((N : ℝ) - 1)) Filter.atTop (nhds 1) := by
  simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)

/-! ## Remark 6.5 -/

/-- Remark 6.5: for `δ ∈ (0,1)` and `N − 1 > 8 log(8/δ)`, with probability at least `1 − δ`
the LCB of arm `1` is at most `r₁ = 0`, the LCB of arm `0` is within `2√(2 log(8/δ)/(N−1))` of
`r₀ = 1`, and arm `0` has the strictly larger LCB. -/
theorem exampleDesign_lcb_selects_optimal (N : ℕ) (δ : ℝ) (hN : 2 ≤ N) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hlarge : 8 * Real.log (8 / δ) < (N : ℝ) - 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin N ↦ gaussianReal 0 1).real
      {z | lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 1 ≤ ![(1 : ℝ), 0] 1 ∧
        |lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 0 - ![(1 : ℝ), 0] 0| ≤
          2 * Real.sqrt (2 * Real.log (8 / δ) / ((N : ℝ) - 1)) ∧
        lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 1 <
          lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 0} := by
  set μ := Measure.pi fun _ : Fin N ↦ gaussianReal 0 1 with hμ
  have hN1 : 1 ≤ N := by omega
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  set F0 := Finset.univ.filter (fun i ↦ exampleDesign N i = 0) with hF0
  set F1 := Finset.univ.filter (fun i ↦ exampleDesign N i = 1) with hF1
  have hc0 : F0.card = N - 1 := exampleDesign_armCount_zero hN1
  have hc1 : F1.card = 1 := exampleDesign_armCount_one hN1
  have hc0R : (F0.card : ℝ) = (N : ℝ) - 1 := by
    rw [hc0, Nat.cast_sub hN1, Nat.cast_one]
  have hcardA : (4 * (Fintype.card (Fin 2) : ℝ) / δ) = 8 / δ := by
    simp only [Fintype.card_fin]; norm_num
  set L := Real.log (8 / δ) with hL
  have hL0 : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  -- bad events
  have hb0 := fixedMask_gaussianMean_tail_pi N (exampleDesign N) (0 : Fin 2)
    (by rw [← hF0, hc0]; omega) δ hδ hδ1
  have hb1 := fixedMask_gaussianMean_tail_pi N (exampleDesign N) (1 : Fin 2)
    (by rw [← hF1, hc1]; omega) δ hδ hδ1
  rw [← hF0, hcardA] at hb0
  rw [← hF1, hcardA] at hb1
  simp only [Fintype.card_fin] at hb0 hb1
  set B0 := {z : Fin N → ℝ | Real.sqrt (2 * L / (F0.card : ℝ)) <
    |(∑ i ∈ F0, z i) / (F0.card : ℝ)|} with hB0
  set B1 := {z : Fin N → ℝ | Real.sqrt (2 * L / (F1.card : ℝ)) <
    |(∑ i ∈ F1, z i) / (F1.card : ℝ)|} with hB1
  set G := {z | lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 1 ≤ ![(1 : ℝ), 0] 1 ∧
        |lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 0 - ![(1 : ℝ), 0] 0| ≤
          2 * Real.sqrt (2 * Real.log (8 / δ) / ((N : ℝ) - 1)) ∧
        lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 1 <
          lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 0} with hG
  -- radius facts
  have hrad : ∀ b : Fin 2, armRadius (Fintype.card (Fin 2)) δ (armCount (exampleDesign N) b) =
      Real.sqrt (2 * L / (armCount (exampleDesign N) b : ℝ)) := by
    intro b; unfold armRadius; rw [hcardA]
  have hb0small : Real.sqrt (2 * L / ((N : ℝ) - 1)) < 1 / 2 := by
    rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ hk]
    linarith
  -- pointwise inclusion
  have hsub : Gᶜ ⊆ B0 ∪ B1 := by
    intro z hz
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨h0, h1⟩ := hcon
    simp only [hB0, hB1, Set.mem_setOf_eq, not_lt] at h0 h1
    rw [hc0R] at h0
    rw [hc1, Nat.cast_one, div_one, div_one, hF1, exampleDesign_filter_one hN1,
      Finset.sum_singleton] at h1
    apply hz
    have hlcb1 : lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 1 =
        z (exampleLast N hN1) - Real.sqrt (2 * L) := by
      unfold lcbFallback
      rw [if_neg (by rw [exampleDesign_armCount_one hN1]; norm_num), hrad,
        exampleDesign_mean_one hN1, exampleDesign_armCount_one hN1, Nat.cast_one, div_one]
    have hlcb0 : lcbFallback ![(1 : ℝ), 0] (exampleDesign N) z δ 0 =
        1 + (∑ i ∈ F0, z i) / ((N : ℝ) - 1) - Real.sqrt (2 * L / ((N : ℝ) - 1)) := by
      unfold lcbFallback
      have h0' : ((armCount (exampleDesign N) 0 : ℕ) : ℝ) = (N : ℝ) - 1 := hc0R
      rw [if_neg (by rw [exampleDesign_armCount_zero hN1]; omega), hrad,
        exampleDesign_mean_zero hN, h0']
    have hA := abs_le.1 h1
    have hB := abs_le.1 h0
    have hs0 : 0 ≤ Real.sqrt (2 * L / ((N : ℝ) - 1)) := Real.sqrt_nonneg _
    simp only [hG, Set.mem_setOf_eq, hlcb1, hlcb0, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, ← hL]
    refine ⟨by linarith [hA.2], ?_, by linarith [hA.2, hB.1]⟩
    rw [abs_le]
    constructor <;> linarith [hB.1, hB.2]
  -- measure bookkeeping
  have h1 : (1 : ℝ) ≤ μ.real G + μ.real Gᶜ := by
    rw [← probReal_univ (μ := μ), ← Set.union_compl_self G]
    exact measureReal_union_le _ _
  have h2 : μ.real Gᶜ ≤ μ.real B0 + μ.real B1 :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hb0' : μ.real B0 ≤ δ / (2 * 2) := hb0
  have hb1' : μ.real B1 ≤ δ / (2 * 2) := hb1
  have : μ.real G ≥ 1 - δ := by
    have : δ / (2 * 2) + δ / (2 * 2) ≤ δ := by linarith
    linarith
  exact this

/-! ## Example 6.1 -/

/-- **Example 6.1**: for every `N ≥ 2` and every selector returning an empirical best arm,
`E[r⋆ − r_{a^emp}] ≥ 0.075` (lower Lebesgue integral; no measurability of the selector). -/
theorem exampleDesign_empiricalBest_regret (N : ℕ) (hN : 2 ≤ N) (sel : (Fin N → ℝ) → Fin 2)
    (hsel : ∀ z b, empiricalArmMean ![(1 : ℝ), 0] (exampleDesign N) z b ≤
      empiricalArmMean ![(1 : ℝ), 0] (exampleDesign N) z (sel z)) :
    ENNReal.ofReal 0.075 ≤
      ∫⁻ z, ENNReal.ofReal (![(1 : ℝ), 0] 0 - ![(1 : ℝ), 0] (sel z))
        ∂(Measure.pi fun _ : Fin N ↦ gaussianReal 0 1) := by
  set μ := Measure.pi fun _ : Fin N ↦ gaussianReal 0 1 with hμ
  have hN1 : 1 ≤ N := by omega
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  set F0 := Finset.univ.filter (fun i ↦ exampleDesign N i = 0) with hF0
  set last := exampleLast N hN1
  set X : (Fin N → ℝ) → ℝ := ∑ j ∈ F0, fun z ↦ z j with hX
  set Y : (Fin N → ℝ) → ℝ := fun z ↦ z last with hY
  have hXapp : ∀ z, X z = ∑ j ∈ F0, z j := fun z ↦ by simp [hX, Finset.sum_apply]
  set E := X ⁻¹' Set.Iic 0 ∩ Y ⁻¹' Set.Ioi 1 with hE
  have hXm : Measurable X := by
    rw [show X = fun z ↦ ∑ j ∈ F0, z j from funext hXapp]
    exact Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j
  have hYm : Measurable Y := measurable_pi_apply last
  have hEm : MeasurableSet E := (hXm measurableSet_Iic).inter (hYm measurableSet_Ioi)
  -- on `E` the selector picks arm `1`
  have hpt : E.indicator 1 ≤ fun z ↦ ENNReal.ofReal (![(1 : ℝ), 0] 0 - ![(1 : ℝ), 0] (sel z)) := by
    intro z
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz]
      have hz' : X z ≤ 0 ∧ 1 < Y z := hz
      have hsel1 : sel z = 1 := by
        rcases fin_two_cases (sel z) with h0 | h1
        · exfalso
          have := hsel z 1
          rw [h0, exampleDesign_mean_one hN1, exampleDesign_mean_zero hN] at this
          have hdiv : (∑ i ∈ F0, z i) / ((N : ℝ) - 1) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by rw [← hXapp]; exact hz'.1) hk.le
          have : 1 < z last := hz'.2
          linarith
        · exact h1
      simp only [Pi.one_apply]
      rw [hsel1]
      simp
    · rw [Set.indicator_of_notMem hz]; exact zero_le _
  -- independence
  have hind : iIndepFun (fun (i : Fin N) (z : Fin N → ℝ) ↦ z i) μ :=
    iIndepFun_pi (X := fun _ x ↦ x) (fun _ ↦ measurable_id.aemeasurable)
  have hXY : IndepFun X Y μ :=
    hind.indepFun_finset_sum_of_notMem (fun i ↦ measurable_pi_apply i)
      (exampleLast_notMem hN1)
  have hmul : μ E = μ (X ⁻¹' Set.Iic 0) * μ (Y ⁻¹' Set.Ioi 1) :=
    hXY.measure_inter_preimage_eq_mul _ _ measurableSet_Iic measurableSet_Ioi
  -- the Gaussian tail
  have hYlaw : μ (Y ⁻¹' Set.Ioi 1) = gaussianReal 0 1 (Set.Ioi 1) :=
    (measurePreserving_eval (fun _ : Fin N ↦ gaussianReal 0 1) last).measure_preimage
      measurableSet_Ioi.nullMeasurableSet
  -- symmetry: `P(X ≤ 0) ≥ 1/2`
  have hneg : MeasurePreserving (fun (z : Fin N → ℝ) (i : Fin N) ↦ -z i) μ μ := by
    refine measurePreserving_pi (α := fun _ : Fin N ↦ ℝ) (β := fun _ : Fin N ↦ ℝ)
      (f := fun _ x ↦ -x) (fun _ ↦ gaussianReal 0 1) (fun _ ↦ gaussianReal 0 1)
      (fun _ ↦ ⟨measurable_neg, ?_⟩)
    rw [gaussianReal_map_neg, neg_zero]
  have hsymm : μ (X ⁻¹' Set.Ici 0) = μ (X ⁻¹' Set.Iic 0) := by
    have hpre : X ⁻¹' Set.Ici 0 =
        (fun (z : Fin N → ℝ) (i : Fin N) ↦ -z i) ⁻¹' (X ⁻¹' Set.Iic 0) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic, hXapp, Finset.sum_neg_distrib]
      constructor <;> intro h <;> linarith
    rw [hpre, hneg.measure_preimage (hXm measurableSet_Iic).nullMeasurableSet]
  have hhalf : 1 ≤ μ (X ⁻¹' Set.Iic 0) * 2 := by
    have hcov : (Set.univ : Set (Fin N → ℝ)) ⊆ X ⁻¹' Set.Iic 0 ∪ X ⁻¹' Set.Ici 0 := by
      intro z _
      simp only [Set.mem_union, Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
      exact le_total _ _
    calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
      _ ≤ μ (X ⁻¹' Set.Iic 0) + μ (X ⁻¹' Set.Ici 0) :=
        (measure_mono hcov).trans (measure_union_le _ _)
      _ = μ (X ⁻¹' Set.Iic 0) * 2 := by rw [hsymm, mul_two]
  have hhalf' : (2 : ℝ≥0∞)⁻¹ ≤ μ (X ⁻¹' Set.Iic 0) := by
    rw [← one_div]
    exact ENNReal.div_le_of_le_mul hhalf
  -- assemble
  have hconst : ENNReal.ofReal 0.075 = (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal 0.15 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc ENNReal.ofReal 0.075 = (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal 0.15 := hconst
    _ ≤ μ (X ⁻¹' Set.Iic 0) * μ (Y ⁻¹' Set.Ioi 1) := by
      rw [hYlaw]
      exact mul_le_mul' hhalf' StatisticalRL.Probability.gaussianReal_Ioi_one_ge
    _ = μ E := hmul.symm
    _ = ∫⁻ z, E.indicator 1 z ∂μ := (lintegral_indicator_one hEm).symm
    _ ≤ _ := lintegral_mono hpt

end StatisticalRL.OfflineRL
