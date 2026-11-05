import Formalization.OfflineRL.OptimalArmCountEvent
import Formalization.OfflineRL.LCBZeroCountRepair
import Formalization.OfflineRL.SafeLCBConfidence

/-! Actual-law regret bound for the commented zero-count fallback LCB.

Source: `thm:MAB_LCB_upper`, `chapters/offlineRL.tex:456–471`, proof `:524–578`;
data law `:243–260`; algorithm `:400–443`, with commented fallback `:429–430`.
This result applies to the fallback variant only. The active printed pseudocode does
not define the zero-count branch; see `docs/SOURCE-ISSUES.md#C18`.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL

variable {Arm : Type*} [Fintype Arm] [DecidableEq Arm]

/-- On a positive count, the safe sandwich follows from the sampled-arm confidence bound. -/
theorem conf_of_safe {N : ℕ} (r : Arm → ℝ) (a : Fin N → Arm) (z : Fin N → ℝ) (δ : ℝ)
    (h : ∀ b, safeMean r a z b - safeRadius a δ b ≤ r b ∧ r b ≤ safeMean r a z b + safeRadius a δ b)
    (b : Arm) (hb : 0 < armCount a b) :
    |empiricalArmMean r a z b - r b| ≤ armRadius (Fintype.card Arm) δ (armCount a b) := by
  have h' := h b
  unfold safeMean safeRadius at h'
  rw [if_neg (by omega), if_neg (by omega)] at h'
  rw [abs_le]
  constructor <;> linarith [h'.1, h'.2]

/-- `2 b⋆ ≤ 4 √((1/d⋆) log(4A/δ)/N)` on the count event. -/
theorem two_radius_le {N : ℕ} (n : ℕ) (dStar δ : ℝ) (A : ℕ) (hA : 1 ≤ A) (hd : 0 < dStar)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hNpos : 0 < N) (hcount : (N : ℝ) * dStar / 2 ≤ n) :
    2 * armRadius A δ n ≤ 4 * Real.sqrt ((1 / dStar) * Real.log (4 * A / δ) / N) := by
  set L := Real.log (4 * (A : ℝ) / δ) with hL
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hpos : (0 : ℝ) < N * dStar / 2 := by positivity
  have hbound : armRadius A δ n ≤ Real.sqrt (4 * ((1 / dStar) * L / N)) := by
    rw [armRadius]
    apply Real.sqrt_le_sqrt
    calc 2 * L / (n : ℝ) ≤ 2 * L / ((N : ℝ) * dStar / 2) :=
          div_le_div_of_nonneg_left (by positivity) hpos hcount
      _ = 4 * ((1 / dStar) * L / N) := by field_simp; ring
  have hsq : Real.sqrt (4 * ((1 / dStar) * L / N)) = 2 * Real.sqrt ((1 / dStar) * L / N) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsq] at hbound
  linarith

/-- **Actual-law regret theorem for the commented zero-count fallback LCB.** -/
theorem lcbFallback_regret_probability [MeasurableSpace Arm] [MeasurableSingletonClass Arm]
    (d : Measure Arm) [IsProbabilityMeasure d] (r : Arm → ℝ) (hr0 : ∀ b, 0 ≤ r b)
    (hr1 : ∀ b, r b ≤ 1) (aStar : Arm) (hopt : ∀ b, r b ≤ r aStar)
    (hd : 0 < d.real {aStar}) (N : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hN : 8 * (1 / d.real {aStar}) * Real.log (2 / δ) ≤ N) :
    1 - δ ≤
      ((Measure.pi fun _ : Fin N => d).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)).real
        {ω : (Fin N → Arm) × (Fin N → ℝ) | ∀ aL : Arm,
          (∀ b, lcbFallback r ω.1 ω.2 δ b ≤ lcbFallback r ω.1 ω.2 δ aL) →
          r aStar - r aL ≤
            4 * Real.sqrt ((1 / d.real {aStar}) *
              Real.log (4 * Fintype.card Arm / δ) / N)} := by
  classical
  set S := Measure.pi fun _ : Fin N => d with hS
  set G := Measure.pi fun _ : Fin N => gaussianReal 0 1 with hG
  set μ := S.prod G with hμ
  set p := d.real {aStar} with hp
  have hlog2 : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
    exact_mod_cast this
  have hA : 1 ≤ Fintype.card Arm := Fintype.card_pos_iff.mpr ⟨aStar⟩
  -- Event 1: the safe all-arm sandwich.
  set Good1 := {ω : (Fin N → Arm) × (Fin N → ℝ) | ∀ b,
      safeMean r ω.1 ω.2 b - safeRadius ω.1 δ b ≤ r b ∧
        r b ≤ safeMean r ω.1 ω.2 b + safeRadius ω.1 δ b}
  have h1 : 1 - δ / 2 ≤ μ.real Good1 := safe_lcb_confidence d r hr0 hr1 N δ hδ hδ1
  -- Event 2: the optimal-arm count on the action marginal.
  set E := {x : Fin N → Arm | (N : ℝ) * p / 2 ≤ visitCount (fun i (y : Fin N → Arm) => y i) aStar x}
  have hE : 1 - δ / 2 ≤ S.real E := by
    have hind : iIndepFun (fun (i : Fin N) (y : Fin N → Arm) => y i) S :=
      iIndepFun_pi (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
    have hlaw : ∀ i : Fin N, HasLaw (fun y : Fin N → Arm => y i) d S :=
      fun i => (measurePreserving_eval (fun _ : Fin N => d) i).hasLaw
    exact optimalArm_count_event S d N (fun i y => y i) (fun i => measurable_pi_apply i)
      hind hlaw aStar hd δ hδ hδ1 hN
  have hEm : MeasurableSet E := (Set.to_countable E).measurableSet
  have hEc : S.real Eᶜ ≤ δ / 2 := by
    rw [measureReal_compl hEm, probReal_univ]
    linarith
  set Good2 := E ×ˢ (Set.univ : Set (Fin N → ℝ))
  have h2c : μ.real Good2ᶜ ≤ δ / 2 := by
    have : Good2ᶜ = Eᶜ ×ˢ (Set.univ : Set (Fin N → ℝ)) := by
      ext ω; simp [Good2]
    rw [this, measureReal_def, hμ, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def]
    exact hEc
  -- Combine without measurability of Good1.
  have hsplit : Good1 ⊆ (Good1 ∩ Good2) ∪ Good2ᶜ := by
    intro ω hω
    by_cases h : ω ∈ Good2
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr h
  have hinter : 1 - δ ≤ μ.real (Good1 ∩ Good2) := by
    have := (measureReal_mono hsplit (measure_ne_top μ _)).trans (measureReal_union_le _ _)
    linarith
  refine hinter.trans (measureReal_mono ?_ (measure_ne_top μ _))
  rintro ω ⟨hω1, hω2⟩ aL hsel
  have hcount : (N : ℝ) * p / 2 ≤ armCount ω.1 aStar := by
    have h := (Set.mem_prod.mp hω2).1
    simp only [E, Set.mem_setOf_eq] at h
    have hvc : (visitCount (fun i (y : Fin N → Arm) => y i) aStar ω.1 : ℕ) = armCount ω.1 aStar := by
      unfold visitCount armCount
      rw [Finset.card_filter]
    rw [hvc] at h
    exact h
  have hNp : (0 : ℝ) < N * p / 2 := by
    have : (0 : ℝ) < N := by exact_mod_cast hNpos
    positivity
  have hposc : 0 < armCount ω.1 aStar := by
    have : (0 : ℝ) < armCount ω.1 aStar := lt_of_lt_of_le hNp hcount
    exact_mod_cast this
  have hreg := lcbFallback_regret r hr0 ω.1 ω.2 δ (conf_of_safe r ω.1 ω.2 δ hω1) aStar hposc aL hsel
  have hrad := two_radius_le (armCount ω.1 aStar) p δ (Fintype.card Arm) hA hd hδ hδ1 hNpos hcount
  linarith

end StatisticalRL.OfflineRL
