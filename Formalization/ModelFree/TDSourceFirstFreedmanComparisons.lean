import Formalization.ModelFree.TDSourceFreedmanScheduleCaps
import Formalization.ModelFree.TDSourceFreedmanLogComparison
import Formalization.ModelFree.TDSourceFreedmanBudgetSmallness
import Formalization.ModelFree.TDSourceFreedmanDyadicCutoff
import Formalization.ModelFree.TDSourceRateFiniteExtension
import Formalization.ModelFree.TDSourceFirstFreedmanUnion

/-! Derive the comparison inputs for the all-state first-Freedman bound from
the source rate schedule and sample budget. The source schedule's large-time
condition, terminal eligibility, and budget conditions remain explicit in the
relevant theorem binders. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The source deterministic variance floor has the advertised `H²` reduction.
This is the precise use of the squared dyadic cutoff, rather than merely
`H ≤ 2^K`. -/
theorem tdSource_firstFreedman_floor_le
    (γ : ℝ) (T : ℕ) (hT : 2 ≤ T)
    (hγhalf : 1 / 2 ≤ γ) (hγ1 : γ < 1) :
    (3 * Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 4 * T)) /
        (2 : ℝ) ^ tdSourceFreedmanLevel γ ≤
      3 * Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 2 * T) := by
  have hgap : 0 < 1 - γ := by linarith
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hHsq := tdSourceFreedmanLevel_covers_effectiveHorizon_sq γ hγhalf hγ1
  have hHsq' : (1 - γ)⁻¹ ^ 2 ≤
      (2 : ℝ) ^ tdSourceFreedmanLevel γ := by
    simpa [one_div] using hHsq
  have hlog0 : 0 ≤ Real.log (T : ℝ) :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < T))).le
  have hnum : 0 ≤ 3 * Real.log (T : ℝ) ^ 3 := by positivity
  have hden₂ : 0 < (1 - γ) ^ 2 * T := by positivity
  have hdenK : 0 < (2 : ℝ) ^ tdSourceFreedmanLevel γ := by positivity
  rw [div_le_div_iff₀ hdenK hden₂]
  have hmul := mul_le_mul_of_nonneg_left hHsq' hnum
  have hrecip : (1 - γ)⁻¹ ^ 2 = 1 / (1 - γ) ^ 2 := by
    field_simp [ne_of_gt hgap]
  rw [hrecip] at hmul
  field_simp [ne_of_gt hgap, ne_of_gt hTpos] at hmul ⊢
  nlinarith [hmul]

/-- Source comparisons for the all-state first-Freedman union. The actual
schedule's weight envelope supplies `A=barEta`; its source increment and
variance scales are `B=4γ log³(T)/((1−γ)²T)` and
`σ²=3 log³(T)/((1−γ)^4T)`. The source log comparison supplies
`L=3log(S T/δ)`. The source schedule/large-time and budget hypotheses are
retained explicitly. -/
theorem tdSource_firstFreedman_comparisons
    (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (c₁ c₂ c₃ ε δ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcprod : c₁ * c₂ ≤ 1 / 8)
    (hc₃ : 384 ≤ c₃) (hT : 2 ≤ T)
    (hγhalf : 1 / 2 ≤ M.discount)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hεmax : ε ≤ M.effectiveHorizon)
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ))
    (hlarge : Real.log (T : ℝ) ^ 2 ≤
        c₁ * (1 - M.discount) * T)
    (hSched : TDStepSizeSchedule M.discount c₁ c₂ T η)
    (ht : t ≤ T)
    (htime : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t) :
    let K := tdSourceFreedmanLevel M.discount
    let A := tdSourceBarEta M.discount T
    let Bsrc := 4 * M.discount * Real.log (T : ℝ) ^ 3 /
      ((1 - M.discount) ^ 2 * T)
    let σsrcSq := 3 * Real.log (T : ℝ) ^ 3 /
      ((1 - M.discount) ^ 4 * T)
    let L := 3 * Real.log ((Fintype.card State : ℝ) * T / δ)
    0 < K ∧ 0 ≤ A ∧
      (∀ k, 1 ≤ k → k ≤ t →
        tdRateWeight M.discount η t k ≤ A) ∧
      (∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) ∧
      2 * M.discount * M.effectiveHorizon * A ≤ Bsrc ∧
      M.discount ^ 2 * M.effectiveHorizon ^ 3 * A ≤ σsrcSq ∧
      Real.log (2 * (K : ℝ) /
        (δ / (2 * (Fintype.card State : ℝ) * T))) ≤ L := by
  dsimp
  have hγ1 : M.discount < 1 := M.discount_lt_one
  have hgap : 0 < 1 - M.discount := sub_pos.mpr hγ1
  have hlogTpos : 0 < Real.log (T : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  let S : ℝ := Fintype.card State
  let K : ℕ := tdSourceFreedmanLevel M.discount
  let A : ℝ := tdSourceBarEta M.discount T
  let Bsrc : ℝ := 4 * M.discount * Real.log (T : ℝ) ^ 3 /
    ((1 - M.discount) ^ 2 * T)
  let σsrcSq : ℝ := 3 * Real.log (T : ℝ) ^ 3 /
    ((1 - M.discount) ^ 4 * T)
  let L : ℝ := 3 * Real.log (S * T / δ)
  have hS : 1 ≤ S := by
    dsimp [S]
    exact_mod_cast Fintype.card_pos_iff.mpr (M.state_nonempty)
  have hK : 0 < K := by
    dsimp [K, tdSourceFreedmanLevel]
    have hHge2 : 2 ≤ 1 / (1 - M.discount) := by
      rw [le_div_iff₀ hgap]
      linarith
    have hceil : 0 < Nat.ceil
        (Real.log (1 / (1 - M.discount)) / Real.log 2) := by
      apply Nat.ceil_pos.mpr
      apply div_pos
      · exact Real.log_pos (lt_of_lt_of_le (by norm_num) hHge2)
      · exact Real.log_pos (by norm_num)
    omega
  have hlogBound := tdSourceBudget_logComparison M.discount c₃ ε δ S T hT
    hγhalf hγ1 hc₃ hδ hδ1 hS hε hεmax hBudget
  have hlogEq :
      2 * (K : ℝ) / (δ / (2 * S * T)) = 4 * S * T * K / δ := by
    dsimp [K, S]
    field_simp [ne_of_gt hδ]
    ring
  have hlogCompare : Real.log
      (2 * (K : ℝ) / (δ / (2 * S * T))) ≤ L := by
    rw [hlogEq]
    simpa [L, S, mul_assoc, mul_left_comm, mul_comm] using hlogBound
  have hcaps := tdSource_freedman_schedule_weight_caps
    M.discount c₁ c₂ T t η hT hγhalf hγ1 hc₁ hc₂ hcprod hlarge hSched ht htime
  have hfinite : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1 :=
    tdSourceRateSchedule_unit_interval M.discount c₁ c₂ T hT hγ1 hc₁ hc₂ η hSched
  have hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1 := by
    intro i hi1 hit
    exact hfinite i hi1 (hit.trans ht)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, tdSourceBarEta]
    exact div_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg hlogTpos.le 3)) (by positivity)
  have hweight : ∀ k, 1 ≤ k → k ≤ t →
      tdRateWeight M.discount η t k ≤ A := by
    intro k hk1 hkt
    simpa [A, tdSourceBarEta] using hcaps.1 k hk1 hkt
  have hB : 2 * M.discount * M.effectiveHorizon * A ≤ Bsrc := by
    dsimp [A, Bsrc, tdSourceBarEta, DiscountedMDP.effectiveHorizon]
    field_simp [ne_of_gt hgap, ne_of_gt hTpos]
    norm_num
  have hσ : M.discount ^ 2 * M.effectiveHorizon ^ 3 * A ≤ σsrcSq := by
    dsimp [A, σsrcSq, tdSourceBarEta, DiscountedMDP.effectiveHorizon]
    field_simp [ne_of_gt hgap, ne_of_gt hTpos]
    have hγsq : M.discount ^ 2 ≤ 1 := by nlinarith
    nlinarith [hγsq]
  exact ⟨hK, hA_nonneg, hweight, hη, hB, hσ, hlogCompare⟩

end StatisticalRL.TemporalDifference
