import Formalization.OfflineRL.FiniteVILCB.Links2
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Ingredients of the final assembly

* data transfer: an event of iid data has the probability of its pull-back to the analysis space;
* the trimming event follows from E1 (aux upper) and E2 (main lower);
* the `H = 1` case holds surely;
* logarithmic facts for `ι = log(16HK/δ)`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance prDecS : DecidableEq S := Classical.decEq S
noncomputable local instance prDecA : DecidableEq A := Classical.decEq A
local instance prMS : MeasurableSpace S := ⊤
local instance prMA : MeasurableSpace A := ⊤
local instance prMT (H : ℕ) : MeasurableSpace (Traj S A H) := ⊤

variable {H K : ℕ}

/-- The analysis measure on `Ω_T`. -/
noncomputable def analysisMeasure (E : Fin H → EnvironmentStage S A)
    (πb : Fin H → StationaryPolicy S A) (ρb : FiniteDistribution S) (K : ℕ) :
    Measure ((Fin (K / 2) → Traj S A H) ×
      ((Fin (K - K / 2) → S) × ActTape S A H (K - K / 2) × NxtTape S A H (K - K / 2))) :=
  (Measure.pi fun _ : Fin (K / 2) ↦ trajMeasure E πb ρb).prod (tapeMeasure E πb ρb (K - K / 2))

instance analysisMeasure_prob (E : Fin H → EnvironmentStage S A)
    (πb : Fin H → StationaryPolicy S A) (ρb : FiniteDistribution S) (K : ℕ) :
    IsProbabilityMeasure (analysisMeasure E πb ρb K) := by
  unfold analysisMeasure; infer_instance

/-- **Data transfer** (gap G3: one product space). -/
theorem data_transfer (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb : FiniteDistribution S) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → Fin K → Traj S A H) (hX : Measurable X)
    (hind : iIndepFun (fun k ω ↦ X ω k) μ)
    (hlaw : ∀ k, μ.map (fun ω ↦ X ω k) = trajMeasure E πb ρb) (P : (Fin K → Traj S A H) → Prop) :
    μ.real {ω | P (X ω)} = (analysisMeasure E πb ρb K).real
      {ω | P (joinData ω.1 (buildMain ω.2.1 ω.2.2.1 ω.2.2.2))} := by
  have hmeas : ∀ k, AEMeasurable (fun ω ↦ X ω k) μ :=
    fun k ↦ ((measurable_pi_apply k).comp hX).aemeasurable
  have hpi : μ.map X = Measure.pi (fun _ : Fin K ↦ trajMeasure E πb ρb) := by
    have := (iIndepFun_iff_map_fun_eq_pi_map hmeas).mp hind
    rw [show (fun ω k ↦ X ω k) = X from rfl] at this
    rw [this]
    congr 1
    funext k
    exact hlaw k
  have hset : {ω | P (X ω)} = X ⁻¹' {x | P x} := rfl
  rw [hset, ← map_measureReal_apply hX (Set.to_countable _).measurableSet, hpi, pi_eq_map_join,
    map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    ← tapeMeasure_map_buildMain E πb ρb (K - K / 2)]
  have hpm := Measure.map_prod_map (Measure.pi fun _ : Fin (K / 2) ↦ trajMeasure E πb ρb)
    (tapeMeasure E πb ρb (K - K / 2)) measurable_id
    (measurable_of_countable (fun t : (Fin (K - K / 2) → S) × ActTape S A H (K - K / 2) ×
      NxtTape S A H (K - K / 2) ↦ buildMain t.1 t.2.1 t.2.2))
  rw [Measure.map_id] at hpm
  rw [hpm, map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  rfl

/-- **E1 ∧ E2 ⇒ E** (trimmed counts never exceed the main visits). -/
theorem trim_of_events (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb : FiniteDistribution S) (ι : ℝ) (hι : 0 ≤ ι) (aux : Fin (K / 2) → Traj S A H)
    (ι₀ : Fin (K - K / 2) → S) (α : ActTape S A H (K - K / 2)) (β : NxtTape S A H (K - K / 2))
    (hE1 : UpperEv E πb ρb ι aux) (hE2 : LowerEv E πb ρb ι (buildMain ι₀ α β)) :
    TrimEvent (auxTrim ι aux) ι₀ α β := by
  intro h s
  set p := stateMarg E πb ρb h.castSucc s
  have hp0 : 0 ≤ p := stateMarg_nonneg _ _ _ _ _
  have hvis : (Finset.univ.filter (fun j ↦ stateVec ι₀ α β h.val j = s)).card =
      visits (buildMain ι₀ α β) h s := rfl
  rw [hvis, auxTrim_eq]
  set X := visits aux h s
  unfold trim
  split_ifs with hX
  · have h1 := hE1 h s
    have hXle : (X : ℝ) ≤ 2 * ((K / 2 : ℕ) : ℝ) * p := by
      rcases le_total (2 * ((K / 2 : ℕ) : ℝ) * p) (16 * ι) with h | h
      · rw [max_eq_right h] at h1; linarith
      · rw [max_eq_left h] at h1; exact h1
    have hnn : ((K / 2 : ℕ) : ℝ) ≤ ((K - K / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hμ : ((K / 2 : ℕ) : ℝ) * p ≤ ((K - K / 2 : ℕ) : ℝ) * p :=
      mul_le_mul_of_nonneg_right hnn hp0
    have h2 := hE2 h s (by linarith)
    have : ((X / 4 : ℕ) : ℝ) ≤ visits (buildMain ι₀ α β) h s := by
      have := (Nat.cast_div_le : ((X / 4 : ℕ) : ℝ) ≤ X / 4)
      linarith
    exact_mod_cast this
  · exact Nat.zero_le _

theorem bonus_zero (cb ι : ℝ) (n : ℕ) (q : FiniteDistribution S) :
    bonus cb ι H n q (fun _ ↦ 0) = 0 := by
  have hv : vmax (fun _ : S ↦ (0 : ℝ)) = 0 := by
    unfold vmax; exact Finset.sup'_const _ _
  unfold bonus
  rw [hv]
  split_ifs
  · rfl
  · exact min_eq_right (le_max_of_le_left (Real.sqrt_nonneg _))

/-- **`H = 1`.** Every greedy policy is optimal, surely. -/
theorem gap_H_one (E : Fin 1 → EnvironmentStage S A) (ρ : FiniteDistribution S) (cb δ ε : ℝ)
    (hε : 0 ≤ ε) {K : ℕ} (x : Fin K → Traj S A 1) (πhat : Fin 1 → S → A)
    (hg : ∀ h s a, qhat cb δ (fun h ↦ (E h).reward) x h s a ≤
      qhat cb δ (fun h ↦ (E h).reward) x h s (πhat h s)) :
    ρ.expectation (optV E 0) - ρ.expectation (polV E πhat 0) ≤ ε := by
  have hq : ∀ s a, qhat cb δ (fun h ↦ (E h).reward) x 0 s a = (E 0).reward s a := by
    intro s a
    unfold qhat qhatGen
    simp only
    have hv : vhatGen cb (iota 1 K δ) (fun h ↦ (E h).reward)
        (keptCount (trimCount (iota 1 K δ) x) x)
        (fun h s a ↦ normRow (keptNext (trimCount (iota 1 K δ) x) x h s a)) ((0 : Fin 1).val + 1) =
        fun _ ↦ 0 := by
      funext t
      exact vhatGen_of_ge _ _ _ _ _ (le_refl 1) t
    rw [hv, bonus_zero]
    simp only [FiniteDistribution.expectation_const, add_zero, sub_zero]
    exact max_eq_left ((E 0).reward_nonneg s a)
  have hopt : ∀ s, optV E 0 s ≤ polV E πhat 0 s := by
    intro s
    have h1 := optV_of_lt E 0 s
    have h2 := polV_of_lt E πhat 0 s
    simp only [Fin.val_zero] at h1 h2
    rw [h1, h2]
    have hz1 : optV E 1 = fun _ ↦ 0 := funext fun t ↦ optV_of_ge E (le_refl 1) t
    have hz2 : polV E πhat 1 = fun _ ↦ 0 := funext fun t ↦ polV_of_ge E πhat (le_refl 1) t
    simp only [zero_add, hz1, hz2, FiniteDistribution.expectation_const, add_zero]
    apply actionMaximum_le
    intro a
    have := hg 0 s a
    rwa [hq, hq] at this
  have : ρ.expectation (optV E 0) - ρ.expectation (polV E πhat 0) ≤ 0 := by
    rw [← FiniteDistribution.expectation_sub]
    exact ρ.expectation_le_const fun s ↦ by linarith [hopt s]
  linarith

/-! ## Logarithmic facts -/

theorem one_le_iota (hH : 1 ≤ H) (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 ≤ iota H K δ := by
  unfold iota
  have hHK : (1 : ℝ) ≤ (H : ℝ) * K := by
    have : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have h16 : (16 : ℝ) ≤ 16 * H * K / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem iota_le_five_log (hHK : 2 ≤ H * K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    iota H K δ ≤ 5 * Real.log (K * H / δ) := by
  unfold iota
  have hHK' : (2 : ℝ) ≤ (H : ℝ) * K := by exact_mod_cast hHK
  have hx : (2 : ℝ) ≤ K * H / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have heq : 16 * (H : ℝ) * K / δ = 16 * (K * H / δ) := by ring
  rw [heq, Real.log_mul (by norm_num) (by linarith)]
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h2 : Real.log 2 ≤ Real.log (K * H / δ) := Real.log_le_log (by norm_num) hx
  linarith

theorem exp_neg_iota (hH : 1 ≤ H) (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-iota H K δ) = δ / (16 * H * K) := by
  unfold iota
  have hpos : 0 < 16 * (H : ℝ) * K / δ := by
    have : (0 : ℝ) < H := by exact_mod_cast hH
    have : (0 : ℝ) < K := by exact_mod_cast hK
    positivity
  rw [Real.exp_neg, Real.exp_log hpos]
  field_simp

end StatisticalRL.FiniteVILCB
