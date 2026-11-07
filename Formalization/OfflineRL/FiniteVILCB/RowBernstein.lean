import Formalization.OfflineRL.FiniteVILCB.RowEvents

/-!
# Event E5 for fixed trimmed counts and action tapes

Conditional on the trimmed counts `m` and the action tapes `α` (fixed here; they are independent
of the next-state tapes in the product tape law), the row event holds for each visited triple
with probability `> 1 - 8δ'`, and for all visited triples simultaneously with probability at
least `1 - 8δ' · #{visited triples}` (gap G2 of the plan check: this is the per-atom statement;
integration over the atoms is in the assembly).
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance rowBDecS : DecidableEq S := Classical.decEq S
noncomputable local instance rowBDecA : DecidableEq A := Classical.decEq A
local instance rowBMS : MeasurableSpace S := ⊤
local instance rowBMRow : MeasurableSpace (FiniteDistribution S) := ⊤

variable {H n : ℕ}

/-- The ideal `V̂_{h+1}` depends only on the next-state tapes at stages `> h`. -/
theorem idealV_factors (cb ι : ℝ) (r : Fin H → S → A → ℝ) (m : Fin H → S → ℕ)
    (α : ActTape S A H n) (β : NxtTape S A H n) (h : Fin H) (x : S) :
    idealV cb ι r m α β (h.val + 1) = idealV cb ι r m α
      (FiniteHorizonGenerative.completeFutureData h n x
        (FiniteHorizonGenerative.futureData h n β)) (h.val + 1) := by
  unfold idealV
  refine vhatGen_congr cb ι r _ _ _ _ (h.val + 1) ?_ (h.val + 1) le_rfl
  intro h' hh'
  refine ⟨rfl, ?_⟩
  have hlt : h < h' := by
    rw [Fin.lt_def]
    omega
  funext s a
  unfold idealRow idealNext
  congr 1
  funext s'
  congr 1
  ext i
  simp [FiniteHorizonGenerative.completeFutureData, FiniteHorizonGenerative.futureData, hlt]

/-- **Row event (Lemma 6.18 at `γ = 0` on `V̂_{h+1}/H`).** -/
theorem row_event (E : Fin H → EnvironmentStage S A) (cb ι : ℝ) (hcb : 0 ≤ cb) (hι : 0 ≤ ι)
    (r : Fin H → S → A → ℝ) (hr0 : ∀ h s a, 0 ≤ r h s a) (hr1 : ∀ h s a, r h s a ≤ 1)
    (δ' : ℝ) (hδ : 0 < δ') (hδ8 : δ' < 1 / 8)
    (m : Fin H → S → ℕ) (α : ActTape S A H n) (h : Fin H) (s : S) (a : A)
    (hpos : 0 < idealCount m α h s a) :
    1 - 8 * δ' < (FiniteHorizonGenerative.samplingLaw E n).real {β |
      RowGood H (Real.log (1 / δ')) (idealCount m α h s a) (idealRow m α β h s a)
        ((E h).transition s a) (idealV cb ι r m α β (h.val + 1))} := by
  classical
  set μ := FiniteHorizonGenerative.samplingLaw E n with hμ
  set N := idealCount m α h s a with hNdef
  have hN : N ≤ n := idealCount_le m α h s a
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt h.isLt)
  set P := (E h).transition s a with hP
  let draw : NxtTape S A H n → Fin N → S := tapeDraw hN h s a
  have hdraw : Measurable draw := measurable_of_countable _
  have hinj : Function.Injective (fun i : Fin N ↦ ((h, s, a), Fin.castLE hN i)) := by
    intro i j he
    exact Fin.castLE_injective hN (congrArg Prod.snd he)
  have hlaw : μ.map draw = P.sampleMeasure N := by
    rw [hμ]
    unfold FiniteHorizonGenerative.samplingLaw FiniteDistribution.sampleMeasure
    exact OfflineRL.StackProjection.pi_map_comp_injective _ _ hinj
  let x0 : S := Classical.arbitrary S
  let F : FiniteHorizonGenerative.FutureCode (State := S) (Action := A) h n → S → ℝ :=
    fun c t ↦ idealV cb ι r m α (FiniteHorizonGenerative.completeFutureData h n x0 c)
      (h.val + 1) t / H
  let V : NxtTape S A H n → S → ℝ := fun β t ↦ idealV cb ι r m α β (h.val + 1) t / H
  have hVF : V = fun β ↦ F (FiniteHorizonGenerative.futureData h n β) := by
    funext β t
    simp only [V, F]
    rw [idealV_factors cb ι r m α β h x0]
  have hV : Measurable V := measurable_of_countable _
  have hindep : IndepFun V (fun β ↦ FiniteDistribution.empiricalRow N hpos (draw β)) μ := by
    have hi := FiniteHorizonGenerative.futureStatistic_indep_row E n h s a F
    have hm : Measurable (fun row : Fin n → S ↦
        FiniteDistribution.empiricalRow N hpos (fun i ↦ row (Fin.castLE hN i))) :=
      measurable_of_countable _
    rw [hVF]
    exact hi.comp measurable_id hm
  have hrange : ∀ β t, 0 ≤ V β t ∧ V β t ≤ 1 / (1 - 0) := by
    intro β t
    have hb := vhatGen_bounds cb ι r (idealCount m α) (idealRow m α β) hcb hι hr0 hr1
      (h.val + 1) t
    have hle : ((H - (h.val + 1) : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le _ _
    refine ⟨div_nonneg hb.1 hHpos.le, ?_⟩
    rw [sub_zero, div_one, div_le_one hHpos]
    exact hb.2.trans hle
  have hB := OfflineVILCB.BernsteinInfinite.bernsteinInfinite_fixedRow μ P 0 (by norm_num) δ' hδ
    hδ8 N hpos draw hdraw hlaw V hV hindep hrange
  refine hB.trans_le (measureReal_mono ?_ (measure_ne_top μ _))
  intro β hβ
  simp only [Set.mem_setOf_eq] at hβ ⊢
  obtain ⟨h1, h2⟩ := hβ
  set W := idealV cb ι r m α β (h.val + 1) with hW
  set q := FiniteDistribution.empiricalRow N hpos (draw β) with hq
  have hrow : idealRow m α β h s a = q := idealRow_eq_empiricalRow m α β h s a hpos
  rw [hrow]
  have hVβ : V β = fun t ↦ W t / H := rfl
  rw [hVβ, expectation_div_const, expectation_div_const, variance_div_const] at h1
  rw [hVβ, variance_div_const, variance_div_const] at h2
  set L := Real.log (1 / δ') with hL
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
  have hsq : Real.sqrt (4 * (q.variance W / (H : ℝ) ^ 2) * L / N) =
      Real.sqrt (4 * q.variance W * L / N) / H := by
    rw [show 4 * (q.variance W / (H : ℝ) ^ 2) * L / N = (4 * q.variance W * L / N) / (H : ℝ) ^ 2 by
      field_simp, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hHpos.le]
  rw [hsq, ← sub_div, abs_div, abs_of_pos hHpos] at h1
  constructor
  · calc |q.expectation W - P.expectation W|
        = H * (|q.expectation W - P.expectation W| / H) := by field_simp
      _ ≤ H * (Real.sqrt (4 * q.variance W * L / N) / H + 5 * L / ((1 - 0) * N)) :=
          mul_le_mul_of_nonneg_left h1 hHpos.le
      _ = Real.sqrt (4 * q.variance W * L / N) + 5 * H * L / N := by field_simp; ring
  · calc q.variance W = (H : ℝ) ^ 2 * (q.variance W / (H : ℝ) ^ 2) := by field_simp
      _ ≤ (H : ℝ) ^ 2 * (2 * (P.variance W / (H : ℝ) ^ 2) + 5 * L / (3 * (1 - 0) ^ 2 * N)) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = 2 * P.variance W + 5 * (H : ℝ) ^ 2 * L / (3 * N) := by field_simp; ring

/-- Visited triples for given trimmed counts and action tapes. -/
noncomputable def visited (m : Fin H → S → ℕ) (α : ActTape S A H n) : Finset (Fin H × S × A) :=
  Finset.univ.filter (fun c ↦ 0 < idealCount m α c.1 c.2.1 c.2.2)

/-- **E5 per atom.** All visited rows are good except on a set of mass `≤ 8δ'·#visited`. -/
theorem rows_event (E : Fin H → EnvironmentStage S A) (cb ι : ℝ) (hcb : 0 ≤ cb) (hι : 0 ≤ ι)
    (r : Fin H → S → A → ℝ) (hr0 : ∀ h s a, 0 ≤ r h s a) (hr1 : ∀ h s a, r h s a ≤ 1)
    (δ' : ℝ) (hδ : 0 < δ') (hδ8 : δ' < 1 / 8)
    (m : Fin H → S → ℕ) (α : ActTape S A H n) :
    (FiniteHorizonGenerative.samplingLaw E n).real {β | ¬ ∀ h s a, 0 < idealCount m α h s a →
      RowGood H (Real.log (1 / δ')) (idealCount m α h s a) (idealRow m α β h s a)
        ((E h).transition s a) (idealV cb ι r m α β (h.val + 1))} ≤
      8 * δ' * (visited m α).card := by
  classical
  set μ := FiniteHorizonGenerative.samplingLaw E n
  let good : Fin H × S × A → Set (NxtTape S A H n) := fun c ↦ {β |
      RowGood H (Real.log (1 / δ')) (idealCount m α c.1 c.2.1 c.2.2)
        (idealRow m α β c.1 c.2.1 c.2.2) ((E c.1).transition c.2.1 c.2.2)
        (idealV cb ι r m α β (c.1.val + 1))}
  have hsub : {β | ¬ ∀ h s a, 0 < idealCount m α h s a →
      RowGood H (Real.log (1 / δ')) (idealCount m α h s a) (idealRow m α β h s a)
        ((E h).transition s a) (idealV cb ι r m α β (h.val + 1))} ⊆
      ⋃ c ∈ visited m α, (good c)ᶜ := by
    intro β hβ
    simp only [Set.mem_setOf_eq, not_forall] at hβ
    obtain ⟨h, s, a, hpos, hbad⟩ := hβ
    simp only [Set.mem_iUnion, Set.mem_compl_iff]
    exact ⟨(h, s, a), by simp [visited, hpos], hbad⟩
  refine (measureReal_mono hsub (measure_ne_top μ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  rw [mul_comm, ← nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro c hc
  have hpos : 0 < idealCount m α c.1 c.2.1 c.2.2 := by simpa [visited] using hc
  have hgood := row_event E cb ι hcb hι r hr0 hr1 δ' hδ hδ8 m α c.1 c.2.1 c.2.2 hpos
  have hmeas : MeasurableSet (good c) := (Set.to_countable _).measurableSet
  rw [measureReal_compl hmeas, probReal_univ]
  linarith

end StatisticalRL.FiniteVILCB
