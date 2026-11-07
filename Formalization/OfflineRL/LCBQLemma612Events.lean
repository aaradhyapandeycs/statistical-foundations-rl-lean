import Formalization.OfflineRL.LCBQMartingale
import Formalization.OfflineRL.LCBQPsiPhi
import Formalization.OfflineRL.SampleSplitActual
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# LCB-Q, Lemma 6.12: the probability events

`lem:lcbq-alpha-xi-psi-phi-bound`, `chapters/offlineRL.tex:2309–2324`; proof `:4786–5496`.
The lemma's proof uses several high-probability events (pessimism from Lemma 6.10, the
prefix-count event, two Freedman events and, for the omitted `φ` argument, the event that no
sample hits a poorly covered pair `(s,π⋆(s))`). Each is run at confidence `δ/5`, so that their
intersection has probability at least `1 − δ`; the extra `log 5` is absorbed using `ι ≥ 1`.

This section generalises the martingale event of Lemma 6.9 to a separate confidence `δc`
(the algorithm's `δ` still enters `H` and `b_n`).
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A]

local instance lcbqStateMeasurable612 : MeasurableSpace S := ⊤

section Conf

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)

theorem fixedLabel_event_prob_conf (hcb : 0 ≤ cb) (hδ : 0 < δ) (hδ1 : δ < 1) (δc : ℝ)
    (hδc : 0 < δc) (hδc1 : δc < 1) (s₀ : S) {T : ℕ}
    (hT : 1 ≤ T) (l : Fin T → S × A) :
    (onlineStackProductLaw (fun t => M.transition (l t).1 (l t).2)).real
      {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δc} < δc := by
  set ν := onlineStackProductLaw (fun t => M.transition (l t).1 (l t).2) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  haveI := M.action_nonempty
  haveI := M.state_nonempty
  have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos (α := S)
  have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set K : ℝ := (Fintype.card S : ℝ) * Fintype.card A * T with hK
  have hK1 : 1 ≤ K := by
    have h1 : (1 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A := by nlinarith
    nlinarith
  set δ' := δc / K with hδ'
  have hδ'0 : 0 < δ' := div_pos hδc (by linarith)
  have hδ'1 : δ' < 1 := by
    rw [hδ', div_lt_one (by linarith)]
    linarith
  have hlogeq : Real.log (2 / δ') =
      Real.log (2 * Fintype.card S * Fintype.card A * T / δc) := by
    congr 1
    rw [hδ', hK]
    field_simp
  set I : Finset ((S × A) × ℕ) := Finset.univ ×ˢ Finset.Icc 1 T with hI
  set bad : (S × A) × ℕ → Set (Fin T → S) := fun p => {y | ¬ |martSum M cb δ sel π₀ (zipData l y)
      p.1 p.2| ≤ 2 * Real.sqrt (horizon M.discount (iota S A T δ) *
        Real.log (2 / δ') / (p.2 * (1 - M.discount) ^ 2))} with hbad
  have hsub : {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δc} ⊆ ⋃ p ∈ I, bad p := by
    intro y hy
    simp only [Set.mem_setOf_eq, martingaleEvent, not_forall] at hy
    obtain ⟨s, a, n, hn1, hnT, hfail⟩ := hy
    simp only [Set.mem_iUnion, hI, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_Icc]
    refine ⟨((s, a), n), ⟨hn1, hnT⟩, ?_⟩
    simp only [hbad, Set.mem_setOf_eq, hlogeq]
    exact hfail
  have hbadp : ∀ p ∈ I, ν.real (bad p) < δ' := by
    intro p hp
    simp only [hI, Finset.mem_product, Finset.mem_Icc] at hp
    have h := fixedLabel_martSum_prob M cb δ sel π₀ hcb hδ hδ1 s₀ l p.1 p.2 hp.2.1 δ' hδ'0 hδ'1
    have hc : bad p = {y | |martSum M cb δ sel π₀ (zipData l y) p.1 p.2| ≤
        2 * Real.sqrt (horizon M.discount (iota S A T δ) * Real.log (2 / δ') /
          (p.2 * (1 - M.discount) ^ 2))}ᶜ := rfl
    rw [hc, probReal_compl_eq_one_sub ((Set.toFinite _).measurableSet)]
    linarith
  have hcard : (I.card : ℝ) = K := by
    simp only [hI, Finset.card_product, Finset.card_univ, Fintype.card_prod, Nat.card_Icc,
      Nat.add_sub_cancel, hK]
    push_cast
    ring
  have hIne : I.Nonempty := by
    obtain ⟨sa⟩ : Nonempty (S × A) := ⟨(M.state_nonempty.some, M.action_nonempty.some)⟩
    exact ⟨(sa, 1), by simp [hI]; omega⟩
  calc ν.real {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δc}
      ≤ ν.real (⋃ p ∈ I, bad p) := measureReal_mono hsub (measure_ne_top ν _)
    _ ≤ ∑ p ∈ I, ν.real (bad p) := measureReal_biUnion_finset_le I bad
    _ < ∑ _p ∈ I, δ' := Finset.sum_lt_sum_of_nonempty hIne hbadp
    _ = δc := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, hδ']
      field_simp

theorem martingaleEvent_prob_conf (hcb : 0 ≤ cb) (db : FiniteDistribution (S × A)) (T : ℕ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (δc : ℝ) (hδc : 0 < δc) (hδc1 : δc < 1) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δc < μ.real {ω | martingaleEvent M cb δ sel π₀ (X ω) δc} := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  rcases Nat.eq_zero_or_pos T with hT0 | hT
  · subst hT0
    have huniv : {ω | martingaleEvent M cb δ sel π₀ (X ω) δc} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro s a n hn hnT
      omega
    rw [huniv, probReal_univ]
    linarith
  -- the actual law of the data
  have hrow : (∑ x : (S × A) × S,
      ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) =
      (JointRow.jointRow db M.transition).rowMeasure := by
    refine Measure.ext_iff_singleton.2 fun x => ?_
    rw [Measure.finset_sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator_apply,
      Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ x)]
    unfold FiniteDistribution.rowMeasure
    rw [@PMF.toMeasure_apply_singleton _ ⊤ _ x MeasurableSpace.measurableSet_top]
    unfold FiniteDistribution.toPMF
    rw [PMF.ofFintype_apply]
    rfl
  have hlaw : μ.map X = Measure.pi (fun _ : Fin T => (JointRow.jointRow db M.transition).rowMeasure) := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (measurable_pi_apply i).comp hX |>.aemeasurable)).1 hind
    simp only [Function.comp_def] at h
    calc μ.map X = μ.map (fun ω i => X ω i) := rfl
      _ = Measure.pi (fun i => μ.map (fun ω => X ω i)) := h
      _ = _ := by
        congr 1
        funext i
        rw [hmarg i, hrow]
  set G : Set (Fin T → (S × A) × S) := {x | martingaleEvent M cb δ sel π₀ x δc} with hG
  have hGm : MeasurableSet G := (Set.toFinite G).measurableSet
  have hbad : μ.real (X ⁻¹' Gᶜ) < δc := by
    rw [← map_measureReal_apply hX hGm.compl, hlaw, pi_rowMeasure_real]
    -- regroup by labels
    set e := Equiv.arrowProdEquivProdArrow (Fin T) (fun _ => S × A) (fun _ => S) with he
    set g : (Fin T → (S × A) × S) → ℝ := fun x =>
      (∏ t, (JointRow.jointRow db M.transition).prob (x t)) * Gᶜ.indicator 1 x with hg
    have hregroup : ∑ x, g x = ∑ l : Fin T → S × A, (∏ t, db.prob (l t)) *
        (onlineStackProductLaw (fun t => M.transition (l t).1 (l t).2)).real
          {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δc} := by
      rw [← Fintype.sum_equiv e.symm (fun p => g (e.symm p)) g (fun _ => rfl),
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold onlineStackProductLaw
      rw [pi_rowMeasure_real, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [hg, he, Equiv.arrowProdEquivProdArrow_symm_apply, JointRow.jointRow,
        Finset.prod_mul_distrib]
      have hind : Gᶜ.indicator (1 : (Fin T → (S × A) × S) → ℝ)
          ((Equiv.arrowProdEquivProdArrow (Fin T) (fun _ => S × A) (fun _ => S)).symm (l, y)) =
          {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δc}.indicator 1 y := by
        simp only [Set.indicator_apply, Set.mem_compl_iff, hG, Set.mem_setOf_eq]
        rfl
      rw [hind]
      ring
    rw [hregroup]
    haveI := M.state_nonempty
    obtain ⟨s₀⟩ := M.state_nonempty
    have hw0 : ∀ l : Fin T → S × A, 0 ≤ ∏ t, db.prob (l t) :=
      fun l => Finset.prod_nonneg fun t _ => db.prob_nonneg _
    have hw1 : ∑ l : Fin T → S × A, ∏ t, db.prob (l t) = 1 := by
      rw [← Fintype.prod_sum (fun _ : Fin T => db.prob), db.sum_prob, Finset.prod_const_one]
    have hpos : ∃ l ∈ (Finset.univ : Finset (Fin T → S × A)), 0 < ∏ t, db.prob (l t) := by
      by_contra hcon
      push_neg at hcon
      have : ∑ l : Fin T → S × A, ∏ t, db.prob (l t) ≤ 0 :=
        Finset.sum_nonpos fun l hl => hcon l hl
      linarith
    calc ∑ l : Fin T → S × A, (∏ t, db.prob (l t)) *
          (onlineStackProductLaw (fun t => M.transition (l t).1 (l t).2)).real
            {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δc}
        < ∑ l : Fin T → S × A, (∏ t, db.prob (l t)) * δc := by
          apply Finset.sum_lt_sum
          · intro l _
            exact mul_le_mul_of_nonneg_left
              (fixedLabel_event_prob_conf M cb δ sel π₀ hcb hδ hδ1 δc hδc hδc1 s₀ hT l).le (hw0 l)
          · obtain ⟨l, hl, hlpos⟩ := hpos
            exact ⟨l, hl, mul_lt_mul_of_pos_left
              (fixedLabel_event_prob_conf M cb δ sel π₀ hcb hδ hδ1 δc hδc hδc1 s₀ hT l) hlpos⟩
      _ = δc := by rw [← Finset.sum_mul, hw1, one_mul]
  have hc : {ω | martingaleEvent M cb δ sel π₀ (X ω) δc} = X ⁻¹' G := rfl
  have hcompl : X ⁻¹' Gᶜ = (X ⁻¹' G)ᶜ := Set.preimage_compl
  rw [hcompl, probReal_compl_eq_one_sub (hX hGm)] at hbad
  rw [hc]
  linarith

end Conf

section Pessimism

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S)

theorem log_ten_le_three : Real.log 10 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h2 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
  norm_num at h2
  linarith

/-- On the martingale event at confidence `δ/5` and for `ι ≥ 1`, `c_b ≥ 4` still absorbs the
martingale term: `|martSum| ≤ c_b √(Hι/(n(1-γ)²))`. -/
theorem martSum_le_of_event_fifth (hcb : 4 ≤ cb) (hδ : 0 < δ) (hι : 1 ≤ iota S A T δ)
    (hE : martingaleEvent M cb δ sel π₀ data (δ / 5)) {t : ℕ} (htT : t ≤ T)
    (s : S) (a : A) (hn : 0 < (run M cb δ sel π₀ data t).count s a) :
    |martSum M cb δ sel π₀ data (s, a) ((run M cb δ sel π₀ data t).count s a)| ≤
      cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
        ((run M cb δ sel π₀ data t).count s a * (1 - M.discount) ^ 2)) := by
  have hcb0 : 0 ≤ cb := by linarith
  have hnT : (run M cb δ sel π₀ data t).count s a ≤ T := by
    rw [run_count M cb δ sel π₀ data htT]
    exact (Nat.count_le _).trans htT
  have h := hE s a _ hn hnT
  refine h.trans (radius_le_of_log_le hcb0 _ (Nat.cast_nonneg _) (by positivity) ?_)
  have hT : 1 ≤ T := by
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · subst h0; simp [iota] at hι; linarith
    · exact h0
  have hX0 : 0 < (Fintype.card S : ℝ) * Fintype.card A * T / δ := by
    have := card_SAT_ge_one M hT
    positivity
  have hL : Real.log (2 * Fintype.card S * Fintype.card A * T / (δ / 5)) =
      Real.log 10 + iota S A T δ := by
    unfold iota
    rw [show 2 * (Fintype.card S : ℝ) * Fintype.card A * T / (δ / 5) =
      10 * ((Fintype.card S : ℝ) * Fintype.card A * T / δ) by field_simp; ring]
    exact Real.log_mul (by norm_num) hX0.ne'
  rw [hL]
  have h10 := log_ten_le_three
  have hcb2 : 16 ≤ cb ^ 2 := by nlinarith
  nlinarith

theorem lowerRecursion_of_event_fifth (hcb : 4 ≤ cb) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : 1 ≤ iota S A T δ) (hE : martingaleEvent M cb δ sel π₀ data (δ / 5)) :
    lowerRecursion M cb δ sel π₀ data := by
  have hcb0 : 0 ≤ cb := by linarith
  intro t ht1 htT s a π
  have hT : 1 ≤ T := le_trans ht1 htT
  have hι0 := iota_pos M hT hδ hδ1
  have hH := horizon_pos M hT hδ hδ1
  rcases Nat.eq_zero_or_pos ((run M cb δ sel π₀ data t).count s a) with hn0 | hn
  · have hQ := run_Q_unroll M cb δ sel π₀ data htT s a
    rw [hn0, Finset.range_zero, Finset.sum_empty] at hQ
    rw [hn0, Finset.range_zero, Finset.sum_empty, mul_zero, hQ, sub_zero,
      M.trajectoryExpectedQ_eq_policyFixedPoint]
    exact (M.policyFixedPoint_bounds _ s a).1
  · have hid := error_identity M cb δ sel π₀ data hδ hδ1 htT s a hn
      (M.trajectoryExpectedValue (detPolicy π))
    rw [← trajectoryQ_eq_reward_add] at hid
    have hm := martSum_le_of_event_fifth M cb δ sel π₀ data hcb hδ hι hE htT s a hn
    have hp := (penalty_sum_bounds hcb0 M.discount_lt_one hι0.le hH hn).1
    have hm' := (abs_le.mp hm).2
    rw [hid]
    linarith

/-- Pessimism `V_u ≤ V⋆` for all `u ≤ T` on the martingale event at confidence `δ/5`. -/
theorem pess_of_event_fifth (hcb : 4 ≤ cb) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : 1 ≤ iota S A T δ) (hE : martingaleEvent M cb δ sel π₀ data (δ / 5)) :
    ∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤ optValue M s :=
  (run_le_opt_of_lowerRecursion M cb δ sel π₀ data hδ hδ1
    (lowerRecursion_of_event_fifth M cb δ sel π₀ data hcb hδ hδ1 hι hE)).1

end Pessimism

section Counts

variable (M : DiscountedMDP S A)

theorem log_five_le_two : Real.log 5 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h2 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h.le 2
  norm_num at h2
  linarith

/-- The iid data law: `μ.map X` is the `T`-fold product of the joint row law. -/
theorem iid_map_eq_pi (db : FiniteDistribution (S × A)) {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      μ.map X = Measure.pi (fun _ : Fin T => (JointRow.jointRow db M.transition).rowMeasure) := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  have hrow : (∑ x : (S × A) × S,
      ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) =
      (JointRow.jointRow db M.transition).rowMeasure := by
    refine Measure.ext_iff_singleton.2 fun x => ?_
    rw [Measure.finset_sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator_apply,
      Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ x)]
    unfold FiniteDistribution.rowMeasure
    rw [@PMF.toMeasure_apply_singleton _ ⊤ _ x MeasurableSpace.measurableSet_top]
    unfold FiniteDistribution.toPMF
    rw [PMF.ofFintype_apply]
    rfl
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).comp hX |>.aemeasurable)).1 hind
  simp only [Function.comp_def] at h
  calc μ.map X = μ.map (fun ω i => X ω i) := rfl
    _ = Measure.pi (fun i => μ.map (fun ω => X ω i)) := h
    _ = _ := by
      congr 1
      funext i
      rw [hmarg i, hrow]

theorem count_eq_sum_fin {T : ℕ} (data : Fin T → (S × A) × S) (sa : S × A) {t : ℕ}
    (ht : t ≤ T) :
    (Nat.count (visitPred data sa) t : ℝ) =
      ∑ i : Fin t, (if (data (Fin.castLE ht i)).1 = sa then (1 : ℝ) else 0) := by
  rw [Nat.count_eq_card_filter_range, Finset.card_filter, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff : visitPred data sa i.val ↔ (data (Fin.castLE ht i)).1 = sa := by
    constructor
    · rintro ⟨h, he⟩; exact he
    · intro he; exact ⟨lt_of_lt_of_le i.isLt ht, he⟩
  by_cases h : visitPred data sa i.val
  · rw [if_pos h, if_pos (hiff.1 h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]; simp

/-- **Prefix-count event** (`eq:prefix-count-lower-bound-lcbq`, via `lem:sample-split-infinite`
at sample size `t` and confidence `δ/(5T)`, union over `t`): probability `≥ 1 − δ/5`. -/
theorem prefixCountEvent_prob (db : FiniteDistribution (S × A)) {T : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) (hι : 1 ≤ iota S A T δ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X →
      μ.map X = Measure.pi (fun _ : Fin T => (JointRow.jointRow db M.transition).rowMeasure) →
      1 - δ / 5 ≤ μ.real {ω | prefixCountEvent db (X ω) δ} := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  letI : MeasurableSpace (S × A) := ⊤
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  intro X hX hlaw
  have hT : 1 ≤ T := by
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · subst h0; simp [iota] at hι; linarith
    · exact h0
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set δ'' := δ / (5 * T) with hδ''
  have hδ''0 : 0 < δ'' := by positivity
  have hδ''1 : δ'' < 1 := by
    rw [hδ'', div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  -- the per-`t` events
  let Xt : (t : ℕ) → t ≤ T → Ω → Fin t → (S × A) × S := fun t ht ω i => X ω (Fin.castLE ht i)
  let good : (t : ℕ) → t ≤ T → Set Ω := fun t ht => {ω | SampleSplitActual.rowLabels (Xt t ht ω) ∈
    sampleSplitCountLowerEvent db.rowMeasure t δ''}
  have hgood : ∀ t (ht : t ≤ T), 2 ≤ t → 1 - δ'' < μ.real (good t ht) := by
    intro t ht ht2
    have hXt : Measurable (Xt t ht) :=
      measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp hX
    have hlawt : μ.map (Xt t ht) = (JointRow.jointRow db M.transition).sampleMeasure t := by
      have hc : Xt t ht = (fun ω : Fin T → (S × A) × S => fun i => ω (Fin.castLE ht i)) ∘ X := rfl
      rw [hc, ← Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply _) hX, hlaw,
        StackProjection.pi_map_comp_injective _ _ (Fin.castLE_injective ht)]
      rfl
    exact SampleSplitActual.sampleSplit_count_lower_of_jointLaw μ db M.transition t ht2 δ'' hδ''0
      hδ''1 (Xt t ht) hXt hlawt
  -- the inclusion
  have hreal : ∀ sa : S × A, db.rowMeasure.real {sa} = db.prob sa := by
    intro sa
    rw [measureReal_def]
    unfold FiniteDistribution.rowMeasure
    rw [@PMF.toMeasure_apply_singleton _ ⊤ _ sa MeasurableSpace.measurableSet_top]
    unfold FiniteDistribution.toPMF
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (db.prob_nonneg sa)]
  have hι0 : 0 < iota S A T δ := by linarith
  have hlog : ∀ t, t ≤ T → (2 / 3 : ℝ) * Real.log ((Fintype.card S : ℝ) * t / δ'') ≤
      3 * iota S A T δ := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp; linarith
    have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast h0
    have htT : (t : ℝ) ≤ T := by exact_mod_cast ht
    set X := (Fintype.card S : ℝ) * Fintype.card A * T / δ with hXdef
    have hX0 : 0 < X := by positivity
    have hle : (Fintype.card S : ℝ) * t / δ'' ≤ 5 * X ^ 2 := by
      rw [hδ'', hXdef, div_pow, div_div_eq_mul_div]
      rw [div_le_iff₀ hδ, show 5 * (((Fintype.card S : ℝ) * Fintype.card A * T) ^ 2 / δ ^ 2) * δ =
        5 * ((Fintype.card S : ℝ) * Fintype.card A * T) ^ 2 / δ by field_simp]
      rw [le_div_iff₀ hδ]
      have h1 : (Fintype.card S : ℝ) * t * T ≤ ((Fintype.card S : ℝ) * Fintype.card A * T) ^ 2 := by
        have : (Fintype.card S : ℝ) ≤ (Fintype.card S : ℝ) ^ 2 := by nlinarith
        have : (1 : ℝ) ≤ (Fintype.card A : ℝ) ^ 2 := by nlinarith
        have : (t : ℝ) * T ≤ (T : ℝ) ^ 2 := by nlinarith
        have := mul_le_mul this (by assumption : (1 : ℝ) ≤ (Fintype.card A : ℝ) ^ 2) zero_le_one
          (by positivity)
        nlinarith [sq_nonneg ((Fintype.card S : ℝ) * Fintype.card A * T)]
      have h2 : (Fintype.card S : ℝ) * t * T * δ ≤ (Fintype.card S : ℝ) * t * T := by
        have : 0 ≤ (Fintype.card S : ℝ) * t * T := by positivity
        nlinarith
      nlinarith
    have hpos : 0 < (Fintype.card S : ℝ) * t / δ'' := by positivity
    have hL := Real.log_le_log hpos hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hL
    have hι' : Real.log X = iota S A T δ := rfl
    have h5 := log_five_le_two
    push_cast at hL
    nlinarith
  set I := Finset.Icc 2 T with hI
  let G : ℕ → Set Ω := fun t => {ω | ∀ ht : t ≤ T, ω ∈ good t ht}
  have hsub : (⋂ t ∈ I, G t) ⊆ {ω | prefixCountEvent db (X ω) δ} := by
    intro ω hω t ht1 htT sa
    have hmax : (t : ℝ) * db.prob sa / 12 ≤ 3 * iota S A T δ ∨
        (t : ℝ) * db.prob sa / 12 ≤ max (Nat.count (visitPred (X ω) sa) t : ℝ)
          ((2 / 3 : ℝ) * Real.log ((Fintype.card S : ℝ) * t / δ'')) := by
      rcases Nat.lt_or_ge t 2 with h1 | h2
      · left
        have : t = 1 := by omega
        subst this
        have := DiscountedMDP.finiteDistribution_prob_le_one db sa
        push_cast
        nlinarith
      · right
        have hm := Set.mem_iInter₂.1 hω t (by simp [hI]; omega) htT
        simp only [good, sampleSplitCountLowerEvent, Set.mem_setOf_eq] at hm
        have h := hm sa
        rw [hreal sa] at h
        have hv : ((visitCount (fun i (x : Fin t → S × A) => x i) sa
            (SampleSplitActual.rowLabels (Xt t htT ω)) : ℕ) : ℝ) =
            ∑ i : Fin t, (if (X ω (Fin.castLE htT i)).1 = sa then (1 : ℝ) else 0) := by
          unfold visitCount; push_cast; rfl
        rw [hv] at h
        rw [count_eq_sum_fin (X ω) sa htT]
        exact h
    rcases hmax with h | h
    · exact h.trans (le_max_right _ _)
    · exact h.trans (max_le_max le_rfl (hlog t htT))
  have hGt : ∀ t ∈ I, MeasurableSet (G t) ∧ μ.real (G t)ᶜ ≤ δ'' := by
    intro t ht
    simp only [hI, Finset.mem_Icc] at ht
    have hG : G t = good t ht.2 := by
      ext ω
      exact ⟨fun h => h ht.2, fun h _ => h⟩
    have hXt : Measurable (Xt t ht.2) :=
      measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp hX
    have hm : MeasurableSet (good t ht.2) :=
      ((measurable_of_countable (SampleSplitActual.rowLabels (State := S) (Action := A)
        (N := t))).comp hXt) (Set.to_countable _).measurableSet
    rw [hG]
    refine ⟨hm, ?_⟩
    rw [probReal_compl_eq_one_sub hm]
    linarith [hgood t ht.2 ht.1]
  have hInter : MeasurableSet (⋂ t ∈ I, G t) :=
    Finset.measurableSet_biInter I fun t ht => (hGt t ht).1
  have hcardI : ((I.card : ℕ) : ℝ) * δ'' ≤ δ / 5 := by
    have : I.card ≤ T := by simp [hI]
    have h' : ((I.card : ℕ) : ℝ) ≤ T := by exact_mod_cast this
    calc ((I.card : ℕ) : ℝ) * δ'' ≤ T * δ'' := mul_le_mul_of_nonneg_right h' hδ''0.le
      _ = δ / 5 := by rw [hδ'']; field_simp
  calc 1 - δ / 5 ≤ 1 - ((I.card : ℕ) : ℝ) * δ'' := by linarith
    _ ≤ 1 - ∑ t ∈ I, μ.real (G t)ᶜ := by
        have : ∑ t ∈ I, μ.real (G t)ᶜ ≤ ∑ _t ∈ I, δ'' := Finset.sum_le_sum fun t ht => (hGt t ht).2
        rw [Finset.sum_const, nsmul_eq_mul] at this
        linarith
    _ ≤ 1 - μ.real (⋃ t ∈ I, (G t)ᶜ) := by
        have := measureReal_biUnion_finset_le (μ := μ) I (fun t => (G t)ᶜ)
        linarith
    _ = μ.real (⋂ t ∈ I, G t) := by
        rw [← Set.compl_iInter₂, probReal_compl_eq_one_sub hInter]; ring
    _ ≤ μ.real {ω | prefixCountEvent db (X ω) δ} := measureReal_mono hsub
end Counts

section PoorlyCovered

variable (M : DiscountedMDP S A)

/-- Real mass of a set under the finite sum of point masses that is the law of one data triple. -/
theorem triple_law_real (db : FiniteDistribution (S × A)) (E : Set ((S × A) × S)) :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    (∑ x : (S × A) × S, ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) •
      Measure.dirac x).real E =
      ∑ x : (S × A) × S, (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) * E.indicator 1 x := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  rw [measureReal_def, Measure.finset_sum_apply]
  rw [ENNReal.toReal_sum (fun x _ => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSpace.measurableSet_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (db.prob_nonneg _) ((M.transition _ _).prob_nonneg _))]
  congr 1
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs <;> simp

/-- **No sample hits a poorly covered pair `(s,π⋆(s))`** (`d^b < δ/(5ST)`): probability
`≥ 1 − δ/5`. This event replaces the omitted argument for the poorly covered part of `φ`
(`offlineRL.tex:5483–5485`). -/
theorem icEvent_prob (db : FiniteDistribution (S × A)) (πstar : S → A) {T : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ / 5 ≤ μ.real {ω | ∀ u : Fin T, δ / (5 * Fintype.card S * T) ≤ db.prob (X ω u).1 ∨
        (X ω u).1.2 ≠ πstar (X ω u).1.1} := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hmarg
  rcases Nat.eq_zero_or_pos T with hT0 | hT
  · subst hT0
    have : {ω | ∀ u : Fin 0, δ / (5 * Fintype.card S * (0 : ℕ)) ≤ db.prob (X ω u).1 ∨
        (X ω u).1.2 ≠ πstar (X ω u).1.1} = Set.univ := by
      ext ω; simp
    rw [this, probReal_univ]; linarith
  haveI := M.state_nonempty
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set thr := δ / (5 * Fintype.card S * T) with hthr
  set E : Set ((S × A) × S) := {x | db.prob x.1 < thr ∧ x.1.2 = πstar x.1.1} with hE
  have hEm : MeasurableSet E := MeasurableSpace.measurableSet_top
  have hbad : ∀ u : Fin T, μ.real ((fun ω => X ω u) ⁻¹' E) ≤ Fintype.card S * thr := by
    intro u
    have hXu : Measurable (fun ω => X ω u) := (measurable_pi_apply u).comp hX
    rw [← map_measureReal_apply hXu hEm, hmarg u, triple_law_real]
    calc ∑ x : (S × A) × S, (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) * E.indicator 1 x
        = ∑ p : S × A, db.prob p * (if db.prob p < thr ∧ p.2 = πstar p.1 then 1 else 0) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [hE, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
          split_ifs
          · simp only [mul_one]
            rw [← Finset.mul_sum, (M.transition p.1 p.2).sum_prob, mul_one]
          · simp
      _ ≤ ∑ p : S × A, (if p.2 = πstar p.1 then thr else 0) := by
          refine Finset.sum_le_sum fun p _ => ?_
          split_ifs with h1 h2 h2
          · rw [mul_one]; exact h1.1.le
          · exact absurd h1.2 h2
          · rw [mul_zero]; positivity
          · rw [mul_zero]
      _ = Fintype.card S * thr := by
          rw [Fintype.sum_prod_type]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
  have hcompl : {ω | ∀ u : Fin T, thr ≤ db.prob (X ω u).1 ∨ (X ω u).1.2 ≠ πstar (X ω u).1.1}ᶜ =
      ⋃ u ∈ (Finset.univ : Finset (Fin T)), (fun ω => X ω u) ⁻¹' E := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_or, not_le, not_not,
      Set.mem_iUnion, Finset.mem_univ, Set.mem_preimage, hE, exists_prop,
      true_and]
  have hm : MeasurableSet {ω | ∀ u : Fin T, thr ≤ db.prob (X ω u).1 ∨
      (X ω u).1.2 ≠ πstar (X ω u).1.1} := by
    have : {ω | ∀ u : Fin T, thr ≤ db.prob (X ω u).1 ∨ (X ω u).1.2 ≠ πstar (X ω u).1.1} =
        X ⁻¹' {x | ∀ u : Fin T, thr ≤ db.prob (x u).1 ∨ (x u).1.2 ≠ πstar (x u).1.1} := rfl
    rw [this]
    exact hX (Set.toFinite _).measurableSet
  have h1 := probReal_compl_eq_one_sub (μ := μ) hm
  rw [hcompl] at h1
  have h2 := measureReal_biUnion_finset_le (μ := μ) (Finset.univ : Finset (Fin T))
    (fun u => (fun ω => X ω u) ⁻¹' E)
  have h3 : ∑ u ∈ (Finset.univ : Finset (Fin T)), μ.real ((fun ω => X ω u) ⁻¹' E) ≤
      T * (Fintype.card S * thr) := by
    calc _ ≤ ∑ _u ∈ (Finset.univ : Finset (Fin T)), (Fintype.card S * thr) :=
          Finset.sum_le_sum fun u _ => hbad u
      _ = T * (Fintype.card S * thr) := by simp
  have h4 : (T : ℝ) * (Fintype.card S * thr) = δ / 5 := by rw [hthr]; field_simp
  linarith

end PoorlyCovered

end StatisticalRL.OfflineRL.LCBQ
