import Formalization.OfflineRL.FiniteVILCB.Prelim

/-!
# Theorem 6.16 for the two-fold-subsampling VI-LCB variant

Source: `chapters/offlineRL.tex:3093–3112` (`thm:finite-VI-LCB`), restricted to the explicit
variant `qhat` of `FiniteVILCB.Definitions` (`docs/SOURCE-ISSUES.md#C32`). Constants: `c_b ≥ 16`,
`c_k = 69120 c_b`. Domain premise `0 < K` (`log(KH/δ)`); `C⋆ ≠ ⊤`.

Assembly (plan §3.4): pull the data event back to the analysis space; the good event is
E1 ∧ E3 (auxiliary counts) ∧ E2 (main counts) ∧ E4 (action tapes) ∧ E5 (visited rows); on it the
algorithm equals the ideal recursion and the deterministic analysis gives gap `≤ ε`; the
failure probability is at most `4·H·S·e^{-ι} + δ/4 ≤ δ/2`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance thDecS : DecidableEq S := Classical.decEq S
noncomputable local instance thDecA : DecidableEq A := Classical.decEq A
local instance thMS : MeasurableSpace S := ⊤
local instance thMA : MeasurableSpace A := ⊤
local instance thMT (H : ℕ) : MeasurableSpace (Traj S A H) := ⊤

/-- The row event E5 for given trimmed counts and tapes. -/
def RowsOK {H n : ℕ} (E : Fin H → EnvironmentStage S A) (cb ι L : ℝ) (m : Fin H → S → ℕ)
    (α : ActTape S A H n) (β : NxtTape S A H n) : Prop :=
  ∀ h s a, 0 < idealCount m α h s a →
    RowGood H L (idealCount m α h s a) (idealRow m α β h s a) ((E h).transition s a)
      (idealV cb ι (fun h ↦ (E h).reward) m α β (h.val + 1))

theorem visits_le {H N : ℕ} (y : Fin N → Traj S A H) (h : Fin H) (s : S) : visits y h s ≤ N := by
  unfold visits
  exact (Finset.card_le_univ _).trans (by simp)

/-- Deterministic part of the assembly: on the good event every greedy output is `ε`-optimal. -/
theorem det_part {H K : ℕ} (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (hπs : IsOptimal E πs)
    (cb ε δ L : ℝ) (hcb : 16 ≤ cb) (hε : 0 < ε) (hεH : ε ≤ H) (hHr : (1 : ℝ) ≤ H)
    (hKpos : (0 : ℝ) < K) (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (hι1 : 1 ≤ iota H K δ) (hL0 : 0 ≤ L) (hLι : L ≤ iota H K δ)
    (hHY : (H : ℝ) * ((H : ℝ) ^ 2 * Fintype.card S * (concentrability E πb ρb ρ πs).toReal *
      iota H K δ / K) ≤ 5 * ε ^ 2 / (69120 * cb))
    (aux : Fin (K / 2) → Traj S A H) (ι₀ : Fin (K - K / 2) → S) (α : ActTape S A H (K - K / 2))
    (β : NxtTape S A H (K - K / 2))
    (hE1 : UpperEv E πb ρb (iota H K δ) aux) (hE3 : LowerEv E πb ρb (iota H K δ) aux)
    (hE2 : LowerEv E πb ρb (iota H K δ) (buildMain ι₀ α β))
    (hE4 : ActEv πb (iota H K δ) πs (auxTrim (iota H K δ) aux) α)
    (hE5 : RowsOK E cb (iota H K δ) L (auxTrim (iota H K δ) aux) α β)
    (πhat : Fin H → S → A)
    (hg : ∀ h s a, qhat cb δ (fun h ↦ (E h).reward) (joinData aux (buildMain ι₀ α β)) h s a ≤
      qhat cb δ (fun h ↦ (E h).reward) (joinData aux (buildMain ι₀ α β)) h s (πhat h s)) :
    ρ.expectation (optV E 0) - ρ.expectation (polV E πhat 0) ≤ ε := by
  have hι0 : 0 ≤ iota H K δ := le_trans zero_le_one hι1
  have hT := trim_of_events E πb ρb (iota H K δ) hι0 aux ι₀ α β hE1 hE2
  have hq := qhat_eq_ideal cb δ (fun h ↦ (E h).reward) aux ι₀ α β hT
  rw [hq] at hg
  set m := auxTrim (iota H K δ) aux
  have hgr : IsGreedy (E := E) (cb := cb) (ι := iota H K δ) (idealCount m α) (idealRow m α β)
    πhat := hg
  have hrows : ∀ h s a, 0 < idealCount m α h s a → RowGood H L (idealCount m α h s a)
      (idealRow m α β h s a) ((E h).transition s a)
      (vhatGen cb (iota H K δ) (fun h ↦ (E h).reward) (idealCount m α) (idealRow m α β)
        (h.val + 1)) := hE5
  have hG : Good E cb (iota H K δ) L (idealCount m α) (idealRow m α β) := ⟨hcb, hL0, hLι, hrows⟩
  have hgap := hG.gap_le hπs (dstar_flow E πs ρ) hgr
  have hB := hG.B_le (dstar_flow E πs ρ) (fun h s ↦ occupancy E πb ρb h s (πs h s))
    (concentrability E πb ρb ρ πs).toReal K ENNReal.toReal_nonneg hKpos
    (lt_of_lt_of_le zero_lt_one hι1) (dstar_le E πb ρb ρ πs hC)
    (fun h s hx ↦ count_chain E πb ρb πs (iota H K δ) hι1 aux α hE3 hE4 h s hx)
  have hY0 : 0 ≤ (H : ℝ) ^ 2 * Fintype.card S * (concentrability E πb ρb ρ πs).toReal *
      iota H K δ / K :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      ENNReal.toReal_nonneg) hι0) hKpos.le
  have hfin := final_arith hcb hHr hε hεH hY0 hHY
  linarith only [hgap, hB, hfin]

/-- **Theorem 6.16, restricted to the explicit variant** (library form). -/
theorem finite_vilcb_restricted (H : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (hπs : IsOptimal E πs)
    (cb : ℝ) (hcb : 16 ≤ cb) (ε δ : ℝ) (hε : 0 < ε) (hεH : ε ≤ H) (hδ : 0 < δ) (hδ1 : δ < 1)
    (K : ℕ) (hK : 0 < K) (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (hKc : 69120 * cb * (H : ℝ) ^ 3 * Fintype.card S *
      (concentrability E πb ρb ρ πs).toReal * Real.log (K * H / δ) / ε ^ 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → Traj S A H) (hX : Measurable X) (hind : iIndepFun (fun k ω ↦ X ω k) μ)
    (hlaw : ∀ k, μ.map (fun ω ↦ X ω k) = trajMeasure E πb ρb) :
    1 - δ ≤ μ.real {ω | ∀ πhat : Fin H → S → A,
      (∀ h s a, qhat cb δ (fun h ↦ (E h).reward) (X ω) h s a ≤
        qhat cb δ (fun h ↦ (E h).reward) (X ω) h s (πhat h s)) →
      ρ.expectation (optV E 0) - ρ.expectation (polV E πhat 0) ≤ ε} := by
  classical
  rcases Nat.lt_or_ge H 2 with hH1 | hH2
  · obtain rfl : H = 1 := by omega
    have huniv : {ω | ∀ πhat : Fin 1 → S → A,
        (∀ h s a, qhat cb δ (fun h ↦ (E h).reward) (X ω) h s a ≤
          qhat cb δ (fun h ↦ (E h).reward) (X ω) h s (πhat h s)) →
        ρ.expectation (optV E 0) - ρ.expectation (polV E πhat 0) ≤ ε} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro πhat hg
      exact gap_H_one E ρ cb δ ε hε.le (X ω) πhat hg
    rw [huniv, probReal_univ]
    linarith
  -- main case `H ≥ 2`
  set ι := iota H K δ with hιdef
  set C := (concentrability E πb ρb ρ πs).toReal with hCdef
  have hH1 : 1 ≤ H := hH
  have hK1 : 1 ≤ K := hK
  have hC1 : 1 ≤ C := one_le_conc hH E πb ρb ρ πs hC
  have hHK : 2 ≤ H * K := by simpa using Nat.mul_le_mul hH2 hK1
  have hι1 : 1 ≤ ι := one_le_iota hH1 hK1 hδ hδ1
  have hι5 : ι ≤ 5 * Real.log (K * H / δ) := iota_le_five_log hHK hδ hδ1
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  have hHr2 : (2 : ℝ) ≤ H := by exact_mod_cast hH2
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKpos : (0 : ℝ) < K := by linarith
  have hHKr : (2 : ℝ) ≤ (K : ℝ) * H := by
    have : ((2 : ℕ) : ℝ) ≤ ((H * K : ℕ) : ℝ) := by exact_mod_cast hHK
    push_cast at this
    linarith [mul_comm (H : ℝ) K]
  have hlog2 : Real.log 2 ≤ Real.log (K * H / δ) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hδ]
    linarith
  have hlog2pos : 0.69 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hS0 : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _
  -- K ≥ S
  have hSK : (Fintype.card S : ℝ) ≤ K := by
    refine le_trans ?_ hKc
    rw [le_div_iff₀ (by positivity)]
    have hε2 : ε ^ 2 ≤ (H : ℝ) ^ 2 := pow_le_pow_left₀ hε.le hεH 2
    have hH3 : (H : ℝ) ^ 2 ≤ (H : ℝ) ^ 3 := pow_le_pow_right₀ hHr (by norm_num)
    have h1 : Fintype.card S * ε ^ 2 ≤ Fintype.card S * (H : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left (hε2.trans hH3) hS0
    have hlog : 0.69 ≤ Real.log (K * H / δ) := hlog2pos.trans hlog2
    have hcbC : 16 ≤ cb * C := by
      have := mul_le_mul hcb hC1 (by norm_num) (by linarith)
      linarith
    have hm := mul_le_mul hcbC hlog (by norm_num) (by linarith)
    have h2 : (1 : ℝ) ≤ 69120 * cb * C * Real.log (K * H / δ) := by linarith
    have h3 : 0 ≤ Fintype.card S * (H : ℝ) ^ 3 := by positivity
    linarith [mul_le_mul_of_nonneg_left h2 h3]
  -- δ' and L
  set δ' := δ / (4 * H * K) with hδ'def
  have hδ'0 : 0 < δ' := by positivity
  have hδ'8 : δ' < 1 / 8 := by
    rw [hδ'def, div_lt_iff₀ (by positivity)]
    linarith [mul_comm (H : ℝ) K]
  set L := Real.log (1 / δ') with hLdef
  have hLeq : 1 / δ' = 4 * H * K / δ := by rw [hδ'def]; field_simp
  have hL0 : 0 ≤ L := by
    rw [hLdef, hLeq]
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    have : (2 : ℝ) ≤ (H : ℝ) * K := by linarith
    linarith
  have hLι : L ≤ ι := by
    rw [hLdef, hLeq, hιdef, iota]
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right _ hδ.le
    have : (0 : ℝ) ≤ (H : ℝ) * K := by positivity
    linarith
  have hexp : Real.exp (-ι) = δ / (16 * H * K) := exp_neg_iota hH1 hK1 hδ
  have hHSe : (H : ℝ) * Fintype.card S * Real.exp (-ι) ≤ δ / 16 := by
    rw [hexp]
    rw [show (H : ℝ) * Fintype.card S * (δ / (16 * H * K)) = δ / 16 * (Fintype.card S / K) by
      field_simp]
    have h1 : (Fintype.card S : ℝ) / K ≤ 1 := (div_le_one hKpos).mpr hSK
    have h0 : 0 ≤ δ / 16 := by positivity
    calc δ / 16 * (Fintype.card S / K) ≤ δ / 16 * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = δ / 16 := mul_one _
  -- arithmetic for the deterministic bound
  have hHY : (H : ℝ) * ((H : ℝ) ^ 2 * Fintype.card S * C * ι / K) ≤ 5 * ε ^ 2 / (69120 * cb) := by
    have hcb0 : 0 < cb := by linarith
    have hA : (H : ℝ) ^ 3 * Fintype.card S * C * Real.log (K * H / δ) ≤
        K * ε ^ 2 / (69120 * cb) := by
      rw [le_div_iff₀ (by positivity)]
      have := hKc
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hpos : 0 ≤ (H : ℝ) ^ 3 * Fintype.card S * C := by positivity
    have hB : (H : ℝ) ^ 3 * Fintype.card S * C * ι ≤
        5 * ((H : ℝ) ^ 3 * Fintype.card S * C * Real.log (K * H / δ)) := by
      have := mul_le_mul_of_nonneg_left hι5 hpos
      linarith
    rw [show (H : ℝ) * ((H : ℝ) ^ 2 * Fintype.card S * C * ι / K) =
      (H : ℝ) ^ 3 * Fintype.card S * C * ι / K by ring, div_le_iff₀ hKpos]
    have : 5 * (K * ε ^ 2 / (69120 * cb)) = 5 * ε ^ 2 / (69120 * cb) * K := by ring
    linarith
  -- pull back to the analysis space
  have htr := data_transfer E πb ρb μ X hX hind hlaw (fun x ↦ ∀ πhat : Fin H → S → A,
    (∀ h s a, qhat cb δ (fun h ↦ (E h).reward) x h s a ≤
      qhat cb δ (fun h ↦ (E h).reward) x h s (πhat h s)) →
    ρ.expectation (optV E 0) - ρ.expectation (polV E πhat 0) ≤ ε)
  simp only at htr
  rw [htr]
  set Q := analysisMeasure E πb ρb K with hQ
  let G : Set ((Fin (K / 2) → Traj S A H) ×
      ((Fin (K - K / 2) → S) × ActTape S A H (K - K / 2) × NxtTape S A H (K - K / 2))) :=
    {ω | UpperEv E πb ρb ι ω.1 ∧ LowerEv E πb ρb ι ω.1 ∧
      LowerEv E πb ρb ι (buildMain ω.2.1 ω.2.2.1 ω.2.2.2) ∧
      ActEv πb ι πs (auxTrim ι ω.1) ω.2.2.1 ∧
      RowsOK E cb ι L (auxTrim ι ω.1) ω.2.2.1 ω.2.2.2}
  -- deterministic part
  have hsub : G ⊆ {ω | ∀ πhat : Fin H → S → A,
      (∀ h s a, qhat cb δ (fun h ↦ (E h).reward)
          (joinData ω.1 (buildMain ω.2.1 ω.2.2.1 ω.2.2.2)) h s a ≤
        qhat cb δ (fun h ↦ (E h).reward)
          (joinData ω.1 (buildMain ω.2.1 ω.2.2.1 ω.2.2.2)) h s (πhat h s)) →
      ρ.expectation (optV E 0) - ρ.expectation (polV E πhat 0) ≤ ε} := by
    rintro ⟨aux, ι₀, α, β⟩ ⟨hE1, hE3, hE2, hE4, hE5⟩ πhat hg
    exact det_part E πb ρb ρ πs hπs cb ε δ L hcb hε hεH hHr hKpos hC hι1 hL0 hLι hHY
      aux ι₀ α β hE1 hE3 hE2 hE4 hE5 πhat hg
  -- probability part
  have hm_le : ∀ aux : Fin (K / 2) → Traj S A H, ∀ h s, auxTrim ι aux h s ≤ K - K / 2 := by
    intro aux h s
    rw [auxTrim_eq]
    unfold trim
    split_ifs
    · have := visits_le aux h s
      omega
    · exact Nat.zero_le _
  have hmeasAll : ∀ B : Set ((Fin (K / 2) → Traj S A H) ×
      ((Fin (K - K / 2) → S) × ActTape S A H (K - K / 2) × NxtTape S A H (K - K / 2))),
      MeasurableSet B := fun B ↦ (Set.to_countable B).measurableSet
  have hB1 : Q.real {ω | ¬ UpperEv E πb ρb ι ω.1} ≤ δ / 16 := by
    rw [hQ, analysisMeasure]
    refine (prod_real_fst _ _ {y | ¬ UpperEv E πb ρb ι y}).le.trans ?_
    exact (upperEv_bad E πb ρb ι (K / 2) (by linarith)).trans hHSe
  have hB3 : Q.real {ω | ¬ LowerEv E πb ρb ι ω.1} ≤ δ / 16 := by
    rw [hQ, analysisMeasure]
    refine (prod_real_fst _ _ {y | ¬ LowerEv E πb ρb ι y}).le.trans ?_
    exact (lowerEv_bad E πb ρb ι (K / 2) (by linarith)).trans hHSe
  have hB2 : Q.real {ω | ¬ LowerEv E πb ρb ι (buildMain ω.2.1 ω.2.2.1 ω.2.2.2)} ≤ δ / 16 := by
    rw [hQ, analysisMeasure]
    have hset : {ω : (Fin (K / 2) → Traj S A H) × ((Fin (K - K / 2) → S) ×
        ActTape S A H (K - K / 2) × NxtTape S A H (K - K / 2)) |
          ¬ LowerEv E πb ρb ι (buildMain ω.2.1 ω.2.2.1 ω.2.2.2)} =
        {p | p.2 ∈ (fun t : (Fin (K - K / 2) → S) × ActTape S A H (K - K / 2) ×
          NxtTape S A H (K - K / 2) ↦ buildMain t.1 t.2.1 t.2.2) ⁻¹'
            {y | ¬ LowerEv E πb ρb ι y}} := by
      ext ω; exact Iff.rfl
    rw [hset, prod_real_snd]
    have hmap := map_measureReal_apply (μ := tapeMeasure E πb ρb (K - K / 2))
      (measurable_of_countable (fun t : (Fin (K - K / 2) → S) × ActTape S A H (K - K / 2) ×
        NxtTape S A H (K - K / 2) ↦ buildMain t.1 t.2.1 t.2.2))
      (s := {y | ¬ LowerEv E πb ρb ι y}) (Set.to_countable _).measurableSet
    rw [tapeMeasure_map_buildMain] at hmap
    rw [← hmap]
    exact (lowerEv_bad E πb ρb ι (K - K / 2) (by linarith)).trans hHSe
  have hB4 : Q.real {ω | ¬ ActEv πb ι πs (auxTrim ι ω.1) ω.2.2.1} ≤ δ / 16 := by
    rw [hQ, analysisMeasure]
    refine prod_real_le_of_sections _ _ (hmeasAll _) _ (by positivity) fun aux ↦ ?_
    rw [tapeMeasure]
    rw [show Prod.mk aux ⁻¹' {ω : (Fin (K / 2) → Traj S A H) × ((Fin (K - K / 2) → S) ×
        ActTape S A H (K - K / 2) × NxtTape S A H (K - K / 2)) |
          ¬ ActEv πb ι πs (auxTrim ι ω.1) ω.2.2.1} =
        {t | t.2 ∈ {p : ActTape S A H (K - K / 2) × NxtTape S A H (K - K / 2) |
          p.1 ∈ {α | ¬ ActEv πb ι πs (auxTrim ι aux) α}}} from rfl,
      prod_real_snd, prod_real_fst]
    exact (actEv_bad πb ι πs (auxTrim ι aux) (hm_le aux) (by linarith)).trans hHSe
  have hB5 : Q.real {ω | ¬ RowsOK E cb ι L (auxTrim ι ω.1) ω.2.2.1 ω.2.2.2} ≤ δ / 4 := by
    rw [hQ, analysisMeasure]
    refine prod_real_le_of_sections _ _ (hmeasAll _) _ (by positivity) fun aux ↦ ?_
    rw [tapeMeasure]
    refine prod_real_le_of_sections _ _ (Set.to_countable _).measurableSet _ (by positivity)
      fun ι₀ ↦ ?_
    refine prod_real_le_of_sections _ _ (Set.to_countable _).measurableSet _ (by positivity)
      fun α ↦ ?_
    have hr := rows_event E cb ι (by linarith) (by linarith) (fun h ↦ (E h).reward)
      (fun h ↦ (E h).reward_nonneg) (fun h ↦ (E h).reward_le_one) δ' hδ'0 hδ'8
      (auxTrim ι aux) α
    have hv := visited_card_le ι aux α
    refine le_trans (le_of_eq ?_) (hr.trans ?_)
    · rfl
    · rw [hδ'def]
      calc 8 * (δ / (4 * H * K)) * ((visited (auxTrim ι aux) α).card : ℝ)
          ≤ 8 * (δ / (4 * H * K)) * (H * K / 8) := by
            apply mul_le_mul_of_nonneg_left hv (by positivity)
        _ = δ / 4 := by field_simp
  -- union bound
  have hGc : Q.real Gᶜ ≤ δ := by
    have hsubc : Gᶜ ⊆ ((({ω | ¬ UpperEv E πb ρb ι ω.1} ∪ {ω | ¬ LowerEv E πb ρb ι ω.1}) ∪
        {ω | ¬ LowerEv E πb ρb ι (buildMain ω.2.1 ω.2.2.1 ω.2.2.2)}) ∪
        {ω | ¬ ActEv πb ι πs (auxTrim ι ω.1) ω.2.2.1}) ∪
        {ω | ¬ RowsOK E cb ι L (auxTrim ι ω.1) ω.2.2.1 ω.2.2.2} := by
      intro ω hω
      simp only [G, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hω
      simp only [Set.mem_union, Set.mem_setOf_eq]
      tauto
    refine (measureReal_mono hsubc (measure_ne_top _ _)).trans ?_
    refine (measureReal_union_le _ _).trans ?_
    have h1 := measureReal_union_le (μ := Q) ((({ω | ¬ UpperEv E πb ρb ι ω.1} ∪
      {ω | ¬ LowerEv E πb ρb ι ω.1}) ∪
      {ω | ¬ LowerEv E πb ρb ι (buildMain ω.2.1 ω.2.2.1 ω.2.2.2)}))
      {ω | ¬ ActEv πb ι πs (auxTrim ι ω.1) ω.2.2.1}
    have h2 := measureReal_union_le (μ := Q) (({ω | ¬ UpperEv E πb ρb ι ω.1} ∪
      {ω | ¬ LowerEv E πb ρb ι ω.1}))
      {ω | ¬ LowerEv E πb ρb ι (buildMain ω.2.1 ω.2.2.1 ω.2.2.2)}
    have h3 := measureReal_union_le (μ := Q) {ω | ¬ UpperEv E πb ρb ι ω.1}
      {ω | ¬ LowerEv E πb ρb ι ω.1}
    linarith
  have hcompl := measureReal_compl (μ := Q) (hmeasAll G)
  rw [probReal_univ] at hcompl
  calc 1 - δ ≤ Q.real G := by linarith
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

end StatisticalRL.FiniteVILCB
