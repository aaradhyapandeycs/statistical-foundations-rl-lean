import Formalization.OfflineRL.FiniteLCBQ.Theorem

/-!
# Theorem 6.17 (finite-horizon LCB-Q, restricted variant): the library export

`lcbqFinite_restricted`: for `c_b ≥ 5`, every `L ≥ log(SAK/δ)` and
`K ≥ 10⁶ c_b² H⁵ S C⋆ L / ε²` (or `|A| = 1`, where every policy is optimal), with probability at least `1 - δ` the policy returned by
`LCBQFinite.output c_b L sel π₀` on `K` iid trajectories is `ε`-optimal from `ρ`.
-/

namespace StatisticalRL.LCBQFinite

open Finset MeasureTheory ProbabilityTheory OnlineRL StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance exDecS : DecidableEq S := Classical.decEq S
noncomputable local instance exDecA : DecidableEq A := Classical.decEq A
local instance exMT (H : ℕ) : MeasurableSpace (Traj S A H) := ⊤

theorem output_eq_it {H K : ℕ} (E : Fin H → EnvironmentStage S A) (cb L : ℝ) (sel : (A → ℝ) → A)
    (π₀ : Fin H → S → A) (x : Fin K → Traj S A H) :
    output cb L sel π₀ (fun h ↦ (E h).reward) x = (it E cb L sel π₀ x K).pol := rfl

/-- **Theorem 6.17, restricted variant: library export.** -/
theorem lcbqFinite_restricted (cb : ℝ) (hcb : 5 ≤ cb) (H : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (hπs : IsOptimal E πs)
    (ε δ : ℝ) (hε : 0 < ε) (hεH : ε ≤ H) (hδ : 0 < δ) (hδ1 : δ < 1) (K : ℕ) (hK : 0 < K)
    (L : ℝ) (hL : Real.log (Fintype.card S * Fintype.card A * K / δ) ≤ L)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) (π₀ : Fin H → S → A)
    (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (hKc : Subsingleton A ∨ 10 ^ 6 * cb ^ 2 * (H : ℝ) ^ 5 * Fintype.card S *
      (concentrability E πb ρb ρ πs).toReal * L / ε ^ 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → Traj S A H) (hX : Measurable X) (hind : iIndepFun (fun k ω ↦ X ω k) μ)
    (hlaw : ∀ k, μ.map (fun ω ↦ X ω k) = trajMeasure E πb ρb) :
    1 - δ ≤ μ.real {ω | ρ.expectation (optV E 0) -
      ρ.expectation (polV E (output cb L sel π₀ (fun h ↦ (E h).reward) (X ω)) 0) ≤ ε} := by
  classical
  set gapP : (Fin K → Traj S A H) → Prop := fun x ↦ ρ.expectation (optV E 0) -
    ρ.expectation (polV E (output cb L sel π₀ (fun h ↦ (E h).reward) x) 0) ≤ ε
  rw [show {ω | ρ.expectation (optV E 0) -
      ρ.expectation (polV E (output cb L sel π₀ (fun h ↦ (E h).reward) (X ω)) 0) ≤ ε} =
      {ω | gapP (X ω)} from rfl, data_transfer' E πb ρb μ X hX hind hlaw gapP]
  have hw1 : ∑ x : Fin K → Traj S A H, prodP E πb ρb x = 1 :=
    sum_prod_eq_one (fun τ ↦ trajProb E πb ρb τ) (sum_trajProb E πb ρb) K
  have hw0 := prodP_nonneg E πb ρb (K := K)
  rcases subsingleton_or_nontrivial A with hA | hA
  · -- corner `|A| = 1`: every policy is optimal
    have hall : ∀ x, gapP x := by
      intro x
      simp only [gapP]
      have := polV_eq_optV_of_subsingleton E (output cb L sel π₀ (fun h ↦ (E h).reward) x)
        (H - 0) 0 rfl
      rw [show polV E (output cb L sel π₀ (fun h ↦ (E h).reward) x) 0 = optV E 0 from funext this]
      linarith
    simp only [hall, if_true, mul_one]
    show 1 - δ ≤ ∑ x : Fin K → Traj S A H, prodP E πb ρb x
    rw [hw1]; linarith
  -- main case
  have hA2 : 2 ≤ Fintype.card A := Fintype.one_lt_card
  have hKc := hKc.resolve_left fun hs ↦ (not_nontrivial_iff_subsingleton.2 hs) hA
  set C := (concentrability E πb ρb ρ πs).toReal
  have hC1 : 1 ≤ C := one_le_conc hH E πb ρb ρ πs hC
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hA2r : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hA2
  set Y := (Fintype.card S : ℝ) * Fintype.card A * K / δ
  have hY2 : 2 ≤ Y := by
    simp only [Y]; rw [le_div_iff₀ hδ]
    have : (2 : ℝ) ≤ Fintype.card S * Fintype.card A * K := by
      have := mul_le_mul hS1 hA2r (by norm_num) (by positivity)
      nlinarith
    nlinarith
  have hι2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
  have hlog2 := Real.log_two_gt_d9
  set ι := Real.log Y
  have hL69 : 0.69 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  -- `H ≤ K`
  have hHK : (H : ℝ) ≤ K := by
    have hSC : 1 ≤ (Fintype.card S : ℝ) * C := one_le_mul_of_one_le_of_one_le hS1 hC1
    have hSCL : 0.69 ≤ (Fintype.card S : ℝ) * C * L := by
      have := mul_le_mul hSC hL69 (by norm_num) (by positivity); linarith
    have hε2 : ε ^ 2 ≤ (H : ℝ) ^ 2 := pow_le_pow_left₀ hε.le hεH 2
    have hA : 0.69 * (H : ℝ) ^ 3 * ε ^ 2 ≤ (H : ℝ) ^ 5 * ((Fintype.card S : ℝ) * C * L) :=
      calc 0.69 * (H : ℝ) ^ 3 * ε ^ 2 ≤ 0.69 * (H : ℝ) ^ 3 * (H : ℝ) ^ 2 := by gcongr
        _ = (H : ℝ) ^ 5 * 0.69 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hSCL (by positivity)
    have hB : 10 ^ 6 * cb ^ 2 * (0.69 * (H : ℝ) ^ 3) ≤ K := by
      refine le_trans ?_ hKc
      rw [le_div_iff₀ (by positivity)]
      calc 10 ^ 6 * cb ^ 2 * (0.69 * (H : ℝ) ^ 3) * ε ^ 2 =
            10 ^ 6 * cb ^ 2 * (0.69 * (H : ℝ) ^ 3 * ε ^ 2) := by ring
        _ ≤ 10 ^ 6 * cb ^ 2 * ((H : ℝ) ^ 5 * ((Fintype.card S : ℝ) * C * L)) :=
            mul_le_mul_of_nonneg_left hA (by positivity)
        _ = _ := by ring
    have hH3 : (H : ℝ) ≤ (H : ℝ) ^ 3 := by
      calc (H : ℝ) = H * 1 * 1 := by ring
        _ ≤ H * H * H := by gcongr
        _ = H ^ 3 := by ring
    have hc : (1 : ℝ) ≤ 10 ^ 6 * cb ^ 2 * 0.69 := by nlinarith
    have : (H : ℝ) ^ 3 ≤ 10 ^ 6 * cb ^ 2 * (0.69 * (H : ℝ) ^ 3) := by
      have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ (H : ℝ) ^ 3)
      linarith
    linarith
  have hHKn : H ≤ K := by exact_mod_cast hHK
  -- the confidence log `ι' = log(6HSAK/δ) ≤ 5ι ≤ 5L`
  set ι' := Real.log (6 * H * Fintype.card S * Fintype.card A * K / δ)
  have hYpos : 0 < Y := by linarith
  have hι'eq : 6 * H * Fintype.card S * Fintype.card A * K / δ = (6 * H) * Y := by
    simp only [Y]; ring
  have hι'5 : ι' ≤ 5 * L := by
    have h1 : (6 * H) * Y ≤ Y ^ 5 := by
      have hKY : (K : ℝ) ≤ Y := by
        simp only [Y]; rw [le_div_iff₀ hδ]
        have hSA : (1 : ℝ) ≤ Fintype.card S * Fintype.card A :=
          one_le_mul_of_one_le_of_one_le hS1 (by linarith)
        calc (K : ℝ) * δ ≤ K * 1 := mul_le_mul_of_nonneg_left hδ1.le (by positivity)
          _ ≤ K * (Fintype.card S * Fintype.card A) := mul_le_mul_of_nonneg_left hSA (by positivity)
          _ = _ := by ring
      have h6 : (6 : ℝ) ≤ Y ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hY2 3
        norm_num at this; linarith
      have hHY : (H : ℝ) ≤ Y := hHK.trans hKY
      have h7 : 6 * (H : ℝ) ≤ Y ^ 3 * Y := mul_le_mul h6 hHY (by positivity) (by positivity)
      calc (6 * H) * Y ≤ (Y ^ 3 * Y) * Y := mul_le_mul_of_nonneg_right h7 hYpos.le
        _ = Y ^ 5 := by ring
    have h2 : ι' ≤ Real.log (Y ^ 5) := by
      simp only [ι']; rw [hι'eq]; exact Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hι'pos : 0 < ι' := by
    simp only [ι']; rw [hι'eq]
    refine Real.log_pos ?_
    have := mul_le_mul (show (6 : ℝ) ≤ 6 * H by linarith) hY2 (by norm_num) (by positivity)
    linarith
  have hcb0 : 0 ≤ cb := by linarith
  have h4ι : 4 * ι' ≤ cb ^ 2 * L := by
    have hcb2 : 25 ≤ cb ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right hcb2 hL0
    linarith
  -- pathwise: good event ⇒ gap ≤ ε
  have hpath : ∀ x, GoodEv E πb ρb ρ πs cb L sel π₀ x C ι' → gapP x := by
    intro x hG
    simp only [gapP]
    rw [output_eq_it]
    refine (gap_le E πb ρb ρ πs cb L sel π₀ x hH hK hcb0 hL0 hι'pos.le hπs hC hsel hG).trans ?_
    unfold remR
    exact final_arith hH1 hS1 hC1 (by positivity) hL69 hι'5 hcb hε hεH hKc
  -- probability
  have hpt : ∀ x, 1 - badSum E πb ρb ρ πs cb L sel π₀ C ι' x ≤ if gapP x then 1 else 0 := by
    intro x
    by_cases hG : GoodEv E πb ρb ρ πs cb L sel π₀ x C ι'
    · rw [if_pos (hpath x hG)]
      linarith [badSum_nonneg E πb ρb ρ πs cb L sel π₀ C ι' x]
    · have := one_le_badSum E πb ρb ρ πs cb L sel π₀ hcb0 hL0 hι'pos.le h4ι x hG
      split_ifs <;> linarith
  have hsum := sum_badSum_le E πb ρb ρ πs cb L sel π₀ hH hcb0 hC hC1 hι'pos (K := K)
  have hexp : Real.exp (-ι') = δ / (6 * H * Fintype.card S * Fintype.card A * K) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hcount : (2 * (H * Fintype.card S * Fintype.card A * K) + 2 * H + H * Fintype.card S : ℝ) *
      (δ / (6 * H * Fintype.card S * Fintype.card A * K)) ≤ δ := by
    have hAK : (1 : ℝ) ≤ Fintype.card A * K := one_le_mul_of_one_le_of_one_le (by linarith) hK1
    have hSAK : (1 : ℝ) ≤ Fintype.card S * (Fintype.card A * K) :=
      one_le_mul_of_one_le_of_one_le hS1 hAK
    have hH0 : (0 : ℝ) ≤ H := by positivity
    have e1 : (H : ℝ) * 1 ≤ H * (Fintype.card S * (Fintype.card A * K)) :=
      mul_le_mul_of_nonneg_left hSAK hH0
    have e2 : (H : ℝ) * Fintype.card S * 1 ≤ H * Fintype.card S * (Fintype.card A * K) :=
      mul_le_mul_of_nonneg_left hAK (by positivity)
    have hP : 0 < (H : ℝ) * Fintype.card S * Fintype.card A * K := by positivity
    have hle : (2 * (H * Fintype.card S * Fintype.card A * K) + 2 * H + H * Fintype.card S : ℝ) ≤
        6 * H * Fintype.card S * Fintype.card A * K := by
      have r1 : (H : ℝ) * (Fintype.card S * (Fintype.card A * K)) =
          H * Fintype.card S * Fintype.card A * K := by ring
      have r2 : (H : ℝ) * Fintype.card S * (Fintype.card A * K) =
          H * Fintype.card S * Fintype.card A * K := by ring
      rw [r1] at e1; rw [r2] at e2
      linarith
    calc _ ≤ (6 * H * Fintype.card S * Fintype.card A * K : ℝ) *
          (δ / (6 * H * Fintype.card S * Fintype.card A * K)) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = δ := by field_simp
  rw [hexp] at hsum
  calc 1 - δ ≤ 1 - ∑ x : Fin K → Traj S A H, prodP E πb ρb x *
        badSum E πb ρb ρ πs cb L sel π₀ C ι' x := by linarith
    _ = ∑ x : Fin K → Traj S A H, prodP E πb ρb x *
        (1 - badSum E πb ρb ρ πs cb L sel π₀ C ι' x) := by
        have e : ∑ x : Fin K → Traj S A H, prodP E πb ρb x *
            (1 - badSum E πb ρb ρ πs cb L sel π₀ C ι' x) = ∑ x : Fin K → Traj S A H, prodP E πb ρb x -
            ∑ x : Fin K → Traj S A H, prodP E πb ρb x * badSum E πb ρb ρ πs cb L sel π₀ C ι' x := by
          rw [← sum_sub_distrib]; exact sum_congr rfl fun x _ ↦ by ring
        rw [e, hw1]
    _ ≤ ∑ x : Fin K → Traj S A H, prodP E πb ρb x * (if gapP x then 1 else 0) :=
        sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hpt x) (hw0 x)
    _ = _ := rfl

/-- **Printed size condition ⇒ export size condition.** If `L ≤ max(ι, ι³)` with
`ι = log(SAK/δ)` and the printed condition `10⁶c_b² H⁵ S C⋆ ι³/ε² ≤ K` holds, then either
`|A| = 1` or the export's condition `10⁶c_b² H⁵ S C⋆ L/ε² ≤ K` holds. (For `|A| ≥ 2` and
`ι < 1` the printed condition is unsatisfiable: it forces `K = 1`.) -/
theorem printed_size_imp_export_size (cb : ℝ) (hcb : 5 ≤ cb) (H : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hεH : ε ≤ H) (hδ : 0 < δ) (hδ1 : δ < 1) (K : ℕ) (hK : 0 < K)
    (L : ℝ) (hL3 : L ≤ max (Real.log (Fintype.card S * Fintype.card A * K / δ))
      (Real.log (Fintype.card S * Fintype.card A * K / δ) ^ 3))
    (hKc : 10 ^ 6 * cb ^ 2 * (H : ℝ) ^ 5 * Fintype.card S *
      (concentrability E πb ρb ρ πs).toReal *
      Real.log (Fintype.card S * Fintype.card A * K / δ) ^ 3 / ε ^ 2 ≤ K) :
    Subsingleton A ∨ 10 ^ 6 * cb ^ 2 * (H : ℝ) ^ 5 * Fintype.card S *
      (concentrability E πb ρb ρ πs).toReal * L / ε ^ 2 ≤ K := by
  set ι := Real.log (Fintype.card S * Fintype.card A * K / δ) with hι
  set C := (concentrability E πb ρb ρ πs).toReal
  have hcb0 : 0 < cb := by linarith
  by_cases hcase : L ≤ ι ^ 3
  · right
    exact le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcase (by positivity))
      (by positivity)) hKc
  rcases subsingleton_or_nontrivial A with hs | hnt
  · exact Or.inl hs
  exfalso
  -- here `ι³ < L ≤ ι`, so `ι < 1`, which forces `K = 1` and contradicts the size condition
  have hLι : L ≤ ι := by
    rcases le_max_iff.1 hL3 with h | h
    · exact h
    · exact absurd h hcase
  have hA2 : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast (Fintype.one_lt_card (α := A))
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hSA : (2 : ℝ) ≤ Fintype.card S * Fintype.card A := by nlinarith
  have hY2 : (2 : ℝ) ≤ Fintype.card S * Fintype.card A * K / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have hι69 : 0.69 ≤ ι := by
    have := Real.log_le_log (by norm_num) hY2
    have := Real.log_two_gt_d9
    linarith
  have hι1 : ι < 1 := by
    by_contra h1; push_neg at h1
    have : ι ≤ ι ^ 3 :=
      calc ι = ι * 1 * 1 := by ring
        _ ≤ ι * ι * ι := mul_le_mul (mul_le_mul le_rfl h1 (by norm_num) (by linarith)) h1
            (by norm_num) (by nlinarith)
        _ = ι ^ 3 := by ring
    exact hcase (hLι.trans this)
  have hY3 : (Fintype.card S : ℝ) * Fintype.card A * K / δ < 3 := by
    have h := Real.exp_lt_exp.2 hι1
    rw [hι, Real.exp_log (by positivity)] at h
    have he := Real.exp_one_lt_d9
    linarith
  have hK2 : (K : ℝ) < 2 := by
    rw [div_lt_iff₀ hδ] at hY3
    nlinarith
  have hKeq : (K : ℝ) = 1 := by
    have : K < 2 := by exact_mod_cast hK2
    have : K = 1 := by omega
    simp [this]
  have hC1 : 1 ≤ C := one_le_conc hH E πb ρb ρ πs hC
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hε2 : ε ^ 2 ≤ (H : ℝ) ^ 2 := pow_le_pow_left₀ hε.le hεH 2
  have hι3 : (0.3 : ℝ) ≤ ι ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.69) hι69 3
    norm_num at this; linarith
  rw [hKeq, div_le_iff₀ (by positivity), one_mul] at hKc
  have hH5 : (H : ℝ) ^ 2 ≤ (H : ℝ) ^ 5 := pow_le_pow_right₀ hH1 (by norm_num)
  have hSC : 1 ≤ (Fintype.card S : ℝ) * C := one_le_mul_of_one_le_of_one_le hS1 hC1
  have hbig : (H : ℝ) ^ 2 * (10 ^ 6 * cb ^ 2 * 0.3) ≤
      10 ^ 6 * cb ^ 2 * (H : ℝ) ^ 5 * Fintype.card S * C * ι ^ 3 := by
    have h1 : (H : ℝ) ^ 2 * 1 * 0.3 ≤ (H : ℝ) ^ 5 * (Fintype.card S * C) * ι ^ 3 :=
      mul_le_mul (mul_le_mul hH5 hSC (by norm_num) (by positivity)) hι3 (by norm_num)
        (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 10 ^ 6 * cb ^ 2)
    calc (H : ℝ) ^ 2 * (10 ^ 6 * cb ^ 2 * 0.3) = 10 ^ 6 * cb ^ 2 * ((H : ℝ) ^ 2 * 1 * 0.3) := by
          ring
      _ ≤ 10 ^ 6 * cb ^ 2 * ((H : ℝ) ^ 5 * (Fintype.card S * C) * ι ^ 3) := h2
      _ = _ := by ring
  have hcb2 : (10 : ℝ) ≤ 10 ^ 6 * cb ^ 2 * 0.3 := by nlinarith
  have h3 : (H : ℝ) ^ 2 * 10 ≤ (H : ℝ) ^ 2 * (10 ^ 6 * cb ^ 2 * 0.3) :=
    mul_le_mul_of_nonneg_left hcb2 (by positivity)
  have hHpos : 0 < (H : ℝ) ^ 2 := by positivity
  linarith

end StatisticalRL.LCBQFinite
