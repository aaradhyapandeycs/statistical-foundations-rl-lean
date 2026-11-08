import Formalization.ModelFree.AsyncQ.Path
import Formalization.ModelFree.AsyncQ.Prep
import Formalization.ModelFree.QLearningSourceTheoremClosure

/-! # Theorem 4.12 (corrected): asynchronous Q-learning on a single Markovian trajectory

Assembly of the plan for `thm:infinite-horizon-asyn` (`chapters/generative_model_model_free.tex`
:2062–2086): good events (Freedman for all windows/pairs/final counts, and Lemma V for all epoch
windows/pairs), their probability via finite union bounds, and the pathwise epoch contraction. -/

open MeasureTheory
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatisticalRL.AsyncQ

open StatisticalRL.FiniteMarkov StatisticalRL.QLearning

universe u v

attribute [local instance] pairMeasurableSpace

local instance pairMeasurableSingletonClass'' {S A : Type*} [Fintype S] [Fintype A] :
    @MeasurableSingletonClass (S × A) pairMeasurableSpace := ⟨fun _ ↦ trivial⟩

theorem one_sub_pow_le_exp {η : ℝ} (hη1 : η ≤ 1) (n : ℕ) :
    (1 - η) ^ n ≤ Real.exp (-(η * n)) := by
  have h1 : 1 - η ≤ Real.exp (-η) := by have := Real.add_one_le_exp (-η); linarith
  calc (1 - η) ^ n ≤ Real.exp (-η) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = Real.exp (-(η * n)) := by rw [← Real.exp_nat_mul]; ring_nf

theorem asyncQ_main (c₁ : ℝ) (hc₁ : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (S : Type u) (A : Type v) [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (μ : FiniteDistribution (S × A))
    (μmin : ℝ) (tmix : ℕ) (s₀ : S) (δ ε : ℝ) (T : ℕ)
    (hγ : 1 / 2 ≤ M.discount)
    (hst : ∀ y, ∑ x, μ.prob x * pairKernel M πb x y = μ.prob y)
    (htmix : ∀ x : S × A, tvDist (pairPow M πb tmix x) μ.prob ≤ 1 / 4)
    (hμmin : ∀ x, μmin ≤ μ.prob x) (hμ0 : 0 < μmin) (hT1 : 1 ≤ T)
    (hT2 : 2 ≤ T ∨ 2 ≤ Fintype.card S * Fintype.card A)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbud : asyncC₂ c₁ * Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / δ) ^ 2 / μmin *
        max (Real.log T ^ 3 / ((1 - M.discount) ^ 4 * ε ^ 2)) (tmix / (1 - M.discount)) ≤ T)
    (Q₀ : S → A → ℝ) (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) :
    1 - δ ≤ (pathLaw M πb s₀ T).real {x | ∀ s a,
      |iterate M (c₁ * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε} := by
  haveI : Nonempty S := M.state_nonempty
  haveI : Nonempty A := M.action_nonempty
  set K := pairKernel M πb with hKdef
  have hK := pairKernel_isStochastic M πb
  have hν := initLaw_isProb πb s₀
  have hμp : IsProb μ.prob := ⟨μ.prob_nonneg, μ.sum_prob⟩
  have hmix : mixDist K μ.prob tmix ≤ 1 / 4 := (mixDist_le_iff _ _ _).2 htmix
  set tb := max tmix 1 with htbdef
  have htb1 : 1 ≤ tb := le_max_right _ _
  have htb : mixDist K μ.prob tb ≤ 1 / 4 := (mixDist_antitone hK _ (le_max_left _ _)).trans hmix
  set SA : ℝ := (Fintype.card S : ℝ) * Fintype.card A with hSAdef
  have hcard : Fintype.card (S × A) = Fintype.card S * Fintype.card A := Fintype.card_prod S A
  have hSA1 : 1 ≤ SA := by
    have h1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
    have h2 : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
    nlinarith
  have hμ1 : μmin ≤ 1 := by
    have x := Classical.arbitrary (S × A)
    have hx : μ.prob x ≤ ∑ y, μ.prob y :=
      single_le_sum (f := μ.prob) (fun y _ ↦ μ.prob_nonneg y) (mem_univ x)
    rw [μ.sum_prob] at hx
    exact (hμmin x).trans hx
  -- `T ≥ 2` (weakest correction `2 ≤ T ∨ 2 ≤ SA`)
  have hT2' : 2 ≤ T := by
    rcases hT2 with h | h
    · exact h
    by_contra hlt
    have hT1' : T = 1 := by omega
    have hcardR : (2 : ℝ) ≤ Fintype.card (S × A) := by rw [hcard]; exact_mod_cast h
    have htm : 1 ≤ tmix := by
      by_contra h0
      have h0' : tmix = 0 := by omega
      have h34 : ∀ x, 3 / 4 ≤ μ.prob x := fun x ↦ by
        have h1 := one_sub_le_tvDist_zero (K := K) hμp x
        have h2 := htmix x
        rw [h0'] at h2
        unfold pairPow at h2
        linarith
      have : ∑ x : S × A, (3 / 4 : ℝ) ≤ ∑ x, μ.prob x := sum_le_sum fun x _ ↦ h34 x
      simp only [sum_const, card_univ, nsmul_eq_mul, μ.sum_prob] at this
      nlinarith
    have hμ2 : μmin ≤ 1 / 2 := by
      have : ∑ x : S × A, μmin ≤ ∑ x, μ.prob x := sum_le_sum fun x _ ↦ hμmin x
      simp only [sum_const, card_univ, nsmul_eq_mul, μ.sum_prob] at this
      nlinarith
    rw [hT1'] at hbud
    simp only [Nat.cast_one] at hbud
    exact budget_excludes_one (le_trans (by norm_num) (le_max_right _ _ : (4096 : ℝ) ≤ asyncC₂ c₁))
      (by rw [hSAdef]; have : (2 : ℝ) ≤ (Fintype.card S * Fintype.card A : ℕ) := by exact_mod_cast h
          push_cast at this; linarith)
      hγ M.discount_lt_one hδ hδ1 hμ0 hμ2 (by exact_mod_cast htm) hbud
  -- arithmetic hypotheses
  have hc₂0 : 0 ≤ asyncC₂ c₁ := le_trans (by norm_num) (le_max_right _ _ : (4096 : ℝ) ≤ asyncC₂ c₁)
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT2'
  have hP2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hTR
  obtain ⟨hA2, hA3⟩ := budget_hyps (c₂ := asyncC₂ c₁) (ι := Real.log (SA * T / δ))
    hγ M.discount_lt_one hμ0 hε hε1 hc₂0 hP2 (Nat.cast_nonneg tmix) hbud
  have htbR : ((tb : ℕ) : ℝ) = max (tmix : ℝ) 1 := by rw [htbdef, Nat.cast_max, Nat.cast_one]
  have H : ArithHyp c₁ M.discount ε δ μmin SA tb M.effectiveHorizon (Real.log T)
      (Real.log (SA * T / δ)) T :=
    { hc₁ := hc₁, hc₁1 := hc₁1, hγ := hγ, hγ1 := M.discount_lt_one, hε := hε, hε1 := hε1,
      hδ := hδ, hδ1 := hδ1, hμ := hμ0, hμ1 := hμ1, hSA := hSA1,
      htb := by exact_mod_cast htb1, hT := hTR, hh := rfl, hP := rfl, hι := rfl,
      hA2 := hA2, hA3 := by rw [htbR]; exact hA3 }
  set γ := M.discount with hγdef
  set h := M.effectiveHorizon with hhdef
  set P := Real.log (T : ℝ) with hPdef
  set ι := Real.log (SA * T / δ) with hιdef
  have hH := M.effectiveHorizon_nonneg
  have hγ0 := M.discount_nonneg
  set η := c₁ * P ^ 3 / ((1 - γ) * T * μmin) with hηdef
  have hηeq : η = c₁ * P ^ 3 * h / (T * μmin) := by
    rw [hηdef, H.hh]
    have : 1 - γ ≠ 0 := by linarith [M.discount_lt_one]
    have : (T : ℝ) ≠ 0 := by positivity
    have : μmin ≠ 0 := hμ0.ne'
    field_simp
  have hη0 : 0 < η := hηeq ▸ H.eta_pos
  have hη1 : η ≤ 1 := hηeq ▸ H.eta_le_one
  obtain ⟨hK1, hKlo, hKhi, hK2⟩ := H.Kep_facts
  set Kep := ⌈2 * h * Real.log (4 * h / ε)⌉₊ with hKepdef
  have hℓ := H.ell_ge (Tn := T) rfl hK1 hKhi hK2
  set ℓ := T / Kep with hℓdef
  have hKℓ : Kep * ℓ ≤ T := Nat.mul_div_le T Kep
  obtain ⟨hb1, hbμ, hb9⟩ := H.block_facts
  set b := ⌈8 * (tb : ℝ) / μmin⌉₊ with hbdef
  obtain ⟨h2b, hJι, hJb⟩ := H.J_facts hℓ hb1 hb9
  set J := ℓ / b with hJdef
  obtain ⟨hδ₁0, hδ₁1, hL0, hL4⟩ := H.delta1_facts
  set δ₁ := δ / (4 * SA * T * (T + 1) ^ 2) with hδ₁def
  set L := Real.log (2 / δ₁) with hLdef
  set ρ := 8 * η * L with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρle : ρ ≤ ε ^ 2 / (128 * h ^ 3) := by rw [hρdef, hηeq]; exact H.rho_le hL0.le hL4
  have hρ16 : ρ ≤ 1 / 16 := by
    refine hρle.trans ?_
    have hh2 := H.h_ge
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
    have h2 : (2 : ℝ) ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ (by norm_num) hh2 3
    norm_num at h2
    linarith
  set θ := Real.exp (-(η * (ℓ * μmin / 8))) with hθdef
  have hθle : θ ≤ ε / (8 * h ^ 2) := by rw [hθdef, hηeq]; exact H.theta_le hℓ
  have hθ0 : 0 ≤ θ := (Real.exp_pos _).le
  have hfin := H.final_le hρ0 hρle hθ0 hθle hKlo
  have hKT : (Kep : ℝ) ≤ T := by linarith
  -- the probability space
  set μP := pathLaw M πb s₀ T with hμPdef
  haveI : IsProbabilityMeasure μP := pathMeasure_isProb hK hν T
  set Qp := qRobustPlusFixedPoint M ρ (2 * ρ * h) hρ0 with hQpdef
  set Qm := qRobustMinusFixedPoint M ρ (2 * ρ * h) hρ0 with hQmdef
  have hspan := qRobustComparator_value_pairwise_span M ρ (2 * ρ * h) hρ0
  let Vc : Bool → S → ℝ := fun σ ↦ if σ then qLearningValue M Qp else qLearningValue M Qm
  have hVspan : ∀ σ s₁ s₂, |Vc σ s₁ - Vc σ s₂| ≤ h := fun σ s₁ s₂ ↦ by
    cases σ
    · exact (hspan s₁ s₂).2
    · exact (hspan s₁ s₂).1
  -- Freedman good event
  let IF : Finset ((S × A) × ℕ × ℕ × ℕ × Bool) :=
    (univ : Finset (S × A)) ×ˢ (range Kep ×ˢ (range (T + 1) ×ˢ (range (T + 1) ×ˢ
      (univ : Finset Bool))))
  let GFi : (S × A) × ℕ × ℕ × ℕ × Bool → Set (Fin (T + 1) → S × A) := fun i ↦
    {x | i.2.1 * ℓ + i.2.2.1 ≤ T →
      |∑ j ∈ range i.2.2.1, weight (visits x (i.2.1 * ℓ) i.1) η i.2.2.2.1 j *
        noise M x (i.2.1 * ℓ) i.1 (Vc i.2.2.2.2) j| ≤
        γ * Real.sqrt (ρ * (M.transition i.1.1 i.1.2).variance (Vc i.2.2.2.2)) + γ * ρ * h / 6}
  have hGF : 1 - ∑ i ∈ IF, δ₁ ≤ μP.real (⋂ i ∈ IF, GFi i) := by
    refine prob_biInter_ge μP IF GFi (fun _ ↦ δ₁) fun i _ ↦ ?_
    by_cases hm : i.2.1 * ℓ + i.2.2.1 ≤ T
    · have hw := window_freedman M πb s₀ (Vc i.2.2.2.2) (hVspan i.2.2.2.2) i.1 hη0 hη1
        (i.2.1 * ℓ) i.2.2.1 i.2.2.2.1 hm δ₁ hδ₁0 hδ₁1
      exact hw.trans (measureReal_mono (fun x hx _ ↦ hx) (measure_ne_top _ _))
    · have : GFi i = Set.univ := Set.eq_univ_of_forall fun x hx ↦ absurd hx hm
      rw [this, probReal_univ]; linarith
  have hIF : ∑ i ∈ IF, δ₁ ≤ δ / 2 := by
    rw [sum_const, nsmul_eq_mul]
    simp only [IF, card_product, card_univ, card_range, Fintype.card_prod, Fintype.card_bool]
    have := H.fail_F hKT (Nat.cast_nonneg _)
    push_cast
    calc ((Fintype.card S : ℝ) * Fintype.card A * (Kep * ((T + 1) * ((T + 1) * 2)))) * δ₁
        = 2 * SA * Kep * (T + 1) * (T + 1) * δ₁ := by rw [hSAdef]; ring
      _ ≤ δ / 2 := this
  -- visit good event (Lemma V)
  obtain ⟨c, hbc⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hbcR : (b : ℝ) = c + 1 := by rw [hbc]; push_cast; ring
  have hJbℓ : J * b ≤ ℓ := Nat.div_mul_le_self ℓ b
  let IV : Finset ((S × A) × ℕ) := (univ : Finset (S × A)) ×ˢ range Kep
  let GVi : (S × A) × ℕ → Set (Fin (T + 1) → S × A) := fun i ↦
    {x | (J : ℝ) * ((c + 1) * μ.prob i.1) / 4 ≤
      ∑ k ∈ range (J * (c + 1)), ind i.1 (pathAt x (i.2 * ℓ + k))}
  have hGV : 1 - ∑ i ∈ IV, Real.exp (-((J : ℝ) / 25)) ≤ μP.real (⋂ i ∈ IV, GVi i) := by
    refine prob_biInter_ge μP IV GVi _ fun i hi ↦ ?_
    have hk : i.2 < Kep := mem_range.mp (mem_product.mp hi).2
    have hz : 0 < μ.prob i.1 := lt_of_lt_of_le hμ0 (hμmin i.1)
    have hb8 : 8 * (tb : ℝ) ≤ (c + 1) * μ.prob i.1 := by
      rw [← hbcR]
      exact hbμ.trans (mul_le_mul_of_nonneg_left (hμmin i.1) (Nat.cast_nonneg _))
    have hJT : i.2 * ℓ + J * (c + 1) ≤ T + 1 := by
      rw [← hbc]
      have : (i.2 + 1) * ℓ ≤ Kep * ℓ := Nat.mul_le_mul_right ℓ hk
      rw [Nat.succ_mul] at this
      omega
    have hw := window_visits_tail hK hν hμp hst htb1 htb hz hb8 (n := T) (i.2 * ℓ) J hJT
    set N : (Fin (T + 1) → S × A) → ℝ :=
      fun x ↦ ∑ k ∈ range (J * (c + 1)), ind i.1 (pathAt x (i.2 * ℓ + k))
    have hbad : μP.real {x | N x < (J : ℝ) * ((c + 1) * μ.prob i.1) / 4} ≤
        Real.exp (-((J : ℝ) / 25)) := by
      rw [hμPdef, pathLaw_eq, pathMeasure_real hK hν.nonneg]
      refine le_trans (le_of_eq ?_) hw
      unfold pathExp
      refine sum_congr rfl fun x _ ↦ ?_
      by_cases hx : N x < (J : ℝ) * ((c + 1) * μ.prob i.1) / 4
      · rw [Set.indicator_of_mem (show x ∈ {x | N x < _} from hx)]
        simp only [N] at hx
        beta_reduce
        rw [if_pos hx]
      · rw [Set.indicator_of_notMem (show x ∉ {x | N x < _} from hx)]
        simp only [N] at hx
        beta_reduce
        rw [if_neg hx]
    have hcompl : GVi i = {x | N x < (J : ℝ) * ((c + 1) * μ.prob i.1) / 4}ᶜ := by
      ext x; simp [GVi, N, not_lt]
    rw [hcompl, measureReal_compl (MeasurableSet.of_discrete), probReal_univ]
    linarith
  have hIV : ∑ i ∈ IV, Real.exp (-((J : ℝ) / 25)) ≤ δ / 2 := by
    rw [sum_const, nsmul_eq_mul]
    simp only [IV, card_product, card_univ, card_range, Fintype.card_prod]
    have := H.fail_V hKT (Nat.cast_nonneg _) hJι
    push_cast
    calc ((Fintype.card S : ℝ) * Fintype.card A * Kep) * Real.exp (-((J : ℝ) / 25))
        = SA * Kep * Real.exp (-((J : ℝ) / 25)) := by rw [hSAdef]
      _ ≤ δ / 2 := this
  have hboth := prob_inter_ge μP hGF hGV
  refine le_trans (by linarith) (hboth.trans (measureReal_mono ?_ (measure_ne_top _ _)))
  rintro x ⟨hxF, hxV⟩
  simp only [Set.mem_iInter] at hxF hxV
  -- visits
  have hvis : ∀ z : S × A, ∀ k < Kep, ∀ K', ℓ ≤ K' →
      (1 - η) ^ cnt (visits x (k * ℓ) z) K' ≤ θ := by
    intro z k hk K' hK'
    have hv := hxV (z, k) (mem_product.mpr ⟨mem_univ _, mem_range.mpr hk⟩)
    simp only [GVi, Set.mem_setOf_eq] at hv
    have hcntR : (cnt (visits x (k * ℓ) z) (J * (c + 1)) : ℝ) =
        ∑ i ∈ range (J * (c + 1)), ind z (pathAt x (k * ℓ + i)) := by
      rw [cnt_cast]; rfl
    have hmono : cnt (visits x (k * ℓ) z) (J * (c + 1)) ≤ cnt (visits x (k * ℓ) z) K' :=
      cnt_mono _ (by rw [← hbc]; omega)
    have hmonoR : (cnt (visits x (k * ℓ) z) (J * (c + 1)) : ℝ) ≤
        (cnt (visits x (k * ℓ) z) K' : ℝ) := by exact_mod_cast hmono
    have hz : μmin ≤ μ.prob z := hμmin z
    have hcnt : (ℓ : ℝ) * μmin / 8 ≤ cnt (visits x (k * ℓ) z) K' := by
      have h1 : (ℓ : ℝ) / 2 ≤ J * (c + 1) := by rw [← hbcR]; exact hJb
      have h2 : (ℓ : ℝ) * μmin / 8 ≤ (J : ℝ) * ((c + 1) * μ.prob z) / 4 := by
        have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
        have : (ℓ : ℝ) / 2 * μmin ≤ (J * (c + 1)) * μ.prob z :=
          mul_le_mul h1 hz hμ0.le (by positivity)
        linarith
      linarith
    calc (1 - η) ^ cnt (visits x (k * ℓ) z) K'
        ≤ Real.exp (-(η * cnt (visits x (k * ℓ) z) K')) := one_sub_pow_le_exp hη1 _
      _ ≤ θ := by
          rw [hθdef]
          exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hcnt hη0.le))
  -- fluctuations
  have hfl : ∀ σ : Bool, ∀ z : S × A, ∀ k < Kep, ∀ m n, m ≤ T → n ≤ T → k * ℓ + m ≤ T →
      |∑ j ∈ range m, weight (visits x (k * ℓ) z) η n j * noise M x (k * ℓ) z (Vc σ) j| ≤
        γ * Real.sqrt (ρ * (M.transition z.1 z.2).variance (Vc σ)) + γ * ρ * h / 6 :=
    fun σ z k hk m n hm hn hkm ↦ hxF (z, k, m, n, σ)
      (by simp only [IF, mem_product, mem_univ, mem_range, true_and, and_true]; omega) hkm
  have hpb := path_bound M hη0 hη1 hρ0 hρ16 hθ0 Q₀ h₀ x Kep ℓ hKℓ hvis
    (fun z k hk m n hm hn hkm ↦ hfl true z k hk m n hm hn hkm)
    (fun z k hk m n hm hn hkm ↦ hfl false z k hk m n hm hn hkm)
  have hB := epochBound_le (R := h) (B₀ := h) hγ0 hθ0 hH hfin.1 Kep
  intro s a
  have hcl := qSource_robust_comparator_closeness_from_stopped_law M ρ hρ0 hρ0 s a
  obtain ⟨hp, hm⟩ := hpb s a
  have hcl1 := abs_le.mp hcl.1
  have hcl2 := abs_le.mp hcl.2
  have hf := hfin.2
  rw [abs_le]
  constructor <;> linarith

end StatisticalRL.AsyncQ

namespace StatisticalRL.AsyncQ

open StatisticalRL.FiniteMarkov StatisticalRL.QLearning

/-- Library form: for every `c₁ ∈ (0,1]` the constant `c₂ = max(e^{32/c₁}, 4096)` works (the
growth `e^{32/c₁}` is a proof artifact). Uniform ergodicity and attainment of `μ_min` are not needed; only
`TV(P^{t_mix}(·|s,a), μ) ≤ 1/4` and stationarity of `μ` are used. -/
theorem asyncQ_exists_c₂ (c₁ : ℝ) (hc₁ : 0 < c₁) (hc₁1 : c₁ ≤ 1) :
    ∃ c₂ : ℝ, 0 < c₂ ∧
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
      (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (μ : FiniteDistribution (S × A))
      (μmin : ℝ) (tmix : ℕ) (s₀ : S) (δ ε : ℝ) (T : ℕ),
      1 / 2 ≤ M.discount →
      (∀ y, ∑ x, μ.prob x * pairKernel M πb x y = μ.prob y) →
      (∀ x : S × A, tvDist (pairPow M πb tmix x) μ.prob ≤ 1 / 4) →
      (∀ x, μmin ≤ μ.prob x) → 0 < μmin → 1 ≤ T →
      (2 ≤ T ∨ 2 ≤ Fintype.card S * Fintype.card A) →
      0 < δ → δ < 1 → 0 < ε → ε ≤ 1 →
      c₂ * Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / δ) ^ 2 / μmin *
          max (Real.log T ^ 3 / ((1 - M.discount) ^ 4 * ε ^ 2)) (tmix / (1 - M.discount)) ≤ T →
      ∀ Q₀ : S → A → ℝ, (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
      1 - δ ≤ (pathLaw M πb s₀ T).real {x | ∀ s a,
        |iterate M (c₁ * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε} :=
  ⟨asyncC₂ c₁, lt_of_lt_of_le (by norm_num) (le_max_right _ _ : (4096 : ℝ) ≤ asyncC₂ c₁),
    fun S A _ _ _ _ M πb μ μmin tmix s₀ δ ε T hγ hst htmix hμmin hμ0 hT1 hT2 hδ hδ1 hε hε1 hbud
      Q₀ h₀ ↦ asyncQ_main c₁ hc₁ hc₁1 S A M πb μ μmin tmix s₀ δ ε T hγ hst htmix hμmin hμ0 hT1
        hT2 hδ hδ1 hε hε1 hbud Q₀ h₀⟩

end StatisticalRL.AsyncQ
