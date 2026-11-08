import Formalization.Ch7Rest.FedSync79Event
import Formalization.Ch7Rest.FedSync79Rate

/-!
# Corrected Theorem 7.9 (FedSynQ, `thm:dist-syncq-local`): the export

`chapters/federated_RL.tex:99–117` (algorithm :35–90), with explicit universal constants
`c_η = 1/216`, `c_T = 10⁴`, the true independent generative law `fedSamplingLaw M T K 1` and the
true optimal Q-function `M.optimalityFixedPoint`, under the added hypothesis `η ≤ 1`
(SOURCE-ISSUES C41: the printed `η` (114) can exceed the algorithm's input range `0 < η < 1`).

The export assumes `1 ≤ K`, `1 ≤ τ`, `1 ≤ T`, `δ ∈ (0,1)`, `0 < ε ≤ 1/(1-γ)`,
`Q₀ ∈ [0, 1/(1-γ)]`, the printed `η` (114), `η ≤ 1`, the printed τ condition (106) and the
printed `T` condition (112–113). It does not use `γ > 0` or `τ ∣ T`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.FedSync

open StatisticalRL StatisticalRL.Ch7Rest.Fed StatisticalRL.Ch7Rest.FedGeneric

variable {State Action : Type} [Fintype State] [Fintype Action]

theorem expectation_of_subsingleton [Subsingleton State] (d : FiniteDistribution State)
    (f : State → ℝ) (y : State) : d.expectation f = f y := by
  have hf : f = fun _ => f y := funext fun x => by rw [Subsingleton.elim x y]
  rw [hf, FiniteDistribution.expectation_const]

theorem noiseG_of_subsingleton [Subsingleton State] (M : DiscountedMDP State Action) (η : ℝ)
    (K τ : ℕ) (Q₀ : State → Action → ℝ) (sm : ℕ → Fin K → State → Action → State) (t : ℕ)
    (k : Fin K) (s : State) (a : Action) : noiseG M η K τ Q₀ sm t k s a = 0 := by
  have hw : ∀ u j, noiseW M η K τ Q₀ sm u j s a = 0 := by
    intro u j
    unfold noiseW
    rw [expectation_of_subsingleton _ _ (sm (u + 1) j s a), sub_self]
  unfold noiseG
  simp [hw]

/-- **Corrected Theorem 7.9 (library export).** -/
theorem fedSynQ_error_le_of_eta_le_one (M : DiscountedMDP State Action) (K τ T : ℕ) (δ ε : ℝ)
    (Q₀ : State → Action → ℝ) (hK : 1 ≤ K) (hτ : 1 ≤ τ) (hT : 1 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεH : ε ≤ 1 / (1 - M.discount))
    (hQ₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) (η : ℝ)
    (hη : η = 1 / 216 * K * (1 - M.discount) ^ 4 * ε ^ 2 /
      Real.log (Fintype.card State * Fintype.card Action * K * T / δ))
    (hη1 : η ≤ 1)
    (hτc : (τ : ℝ) ≤ 1 + 1 / η * min ((1 - M.discount) / (8 * M.discount)) (1 / (K : ℝ)))
    (hTc : 10000 / (K * (1 - M.discount) ^ 5 * ε ^ 2) *
        Real.log (Fintype.card State * Fintype.card Action * K * T /
          (δ * ε * (1 - M.discount) ^ 2)) ^ 3 ≤ T) :
    1 - δ ≤ (fedSamplingLaw M T K 1).real {data | ∀ s a,
      |fedOutput M η K τ Q₀ (fun t k s a ↦ fedSamplesExtend M T K 1 data t k s a 0) T s a -
        M.optimalityFixedPoint s a| ≤ ε} := by
  haveI := fedSamplingLaw_isProbability M T K
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hg0 : 0 < 1 - M.discount := by linarith
  have hg1 : 1 - M.discount ≤ 1 := by linarith
  have hSn : 1 ≤ Fintype.card State := Fintype.card_pos
  have hAn : 1 ≤ Fintype.card Action := Fintype.card_pos
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast hSn
  have hA : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast hAn
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set P : ℝ := Fintype.card State * Fintype.card Action * K * T with hP
  have hP1 : 1 ≤ P := by
    rw [hP]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hS hA) hKr) hTr
  have hℓpos : 0 < Real.log (P / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ]; linarith
  have hηpos : 0 < η := by
    rw [hη]
    have : (0 : ℝ) < K := by linarith
    positivity
  have hη0 : 0 ≤ η := hηpos.le
  have hητ : η * ((τ : ℝ) - 1) ≤ 1 / (K : ℝ) := by
    have h1 : (τ : ℝ) - 1 ≤ 1 / η * (1 / (K : ℝ)) := by
      have := mul_le_mul_of_nonneg_left
        (min_le_right ((1 - M.discount) / (8 * M.discount)) (1 / (K : ℝ)))
        (by positivity : (0 : ℝ) ≤ 1 / η)
      linarith
    calc η * ((τ : ℝ) - 1) ≤ η * (1 / η * (1 / (K : ℝ))) := mul_le_mul_of_nonneg_left h1 hη0
      _ = 1 / (K : ℝ) := by field_simp
  have hεg : ε * (1 - M.discount) ≤ 1 := by
    rw [le_div_iff₀ hg0] at hεH; linarith
  by_cases hP2 : 2 ≤ Fintype.card State * Fintype.card Action * K * T
  · -- general case
    have hP2r : (2 : ℝ) ≤ P := by rw [hP]; exact_mod_cast hP2
    have hE := goodEvent_prob M η K τ Q₀ T hη0 hη1 hτ hK hητ hQ₀ δ hδ hδ1
    set C : ℝ := ((T : ℝ) + 1) * K * Fintype.card State * Fintype.card Action with hC
    set σ := Real.sqrt (2 * ((1 / (1 - M.discount)) ^ 2 * (2 * η / K)) *
      Real.log (2 / (δ / C))) with hσ
    have hC1 : 1 ≤ C := by
      have h0 : (1 : ℝ) ≤ (T : ℝ) + 1 := by linarith
      rw [hC]
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le h0 hKr) hS) hA
    have hCP : 2 * C ≤ 4 * P := by
      have hd : 4 * P - 2 * C =
          2 * ((K : ℝ) * Fintype.card State * Fintype.card Action) * ((T : ℝ) - 1) := by
        rw [hP, hC]; ring
      have : 0 ≤ 2 * ((K : ℝ) * Fintype.card State * Fintype.card Action) * ((T : ℝ) - 1) := by
        have : (0 : ℝ) ≤ (T : ℝ) - 1 := by linarith
        positivity
      linarith
    have hσle : σ ≤ (1 - M.discount) * ε / 2 :=
      noise_le (1 - M.discount) ε δ η K P C hg0 hε hδ hδ1 (by linarith) hP2r hC1 hCP hη
    have hbias : (1 - η * (1 - M.discount)) ^ T * (1 / (1 - M.discount)) ≤ ε / 2 :=
      bias_le (1 - M.discount) ε δ η K P T hg0 hg1 hε hεg hδ hδ1 (by linarith) hP2r hη hη1 hTc
    have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
    have hnoise : M.discount ^ 2 * σ / (1 - M.discount) + M.discount * σ ≤ ε / 2 := by
      have heq : M.discount ^ 2 * σ / (1 - M.discount) + M.discount * σ =
          M.discount * σ / (1 - M.discount) := by
        field_simp
        ring
      rw [heq, div_le_iff₀ hg0]
      have h1 : M.discount * σ ≤ σ := by
        have := mul_le_mul_of_nonneg_right hγ1.le hσ0
        linarith
      have h2 : σ ≤ ε / 2 * (1 - M.discount) := by linarith
      linarith
    refine le_of_lt (lt_of_lt_of_le hE (measureReal_mono ?_))
    intro data hd s a
    have := fedOutput_abs_le M η K τ Q₀ (smOf M T K data) hη0 hη1 hK hQ₀ σ hσ0 T hd s a
    exact this.trans (by linarith)
  · -- degenerate case `S = A = K = T = 1`
    have hprod : Fintype.card State * Fintype.card Action * K * T = 1 := by
      have : 1 ≤ Fintype.card State * Fintype.card Action * K * T :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    have hT1 : T = 1 := Nat.eq_one_of_mul_eq_one_left hprod
    have h3 := Nat.eq_one_of_mul_eq_one_right hprod
    have hK1 : K = 1 := Nat.eq_one_of_mul_eq_one_left h3
    have h2 := Nat.eq_one_of_mul_eq_one_right h3
    have hS1 : Fintype.card State = 1 := Nat.eq_one_of_mul_eq_one_right h2
    have hA1 : Fintype.card Action = 1 := Nat.eq_one_of_mul_eq_one_left h2
    haveI : Subsingleton State := Fintype.card_le_one_iff_subsingleton.mp hS1.le
    subst hT1 hK1
    rw [hP, hS1, hA1] at hη hTc
    simp only [Nat.cast_one, one_mul, mul_one] at hη hTc
    have hdeg := degenerate_le (1 - M.discount) ε δ η hg0 hg1 hε hεg hδ hδ1 hη hTc
    have huniv : {data : FedSamples State Action 1 1 1 | ∀ s a,
        |fedOutput M η 1 τ Q₀ (fun t k s a ↦ fedSamplesExtend M 1 1 1 data t k s a 0) 1 s a -
          M.optimalityFixedPoint s a| ≤ ε} = Set.univ := by
      ext data
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro s a
      have hG : ∀ u ≤ 1, ∀ k s a, |noiseG M η 1 τ Q₀ (smOf M 1 1 data) u k s a| ≤ 0 := by
        intro u _ k s a
        rw [noiseG_of_subsingleton]
        simp
      have := fedOutput_abs_le M η 1 τ Q₀ (smOf M 1 1 data) hη0 hη1 le_rfl hQ₀ 0 le_rfl 1 hG s a
      simp only [pow_one, mul_zero, zero_div, add_zero] at this
      exact this.trans hdeg
    rw [huniv, probReal_univ]
    linarith

end StatisticalRL.Ch7Rest.FedSync
