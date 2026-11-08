import Formalization.Ch7Rest.FedSync79Noise

/-!
# Corrected Theorem 7.9 (FedSynQ): the good event (union bound)

Union over the `(T+1) K S A` targets `(t, k, s, a)`, `t ≤ T`, of the Azuma tail bounds
`noiseG_tail` at confidence `δ' = δ / ((T+1) K S A)`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Classical

namespace StatisticalRL.Ch7Rest.FedSync

open StatisticalRL StatisticalRL.OnlineRL StatisticalRL.Ch7Rest.Fed StatisticalRL.Ch7Rest.FedGeneric

set_option linter.unusedSectionVars false

local instance fedSyncEventStateMeasurable {State : Type} : MeasurableSpace State := ⊤

variable {State Action : Type} [Fintype State] [Fintype Action]

theorem fedSamplingLaw_isProbability (M : DiscountedMDP State Action) (T K : ℕ) :
    IsProbabilityMeasure (fedSamplingLaw M T K 1) := by
  show IsProbabilityMeasure (onlineStackProductLaw (rowLaw M T K))
  infer_instance

/-- **Good event.** With probability `> 1 - δ`, every noise process `noiseG u k s a`, `u ≤ T`, is
bounded by `σ = √(2 (1/(1-γ))² (2η/K) log(2/δ'))`, `δ' = δ / ((T+1) K S A)`. -/
theorem goodEvent_prob (M : DiscountedMDP State Action) (η : ℝ) (K τ : ℕ)
    (Q₀ : State → Action → ℝ) (T : ℕ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hτ : 1 ≤ τ) (hK : 1 ≤ K)
    (hητ : η * ((τ : ℝ) - 1) ≤ 1 / (K : ℝ))
    (hQ₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    1 - δ < (fedSamplingLaw M T K 1).real {data | ∀ u ≤ T, ∀ k s a,
      |noiseG M η K τ Q₀ (smOf M T K data) u k s a| ≤
        Real.sqrt (2 * ((1 / (1 - M.discount)) ^ 2 * (2 * η / K)) *
          Real.log (2 / (δ / (((T : ℝ) + 1) * K * Fintype.card State *
            Fintype.card Action))))} := by
  haveI := fedSamplingLaw_isProbability M T K
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  set μ := fedSamplingLaw M T K 1
  set C : ℝ := ((T : ℝ) + 1) * K * Fintype.card State * Fintype.card Action with hC
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hA : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast Fintype.card_pos
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hT1 : (1 : ℝ) ≤ (T : ℝ) + 1 := by have : (0 : ℝ) ≤ T := Nat.cast_nonneg T; linarith
  have hC1 : 1 ≤ C := by
    have h1 : (1 : ℝ) ≤ ((T : ℝ) + 1) * K := by nlinarith
    have h2 : (1 : ℝ) ≤ ((T : ℝ) + 1) * K * Fintype.card State := by nlinarith
    rw [hC]; nlinarith
  set δ' := δ / C with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ (by linarith)
  have hδ'1 : δ' < 1 := by
    rw [hδ', div_lt_one (by linarith)]
    linarith
  set σ := Real.sqrt (2 * ((1 / (1 - M.discount)) ^ 2 * (2 * η / K)) * Real.log (2 / δ'))
  set I : Finset (ℕ × Fin K × State × Action) := Finset.range (T + 1) ×ˢ Finset.univ with hI
  set bad : ℕ × Fin K × State × Action → Set (FedSamples State Action T K 1) := fun p =>
    {data | ¬ |noiseG M η K τ Q₀ (smOf M T K data) p.1 p.2.1 p.2.2.1 p.2.2.2| ≤ σ} with hbad
  set good := {data : FedSamples State Action T K 1 | ∀ u ≤ T, ∀ k s a,
      |noiseG M η K τ Q₀ (smOf M T K data) u k s a| ≤ σ} with hgood
  have hsub : goodᶜ ⊆ ⋃ p ∈ I, bad p := by
    intro data hd
    simp only [hgood, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hd
    obtain ⟨u, hu, k, s, a, hfail⟩ := hd
    simp only [Set.mem_iUnion, hI, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
      and_true]
    exact ⟨(u, k, s, a), by omega, hfail⟩
  have hbadp : ∀ p ∈ I, μ.real (bad p) < δ' := by
    intro p hp
    simp only [hI, Finset.mem_product, Finset.mem_range] at hp
    have h := noiseG_tail M η K τ Q₀ T hη0 hη1 hτ hητ hQ₀ p.1 (by omega) p.2.1 p.2.2.1 p.2.2.2
      δ' hδ'0 hδ'1
    have hc : bad p = {data | |noiseG M η K τ Q₀ (smOf M T K data) p.1 p.2.1 p.2.2.1 p.2.2.2| ≤
        σ}ᶜ := rfl
    rw [hc, probReal_compl_eq_one_sub ((Set.toFinite _).measurableSet)]
    linarith
  have hcard : (I.card : ℝ) = C := by
    simp only [hI, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, hC]
    push_cast
    ring
  have hIne : I.Nonempty := by
    obtain ⟨s⟩ := M.state_nonempty
    obtain ⟨a⟩ := M.action_nonempty
    exact ⟨(0, ⟨0, by omega⟩, s, a), by simp [hI]⟩
  have hbadsum : μ.real goodᶜ < δ :=
    calc μ.real goodᶜ ≤ μ.real (⋃ p ∈ I, bad p) := measureReal_mono hsub (measure_ne_top μ _)
      _ ≤ ∑ p ∈ I, μ.real (bad p) := measureReal_biUnion_finset_le I bad
      _ < ∑ _p ∈ I, δ' := Finset.sum_lt_sum_of_nonempty hIne hbadp
      _ = δ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, hδ']
        field_simp
  rw [probReal_compl_eq_one_sub ((Set.toFinite _).measurableSet)] at hbadsum
  linarith

end StatisticalRL.Ch7Rest.FedSync
