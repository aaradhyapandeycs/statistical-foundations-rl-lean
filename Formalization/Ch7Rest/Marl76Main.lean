import Formalization.Ch7Rest.Marl76Event
import Formalization.Ch7Rest.Marl76Arith

/-!
# Theorem 7.6 (restricted): the main probabilistic bound

`core`: for two data-causal maps from samples to joint policies that always return an (h = 1)
CCE of the empirical game, at the printed threshold with `C₁ = 400`, with probability at least
`1 − δ` both true gaps are at most `ε`.

Degenerate cases (`H ≤ 1`, or every player has a single action) hold surely. Otherwise the
simultaneous Bernstein event (`simultaneous_event`) with `k = 4 m' H S |𝒜|` rows is used; on it
the gap decomposition and the self-bounding evaluation error give the bound.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.FiniteHorizonGenerative

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- With a single step, values only depend on the rewards. -/
theorem valueJ_one_step (G Ĝ : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hr : ∀ t, Ĝ.reward i t = G.reward i t) (s : Fin S) :
    valueJ Ĝ π i 1 1 s = valueJ G π i 1 1 s := by
  simp [valueJ, FiniteDistribution.expectation, hr]

theorem gapJ_le_of_forall (G : MarkovGame m S H A) (π : JointPolicy m S A) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s i, bestResponseValueJ G π i s - valueJ G π i 1 H s ≤ ε) : gapJ G π ≤ ε :=
  Real.iSup_le (fun s => Real.iSup_le (fun i => h s i) hε) hε

instance gameSamplingLaw_isProbabilityMeasure (G : MarkovGame m S H A) (hS : 0 < S)
    (hA : ∀ i, 0 < A i) (N : ℕ) : IsProbabilityMeasure (gameSamplingLaw G hS hA N) := by
  change IsProbabilityMeasure (samplingLaw (gameStages G hS hA) N); infer_instance

theorem core (G : MarkovGame m S H A)
    (hR : ∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1)
    (hS : 0 < S) (hA : ∀ i, 0 < A i) (N : ℕ) (hN : 0 < N) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hεH : ε ≤ Real.sqrt H)
    (hthr : 400 * (H : ℝ) ^ 3 / ε ^ 2 *
      Real.log ((S : ℝ) * H * N * (∏ i, (A i : ℝ)) / δ) ≤ N)
    (Pol : Fin 2 → GameSamples m S H A N → JointPolicy m S A) (hPol : ∀ o, DataCausal (Pol o))
    (hcce : ∀ o data, IsCCE (empiricalGame G N hN data) (Pol o data)) :
    1 - δ ≤ (gameSamplingLaw G hS hA N).real {data | ∀ o, gapJ G (Pol o data) ≤ ε} := by
  classical
  set μ := gameSamplingLaw G hS hA N
  haveI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (samplingLaw (gameStages G hS hA) N); infer_instance
  have hH0 : 0 < H := by
    by_contra h0
    have : H = 0 := by omega
    subst this
    simp at hεH
    linarith
  have hεsq : ε ^ 2 ≤ H := by
    have h1 := pow_le_pow_left₀ hε.le hεH 2
    rwa [Real.sq_sqrt (Nat.cast_nonneg H)] at h1
  by_cases hdeg : H ≤ 1 ∨ ∀ i, A i < 2
  · -- degenerate cases hold surely
    have hall : ∀ data o, gapJ G (Pol o data) ≤ ε := by
      intro data o
      refine gapJ_le_of_forall G _ hε.le fun s i => ?_
      by_cases hAi1 : A i = 1
      · rw [bestResponseValueJ_eq_of_one G _ i hAi1 s, sub_self]; exact hε.le
      · have hH1 : H = 1 := by
          rcases hdeg with h | h
          · omega
          · have := h i; have := hA i; omega
        have hdec := gap_decomposition G (empiricalGame G N hN data) (Pol o data) (hcce o data) i
          (hA i) s
        subst hH1
        have e1 := valueJ_one_step (empiricalGame G N hN data) G
          (deviate (Pol o data) i (brPolicy G (Pol o data) i (hA i))) i (fun t => rfl) s
        have e2 := valueJ_one_step (empiricalGame G N hN data) G (Pol o data) i (fun t => rfl) s
        linarith
    have hset : {data | ∀ o, gapJ G (Pol o data) ≤ ε} = Set.univ :=
      Set.eq_univ_of_forall fun data o => hall data o
    rw [hset, probReal_univ]
    linarith
  · push_neg at hdeg
    obtain ⟨hH2, i0, hi0⟩ := hdeg
    have hJ : Nonempty (EventIndex m S H A) :=
      ⟨(0, ⟨i0, hi0⟩, false, ⟨0, hH0⟩, ⟨0, hS⟩, fun i => ⟨0, hA i⟩)⟩
    have hev := simultaneous_event G hR hS hA N hN Pol hPol hJ δ hδ hδ1
    refine hev.trans (measureReal_mono ?_ (measure_ne_top _ _))
    -- arithmetic
    set L := Real.log (4 * (Fintype.card (EventIndex m S H A) : ℝ) / δ) with hLdef
    set M : ℝ := ((Finset.univ.filter (fun i : Fin m => 2 ≤ A i)).card : ℝ)
    set P : ℝ := ∏ i, (A i : ℝ)
    set Λ := Real.log ((S : ℝ) * H * N * P / δ)
    have hMP : 2 * M ≤ P := by
      have := two_mul_card_le_prod A hA
      simp only [M, P]
      exact_mod_cast this
    have hM1 : 1 ≤ M := by
      simp only [M]
      exact_mod_cast Finset.card_pos.mpr ⟨i0, by simp [hi0]⟩
    have hP2 : 2 ≤ P := by linarith
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hL0 : 0 ≤ L := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hδ]
      have : (1 : ℝ) ≤ Fintype.card (EventIndex m S H A) := by
        exact_mod_cast Fintype.card_pos_iff.mpr hJ
      linarith
    have hLΛ : L ≤ 3 * Λ := by
      rw [hLdef, card_eventIndex]
      exact log_absorb M H S N P δ (by exact_mod_cast hH2) hP2 (by exact_mod_cast hS)
        (by exact_mod_cast hN) hδ hδ1 hMP hM1
    obtain ⟨hx, hfin⟩ := final_arith H ε Λ L N (by exact_mod_cast hH0) hε hεsq hNr hL0 hLΛ hthr
    set lam := ε / (8 * (H : ℝ) ^ 2)
    have hlam : 0 < lam := by positivity
    intro data hd o
    refine gapJ_le_of_forall G _ hε.le fun s i => ?_
    by_cases hAi1 : A i = 1
    · rw [bestResponseValueJ_eq_of_one G _ i hAi1 s, sub_self]; exact hε.le
    have hi : 2 ≤ A i := by have := hA i; omega
    have hAi : 0 < A i := hA i
    have hsb : ∀ b : Bool, ∀ s, |valueJ (empiricalGame G N hN data) (rhoSel G (Pol o data) i hAi b)
        i 1 H s - valueJ G (rhoSel G (Pol o data) i hAi b) i 1 H s| ≤
        lam * H ^ 2 + 2 * H * L / (lam * N) + 4 / 3 * H ^ 2 * L / N := by
      intro b s
      refine selfBound G (empiricalGame G N hN data) (rhoSel G (Pol o data) i hAi b) i
        (fun t => rfl) (fun t h1 h2 s a => hR i t s a h1 h2) L N hL0 hNr ?_ hx lam hlam s
      intro t ht1 ht2 s a
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      exact hd (o, ⟨i, hi⟩, b, ⟨t', by omega⟩, s, a)
    have hdec := gap_decomposition G (empiricalGame G N hN data) (Pol o data) (hcce o data) i hAi s
    have h1 := hsb true s
    have h2 := hsb false s
    simp only [rhoSel] at h1 h2
    have e1 := neg_abs_le (valueJ (empiricalGame G N hN data)
      (deviate (Pol o data) i (brPolicy G (Pol o data) i hAi)) i 1 H s -
        valueJ G (deviate (Pol o data) i (brPolicy G (Pol o data) i hAi)) i 1 H s)
    have e2 := le_abs_self (valueJ (empiricalGame G N hN data) (Pol o data) i 1 H s -
        valueJ G (Pol o data) i 1 H s)
    linarith

end StatisticalRL.Ch7Rest.Marl76
