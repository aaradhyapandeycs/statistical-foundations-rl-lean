import Formalization.Online.Regret.T0.OnlineT0ActualConditionalAssembly
import Formalization.Online.Regret.T0.OnlineT0ScalarHelpers
import Formalization.Online.Regret.T0.OnlineT0SingletonBudget
import Formalization.Online.Regret.Algebra.OnlineT56ScalarAlgebra

/-! Same-experiment suffix proof component: OnlineT0UniformConditional.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineActualStagePolicyGap_uniform_le_sourceT0_of_suffixBounds
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))
    (δ' c₁ c₂ : ℝ) (hδ' : 0 < δ') (hδ'small : δ' ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hw : sample ∈ onlineActualW12SuffixIotaEvent H K hH E fallback δ' c₁ c₂)
    (hT3 : ∀ j : Fin H,
      (∑ k : Fin K, ∑ n ∈ Finset.Ico j.val H,
        onlineCappedEpisodeT3 H (onlineT0ActualSuffixStage H K hH E sample.1 fallback sample.2 δ' c₁ c₂ k)
          (onlineT0ActualSuffixState H K hH E sample.1 fallback sample.2 δ' c₁ c₂ k)
          (onlineT0ActualSuffixAction H K hH E sample.1 fallback sample.2 δ' c₁ c₂ k)
          (Real.log (1 / δ')) c₁ c₂ n) ≤
      4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * Real.log (1 / δ')) +
      4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * Real.log (1 / δ')) +
      5 * (H : ℝ) * Real.log (1 / δ'))
    (hT4 : ∀ j : Fin H,
      |∑ k : Fin K, onlineT4SuffixEpisodeIncrement H K hH E fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂) j.val k sample| ≤
          Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ'))) :
    ∀ j : Fin H,
      (∑ k : Fin K, onlineActualStagePolicyGap H K hH E sample.1 fallback sample.2 δ' c₁ c₂ j k) ≤
        onlineActualT0SourceUpper H K hH E fallback sample δ' c₁ c₂ := by
  classical
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ'
  let L := Real.log (1 / δ')
  let V := onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂
  let D := onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  have hS : 1 ≤ S := by dsimp [S]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card State)
  have hA : 1 ≤ A := by dsimp [A]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Action)
  have hHreal : 1 ≤ (H : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hH)
  have hSA : 1 ≤ S * A := by
    have := mul_le_mul hS hA (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa using this
  have hSAH : 1 ≤ S * A * (H : ℝ) := by
    have := mul_le_mul hSA hHreal (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa [mul_assoc] using this
  have hSAH2 : 1 ≤ S^2 * A * (H : ℝ) := by
    have hS2 : 1 ≤ S^2 := by nlinarith [sq_nonneg (S - 1)]
    have hS2A := mul_le_mul hS2 hA (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    have hS2AH := mul_le_mul hS2A hHreal (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    simpa [mul_assoc] using hS2AH
  have hL : 1 ≤ L := onlineSmallConfidence_log_ge_one δ' hδ' hδ'small
  have hLnonneg : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1) hL
  have hIlarge : 20000 * L ≤ I := by
    dsimp [I, L]
    exact onlineT56_source_iota_large (Fintype.card State) (Fintype.card Action)
      H K δ' Fintype.card_pos Fintype.card_pos hH hK hδ' hδ'small
  have hV : 0 ≤ V := by
    dsimp [V, onlineActualT6Policy]
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hD : 0 ≤ D := by
    dsimp [D, onlineActualT6Difference]
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.expectation_nonneg _ (by intro s; positivity)
  have hIpos : 0 ≤ I := le_trans (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20000) hLnonneg) hIlarge
  have hDroot : Real.sqrt (S * A * H * D * I) ≤
      Real.sqrt (S^2 * A * H * D * I) := by
    apply Real.sqrt_le_sqrt
    have hS2 : S ≤ S^2 := by
      have hm := mul_le_mul_of_nonneg_right hS (show 0 ≤ S by positivity)
      simpa [pow_two] using hm
    have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1) hA
    have hH0 : 0 ≤ (H : ℝ) := le_trans (by norm_num : (0 : ℝ) ≤ 1) hHreal
    have hfac : 0 ≤ A * H * D * I :=
      mul_nonneg (mul_nonneg (mul_nonneg hA0 hH0) hD) hIpos
    have hmul := mul_le_mul_of_nonneg_right hS2 hfac
    calc
      S * A * H * D * I = S * (A * H * D * I) := by ring
      _ ≤ S^2 * (A * H * D * I) := hmul
      _ = S^2 * A * H * D * I := by ring
  have hAbsorbV := onlineT0Suffix_sqrt_radius_absorb S A (H : ℝ) V L I
    hSAH hV hLnonneg (by nlinarith)
  have hAbsorbD := onlineT0Suffix_sqrt_radius_absorb S A (H : ℝ) D L I
    hSAH hD hLnonneg (by nlinarith)
  have hAbsorbD2 := hAbsorbD.trans
    (mul_le_mul_of_nonneg_left hDroot (by norm_num : (0 : ℝ) ≤ 1 / 8))
  have hAdd : 5 * (H : ℝ) * L + Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * L) ≤
      7 * Real.sqrt ((K : ℝ) * (H : ℝ)^2) * L := by
    have hKroot : (H : ℝ) ≤ Real.sqrt ((K : ℝ) * (H : ℝ)^2) := by
      apply Real.le_sqrt_of_sq_le
      have hk1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
      have hmul := mul_le_mul_of_nonneg_right hk1 (sq_nonneg (H : ℝ))
      simpa only [one_mul] using hmul
    have hroot := onlineT0Suffix_random_radius_absorb
      ((K : ℝ) * (H : ℝ)^2) L (by positivity) hLnonneg hL
    have hrad : 2 * (K : ℝ) * (H : ℝ)^2 * L =
        2 * ((K : ℝ) * (H : ℝ)^2) * L := by ring
    have hroot' : Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * L) ≤
        2 * Real.sqrt ((K : ℝ) * (H : ℝ)^2) * L := by
      rw [hrad]
      exact hroot
    have h5L : 0 ≤ 5 * L := mul_nonneg (by norm_num) hLnonneg
    have hlinear := mul_le_mul_of_nonneg_right hKroot h5L
    have hlinear' : 5 * (H : ℝ) * L ≤
        5 * Real.sqrt ((K : ℝ) * (H : ℝ)^2) * L := by
      calc
        5 * (H : ℝ) * L = (H : ℝ) * (5 * L) := by ring
        _ ≤ Real.sqrt ((K : ℝ) * (H : ℝ)^2) * (5 * L) := hlinear
        _ = 5 * Real.sqrt ((K : ℝ) * (H : ℝ)^2) * L := by ring
    calc
      _ ≤ 5 * Real.sqrt ((K : ℝ) * (H : ℝ)^2) * L +
          2 * Real.sqrt ((K : ℝ) * (H : ℝ)^2) * L := add_le_add hlinear' hroot'
      _ = 7 * Real.sqrt ((K : ℝ) * (H : ℝ)^2) * L :=
        onlineT0Suffix_five_plus_two _ _
  have hmass : (1 / 8 : ℝ) * S * A * H^2 * I +
      (1 / 8 : ℝ) * S^2 * A * H^2 * I ≤ (1 / 4 : ℝ) * S^2 * A * H^2 * I := by
    simpa [mul_assoc] using onlineT0Suffix_mass_coefficient S (A * ((H : ℝ)^2 * I)) hS (by positivity)
  intro j
  have hwj := hw j
  have hb := onlineActualStageGap_suffix_conditional H K hH E sample.1 fallback sample.2 δ' c₁ c₂
    hδ' hδ'small hc₁ hc₂ j
    ((1 / 8 : ℝ) * Real.sqrt (S * A * H * V * I) +
      (1 / 8 : ℝ) * Real.sqrt (S * A * H * D * I) + (1 / 8 : ℝ) * S * A * H^2 * I)
    ((1 / 8 : ℝ) * Real.sqrt (S^2 * A * H * D * I) + (1 / 8 : ℝ) * S^2 * A * H^2 * I)
    (4 * Real.sqrt (V * L) + 4 * Real.sqrt (D * L) + 5 * (H : ℝ) * L)
    (Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * L))
    hwj.1 hwj.2 (hT3 j) ((le_abs_self _).trans (hT4 j))
  have hRV : 0 ≤ Real.sqrt (S * A * H * V * I) := Real.sqrt_nonneg _
  dsimp [onlineActualT0SourceUpper, S, A, I, L, V, D] at hb ⊢
  dsimp [S, A, I, L, V, D] at hDroot hAbsorbV hAbsorbD2 hAdd hmass hRV
  linarith
end StatisticalRL.OnlineRL
