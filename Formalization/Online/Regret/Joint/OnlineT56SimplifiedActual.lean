import Formalization.Online.Regret.T2.OnlineT2SourceBound
import Formalization.Online.Regret.T3.OnlineRegretT3SourceBound
import Formalization.Online.Regret.Joint.W123Definitions
import Formalization.Online.Regret.Algebra.OnlineT56RadiusBridge

/-! Pointwise source T56 simplification, onlineRL.tex 4040–4067.
The actual first T5/low bounds and W3 bound are explicit intermediate inputs.
The final same-law probability producer must discharge them separately. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem onlineActualT56_simplified_of_bounds
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hI : 8 * max (c₁^2) c₂ * (Real.log K / Real.log 2) * Real.log (1 / δ) ≤
      onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ)
    (hlarge : (Fintype.card State : ℝ) * Fintype.card Action * H^2 *
      onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ ≤ (K : ℝ))
    (h5 : onlineActualT5 H K hH E initial fallback path δ c₁ c₂ ≤
      (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E initial fallback path δ c₁ c₂ h k) +
      2 * (H : ℝ) * onlineActualT2 H K hH E initial fallback path δ c₁ c₂ +
      2 * (K : ℝ) * (H : ℝ)^2 +
      Real.sqrt (32 * (H : ℝ)^2 * onlineActualT6UCB H K hH E initial fallback path δ c₁ c₂ * Real.log (1 / δ)) +
      5 * (H : ℝ)^2 * Real.log (1 / δ))
    (hlow : onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂ ≤
      (K : ℝ) * (H : ℝ)^2 + Real.sqrt (2 * (K : ℝ) * (H : ℝ)^6 * Real.log (1 / δ)))
    (hw3 : (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E initial fallback path δ c₁ c₂ h k) ≤
      (1 / 8 : ℝ) * Real.sqrt ((Fintype.card State : ℝ) * Fintype.card Action * H^3 *
        onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂ *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ) +
      (1 / 8 : ℝ) * Real.sqrt ((Fintype.card State : ℝ)^2 * Fintype.card Action * H^3 *
        onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ) +
      (1 / 8 : ℝ) * (Fintype.card State : ℝ)^2 * Fintype.card Action * H^3 *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ) :
    onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂ ≤ 2 * (K : ℝ) * (H : ℝ)^2 ∧
    onlineActualT5 H K hH E initial fallback path δ c₁ c₂ ≤
      6 * (K : ℝ) * (H : ℝ)^2 +
      (1 / 2 : ℝ) * Real.sqrt ((Fintype.card State : ℝ)^2 * Fintype.card Action * H^3 *
        onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ) +
      4 * (Fintype.card State : ℝ)^2 * Fintype.card Action * H^3 *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let Hr : ℝ := H
  let Kr : ℝ := K
  let L := Real.log (1 / δ)
  let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ
  let T := onlineActualT5 H K hH E initial fallback path δ c₁ c₂
  let V := onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂
  let D := onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂
  let U := onlineActualT6UCB H K hH E initial fallback path δ c₁ c₂
  let T2 := onlineActualT2 H K hH E initial fallback path δ c₁ c₂
  let W := ∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E initial fallback path δ c₁ c₂ h k
  let J := S * A * Hr * I
  let P := S * A * Hr^3 * I
  let Q := S^2 * A * Hr^3 * I
  let B := Kr * Hr^2
  have hS : 1 ≤ S := by dsimp only [S]; exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card State))
  have hA : 1 ≤ A := by dsimp only [A]; exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card Action))
  have hHr : 1 ≤ Hr := by dsimp only [Hr]; exact_mod_cast (Nat.succ_le_iff.mpr hH)
  have hKr : 0 ≤ Kr := Nat.cast_nonneg K
  have hHr0 : 0 ≤ Hr := by linarith only [hHr]
  have hL : 0 ≤ L := (onlineSmallConfidence_log_ge_one δ hδ hδsmall).trans' (by norm_num)
  have hIL : 20000 * L ≤ I := onlineT56_source_iota_large
    (Fintype.card State) (Fintype.card Action) H K δ Fintype.card_pos Fintype.card_pos hH hK hδ hδsmall
  have hI0 : 0 ≤ I := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20000) hL).trans hIL
  have hI2 : 2 * L ≤ I := by linarith only [hIL,hL]
  have hI4k : 4096 * L ≤ I := by linarith only [hIL,hL]
  have hSA : 1 ≤ S * A := by nlinarith only [hS,hA,mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hA)]
  have hSAH : 1 ≤ S * A * Hr := by
    nlinarith only [hSA,hHr,mul_nonneg (sub_nonneg.mpr hSA) (sub_nonneg.mpr hHr)]
  have hT : 0 ≤ T := by
    unfold T onlineActualT5
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hV : 0 ≤ V := by
    unfold V onlineActualT6Policy
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hD : 0 ≤ D := by
    unfold D onlineActualT6Difference
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.expectation_nonneg _ (fun _ => sq_nonneg _)
  have hU : 0 ≤ U := by
    unfold U onlineActualT6UCB
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hP0 : 0 ≤ P := by dsimp only [P]; positivity
  have hB0 : 0 ≤ B := mul_nonneg hKr (sq_nonneg Hr)
  have hPQ : P ≤ Q := by
    calc
      P = 1 * P := (one_mul P).symm
      _ ≤ S * P := mul_le_mul_of_nonneg_right hS hP0
      _ = Q := by dsimp only [P,Q]; ring
  have hPfactor : P = (S * A * Hr) * Hr^2 * I := by dsimp only [P]; ring
  have hPnoise : 4096 * Hr^2 * L ≤ P := by
    rw [hPfactor]
    exact onlineT56_source_coefficient_dominates_noise (S*A*Hr) Hr I L hSAH hL hI4k
  have hKlarge : (S * A) * Hr^2 * I ≤ Kr := hlarge
  have hcap := onlineT56_largeK_implies_logCap (S*A) Hr I Kr L hSA hL hI2 hKlarge
  have hlow' : V ≤ Kr * Hr^2 + Real.sqrt (2 * Hr^6 * Kr * L) := by
    change V ≤ Kr * Hr^2 + Real.sqrt (2 * Kr * Hr^6 * L) at hlow
    have heq : 2 * Hr^6 * Kr * L = 2 * Kr * Hr^6 * L := by ring
    rw [heq]
    exact hlow
  have hVs := onlineT56_low_simplify Hr Kr L V hHr0 hKr hL hcap hlow'
  have hVsB : V ≤ 2 * B := by simpa only [B,mul_assoc] using hVs
  have hcompare : U ≤ 2*V+2*D :=
    onlineActualT6UCB_le_policy_difference H K hH E initial fallback path δ c₁ c₂
  let R := Real.sqrt (32 * Hr^2 * U * L) + 5 * Hr^2 * L
  have hR : R ≤ 8*Hr*Real.sqrt (V*L)+8*Hr*Real.sqrt (D*L)+5*Hr^2*L :=
    onlineT56_T8_radius_expand Hr U V D L hHr0 hU hV hD hL hcompare
  have hbase : T ≤ W + R + (2*Hr*T2) + 2*B := by
    change T ≤ W + 2*Hr*T2 + 2*Kr*Hr^2 + Real.sqrt (32*Hr^2*U*L)+5*Hr^2*L at h5
    dsimp only [R,B]
    linarith only [h5]
  have hPV : P * V = S*A*Hr^3*V*I := by dsimp only [P]; ring
  have hQD : Q * D = S^2*A*Hr^3*D*I := by dsimp only [Q]; ring
  have hQlin : (1/8:ℝ)*Q = (1/8:ℝ)*S^2*A*Hr^3*I := by dsimp only [Q]; ring
  have hW : W ≤ (1/8:ℝ)*Real.sqrt (P*V)+(1/8:ℝ)*Real.sqrt (Q*D)+(1/8:ℝ)*Q := by
    rw [hPV,hQD,hQlin]
    exact hw3
  have hcoarse := onlineT56_T5_coarse_from_radii T W R (2*Hr*T2) B P Q V D Hr L
    hHr0 hL hV hD hPnoise hPQ hbase hW hR
  have h2 := onlineActualT2_le_sourceBound H K hH hK E initial fallback path δ c₁ c₂ I
    hδ hδsmall hc₁ hc₂ hI
  have hJT : J*T = S*A*Hr*T*I := by dsimp only [J]; ring
  have h2lin : (1/2:ℝ)*Hr*J = (1/2:ℝ)*S*A*Hr^2*I := by dsimp only [J]; ring
  have h2' : T2 ≤ (1/2:ℝ)*Real.sqrt (J*T)+(1/2:ℝ)*Hr*J := by
    rw [hJT,h2lin]
    exact h2
  have hbonus := onlineT56_scaled_T2_bound Hr J T T2 hHr0 h2'
  have hPalt : Hr^2 * J = P := by dsimp only [J,P]; ring
  rw [hPalt] at hbonus
  have hTs := onlineT56_T5_simplify T P Q B V D (2*Hr*T2) hT hP0 hPQ hB0 hVsB hcoarse hbonus
  have h6B : 6*B = 6*Kr*Hr^2 := by dsimp only [B]; ring
  have h4Q : 4*Q = 4*S^2*A*Hr^3*I := by dsimp only [Q]; ring
  rw [h6B,hQD,h4Q] at hTs
  exact ⟨hVs,hTs⟩

end StatisticalRL.OnlineRL
