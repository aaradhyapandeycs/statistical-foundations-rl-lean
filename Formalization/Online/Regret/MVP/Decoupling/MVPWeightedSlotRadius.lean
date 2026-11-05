import Formalization.Online.Regret.MVP.Decoupling.MVPDyadicSlotSums
import Formalization.Online.Regret.W1.OnlineW1CauchyBudget

/-! finite weighted Cauchy aggregation. All assumptions are analytic
inputs to a helper, not additional premises on a source-facing result. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem mvp_weightedSlot_sqrt_sum {ι : Type*} (s : Finset ι)
    (w v : ι → ℝ) (C W T : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hC : 0 ≤ C) (_hW : 0 ≤ W) (hT : 0 ≤ T)
    (hsw : (∑ i ∈ s, w i) ≤ W) (hsv : (∑ i ∈ s, v i) ≤ T) :
    (∑ i ∈ s, Real.sqrt (C*w i*v i)) ≤ Real.sqrt (C*W*T) := by
  have h := onlineW1_sqrt_budget s v w (C/2) (by positivity) hv hw
  have heq (i : ι) : 2*(C/2)*v i*w i = C*w i*v i := by ring
  simp_rw [heq] at h
  have hc : 2*(C/2)*(∑ i ∈ s, v i) = C*(∑ i ∈ s, v i) := by ring
  rw [hc] at h
  have hsv0 : 0 ≤ ∑ i ∈ s, v i := Finset.sum_nonneg (fun i _ => hv i)
  have hsw0 : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg (fun i _ => hw i)
  calc
    _ ≤ Real.sqrt (C*(∑ i ∈ s, v i))*Real.sqrt (∑ i ∈ s, w i) := h
    _ = Real.sqrt (C*(∑ i ∈ s, v i)*(∑ i ∈ s, w i)) :=
      (Real.sqrt_mul (mul_nonneg hC hsv0) _).symm
    _ ≤ Real.sqrt (C*W*T) := by
      apply Real.sqrt_le_sqrt
      calc
        _ ≤ C*T*W := by gcongr
        _ = C*W*T := by ring

theorem mvp_weightedSlot_radius_sum {ι : Type*} (s : Finset ι)
    (w v e : ι → ℝ) (C D W T : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hW : 0 ≤ W) (hT : 0 ≤ T)
    (hsw : (∑ i ∈ s, w i) ≤ W) (hsv : (∑ i ∈ s, v i) ≤ T)
    (he : ∀ i ∈ s, e i ≤ Real.sqrt (C*w i*v i)+D*w i) :
    (∑ i ∈ s, e i) ≤ Real.sqrt (C*W*T)+D*W := by
  calc
    _ ≤ ∑ i ∈ s, (Real.sqrt (C*w i*v i)+D*w i) := Finset.sum_le_sum he
    _ = (∑ i ∈ s, Real.sqrt (C*w i*v i))+D*(∑ i ∈ s, w i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ Real.sqrt (C*W*T)+D*W :=
      add_le_add (mvp_weightedSlot_sqrt_sum s w v C W T hw hv hC hW hT hsw hsv)
        (mul_le_mul_of_nonneg_left hsw hD)

/-- The strengthened radius leaves enough additive slack for ranks zero and
one while yielding the printed linear coefficient. -/
theorem mvp_linearSlot_final_absorb (d H I T B : ℝ)
    (hd : 0 ≤ d) (hH : 0 ≤ H) (hI : 4 ≤ I) (hT : 0 ≤ T)
    (hB : B ≤ Real.sqrt (d*I*(1/8)*T)+d*H*I/8+2*d*H) :
    B ≤ Real.sqrt (d*I*T)+d*H*I := by
  have hI0 : 0 ≤ I := by linarith
  have hr : Real.sqrt (d*I*(1/8)*T) ≤ Real.sqrt (d*I*T) := by
    apply Real.sqrt_le_sqrt
    have h := mul_nonneg (mul_nonneg hd hI0) hT
    nlinarith only [h]
  have ha := mvp_initialRanks_absorb (d*H) I (mul_nonneg hd hH) hI
  nlinarith only [hB,hr,ha]

/-- The normalized-square variance factor four still leaves a factor two of
slack inside the printed square root. -/
theorem mvp_squareSlot_final_absorb (d H I T B : ℝ)
    (hd : 0 ≤ d) (hH : 0 ≤ H) (hI : 4 ≤ I) (hT : 0 ≤ T)
    (hB : B ≤ H*Real.sqrt (d*I*(1/8)*(4*T))+d*H^2*I/8+2*d*H^2) :
    B ≤ Real.sqrt (d*H^2*I*T)+d*H^2*I := by
  have hI0 : 0 ≤ I := by linarith
  have hp : 0 ≤ d*I*T := mul_nonneg (mul_nonneg hd hI0) hT
  have hr : H*Real.sqrt (d*I*(1/8)*(4*T)) ≤ Real.sqrt (d*H^2*I*T) := by
    calc
      _ = Real.sqrt (H^2*(d*I*(1/8)*(4*T))) := by
        rw [Real.sqrt_mul (sq_nonneg H), Real.sqrt_sq hH]
      _ ≤ Real.sqrt (d*H^2*I*T) := by
        apply Real.sqrt_le_sqrt
        have h := mul_nonneg (sq_nonneg H) hp
        nlinarith only [h]
  have ha := mvp_initialRanks_absorb (d*H^2) I (mul_nonneg hd (sq_nonneg H)) hI
  nlinarith only [hB,hr,ha]

end StatisticalRL.OnlineRL
