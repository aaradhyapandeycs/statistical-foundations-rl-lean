import Formalization.Online.Regret.MVP.Decoupling.MVPWeightedSlotRadius
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! finite-sigma aggregation of every dyadic slot. This consumes
separately proved simultaneous radii and an actual variance budget. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem mvp_dyadicSlot_radius_sum (J : ℕ) (x C D T : ℝ)
    (v e : ℕ → ℕ → ℝ) (hx : 0<x) (hJ : (J:ℝ)≤x)
    (hC : 0≤C) (hD : 0≤D) (hT : 0≤T) (hv : ∀ j i,0≤v j i)
    (hsv : (∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (2*2^j),v j i) ≤ T)
    (he : ∀ j, j<J → ∀ i, i<2*2^j →
      e j i ≤ Real.sqrt (C*((1:ℝ)/(16*(2:ℝ)^j*x))*v j i) +
        D*((1:ℝ)/(16*(2:ℝ)^j*x))) :
    (∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (2*2^j),e j i) ≤
      Real.sqrt (C*(1/8)*T)+D/8 := by
  let slots : Finset (Σ _j : ℕ,ℕ) :=
    (Finset.range J).sigma (fun j=>Finset.range (2*2^j))
  let w : (Σ _j : ℕ,ℕ) → ℝ := fun a=>(1:ℝ)/(16*(2:ℝ)^a.1*x)
  have hw (a : Σ _j : ℕ,ℕ) : 0≤w a := by dsimp [w]; positivity
  have hsw : (∑ a ∈ slots,w a) ≤ 1/8 := by
    simpa only [slots,w,Finset.sum_sigma] using mvp_dyadicSlot_weight_budget J x hx hJ
  have hvs : (∑ a ∈ slots,v a.1 a.2) ≤ T := by
    simpa only [slots,Finset.sum_sigma] using hsv
  have hes : ∀ a ∈ slots,e a.1 a.2 ≤ Real.sqrt (C*w a*v a.1 a.2)+D*w a := by
    intro a ha
    obtain ⟨hj,hi⟩ := Finset.mem_sigma.mp ha
    exact he a.1 (Finset.mem_range.mp hj) a.2 (Finset.mem_range.mp hi)
  have h := mvp_weightedSlot_radius_sum slots w (fun a=>v a.1 a.2)
    (fun a=>e a.1 a.2) C D (1/8) T hw (fun a=>hv a.1 a.2)
    hC hD (by norm_num) hT hsw hvs hes
  have hd : D*(1/8:ℝ)=D/8 := by ring
  rw [hd] at h
  simpa only [slots,Finset.sum_sigma] using h

end StatisticalRL.OnlineRL
