import Formalization.Probability.OnlineT234ConfidenceAlgebra
import Mathlib.Tactic

/-! Finite-law intersection and failure-budget arithmetic from explicit event probability bounds. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory

theorem mvp_main_five_event_collector
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B C D E : Set Ω)
    (a b c d e : ℝ)
    (ha : 1-a ≤ μ.real A) (hb : 1-b < μ.real B)
    (hc : 1-c ≤ μ.real C) (hd : 1-d ≤ μ.real D) (he : 1-e ≤ μ.real E) :
    1-(a+b+c+d+e) < μ.real ((((A∩B)∩C)∩D)∩E) := by
  have hab := onlineTwoEvent_confidence_strict μ A B a b ha hb
  have habc := onlineTwoEvent_confidence_strict μ C (A∩B) c (a+b) hc hab
  have habcd := onlineTwoEvent_confidence_strict μ D (C∩(A∩B)) d (c+(a+b)) hd habc
  have habcde := onlineTwoEvent_confidence_strict μ E (D∩(C∩(A∩B))) e (d+(c+(a+b))) he habcd
  simpa only [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm, add_assoc, add_left_comm, add_comm] using habcde

theorem mvp_main_failure_budget_scalar (d K H δ B L : ℝ)
    (hd : 1≤d) (hK : 1≤K) (hH : 1≤H) (hδ : 0≤δ)
    (hB : B≤K) (hL : L≤K*H) (hHd : H≤d) :
    (2*d*K+1+4*B+2*L+4*d*K)*(δ/(100*(d*K)^2)) ≤ δ := by
  have hdk : 1≤d*K := by nlinarith
  have hden : 0<100*(d*K)^2 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).2
  have hcoef : 2*d*K+1+4*B+2*L+4*d*K ≤ 13*d*K := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hHd) (show 0≤K by linarith)]
  have hquad : 13*d*K ≤ 100*(d*K)^2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) hδ, mul_nonneg (sub_nonneg.mpr hquad) hδ]
end StatisticalRL.OnlineRL

namespace StatisticalRL.OnlineRL
/-- Logarithm estimates needed to instantiate the generic failure budget. -/
theorem mvp_main_log_budget_bounds (K H : ℕ) (hK : 2 ≤ K) (hH : 0 < H) :
    Real.log K / Real.log 2 ≤ K ∧ Real.log (K*H : ℕ) ≤ (K : ℝ)*H := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwohalf : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (1/2 : ℝ))
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0), Real.log_one] at h
    norm_num at h ⊢
    linarith
  have hk : (0 : ℝ) < K := by exact_mod_cast (show 0<K by omega)
  have hk2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hkh : (0 : ℝ) < (K*H : ℕ) := by exact_mod_cast (Nat.mul_pos (by omega) hH)
  have hquot := Real.log_le_sub_one_of_pos (show (0:ℝ)<(K:ℝ)/2 by positivity)
  rw [Real.log_div (ne_of_gt hk) (by norm_num : (2:ℝ) ≠ 0)] at hquot
  have hlkh := Real.log_le_sub_one_of_pos hkh
  constructor
  · apply (div_le_iff₀ htwo).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hk2) (sub_nonneg.mpr htwohalf)]
  · push_cast at hlkh ⊢
    linarith
end StatisticalRL.OnlineRL
