import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Uncompiled deterministic intermediate for onlineRL.tex:4487–4560.
`hdecomp`, `htail`, and `hbudget` must be proved from the actual MVP
trajectory, Freedman event, and corrected source allocation respectively;
they are not assumptions of the source-facing lemma. -/
namespace StatisticalRL.OnlineRL

theorem mvp_sqrt_variance_young (H V L : ℝ)
    (hH : 0 ≤ H) (hV : 0 ≤ V) (hL : 0 ≤ L) :
    Real.sqrt (32 * H^2 * V * L) ≤ V/2 + 16*H^2*L := by
  have hr : 0 ≤ 32 * H^2 * V * L := by positivity
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (32 * H^2 * V * L)
  have ht : 0 ≤ V/2 + 16*H^2*L := by positivity
  nlinarith [sq_nonneg (V/2 - 16*H^2*L)]

/-- Closure from the actual-path decomposition and one-sided square-tail
bound. The displayed budget is deliberately intermediate. -/
theorem mvp_t6_ucb_scalar_closure (H K I L V T2 W4 T8 : ℝ)
    (hH : 0 ≤ H) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hdecomp : V ≤ T8 + 2*H*T2 + 2*K*H^2 + 2*H*W4)
    (htail : T8 ≤ Real.sqrt (32*H^2*V*L) + 5*H^2*L)
    (hbudget : 4*K + 42*L ≤ K*I) :
    V ≤ 4*H*T2 + 4*H*W4 + K*H^2*I := by
  have hy := mvp_sqrt_variance_young H V L hH hV hL
  have hb : 4*K*H^2 + 42*H^2*L ≤ K*H^2*I := by
    nlinarith [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr hbudget)]
  nlinarith
end StatisticalRL.OnlineRL
