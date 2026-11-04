import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVarianceConditional
import Formalization.Online.Regret.T4.OnlineRegretT4EpisodeAzuma

/-! Actual-law variance and gap proof component: EpisodeVarianceClip.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL

noncomputable def onlineVarianceMeanClip (B x : ℝ) : ℝ := max 0 (min B x)

theorem onlineVarianceMeanClip_mem (B x : ℝ) (hB : 0 ≤ B) :
    onlineVarianceMeanClip B x ∈ Set.Icc 0 B := by
  constructor
  · exact le_max_left _ _
  · exact max_le hB (min_le_left _ _)

theorem onlineVarianceMeanClip_eq (B x : ℝ) (hx : 0 ≤ x) (hxB : x ≤ B) :
    onlineVarianceMeanClip B x = x := by
  simp [onlineVarianceMeanClip, min_eq_right hxB, max_eq_right hx]

theorem onlineVarianceCentered_mem (B u m : ℝ) (hB : 0 ≤ B)
    (hu : u ∈ Set.Icc 0 B) :
    u - onlineVarianceMeanClip B m ∈ Set.Icc (-B) B := by
  have hm := onlineVarianceMeanClip_mem B m hB
  constructor <;> linarith [hu.1, hu.2, hm.1, hm.2]

end StatisticalRL.OnlineRL
