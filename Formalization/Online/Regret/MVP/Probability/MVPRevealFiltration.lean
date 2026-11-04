import Formalization.Online.Regret.MVP.Probability.MVPRevealedMoments
import Formalization.Probability.FreedmanExactAssembly

/-! Finite-product prefix filtration for an injective fixed reveal order. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {Index Outcome : Type*} [Fintype Index] [Fintype Outcome]
local instance : MeasurableSpace Outcome := ⊤

/-- The first t coordinates in a fixed finite reveal order. -/
noncomputable def mvpRevealedPrefix {M : ℕ} (order : Fin M → Index) (t : ℕ) : Finset Index := by
  classical
  exact Finset.univ.image order |>.filter (fun i => ∃ j : Fin M, j.val < t ∧ order j = i)

theorem mvpRevealedPrefix_mono {M : ℕ} (order : Fin M → Index) :
    Monotone (mvpRevealedPrefix order) := by
  classical
  intro s t hst i hi
  simp only [mvpRevealedPrefix, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, by rcases hi.2 with ⟨j,hj,hji⟩; exact ⟨j, lt_of_lt_of_le hj hst, hji⟩⟩

theorem mvpRevealedPrefix_fresh {M : ℕ} (order : Fin M → Index)
    (hinj : Function.Injective order) (j : Fin M) :
    order j ∉ mvpRevealedPrefix order j.val := by
  classical
  simp only [mvpRevealedPrefix, Finset.mem_filter, not_and]
  intro _ hex
  rcases hex with ⟨k,hk,heq⟩
  have : k = j := hinj heq
  subst k
  exact (lt_irrefl j.val) hk

/-- A filtration revealing exactly the ordered coordinates strictly before t. -/
noncomputable def mvpRevealFiltration {M : ℕ} (order : Fin M → Index) :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (Index → Outcome)) where
  seq t := onlineRevealedSigma (mvpRevealedPrefix order t)
  mono' := by
    intro s t hst
    exact Filtration.piFinset.mono (mvpRevealedPrefix_mono order hst)
  le' t := (measurable_of_countable (onlineRevealedCode (Outcome := Outcome)
    (mvpRevealedPrefix order t))).comap_le

/-- True conditional moments for any test measurable in the revealed prefix. -/
theorem mvp_prefix_centered_moments {M : ℕ} (order : Fin M → Index)
    (hinj : Function.Injective order) (d : Index → FiniteDistribution Outcome)
    (j : Fin M) (F : ((i : mvpRevealedPrefix order j.val) → Outcome) → Outcome → ℝ) :
    let μ := onlineStackProductLaw d
    let I := mvpRevealedPrefix order j.val
    let X := fun data => F (onlineRevealedCode I data) (data (order j)) -
      (d (order j)).expectation (F (onlineRevealedCode I data))
    (μ[X | mvpRevealFiltration (Outcome := Outcome) order j.val] =ᵐ[μ] 0) ∧
    (μ[(fun data => (X data)^2) | mvpRevealFiltration (Outcome := Outcome) order j.val] =ᵐ[μ]
      (fun data => (d (order j)).variance (F (onlineRevealedCode I data)))) := by
  exact ⟨mvp_revealedCenteredTest_mean d _ _ (mvpRevealedPrefix_fresh order hinj j) F,
    mvp_revealedCenteredTest_secondMoment d _ _ (mvpRevealedPrefix_fresh order hinj j) F⟩
end StatisticalRL.OnlineRL
