import Formalization.Online.Regret.MVP.Probability.MVPRevealFiltration

/-! Exact conditional variation for a finite sequence of revealed-code tests. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Index Outcome : Type*} [Fintype Index] [Fintype Outcome]
local instance : MeasurableSpace Outcome := ⊤

noncomputable def mvpPaddedRevealIncrement {M : ℕ} (order : Fin M → Index)
    (d : Index → FiniteDistribution Outcome)
    (F : (j : Fin M) → ((i : mvpRevealedPrefix order j.val) → Outcome) → Outcome → ℝ)
    (k : ℕ) (data : Index → Outcome) : ℝ :=
  if hk : k < M then
    let j : Fin M := ⟨k,hk⟩
    F j (onlineRevealedCode (mvpRevealedPrefix order k) data) (data (order j)) -
      (d (order j)).expectation (F j (onlineRevealedCode (mvpRevealedPrefix order k) data))
  else 0

theorem mvp_reveal_predictableSecondMomentSum {M : ℕ} (order : Fin M → Index)
    (hinj : Function.Injective order) (d : Index → FiniteDistribution Outcome)
    (F : (j : Fin M) → ((i : mvpRevealedPrefix order j.val) → Outcome) → Outcome → ℝ) :
    StatisticalRL.predictableSecondMomentSum (onlineStackProductLaw d)
      (mvpRevealFiltration (Outcome := Outcome) order) (mvpPaddedRevealIncrement order d F) M
      =ᵐ[onlineStackProductLaw d] fun data =>
        ∑ j : Fin M, (d (order j)).variance
          (F j (onlineRevealedCode (mvpRevealedPrefix order j.val) data)) := by
  classical
  have hs : ∀ᵐ data ∂(onlineStackProductLaw d), ∀ j : Fin M,
      (onlineStackProductLaw d)[(fun data => (mvpPaddedRevealIncrement order d F j.val data)^2) |
        mvpRevealFiltration (Outcome := Outcome) order j.val] data =
        (d (order j)).variance (F j (onlineRevealedCode (mvpRevealedPrefix order j.val) data)) := by
    apply ae_all_iff.mpr
    intro j
    have h := (mvp_prefix_centered_moments order hinj d j (F j)).2
    simpa [mvpPaddedRevealIncrement, j.isLt] using h
  filter_upwards [hs] with data hd
  unfold StatisticalRL.predictableSecondMomentSum
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  exact hd j
end StatisticalRL.OnlineRL
