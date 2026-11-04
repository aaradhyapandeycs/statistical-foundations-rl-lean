import Formalization.Online.Regret.MVP.Probability.MVPRevealIncrement

/-! A fixed predictable test family on a finite product satisfies Freedman. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Index Outcome : Type*} [Fintype Index] [Fintype Outcome]
local instance : MeasurableSpace Outcome := ⊤

theorem mvp_finiteProduct_freedman {M : ℕ} (order : Fin M → Index)
    (hinj : Function.Injective order) (d : Index → FiniteDistribution Outcome)
    (F : (j : Fin M) → ((i : mvpRevealedPrefix order j.val) → Outcome) → Outcome → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀ j code x, 0 ≤ F j code x ∧ F j code x ≤ C)
    (peels : ℕ) (hp : 0 < peels) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (onlineStackProductLaw d).real {data |
      |StatisticalRL.incrementSum (mvpPaddedRevealIncrement order d F) M data| ≤
        Real.sqrt (8 * max
          (StatisticalRL.predictableSecondMomentSum (onlineStackProductLaw d)
            (mvpRevealFiltration (Outcome := Outcome) order)
            (mvpPaddedRevealIncrement order d F) M data)
          ((M : ℝ) * C^2 / (2 : ℝ)^peels) * Real.log (2 * peels / δ)) +
          (4/3) * C * Real.log (2 * peels / δ)} := by
  have hcap : ∀ᵐ data ∂(onlineStackProductLaw d),
      StatisticalRL.predictableSecondMomentSum (onlineStackProductLaw d)
        (mvpRevealFiltration (Outcome := Outcome) order) (mvpPaddedRevealIncrement order d F) M data
        ≤ (M : ℝ)*C^2 := by
    filter_upwards [mvp_reveal_predictableSecondMomentSum order hinj d F] with data heq
    rw [heq]
    calc
      _ ≤ ∑ _j : Fin M, C^2 := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ (d (order j)).expectation (fun x => (F j (onlineRevealedCode
                (mvpRevealedPrefix order j.val) data) x)^2) :=
            (d (order j)).variance_le_expectation_sq _
          _ ≤ C^2 := by
            apply (d (order j)).expectation_le_const
            intro x
            have hx := hF j (onlineRevealedCode (mvpRevealedPrefix order j.val) data) x
            nlinarith
      _ = _ := by simp
  exact StatisticalRL.freedman_source_bound (onlineStackProductLaw d)
    (mvpRevealFiltration (Outcome := Outcome) order) (mvpPaddedRevealIncrement order d F)
    C ((M : ℝ)*C^2) hC (by positivity)
    (mvp_paddedRevealIncrement_adapted order d F)
    (fun k => Filter.Eventually.of_forall (mvp_paddedRevealIncrement_bound order d F C hC hF k))
    (mvp_paddedRevealIncrement_centered order hinj d F) M peels hp hcap δ hδ hδ1
end StatisticalRL.OnlineRL
