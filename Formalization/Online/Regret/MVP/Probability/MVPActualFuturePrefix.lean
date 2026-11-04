import Formalization.Online.Regret.MVP.Probability.MVPActualOrder

/-! Strictly later-stage expanded coordinates are already revealed. -/
namespace StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpExpandedOrder_surjective (H K : ℕ) :
    Function.Surjective (mvpExpandedOrder (State := State) (Action := Action) H K) := by
  classical
  have hc : Fintype.card (Fin (H * Fintype.card (State × Action × Fin K))) =
      Fintype.card (SampleIndex State Action H K) := by
    simp [SampleIndex, Fintype.card_prod, Nat.mul_assoc]
  let e := Fintype.equivOfCardEq hc
  exact (Finite.injective_iff_surjective_of_equiv e).1 (mvpExpandedOrder_injective H K)

theorem mvp_later_coord_mem_prefix (H K : ℕ)
    (j : Fin (H * Fintype.card (State × Action × Fin K)))
    (x : SampleIndex State Action H K)
    (hstage : (mvpExpandedOrder (State := State) (Action := Action) H K j).1.1 < x.1.1) :
    x ∈ mvpRevealedPrefix (mvpExpandedOrder (State := State) (Action := Action) H K) j.val := by
  classical
  obtain ⟨i,hi⟩ := mvpExpandedOrder_surjective (State := State) (Action := Action) H K x
  have hlt : i.val < j.val := mvpExpandedOrder_later_first H K i j (by simpa [hi] using hstage)
  simp only [mvpRevealedPrefix, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨i,hi⟩,i,hlt,hi⟩
end StatisticalRL.FiniteHorizonGenerative
