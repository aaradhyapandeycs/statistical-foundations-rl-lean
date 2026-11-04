import Formalization.Online.Regret.MVP.Probability.MVPProfileDyadic
import Formalization.Online.Regret.MVP.Probability.MVPUniformCardinality
import Formalization.Online.Regret.MVP.MVPActualProfiles

/-! The monotone source-profile cover is a valid finite index for the uniform bound. -/
namespace StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL StatisticalRL.OnlineRL.MVPProfile
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The source-profile cover, with the verified ceiling level cap that includes
all actual pre-episode profiles. -/
abbrev mvpUniformSourceProfile (H K : ℕ) :=
  MonotoneProfiles K (Fintype.card (Fin H × (State × Action))) (profileLevelCap K)

noncomputable instance mvpUniformSourceProfile_nonempty (H K : ℕ) :
    Nonempty (mvpUniformSourceProfile (State := State) (Action := Action) H K) := by
  classical
  refine ⟨⟨fun _ _ => ⟨0, ?_⟩, ?_⟩⟩
  · unfold profileLevelCap
    omega
  · intro i j k hij
    exact le_rfl

theorem mvpUniformSourceProfile_card_bound (H K : ℕ)
    (hH : 0 < H) (hS : 0 < Fintype.card State) (hA : 0 < Fintype.card Action)
    (hK : 2 ≤ K)
    (hbudget : (K : ℝ) ≥ (Fintype.card (Fin H × (State × Action)) : ℝ) * logTwoReal K) :
    (Fintype.card (mvpUniformSourceProfile (State := State) (Action := Action) H K) : ℝ) ≤
      (4 * (Fintype.card (Fin H × (State × Action)) : ℝ) * K) ^
        ((Fintype.card (Fin H × (State × Action)) : ℝ) * logTwoReal K + 1) := by
  have hd : 1 ≤ Fintype.card (Fin H × (State × Action)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have hp : 0 < H * (Fintype.card State * Fintype.card Action) :=
      Nat.mul_pos hH (Nat.mul_pos hS hA)
    omega
  exact sourceMVP_profileFamily_card_bound K _ hK hd hbudget
end StatisticalRL.FiniteHorizonGenerative
