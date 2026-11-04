import Formalization.Online.Regret.MVP.Probability.MVPProfileUniform

/-! Exact finite union index size for profiles, row choices, levels and masks. -/
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action Profile Level : Type*} [Fintype State] [Fintype Action]
  [Fintype Profile] [Fintype Level]
noncomputable local instance mvpCardStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpCardActionDecidable : DecidableEq Action := Classical.decEq Action

theorem mvp_profileChoiceMask_card (H K : ℕ) :
    Fintype.card
      ((Profile × (Fin H → State → Action → Fin (K+1)) × Level) ×
        (Fin H → State → Action → Bool)) =
      Fintype.card Profile * ((K+1) ^ (H * Fintype.card State * Fintype.card Action)) *
        Fintype.card Level * (2 ^ (H * Fintype.card State * Fintype.card Action)) := by
  classical
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← Nat.pow_mul]
  have he : Fintype.card Action * Fintype.card State * H =
      H * Fintype.card State * Fintype.card Action := by ring
  rw [he]
  ring
end StatisticalRL.FiniteHorizonGenerative
