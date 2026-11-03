import Formalization.Generative.GenerativeLowerBoundFamilyMDP

/-! One-row-change MDP family for baseline-versus-mixture Q estimation. -/
namespace StatisticalRL.GenerativeLowerBound

/-- Baseline or one changed active-state/action row, with the exact action
count A and the exact state count m+1. -/
abbrev QMixtureIndex (m A : ℕ) := Option (Fin m × Fin A)

/-- Baseline uses p in all rows. An alternative uses q only in its own row. -/
def qMixtureStay {m A : ℕ} (i : QMixtureIndex m A) (p q : ℝ)
    (j : Fin m) (a : Fin A) : ℝ :=
  if i = some (j,a) then q else p

/-- The true finite MDP: all absorber actions self-loop, all active rewards
are 1, and exactly one state/action row may be perturbed. -/
noncomputable def qMixtureMDP {m A : ℕ} [NeZero A] (i : QMixtureIndex m A)
    (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hp : 0 ≤ p)
    (hpq : p ≤ q) (hq : q < 1) : DiscountedMDP (Option (Fin m)) (Fin A) where
  state_nonempty := inferInstance
  action_nonempty := inferInstance
  transition s a := match s with
    | none => EnvironmentStage.pointMass none
    | some j => familyActiveRow j (qMixtureStay i p q j a)
        (by unfold qMixtureStay; split <;> linarith)
        (by unfold qMixtureStay; split <;> linarith)
  reward s _ := match s with | none => 0 | some _ => 1
  reward_nonneg := by intro s a; cases s <;> simp
  reward_le_one := by intro s a; cases s <;> simp
  discount := γ
  discount_nonneg := hγ
  discount_lt_one := hγ1

/-- The best self-loop in each active state of a baseline/alternative model. -/
def qMixtureBestStay {m A : ℕ} (i : QMixtureIndex m A) (p q : ℝ) (j : Fin m) : ℝ :=
  if ∃ a : Fin A, i = some (j,a) then q else p

/-- Proposed forced-first-action Q formula. It must be identified with the
actual optimal trajectory Q before it can serve as proof evidence. -/
noncomputable def qMixtureOptimalQCandidate {m A : ℕ} (i : QMixtureIndex m A)
    (γ p q : ℝ) : Option (Fin m) → Fin A → ℝ :=
  fun s a ↦ match s with
    | none => 0
    | some j => 1 + γ * qMixtureStay i p q j a / (1 - γ * qMixtureBestStay i p q j)

/-- A matching active row is changed exactly in its designated alternative. -/
theorem qMixtureStay_alternative {m A : ℕ} (j : Fin m) (a : Fin A) (p q : ℝ) :
    qMixtureStay (some (j,a)) p q j a = q := by
  simp [qMixtureStay]

/-- Every baseline active row uses p. -/
theorem qMixtureStay_baseline {m A : ℕ} (j : Fin m) (a : Fin A) (p q : ℝ) :
    qMixtureStay none p q j a = p := by
  simp [qMixtureStay]

end StatisticalRL.GenerativeLowerBound
