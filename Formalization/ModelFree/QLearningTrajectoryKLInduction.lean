import Formalization.ModelFree.QLearningTrajectoryKLPrefix
import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing

/-! Finite forced-prefix expected row-KL cost and its linear bound. -/
open scoped BigOperators
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The recursive sum of row KL costs along the actual prefix. The first row
uses the externally fixed initial pair; each later state/action is drawn from
the primed model and the shared policy. -/
noncomputable def qForcedPrefixKLRec (M M' : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun y ↦ (M'.transition s a).prob y)
          (fun y ↦ (M.transition s a).prob y) +
        (M'.transition s a).expectation (fun x ↦
          (π x).expectation (fun b ↦ qForcedPrefixKLRec M M' π x b k))

/-- If every actual transition row has finite KL at most `ρ`, then the
recursive source-prefix cost is at most `kρ`. This is the numerical half of
the finite-horizon induction; it does not assert that the path-law KL equals
this recursion. -/
theorem qForcedPrefixKLRec_le (M M' : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : ℝ) (k : ℕ)
    (hrow : ∀ s a,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun y ↦ (M'.transition s a).prob y)
          (fun y ↦ (M.transition s a).prob y) ≤ ρ) :
    ∀ s a, qForcedPrefixKLRec M M' π s a k ≤ (k : ℝ) * ρ := by
  induction k with
  | zero =>
      intro s a
      simp [qForcedPrefixKLRec]
  | succ k ih =>
      intro s a
      change StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun y ↦ (M'.transition s a).prob y)
          (fun y ↦ (M.transition s a).prob y) +
        (M'.transition s a).expectation (fun x ↦
          (π x).expectation (fun b ↦ qForcedPrefixKLRec M M' π x b k)) ≤
        ((k + 1 : ℕ) : ℝ) * ρ
      have htail : ∀ x b, qForcedPrefixKLRec M M' π x b k ≤ (k : ℝ) * ρ := ih
      have hpolicy (x : State) :
          (π x).expectation (fun b ↦ qForcedPrefixKLRec M M' π x b k) ≤
            (k : ℝ) * ρ :=
        (π x).expectation_le_const (fun b ↦ htail x b)
      have houter :
          (M'.transition s a).expectation (fun x ↦
            (π x).expectation (fun b ↦ qForcedPrefixKLRec M M' π x b k)) ≤
            (k : ℝ) * ρ :=
        (M'.transition s a).expectation_le_const hpolicy
      have hfirst := hrow s a
      rw [Nat.cast_succ]
      nlinarith

end StatisticalRL.QLearning
