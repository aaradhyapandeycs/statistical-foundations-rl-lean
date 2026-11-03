import Formalization.ModelFree.QLearningTrajectoryKLInduction
import Formalization.ModelFree.QLearningTrajectoryKLHeterogeneous

/-! Finite forced-prefix KL induction under explicit support conditions. -/
open scoped BigOperators
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Conditional continuation after the first next state: draw the next action
from the common policy, then draw the actual remaining prefix. -/
def qForcedPrefixContinuationLaw (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (x : State) (k : ℕ) :
    FiniteDistribution
      (Action × QForcedPrefix (State := State) (Action := Action) k) :=
  qConditionalJointLaw (π x) (fun b ↦ qForcedPrefixLaw M π x b k)

/-- Successor factorization of the actual prefix law. There is one first
transition row, followed by the common action draw and the remaining prefix. -/
theorem qForcedPrefixLaw_succ_prob (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) (k : ℕ)
    (path : State × Action × QForcedPrefix (State := State) (Action := Action) k) :
    (qForcedPrefixLaw M π s a (k + 1)).prob path =
      (qConditionalJointLaw (M.transition s a)
        (fun x ↦ qForcedPrefixContinuationLaw M π x k)).prob path := by
  change ((M.transition s a).prob path.1 * (π path.1).prob path.2.1) *
      qForcedPrefixWeight M π path.1 path.2.1 k path.2.2 =
    (M.transition s a).prob path.1 *
      ((π path.1).prob path.2.1 *
        qForcedPrefixWeight M π path.1 path.2.1 k path.2.2)
  ring

/-- The conditional continuation laws inherit support inclusion from the
actual transition-row support condition. Shared-policy zero atoms are handled
by the positive joint-mass premise. -/
theorem qForcedPrefixContinuation_support
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (k : ℕ)
    (hrow : ∀ s a y, (M'.transition s a).prob y ≠ 0 →
      (M.transition s a).prob y ≠ 0)
    (x : State) (z : Action × QForcedPrefix (State := State) (Action := Action) k)
    (hz : (qForcedPrefixContinuationLaw M' π x k).prob z ≠ 0) :
    (qForcedPrefixContinuationLaw M π x k).prob z ≠ 0 := by
  have hpolicy : (π x).prob z.1 ≠ 0 := by
    intro hzero
    apply hz
    simp [qForcedPrefixContinuationLaw, qConditionalJointLaw, hzero]
  have htail' : (qForcedPrefixLaw M' π x z.1 k).prob z.2 ≠ 0 := by
    intro hzero
    apply hz
    simp [qForcedPrefixContinuationLaw, qConditionalJointLaw, hzero]
  have htail : (qForcedPrefixLaw M π x z.1 k).prob z.2 ≠ 0 :=
    qForcedPrefixWeight_support M M' π x z.1 k hrow z.2 htail'
  exact mul_ne_zero hpolicy htail

/-- Finite-horizon KL chain rule for the actual forced-initial-action prefix.
The source model's first pair `(s,a)` is fixed in both laws. A horizon `k`
contains exactly `k` transition factors; the `k=0` law is the common unit
law. The proof uses the heterogeneous joint chain rule at each successor and
the common-marginal rule for each shared policy draw. -/
theorem qForcedPrefixLaw_finiteKL_eq_rec
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (k : ℕ)
    (hrow : ∀ s a y, (M'.transition s a).prob y ≠ 0 →
      (M.transition s a).prob y ≠ 0) :
    ∀ s a,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
          (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) =
        qForcedPrefixKLRec M M' π s a k := by
  induction k with
  | zero =>
      intro s a
      unfold StatisticalRL.GenerativeLowerBound.finiteKLExpression
      simp [qForcedPrefixLaw, qForcedPrefixWeight, QForcedPrefix,
        qForcedPrefixKLRec]
  | succ k ih =>
      intro s a
      let K' : State → FiniteDistribution
          (Action × QForcedPrefix (State := State) (Action := Action) k) :=
        fun x ↦ qForcedPrefixContinuationLaw M' π x k
      let K : State → FiniteDistribution
          (Action × QForcedPrefix (State := State) (Action := Action) k) :=
        fun x ↦ qForcedPrefixContinuationLaw M π x k
      have hmass' :
          (fun path : State × Action × QForcedPrefix (State := State) (Action := Action) k ↦
            (qForcedPrefixLaw M' π s a (k + 1)).prob path) =
          (fun path ↦ (qConditionalJointLaw (M'.transition s a) K').prob path) := by
        funext path
        exact qForcedPrefixLaw_succ_prob M' π s a k path
      have hmass :
          (fun path : State × Action × QForcedPrefix (State := State) (Action := Action) k ↦
            (qForcedPrefixLaw M π s a (k + 1)).prob path) =
          (fun path ↦ (qConditionalJointLaw (M.transition s a) K).prob path) := by
        funext path
        exact qForcedPrefixLaw_succ_prob M π s a k path
      have hKLsucc :
          StatisticalRL.GenerativeLowerBound.finiteKLExpression
              (fun path ↦ (qForcedPrefixLaw M' π s a (k + 1)).prob path)
              (fun path ↦ (qForcedPrefixLaw M π s a (k + 1)).prob path) =
            StatisticalRL.GenerativeLowerBound.finiteKLExpression
                (fun y ↦ (M'.transition s a).prob y)
                (fun y ↦ (M.transition s a).prob y) +
              (M'.transition s a).expectation (fun x ↦
                StatisticalRL.GenerativeLowerBound.finiteKLExpression
                  (fun z ↦ (K' x).prob z) (fun z ↦ (K x).prob z)) := by
        calc
          _ = StatisticalRL.GenerativeLowerBound.finiteKLExpression
              (fun path ↦ (qConditionalJointLaw (M'.transition s a) K').prob path)
              (fun path ↦ (qConditionalJointLaw (M.transition s a) K).prob path) := by
            apply congrArg₂ StatisticalRL.GenerativeLowerBound.finiteKLExpression
            · exact hmass'
            · exact hmass
          _ = _ := qConditionalJoint_finiteKL_chainRule
            (M.transition s a) (M'.transition s a) K K'
            (hrow s a) (qForcedPrefixContinuation_support M M' π k hrow)
      have hinner (x : State) :
          StatisticalRL.GenerativeLowerBound.finiteKLExpression
              (fun z ↦ (K' x).prob z) (fun z ↦ (K x).prob z) =
            (π x).expectation (fun b ↦
              qForcedPrefixKLRec M M' π x b k) := by
        have hKtail : ∀ b path,
            (qForcedPrefixLaw M' π x b k).prob path ≠ 0 →
              (qForcedPrefixLaw M π x b k).prob path ≠ 0 := by
          intro b path hp
          exact qForcedPrefixWeight_support M M' π x b k hrow path hp
        change StatisticalRL.GenerativeLowerBound.finiteKLExpression
            (fun z ↦ (qConditionalJointLaw (π x)
              (fun b ↦ qForcedPrefixLaw M' π x b k)).prob z)
            (fun z ↦ (qConditionalJointLaw (π x)
              (fun b ↦ qForcedPrefixLaw M π x b k)).prob z) = _
        rw [qConditionalJoint_commonMarginal_chainRule
          (π x) (fun b ↦ qForcedPrefixLaw M π x b k)
          (fun b ↦ qForcedPrefixLaw M' π x b k) hKtail]
        simp_rw [ih x]
      rw [hKLsucc]
      simp_rw [hinner]
      rfl

end StatisticalRL.QLearning
