import Formalization.ModelFree.QLearningTrajectoryKLPrefix
import Formalization.MDP.OptimalTrajectoryValue

/-! Actual terminal rewards and finite means for forced-action prefixes. -/
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- At depth zero the initial action is still forced, with no sampled transition.
At successor depth the stored next state/action becomes the initial pair of the suffix. -/
def qPrefixTerminalReward (M : DiscountedMDP State Action) (s : State) (a : Action) :
    (k : ℕ) → QForcedPrefix (State := State) (Action := Action) k → ℝ
  | 0, _ => M.reward s a
  | k + 1, path => qPrefixTerminalReward M path.1 path.2.1 k path.2.2

theorem qPrefixTerminalReward_bounds (M : DiscountedMDP State Action)
    (s : State) (a : Action) (k : ℕ)
    (path : QForcedPrefix (State := State) (Action := Action) k) :
    0 ≤ qPrefixTerminalReward M s a k path ∧
      qPrefixTerminalReward M s a k path ≤ 1 := by
  induction k generalizing s a with
  | zero => exact ⟨M.reward_nonneg s a, M.reward_le_one s a⟩
  | succ k ih => exact ih path.1 path.2.1 path.2.2

/-- Actual finite-law expected reward at the terminal pair, not a free sequence. -/
def qPrefixRewardMean (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (k : ℕ) (s : State) (a : Action) : ℝ :=
  (qForcedPrefixLaw M π s a k).expectation (qPrefixTerminalReward M s a k)

theorem qPrefixRewardMean_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    qPrefixRewardMean M π 0 s a = M.reward s a := by
  exact (qForcedPrefixLaw M π s a 0).expectation_const (M.reward s a)

theorem qPrefixRewardMean_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (k : ℕ) (s : State) (a : Action) :
    0 ≤ qPrefixRewardMean M π k s a ∧ qPrefixRewardMean M π k s a ≤ 1 := by
  exact ⟨(qForcedPrefixLaw M π s a k).expectation_nonneg
      (fun path => (qPrefixTerminalReward_bounds M s a k path).1),
    (qForcedPrefixLaw M π s a k).expectation_le_const
      (fun path => (qPrefixTerminalReward_bounds M s a k path).2)⟩

/-- One transition followed by one policy draw; depth k+1 contains precisely
one more transition than depth k. There is no post-terminal transition. -/
theorem qPrefixRewardMean_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (k : ℕ) (s : State) (a : Action) :
    qPrefixRewardMean M π (k + 1) s a =
      (M.transition s a).expectation (fun x => (π x).expectation
        (fun b => qPrefixRewardMean M π k x b)) := by
  classical
  change (∑ path : State × Action × QForcedPrefix (State := State) (Action := Action) k,
    ((M.transition s a).prob path.1 * (π path.1).prob path.2.1 *
      qForcedPrefixWeight M π path.1 path.2.1 k path.2.2) *
      qPrefixTerminalReward M path.1 path.2.1 k path.2.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  unfold FiniteDistribution.expectation qPrefixRewardMean
  simp only [FiniteDistribution.expectation, qForcedPrefixLaw]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro path _
  ring

/-- The ordinary discounted finite reward sum, with n terms (depths 0,…,n−1). -/
def qPrefixDiscountedSum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) (a : Action) : ℝ :=
  ∑ k ∈ Finset.range n, M.discount ^ k * qPrefixRewardMean M π k s a

end StatisticalRL.QLearning
