import Formalization.MDP.Basic

/-! Finite forced-action prefix laws, normalization and support. -/
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
universe u v

/-- The continuation after a fixed initial pair `(s₀,a₀)`, through exactly
`k` transitions. At each transition we store the next state and the action
chosen there. Thus at `k = 0` the outcome is `PUnit`: the initial action is
still fixed externally, and no transition is sampled. -/
def QForcedPrefix {State : Type u} {Action : Type v} : ℕ → Type (max u v)
  | 0 => PUnit
  | k + 1 => State × Action × QForcedPrefix (State := State) (Action := Action) k

namespace QForcedPrefix

instance instFintype : (k : ℕ) → Fintype (QForcedPrefix (State := State) (Action := Action) k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k + 1 => by
      letI := instFintype k
      exact inferInstanceAs (Fintype (State × Action × QForcedPrefix (State := State) (Action := Action) k))

end QForcedPrefix

/-- Product mass of the actual suffix following fixed initial pair `(s,a)`.
The first action `a` is forced. Each later action is drawn from the common
policy `π`; each of the `k` transition factors is the model's actual row.
There is no transition after the terminal action. -/
def qForcedPrefixWeight (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    (k : ℕ) → QForcedPrefix (State := State) (Action := Action) k → ℝ
  | 0, _ => 1
  | k + 1, path =>
      (M.transition s a).prob path.1 * (π path.1).prob path.2.1 *
        qForcedPrefixWeight M π path.1 path.2.1 k path.2.2

/-- The actual law of the post-initial-action prefix. At `k=0` this is the
unit law and contains no transition factor. -/
def qForcedPrefixLaw (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) (k : ℕ) :
    FiniteDistribution (QForcedPrefix (State := State) (Action := Action) k) where
  prob := qForcedPrefixWeight M π s a k
  prob_nonneg := by
    induction k generalizing s a with
    | zero =>
        intro path
        exact zero_le_one
    | succ k ih =>
        intro path
        exact mul_nonneg
          (mul_nonneg ((M.transition s a).prob_nonneg _) ((π _).prob_nonneg _))
          (ih path.1 path.2.1 path.2.2)
  sum_prob := by
    induction k generalizing s a with
    | zero => simp [qForcedPrefixWeight, QForcedPrefix]
    | succ k ih =>
        change (∑ path : State × Action × QForcedPrefix (State := State) (Action := Action) k,
          (M.transition s a).prob path.1 * (π path.1).prob path.2.1 *
            qForcedPrefixWeight M π path.1 path.2.1 k path.2.2) = 1
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, ih, mul_one]
        simp_rw [← Finset.mul_sum, (π _).sum_prob, mul_one]
        simp only [← Finset.mul_sum, (M.transition s a).sum_prob, mul_one]

/-- Rowwise support inclusion lifts to the actual fixed-initial-action
finite-prefix law. The policy is shared by both models, including at the
terminal action. The `k=0` case is immediate and requires no transition-row
premise to be used. -/
theorem qForcedPrefixWeight_support
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) (a : Action) (k : ℕ)
    (hrow : ∀ x b y, (M'.transition x b).prob y ≠ 0 → (M.transition x b).prob y ≠ 0)
    (path : QForcedPrefix (State := State) (Action := Action) k)
    (hq : qForcedPrefixWeight M' π s a k path ≠ 0) :
    qForcedPrefixWeight M π s a k path ≠ 0 := by
  induction k generalizing s a with
  | zero => simpa [qForcedPrefixWeight] using hq
  | succ k ih =>
      have htrans' : (M'.transition s a).prob path.1 ≠ 0 := by
        intro hz
        apply hq
        simp [qForcedPrefixWeight, hz]
      have hpolicy : (π path.1).prob path.2.1 ≠ 0 := by
        intro hz
        apply hq
        simp [qForcedPrefixWeight, hz]
      have hsuffix' :
          qForcedPrefixWeight M' π path.1 path.2.1 k path.2.2 ≠ 0 := by
        intro hz
        apply hq
        simp [qForcedPrefixWeight, hz]
      have htrans : (M.transition s a).prob path.1 ≠ 0 :=
        hrow s a path.1 htrans'
      have hsuffix := ih path.1 path.2.1 path.2.2 hsuffix'
      exact mul_ne_zero (mul_ne_zero htrans hpolicy) hsuffix

end StatisticalRL.QLearning
