# Finite trajectory return: builder handoff

Status: compiled implementation; independent source review pending. This is a
finite-horizon policy-evaluation component, not completion of Chapter 2 or the
monograph. No frozen-declaration or author-approval status is claimed.

## Source correspondence to review

Pinned source: arXiv:2610.41903v1, `source/upstream/tex/chapters/prelim.tex`.

- Lines 661–685 describe finite states/actions, horizon, time-dependent transition
  distributions, and deterministic rewards in `[0,1]`.
- Lines 695–697 allow a distinct randomized Markov policy at each time.
- Lines 702–716, label `eq:defn-V-pi-finite`, define expected total reward along
  sampled actions and states from the supplied starting state.
- Lines 784–791, label `eq:Bellman-finite-pi`, state the zero terminal value and
  backward policy Bellman recursions.

`FiniteTrajectory.lean` imports the existing `DecisionStage`/`backwardValue`
definitions without changing them. A list represents the actual remaining
stages, allowing different rewards, transition laws, and randomized policies at
every time. A suffix corresponds to starting at the source's step `h`.

## Actual definitions and proofs

- `FinitePath State Action n` is a recursive tuple of exactly `n` action/next-state
  pairs. The current state is supplied separately. `actions` and `nextStates`
  extract actual stored sequences; their lengths are proved to equal `n`.
- `pathWeight` multiplies `π_h(a_h | s_h)`, `P_h(s_{h+1} | s_h,a_h)`, and the
  subsequent path's actual mass. It does not invoke a value function or a
  Bellman equation. Nonnegativity and total mass one are proved.
- `trajectoryLaw` packages these proved weights as a `FiniteDistribution`.
- `pathReward` accumulates each stage's reward at the stored current state and
  selected action, advancing to that path's sampled next state.
- `trajectoryValue` is the genuine finite weighted sum of `pathReward` under
  `trajectoryLaw`, not an alias for `backwardValue`.
- `trajectoryExpectation_cons` proves first-step conditioning for any function
  of the entire path by splitting the finite product-carrier sum.
- `trajectoryValue_cons` derives the Bellman value backup from that conditioning
  identity and normalization. `trajectoryValue_eq_backwardValue` proves equality
  with the pre-existing backward recursion by induction on the stage list.

The law includes the next state after the final action, consistent with the
source's stated sampling rule. The extra terminal state does not enter a reward;
its transition probability sums to one. No positivity of a conditioning event is
required: the distribution is constructed directly from each supplied initial
state, including states unreachable under some separate initial distribution.

## Validation performed

Clean focused compilation:

```sh
bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/MDP/FiniteTrajectory.olean Formalization/MDP/FiniteTrajectory.lean
```

The command completed with no errors or warnings. A separate stdin probe imported
the compiled module and ran `#print axioms` on the two path-length theorems,
`pathWeight_nonneg`, `sum_pathWeight`, `trajectoryExpectation_cons`, and
`trajectoryValue_eq_backwardValue`. The path-length results use only `propext`;
the remaining inspected results use only `propext`, `Classical.choice`, and
`Quot.sound`. No custom axioms or unfinished proofs were introduced.

## Remaining boundaries

Independent review must confirm the source translation and the list-suffix time
index correspondence. A separate fixed-first-action trajectory Q-law, occupancy
marginals, randomized initial-state joint law, deterministic optimal-policy
existence, infinite-horizon trajectories, and the remaining chapters are not
established by this file. This handoff does not assert any of those results.
