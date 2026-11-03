# Independent source review: finite-horizon optimality

Source-first reconstruction, before inspecting `FiniteOptimal.lean`:

- `prelim.tex` lines 663–687 specifies one common finite MDP: finite state and
  action carriers, one horizon, and time-indexed transition kernels and
  deterministic rewards in `[0,1]`. Kernels and rewards are independent of the
  policy. A policy may randomize, independently at each state and stage, with
  any nonstationary family of finite action distributions (lines 694–696).
- At every `h ∈ [H]`, `V_h^π(s)` is the trajectory expectation of cumulative
  rewards from the chosen state, while `Q_h^π(s,a)` fixes the first action and
  follows the policy thereafter, including transition and later action
  randomness (lines 700–716, 724–733). These are conditional continuation laws,
  also for state-action pairs reached with zero probability initially.
- One deterministic Markov policy must simultaneously attain at least the
  value and Q value of every randomized nonstationary policy, at all states,
  actions and times (lines 737–745). It must use the same MDP as the compared
  policy. The existential policy quantifier precedes competitor policy, time,
  state and action quantifiers. Stagewise choices may depend on the MDP and the
  stage/state, but cannot choose a different policy for each query or rival.
- Lines 784–804 add terminal zero for both value and Q at `H+1` and the two
  Bellman equations for every decision time and state/action. A maximizing
  action must be a true argmax in the same finite action carrier. If `H = 0`
  is allowed, there are no decision-time queries and the sole terminal values
  are zero; the empty policy exists. Empty action carriers require special
  care because nonempty maximization is implicit at a genuine decision stage.

Source SHA-256: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

## Findings

**Result: PASS for the stated positive-horizon finite-model source claims,
subject to the representational boundary below.** This is an independent
source/code review of the indicated implementation, not an author-approved
frozen-statement or whole-paper certification.

- `EnvironmentStage` (lines 21–28) owns kernels, rewards, reward bounds, and
  nonemptiness; `withPolicy` (33–41) copies those fields unchanged. The
  randomized competitor sequence is attached by `controlled` (44–47). Thus
  comparisons cannot improve their objective by modifying the model.
- `FiniteTrajectory.lean` lines 71–83, 96–117 define and normalize the actual
  policy/transition path mass and reward sum, and take their expectation.
  `FiniteQTrajectory.lean` lines 24–33 and 55–59 first fixes an action, samples
  the model transition, and then samples the tail policy. Thus Q is meaningful
  even for an action with zero policy probability. The extra terminal
  transition is normalized away and does not add a reward.
- A single constructed policy list `greedyStages es` (lines 99–104) is
  independent of the rival, query index, state, and action. Every rule is a
  point mass (86–91) at `greedyAction`; `greedyAction_max` (78–84) proves its
  selected action actually attains the finite maximum. Continuations are
  computed from the correct tail of the *same* environment list.
- `greedy_suffix_dominates` (213–220), together with `controlled_drop` and
  `greedyStages_drop` (188–209), compares that one constructed policy against
  arbitrary randomized nonstationary competitors at all suffixes, states and
  actions. `greedy_suffix_value` and `greedy_suffix_Q` (241–249) identify the
  recursive optimal values with the greedy policy's actual trajectory values.
  `optimalAt_bellman` (252–265) supplies both indexed source equations at each
  `i : Fin es.length`, where source time is `h = i + 1`; terminal theorems
  (230–238) yield both zeros at `H+1`.
- All stage list lengths, final decision time, and last-step transition are
  covered; when `H = 0`, there are no `Fin 0` decision indices and the
  constructed greedy list is empty, with both terminal values zero.

Binder check for `greedy_suffix_dominates` (no author-approved frozen
manifest is claimed):

| Binder, expanded where relevant | Classification and evidence |
| --- | --- |
| `State`, `Action`, their `Fintype` instances | TYPING: finite state/action carriers, source 663–668. |
| `es : List (EnvironmentStage State Action)` | SOURCE/STANDING: fixed horizon as list length, each transition is a normalized nonnegative `FiniteDistribution`, each reward is in `[0,1]`, and each genuine stage records nonempty state/action; source 663–687. No policy or optimality hypothesis is bundled. |
| `π : ℕ → State → FiniteDistribution Action` | SOURCE policy, source 694–696; every rule is an arbitrary normalized action law. The total-ℕ representation is discussed below. |
| `n : ℕ` | SOURCE time `h=n+1` when `n < H`; the theorem also covers terminal and longer dropped suffixes. |
| `s : State`, `a : Action` | SOURCE universally quantified state and action, source 724–738. |

No excess proposition, pre-assumed Bellman equation, maximizer, dominance, or
trajectory identification is an input. The source's existential policy is
represented by the explicit construction `greedyStages es`; the source
competitor and query quantifiers occur afterward in `greedy_suffix_dominates`.
The formally stronger natural suffix range includes values past `H` as empty
suffixes; the source-facing indexed Bellman theorem itself restricts to valid
decision times.

**Boundary/representation limitation.** Competitors are total functions on
`ℕ` rather than functions on `Fin H`. For `H > 0`, the environment supplies a
nonempty action carrier, so any finite nonstationary randomized policy has an
extension by a fixed point mass; only the first `H` rules are consumed. For
`H = 0`, if the state carrier is nonempty and the action carrier is empty, a
mathematical empty-horizon policy exists but `ℕ → State →
FiniteDistribution Action` has no inhabitant. The terminal-value and empty
greedy-list results still hold, but the competitor statement is then vacuous
and is not a general equivalence of empty-horizon policy spaces. No theorem
explicitly constructs the finite-policy extension; it is a semantic argument,
not a separately compiled bridge. The source discusses finite action sets and
finite maximization, but does not expressly resolve this zero-horizon corner.
The implementation also does not supply a standalone theorem that its greedy
list is equal to `controlled es π` for some total deterministic `π`; its actual
point-mass stage construction and common-environment fields are transparent
in the definitions. These are interface limitations, not evidence of a wrong
positive-horizon result.

## Checked evidence and identity

A temporary copy of `FiniteOptimal.lean` was compiled with
`bash scripts/lean-local.sh <temporary-probe>` after
adding `#print axioms` and a source-indexed composition probe. The probe
establishes both V and Q dominance at `i : Fin es.length` using the same
`greedyStages es`, after proving `controlled` preserves length. It passed. The
seven checked exports were `greedy_suffix_dominates`, `greedy_suffix_value`,
`greedy_suffix_Q`, `optimalAt_bellman`, `optimalValueAt_terminal`,
`optimalQAt_terminal`, and `greedyAction_max`; all reported only `propext`,
`Classical.choice`, and `Quot.sound`. No integration build was run here.

Reviewed SHA-256 digests:

- `Formalization/MDP/FiniteOptimal.lean`: `abd23ed8206032df152160f50d838d91bf99a169a09bbf2612bc5e9608494e85`
- `Formalization/MDP/FiniteQTrajectory.lean`: `1810d6ae58d337e2614f56d1a603bf9e3e0d49367cef37066f992112eaa7ccba`
- `Formalization/MDP/FiniteTrajectory.lean`: `5b6f53bc1822729beb715ad385b74951dedf7c0596ca654cf246945593ca3130`
- `Formalization/MDP/FiniteHorizon.lean`: `585b0cd1a0a4fce3f98484cf6a5e671356a2aa2970af563d0764fa022f2050ba`
- `Formalization/MDP/Basic.lean`: `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088`
