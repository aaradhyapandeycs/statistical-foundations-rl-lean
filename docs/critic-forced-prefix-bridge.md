# Independent source review: forced-action prefix and infinite Q bridge

**Verdict: PASS for the fixed-state, forced-initial-action trajectory Q
expectation, its all-discount policy Bellman fixed-point identification and
source V–Q policy-average identity.** This is scoped to the reviewed staged
source and its reviewed/integrated dependencies, not an optimal-Q or
whole-chapter certification.

## Source reconstruction

`prelim.tex` lines 114–123 defines `Q^π(s,a)` as the expected infinite
discounted trajectory reward with initial state `s`, first action `a`, the
model transition after that action, and π controlling later actions. It
quantifies over every state and action; the intervention interpretation is
needed when `π(a|s)=0`, since ordinary conditioning on a null event is not a
unique probability law. Lines 123–128 assert `V^π(s)=E_{a∼π(s)}Q^π(s,a)`;
lines 190–207 define the Q-Bellman operator and state that the source Q is its
fixed point. A valid bridge must identify actual forced-path expectations,
not merely define a value as a fixed point, and must use the original π rather
than forcing the same action at later times.

## Findings

1. The imported `forcedActionTrajectoryLaw` is the reviewed actual
   Ionescu–Tulcea law: its first pair is sampled from the action point mass at
   `a` and the corresponding `P(·|s,a)`, while its history kernel uses π at
   every later reached state. The staged `forcedInitialStage` similarly
   attaches the point-mass policy **only to the first finite stage**; its tail
   stage list is required to consist of the original model's stationary π
   stage. Thus the finite and infinite constructions use the same intervention
   and continuation.
2. `forcedHistoryMass` and `forcedPrefix_singleton_eq_mass` prove the actual
   infinite law's finite cylinder masses: the first factor uses the point
   mass, and each subsequent factor uses π at the preceding next state and
   the original transition. `forcedHistoryMass_eq_pathWeight` matches this
   product to the independently defined finite path mass. No division or
   positivity hypothesis occurs, so zero-probability histories and
   `π(a|s)=0` are covered.
3. `forcedActionTrajectoryLaw_map_finitePrefix` uses the previously reviewed
   index-preserving history/path equivalence and singleton extensionality to
   prove equality of **measures** for a forced first stage and any finite
   stationary tail. `partialDiscountedReturn_eq_forcedPath` maps the correct
   first reward and the shifted tail path, then
   `forced_integral_partial_return` transports its actual integral and
   establishes, for every `n : ℕ`,

   ```text
   E_forced[sum_{t=0}^n γ^t r_t]
     = r(s,a) + γ E_{t∼P(·|s,a)}[finiteDiscountedValue π n t].
   ```

   The general finite-prefix measure theorem is deliberately nonempty because
   the first action is an intervention. The `n=0` instance of the displayed
   formula is the one-reward horizon; a separate compiled probe checked this is
   exactly `r(s,a)`. Another checked that the genuinely empty partial sum has
   integral zero. Hence there is no unhandled zero-horizon or n/n+1 shift in
   the claimed expectation result.
4. `trajectoryExpectedQ_eq_policyFixedPoint` takes the proved limit of the
   forced-law partial-return integrals and the finite state-value evaluation
   limit. Finiteness permits passing the limit through the actual transition
   expectation. It identifies their limits and uses the independently proved
   policy Q fixed-point/continuation formula. It quantifies over every model
   discount `0 ≤ γ < 1`, including γ=0, every state and every action, with no
   extra transition, support, convergence, or fixed-point assumption.
   `trajectoryExpectedQ_bellman` then uses the actual fixed-point equation.
5. `trajectoryExpectedValue_eq_policyAverageQ` uses the independently
   integrated `PrefixValueBridge` trajectory-V/fixed-point identification,
   the policy fixed-point average relation, and the Q identification above.
   Its two sides are the source's actual trajectory expectations; this is not
   merely an identity between unnamed Bellman fixed points.
6. An independent compiled example takes a policy concentrated on `b` with
   `a ≠ b`, proves its probability of `a` is zero, and still instantiates the
   forced Q/fixed-point equality at `a`. The result is an intervention-based
   extension at null events; it does not claim every possible version of a
   regular conditional expectation agrees there.

The theorem binders expand to finite nonempty model carriers, normalized
transition and stationary-policy rows, source reward/discount bounds, an
arbitrary state and first action; tail-stage equality in the general measure
bridge expresses that it is the **same stationary model and policy** and is
proved from `List.replicate` in the all-horizons expectation theorem. No
statistical lower bound or optimal-Q trajectory identification is proved by
this file.

## Checks and identity

A copy of the exact stable staged source compiled via
`bash scripts/lean-local.sh <temporary-probe>`,
with the zero-policy-support and zero-/one-reward-horizon probes above. Eight
`#print axioms` checks covered `forcedPrefix_singleton_eq_mass`,
`forcedHistoryMass_eq_pathWeight`,
`forcedActionTrajectoryLaw_map_finitePrefix`,
`partialDiscountedReturn_eq_forcedPath`, `forced_integral_partial_return`,
`trajectoryExpectedQ_eq_policyFixedPoint`, `trajectoryExpectedQ_bellman`, and
`trajectoryExpectedValue_eq_policyAverageQ`; all used only `propext`,
`Classical.choice`, and `Quot.sound`. The temporary file was removed. The
probe checks the staged source against existing imported project artifacts;
facade/export integration and whole-project build remain separate.

SHA-256:

- `.local/ForcedPrefixBridge.lean`: `f8b1e459e311c7dfc914f13bd70f9129931bf7b6e3d79b7d2b6d69fe2bc50e3a`
- `Formalization/MDP/PrefixValueBridge.lean`: `bd286567aa059c3e5fb293f1943eb06bd2e3d79c8dc9484d8a73195a2db16e89`
- `Formalization/MDP/ForcedActionReturn.lean`: `87f447460f55da6d49a7311a73d69537f934395d3fbadf9c7a88b0c0c4bca0c2`
- `Formalization/MDP/ForcedActionTrajectory.lean`: `77fe3fbe10217a1e8a6476a3ed1ea978c698c1972dec82b769f427491a9d9346`
- `Formalization/MDP/PolicyValueQ.lean`: `3f1c5c812a7b60a8f99aecce5d7ce02cc3bab92c8335186feccf7e8fbc9b6369`
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`
