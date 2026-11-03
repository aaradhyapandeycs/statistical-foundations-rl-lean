# Independent review: absorbing-value parameter stability

**Verdict: pass for fixed-parameter stability of actual optimal trajectory values.** This is the deterministic sensitivity ingredient of the source cover proof, not the finite cover or a statistical independence result.

The source uses `prelim.tex:636–651`, especially `eq:V-star-perturbabtion-r-inf`, in the proof of `LemValueCover` at `generative_model_model_based.tex:2621–2629`: for the same absorbing state and admissible parameters u,v, the models have identical transition kernels and rewards differing by at most `(1−γ)|u−v|`. The source reward perturbation bound then gives `‖V*_(x,u)−V*_(x,v)‖∞≤|u−v|`.

The staged file proves this inequality and the sharper equality for every admissible finite MDP M, x and `u,v∈[0,1/(1−γ)]`. Its fixed parameters are real numbers, with both admissibility endpoints explicit; nonempty state/action carriers and `0≤γ<1` come from M. The source models are the reviewed `stateAbsorbingModel`, with the same x and original M. Both transitions and discount are definitionally equal across the two parameters, and the reward difference vanishes away from x and equals `(1−γ)(u−v)` at x for every action.

For the Q estimate, the proof compares the two actual optimal Q fixed points using the discounted optimal Bellman contraction. Holding one Q vector fixed, the difference between the two Bellman operators is exactly their reward difference, so `‖Q_u−Q_v‖∞≤γ‖Q_u−Q_v‖∞+(1−γ)|u−v|`. Since `1−γ>0`, this gives the exported Q bound `≤|u−v|`. Nested finite sup norms cover all states and actions and no choice of greedy actions is presumed equal.

The state-value result uses the separately proved identity between actual optimal-policy trajectory value and the maximum of the optimal Q row, then nonexpansiveness of finite action maximum. The reverse inequality for `absorbingOptimalValue_parameter_norm_eq` evaluates at x: the reviewed absorbing-state trajectory theorem gives values u and v for every stationary policy, including each model's own optimal greedy policy. Hence the sup norm is at least `|u−v|`, making equality correct even if the policies choose different maximizing actions. The argument also covers γ=0 and u=v; no division by γ or nonzero-distance assumption occurs.

The dependency `PolicyLearningAbsorbingPreservation` defines `optimalTrajectoryValue` and provides its actual trajectory-to-Q maximum identification; this module imports it, but does not itself establish the complete source preservation theorem, grid existence, empirical-data independence, random-parameter decoupling or the cover lemma. Its bound may later be applied pointwise to a data-dependent admissible parameter, but such application does not make that parameter independent of a removed row. The preservation source and its separate independent review must be retained as dependencies when using this result for `LemValueCover`.

## Verification

Staged source SHA-256 `41f647e9c3c10253eb78a1089f22def29460b4452149e3b6bd5c3a0a9684f86e`; staged preservation dependency SHA-256 `f30ea6939c2f18a913321da758575a13d023241ec8ff19c174e899bcb3cc034b`; staged absorbing dependency SHA-256 `dfdedc125e606f88241c2c491df64306ee3b0b2f83b6361f5f9dcaa6b2bd0a92`. Both dependencies were freshly built in an isolated project-owned staging directory. An exact unchanged source copy with original imports and three appended `#print axioms` commands compiled independently, exit 0. All three exported theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Actual integrated export verification remains separate.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningAbsorbingLipschitz.lean` SHA-256 `65c20456263f0ce790b7da68951776a01bc08dcd313ed09f6da07c7f25f361fe` differs from the reviewed staged source only by qualification of the preservation import. The actual production module compiled, and an import-only audit of all three exports used only `propext`, `Classical.choice`, and `Quot.sound`.
