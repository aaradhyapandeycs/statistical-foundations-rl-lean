# Independent review: conditional Q-learning final assembly

Status: the exact staged conditional final assembly and its budget/rate chain
were source-reviewed, freshly compiled in an isolated output, and axiom-probed.
This remains a **conditional** result: source comparator closeness is an
explicit premise. No production module was changed.

## Exact reviewed sources

| Item | SHA-256 |
|---|---|
| `QLearningComparatorRecursionDraft.lean` (private staged draft, not shipped) | `5afb53aed98e0ff2e4997c9b30b4388804b454b55e601b9ec1644241a08ae2dd` |
| `QLearningComparatorUnrollDraft.lean` (private staged draft, not shipped) | `bca8f09ad4448dfefb72345eefb062e1178b71a2dff8b0fd32a472117dfee72d` |
| `QLearningComparatorSandwichDraft.lean` (private staged draft, not shipped) | `681229bc763fce35a7f8317f27e544c597000c4071372cd85f46e2d26841ef60` |
| `QLearningComparatorSameDataDraft.lean` (private staged draft, not shipped) | `efbb587d08efabe00fa574b0b95692aeddc1bf156c6f6df2437d17ead17abe7b` |
| `QLearningFinalRateArithmeticDraft.lean` (private staged draft, not shipped) | `f73511348bb282488d048ed3543cd1d2e1a3e6e6bbe33c152e820490e372a408` |
| `QLearningFinalSampleBudgetDraft.lean` (private staged draft, not shipped) | `d1a4de44468a3011a02740e751a53d7015fb73e5ef03af56367ed0ea089d9171` |
| `QLearningFinalBudgetConsequencesDraft.lean` (private staged draft, not shipped) | `2666f637c7046b929cd95ff160b45b11051398b36fb9e46a5186c33ecd3fdc84` |
| `QLearningConditionalFinalAssemblyDraft.lean` (private staged draft, not shipped) | `6321dfcf7efe900b191f1bfce387b31f2928066be5f9a4795ceda506b8ce8b9a` |
| `QLearningConditionalUniversalConstantsDraft.lean` (private staged draft, not shipped) | `d03b576cbff63b78050762b624bcabd2a2a0a4ddb67dec93b2055ddba9be4cb5` |
| `Formalization/MDP/OptimalTrajectoryValue.lean` | `d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7` |
| `Formalization/ModelFree/QLearningLateRateSchedule.lean` | `984d87bdfada63b31da1ca967bbfe90fdbcef2587e7dcdd2da30d4c324637c1d` |
| Source `generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |

The source targets are the main theorem/domains at lines 894–908; the rate cap
at equation `eq:Q-comparison-parameters` (1087); comparator definitions and
the source residual/stability comparison around lines 1390–1562; the
same-data sandwich and radius at lines 1564–1753; `eq:Delta-final`; and the
final scalar conversion at lines 1787–1860.

## Source and premise review

The conditional error-radius theorem consumes the actual same-data sandwich
under `qSamplingLaw M T`. Its common event uses the same sample array both in
the source-indexed fluctuation and in every Q-learning iterate; it does not
substitute a separately resampled or coupled path. The finite-layer bridge
keeps `n+1` as the source update index, the source warm-up `T/2`, and the exact
positive-update interval through terminal `T`. The resulting event is
simultaneous over all state-action pairs and compares the actual sampled
iterate with `M.trajectoryExpectedQ M.optimalGreedyPolicy`. The production
bridge `optimalGreedy_trajectoryQ` identifies that expected return with the
true optimal Bellman Q-function.

The robust-comparator closeness is preserved as a visible hypothesis in both
conditional theorems and the existential wrapper. It separately bounds both
constructed fixed points, with the plus and minus signs retained, by
`D = sqrt(γρ/(2(1−γ)^3)) + 2ρ/(1−γ)^2`. The first term is precisely the
source part-(ii) stability scale; the second is the source reward-shift /
robust fixed-point residual contribution. The proof passes the lower
comparator's closeness to the lower side of the sandwich and the upper
comparator's closeness to the upper side. It does not derive this premise from
part (i), the same-data event, or arithmetic. Consequently this artifact is
not an unconditional proof of the source main theorem.

The source scalar radius matches `eq:Delta-final`: comparison coefficient
`1+2ρ+√ρ`, the actual late product, and the two terms in `D`. The budget
consequence chain uses the exact threshold
`c₃ log⁴(T) log(SAT/δ)/((1−γ)⁴ ε²)≤T`, proves the needed large-time/log and
transient conditions, derives the actual schedule product bound `T⁻⁴`, and
consumes the rho budget with the source constants. The source domain
`γ∈[1/2,1)`, `ε∈(0,H]`, `T≥2`, `δ∈(0,1)`, source rate schedule, and
initialization range are present in the conditional final theorem. The
universal wrapper fixes `c₁=c₂=1/4` and chooses `c₃` from a maximum depending
only on numerical constants and this fixed `c₂`; comparator closeness remains
after those constants and all problem parameters as a separate premise.

No source mismatch was found in the event law, update indices, signs, error
radius, budget constants, or the explicit conditional status. The conditional
wrapper does not silently assert source part-(ii) or the desired actual Q
error; both robust-comparator distance bounds remain in its theorem type.

## Independent build and axiom evidence

The nine exact staged files above were compiled in dependency order into fresh
isolated output in a local audit directory (not shipped)
using the pinned Lean executable. All nine compile logs are empty. The conditional
assembly artifact SHA-256 is
`a8f605dccd1f02ca6536f0ff051364fe64ce766d36a007041a8e97807e665e4b`; the
universal-wrapper artifact SHA-256 is
`40c2de5bbf7dfb3b24e8cbfd6263235ef45c393e1d0aa5de3a30497a8b82ddd7`.
The combined import-probe source SHA-256 is
`3b733bfbe4b5b7526efdae8ec72c61ef774148c3157530011cc8f87b7b48bead`; its
compiled artifact SHA-256 is
`a2cddc3f7dedbae3d28789612f56e9542cf9bbd3ddd1530970e3dd4b194817d2`.
The probe covered all 41 declarations/definitions across the nine local
modules, including both conditional final exports and both universal-wrapper
exports. Every one depends only on `propext`, `Classical.choice`, and
`Quot.sound`. A scan of the exact staged sources and probe found no `sorry`,
`admit`, or custom `axiom`.

The independent build reused existing compiled project and pinned-package
dependencies; it did not rebuild packages or overwrite production outputs.
This is isolated staged-build and source-review evidence, not a production
landing. It does not close source part-(ii) robust-model stability or justify
removing the explicit comparator-closeness premise.

## Production integration

The reviewed final-rate arithmetic, budget consequences, conditional accuracy assembly and universal-constant wrapper are integrated as corresponding `Formalization/ModelFree/QLearning*.lean` modules. Comparator closeness remains an explicit unproved hypothesis; this is not the unconditional source theorem. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 278 modules and audited 3,623 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
