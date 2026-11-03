# Independent audit of the staged Theorem 3.7(ii) negation

Reviewed 2026-11-02. Exact staged target: `.local/Theorem37Negation.lean`, SHA-256 `d9ae884a0ec7245a3acaae1f07d02a67a0443ce268a2f63facbe215d7368dd12`. This is an ordinary staged declaration, not an author-frozen source transcription. This reviewer owns only this report.

## Verdict

**PASS: the literal Lean theorem `¬ printedTheorem37ii`, with clean axiom closure, for its explicitly encoded experiment and estimator interface. NOT CERTIFIED: exact, interpretation-free equivalence of `printedTheorem37ii` with every possible intended reading of the manuscript.**

The encoded assertion is source-shaped and general in S, A, N, γ, ε and the represented estimators; its contradiction specializes to S=1, A=16, N=1 and γ=2/3. There is no assumed one-state restriction on the encoded claim, no model-specific oracle supplied to the witness estimator, and no assumed statistical error bound. The one-state specialization is made inside the proof. A source reader accepting the theorem's displayed parameter range and the stated known-reward convention obtains a substantive counterexample, not merely a syntactic inconsistency of an artificial estimator class.

No source/author ruling was supplied to resolve the remaining interpretation boundaries below. This report therefore does not award an exact original-source theorem-negation certification or silently repair the source.

## Independent source reconstruction

I read the raw `theorem:azar`, model-based chapter lines 1438–1464, and the sampling/reward conventions at lines 15–31. The source asserts a small universal positive c_N such that, for any ε and γ in the displayed ranges and any size with SA≥16, when N independent samples per state-action pair meet the displayed upper bound, every Q estimator admits an S-state/A-action γ-discounted MDP with strict sup-norm error probability at least 1/4. A universal constant must precede the problem parameters. The MDP may depend on the estimator and those parameters.

The encoded order is exactly `∃ c>0, ∀ S A N γ ε, displayed restrictions → ∀ Seed/measurable structure/ν/probability instance/estimator, ∃ M, discount equality ∧ failure probability ≥1/4`. Thus an estimator may depend on S,A,N,γ,ε and even the proposed c; the proof's witness does not need dependence on c or ε. It is chosen before M.

The source MDP definition (`prelim.tex:31–45`) uses stationary transitions, deterministic rewards in [0,1], known rewards, and discount in [0,1). The source policy convention is stationary randomized (`:63–76`), its Q is the discounted expected return after the designated first action (`:114–123`), and Q* is the value of a simultaneous deterministic optimizer (`:133–141`). These conventions support the project's actual trajectory Q of its optimal greedy stationary policy. The forced-action meaning is supported by the source prose and handles actions with zero policy support.

Source hashes: model-based chapter `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`; prelim `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

## Expanded binder and scope audit

Each logical input of the encoded source proposition is listed below, including estimator fields and MDP fields. The finite-carrier instances for `Fin` are canonical typing infrastructure. The entries marked EXCESS/UNRULED mean extra formal restrictions relative to the manuscript's unqualified estimator wording; they are not assumptions that make the concrete counterexample spuriously succeed.

| Input or quantified field | Bin | Source or interpretation |
|---|---|---|
| ∃ c : ℝ | SOURCE | Universal c_N |
| 0<c | SOURCE | Positive constant |
| ∀ S : ℕ | SOURCE | Number of states |
| ∀ A : ℕ | SOURCE | Number of actions |
| ∀ N : ℕ | SOURCE | Samples per row |
| ∀ γ : ℝ | SOURCE | Discount parameter |
| ∀ ε : ℝ | SOURCE | Accuracy parameter |
| 16≤S*A | SOURCE | Displayed size bound |
| 2/3≤γ | SOURCE | Displayed discount lower bound |
| γ<1 | SOURCE | Displayed discount upper bound |
| 0<ε | SOURCE | Displayed accuracy lower bound |
| ε<1/(32*(1−γ)) | SOURCE | Strict displayed accuracy upper bound |
| N≤c*log(S*A)/((1−γ)^3*ε^2) | SOURCE | Exact displayed sample upper bound |
| ∀ Seed : Type | EXCESS/UNRULED | Explicit independently seeded estimator representation; fixed universe |
| MeasurableSpace Seed | TYPING | Needed for encoded seed experiment |
| ∀ ν : Measure Seed | EXCESS/UNRULED | Randomization interface not specified by the printed theorem |
| IsProbabilityMeasure ν | TYPING | Probability seed normalization |
| ∀ est.estimate | SOURCE | Universal Q-estimator rule, within encoded interface |
| est.estimate_measurable : ∀ r γ, Measurable (estimate r γ) | EXCESS/UNRULED | Printed theorem does not explicitly restrict or define measurable estimators |
| reward-table argument r of estimate | STANDING | Known reward, chapter :31 and prelim :43 |
| discount argument γ of estimate | STANDING | Known discount in generative-model algorithm setup |
| sample-array argument of estimate | SOURCE | N observations per state-action row |
| seed argument of estimate | TYPING | Randomization coordinate of encoded experiment |
| finite Q-array codomain of estimate | TYPING | Source Q-estimation output |
| ∃ M | SOURCE | Adversarial fixed-size MDP after estimator |
| M.state_nonempty | STANDING | Nonempty source state carrier |
| M.action_nonempty | STANDING | Nonempty source action carrier |
| M.transition | STANDING | Stationary source probability rows |
| M.transition mass nonnegative | STANDING | Probability distribution definition |
| M.transition row sum =1 | STANDING | Probability distribution definition |
| M.reward | STANDING | Deterministic reward table |
| M.reward_nonneg | STANDING | Source [0,1] range |
| M.reward_le_one | STANDING | Source [0,1] range |
| M.discount | STANDING | Discounted source model |
| M.discount_nonneg | STANDING | Source [0,1) range |
| M.discount_lt_one | STANDING | Source [0,1) range |
| M.discount=γ | SOURCE | Same prescribed discount |

Inventory counts: SOURCE 17, STANDING 13, TYPING 4, EXCESS/UNRULED 3, RULED 0. Consequently the strict exact-source five-bin test is **not passed**. The unruled restrictions narrow the universal estimator assertion; a theorem proving that narrower assertion would not establish the full printed universal assertion. Here its negation is proved. A conventional deterministic estimator lies in the narrow class, so the narrowing does not invalidate the exhibited counterexample against any broader intended class containing that rule. This logical direction must not be reversed.

The Lean theorem `not_printedTheorem37ii` has no explicit extra premise: it concludes the literal negation of the definition. Its temporary proof assumption is exactly that definition, expanded above. The auxiliary error theorem takes arbitrary M and data, no bound or exactness premise. The positive-constant premise of the feasibility helper is discharged from the proposed universal c; its reward/discount equalities are discharged by reflexivity when using exactness.

## Object semantics and sampling

`Theorem37Samples` is the full array indexed by ((s,a),i). `theorem37GenerativeLaw` is literally the finite product of the true row measures, not an assumed law. Normalization, actual coordinate marginals and joint independence are proved. The source generative-model convention states independence per query, so cross-row independence is appropriate. The seed law is multiplied with that genuine data law. ν is selected before M, so it cannot itself encode the unknown transition.

For fixed r,γ the estimator output is measurable jointly in data and seed. The norm is the finite function-space sup norm, equivalent to the source maximum absolute error over state-action pairs. The strict event uses ε<norm, matching the source >ε. A probability measure is used, so `Measure.real` is the usual real probability rather than a misuse of infinite-mass conversion.

The estimator receives M.reward and M.discount as observable inputs. It never receives M.transition. Allowing reward to vary with the adversarial M is compatible with known rewards: one single rule maps each supplied reward table to an answer. Its error is zero for every such table and every admissible one-state transition, rather than only for an artificially fixed reward family.

The concrete rule is `r(s,a)+γ max_b r(s,b)/(1−γ)`. With one state every transition is forced to stay there, so after the initial action the best known reward can be repeated. The imported actual-trajectory theorem proves this equality, not an unproved Bellman interpretation. The witness ignores samples and its Unit seed. Its joint measurability in reward, discount and data is separately proved in `OneStateExperiment`; therefore even a reasonable stronger requirement of joint measurable dependence would not exclude the witness.

The constant feasibility result works for every c>0, choosing ε>0 sufficiently small so N=1 meets the exact printed bound. It also meets the strict ε upper bound and all size/discount restrictions. It does not rely on N=0. No special value or limiting argument replaces the source's universal constant.

## Unruled interpretation boundaries

1. The source does not specify a universal measurable seed interface or a representation theorem for all randomized probability-kernel algorithms. The encoded seed is in `Type`, and estimator measurability is required for each fixed reward and discount. Exact equivalence of classes is unproved. The deterministic witness belongs to the ordinary intended class without needing such a representation theorem.
2. The source's preliminary prose says it focuses on regimes where S, A and the effective horizon are all large (`prelim.tex:59`). This gives no numerical restriction that can be inserted into the displayed theorem. The staged proposition follows its explicit SA≥16 condition and does not import an unprinted S≥2. If that narrative was intended to exclude S=1, the exhibited contradiction would address the displayed extension, not the restricted intended claim. Author clarification is required to settle that intent. The nearby A≥2 policy-learning setup, even if carried forward, does not exclude A=16.
3. The encoded claim has no N>0 premise, because none is displayed. Positive N may be implicit in ordinary sampling terminology; adding it would weaken the encoded assertion, but the N=1 counterexample survives. Fin S/Fin A implement labeled finite carriers by harmless relabeling. SA≥16 already forces S,A positive, so no empty-state trick is used.
4. Q* is interpreted in the manuscript's stationary policy framework. No new certification of optimization over arbitrary history-dependent policies is supplied here.

Accordingly this report certifies the encoded proposition's falsity and identifies the concrete known-reward obstruction to the displayed range. It does not certify a fully ruled, author-approved replacement or an interpretation-independent negation of the entire original theorem.

## Independent compilation and axioms

I coordinated with the other workers so the two-compiler limit was respected. I copied the exact reviewed source unchanged to `.local/Theorem37IndependentAudit.lean`, appended five axiom commands, and ran:

`bash scripts/lean-local.sh .local/Theorem37IndependentAudit.lean`

Exit status 0; no compiler diagnostics. `theorem37GenerativeLaw_probability`, `theorem37GenerativeLaw_marginal`, `theorem37GenerativeLaw_independent`, `theorem37OneStateEstimator_error`, and `not_printedTheorem37ii` each depend only on `propext`, `Classical.choice`, `Quot.sound`. The temporary source was deleted. This is exact staged-file compilation and transitive axiom evidence, not public-export integration or whole-project completion.
