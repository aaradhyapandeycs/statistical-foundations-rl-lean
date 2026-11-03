# Independent review: conservative policy-learning Hoeffding guarantee

Reviewed 2026-11-02. Exact staged target `.local/PolicyLearningHoeffding.lean` SHA-256 `b30bd558ad8f2e7d708b89b8541509e4616c508d0d77d0b8f9539e7a59b9912a`, independently recomputed. Reviewer owns only this report. This is an ordinary scratch/staged contribution, not a frozen source theorem or integrated export.

## Semantic verdict and source comparison

**PASS for the stated conservative true-model V-loss bound. It does not prove the source's sharp policy-learning theorem or its Q conclusion.**

I independently checked `generative_model_model_based.tex:814–865` (actual empirical MDP/greedy algorithm) and `:898–922` (`Thm:sample-compl-main`). The source theorem has one universal positive constant and the implicit sample condition with denominator `(1−γ)^3 ε²` and numerator `log(SAN/((1−γ)^2 εδ))`. It covers ε up to 1/(1−γ), asserts simultaneous true V and Q guarantees with errors ε and γε, and permits any empirical optimal deterministic output.

The staged theorem instead proves that, for every fixed admissible M, N>0 and δ in (0,1), with probability strictly greater than 1−δ, every state's actual true-model value loss of the implemented empirical greedy selector is at most

`2γ/(1−γ)^2 * sqrt(log(2K/δ)/(2N))`,

where `K=card((State→Action)×State×Action)=A^S*S*A`. This is a real finite-sample guarantee, not merely a conditional shell. It uses a much larger policy-class logarithm and the conservative horizon-four sample scaling that follows from a horizon-squared error coefficient. It does not give the source N-dependent logarithm, horizon-three rate, universal constant theorem, or a separate Q-error theorem. There is no explicit sample-complexity corollary in the reviewed file. Its selected output is the existing greedy selector; no claim for every possible empirical optimizer is formally exported here.

## Actual experiment and trajectory objects

The experiment is the integrated `samplingLaw M N`, the finite product of the true transition-row measures for every ((s,a),i), not an arbitrary probability law. `samplingLaw_stateActionRow` derives that its restriction to one state-action row is exactly that row's N-fold iid law, from proved global indexed independence and actual coordinate marginals. The empirical row in every deviation is the actual observed relative-frequency distribution for that same coordinate family and sample count.

Known reward and discount are copied exactly by `empiricalModel`. Its empirical policy selector is the actual previously reviewed fixed-point greedy selector, with proven empirical trajectory optimality. Both sides of the final loss concern **M**, the true model, and actual `trajectoryExpectedValue`; the empirical model appears only in construction and intermediate evaluation errors. The comparator is M.optimalGreedyPolicy, whose simultaneous stationary randomized trajectory optimality has already been proved. No empirical value is relabeled as true performance.

## Data dependence is correctly handled

For each deterministic map f:State→Action, the test vector is the **true** trajectory value under its point-mass stationary policy. That vector is fixed before sampling for that f, even though it depends on the unknown M. Ordinary fixed-vector Hoeffding is therefore applicable separately to it.

The proof unions simultaneously over all triples (f,s,a), with failure allocation δ/K. There are finitely many such triples and at least one, because source MDP carriers are finite nonempty. Hence 0<δ/K<1. The per-triple radius is

`‖V^f‖∞ sqrt(log(2K/δ)/(2N))`.

The finite union gives a single event containing the residual bound for **every** f and row. Only inside this event does the proof choose f equal to `policyEstimator M N hN data`. That pointwise specialization is valid even though this f depends on the same data. It is not an application of fixed-policy concentration to a dependent fitted policy, and no independence of the fitted policy from its samples is assumed.

Different policies' deviations share all their samples and are generally dependent. The union bound needs no independence among these events. Full original coordinate independence is used only to obtain the actual row iid law and the one-vector tail. Finite-domain measurability ensures the unions, complements and final success event are measurable. The strict probability >1−δ uses the independently proved strict-violation finite-sample Hoeffding lemma, not an unjustified conversion of a weak tail inequality.

## Transfer and constant check

The pointwise deterministic comparison decomposes true optimal V minus selected true V into the empirical evaluation errors of the true optimal policy and selected policy, plus a middle empirical-optimality difference that is nonpositive. Bounding the two coordinate errors by their full finite sup norms gives exactly the sum of two evaluation norms, with no reversed sign or missing absolute value.

For each deterministic f, `deterministic_policy_residual` proves the policy-induced transition residual reduces to the single action-row residual at (s,f(s)). This is the correct use of point-mass expectation and the same empirical MDP. The perturbation bound is applied with original M and that empirical model; reward and discount equality are discharged by reflexivity, rather than assumed approximation or hidden reward collapse.

On the simultaneous event, the actual true-value bound `‖V^f‖∞≤1/(1−γ)` gives the uniform residual tolerance

`e = 1/(1−γ) * sqrt(log(2K/δ)/(2N))`.

Each of the two evaluation errors is at most γe/(1−γ), so their sum is exactly the displayed `2γ/(1−γ)^2` coefficient. The factor 2 is the two-policy comparison, and 1/2 inside the square root is the Hoeffding constant. Neither N nor K is silently replaced with total samples or state cardinality alone.

At γ=0 the threshold is zero and the true greedy reward maximization makes the statement consistent with the previously independently reviewed exact endpoint theorem. There is no division by γ or true value norm. A zero test vector is handled by the imported zero-norm Hoeffding branch. Singleton action/state carriers and N=1 are allowed; N=0 is explicitly excluded because empirical frequency rows need a positive denominator.

## Expanded premise inventory

The final probability theorem has State/Action carriers (TYPING), Fintype instances (STANDING), and M expanded into nonempty state/action sets, true nonnegative normalized transition rows, known deterministic reward in [0,1], and discount in [0,1) (STANDING). Its remaining inputs are N (SOURCE algorithm count), hN:0<N (SOURCE positive sampling domain), δ and 0<δ<1 (SOURCE confidence domain). All constants and family cardinality are determined by those inputs. No supplied policy, concentration event, true-optimality certificate, sample accuracy, variance bound or target loss is a premise.

The helper with a uniform residual antecedent is explicitly conditional, but the probability theorem produces that antecedent on the constructed event. It does not export a conditional source theorem with an unproduced error estimate. The norm bound, perturbation estimates and empirical optimality are actual proved dependencies applied to their real objects. EXCESS=0 for the stated conservative theorem. Treating its result as a proof of the source's sharper theorem would fail source fidelity because its rate/logarithm and missing Q assertion differ, irrespective of compilation.

## Dependency identity and remaining work

Independently recomputed dependency hashes: `ModelBasedPolicyLearning.lean` `6f568330fd0744f11c0e965e5e3fd884dac5fd579965bbe4d7918f571e8c4f8c`; `PolicyEvaluationPerturbation.lean` `eb8844a5cb2f05a5ea44c2b48a9f9182947731e86ec66d57890e2cf800dfff38`; `PolicyEvaluationHoeffding.lean` `95779576e3078fbc7bd44c0e3d774e1abca99dd24fdaa2f622cf5d1b2975da3e`; `EmpiricalHoeffdingFamily.lean` `0b8bf547984a749623012f9a6a19ffe92ffa9c10f8a69d6b4abf139c794dc12d`. These are the previously reviewed integrated constructions, not new assumptions introduced to obtain the bound.

A sharp source theorem still requires improved concentration/dependence control without the policy-enumeration logarithm, sharper variance/resolvent analysis, the exact sample arithmetic and the simultaneous source V/Q event. The current finite-union construction solves the dependence problem conservatively, without claiming those sharp improvements. Production integration and actual imported-export auditing remain separate.

## Independent compiler and axioms

Source review was completed while awaiting the lead's explicit compiler slot. After the lead provided that slot, I copied the exact reviewed source unchanged to `.local/LearningHoeffdingIndependentAudit.lean`, appended `#print axioms` for all seven theorem exports, and ran:

`bash scripts/lean-local.sh .local/LearningHoeffdingIndependentAudit.lean`

Exit status 0, without warnings or errors. `samplingLaw_stateActionRow`, `samplingLaw_row_hoeffding`, `samplingLaw_all_policy_rows_hoeffding`, `deterministic_policy_residual`, `policyEstimator_loss_le_evaluation_errors`, `policyEstimator_loss_le_uniform_residual`, and `policyEstimator_hoeffding` each reported exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs in the reviewed source. The temporary source was deleted, and the compiler slot was immediately released to the lead. This validates the exact staged implementation and its transitive axioms; a future integration diff needs its own actual export check.

## Integrated source and actual export verification

Independently compared `Formalization/Generative/PolicyLearningHoeffding.lean` to the reviewed staged source: they are byte-identical, with SHA-256 `b30bd558ad8f2e7d708b89b8541509e4616c508d0d77d0b8f9539e7a59b9912a`. The integrated object was initially absent. Using the lead-allocated compiler slot, I compiled the exact integrated module to `.lake/build/lib/lean/Formalization/Generative/PolicyLearningHoeffding.olean` with `bash scripts/lean-local.sh -o ... Formalization/Generative/PolicyLearningHoeffding.lean`; exit 0 without diagnostics. I then ran `bash scripts/lean-local.sh .local/IntegratedLearningHoeffdingAudit.lean`, whose only import was the integrated module and whose seven commands inspected all seven actual imported theorem exports. Exit 0 without diagnostics; each reported exactly `propext`, `Classical.choice`, `Quot.sound`. The temporary probe was deleted, and the compiler slot was released to the recursive-unroll reviewer. This closes the integrated export check for this exact version; all source-sharp limitations above remain.
