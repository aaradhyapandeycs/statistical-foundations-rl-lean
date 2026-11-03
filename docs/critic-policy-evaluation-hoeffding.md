# Independent review: conservative policy-evaluation Hoeffding bound

Reviewed 2026-11-02. Stable staged `.local/PolicyEvaluationHoeffding.lean` SHA-256 `75b1c4e40ad366e07e88d3b9fab10650da84e0ab7722c3b5e04fd81bd14d4d30`, independently recomputed after builder handoff. Reviewer owns only this report.

## Verdict and rate

**PASS for the stated conservative probability theorem under the actual policy-row sampling law. It does not prove the source's sharp policy-evaluation theorem.**

For every fixed admissible M, fixed stationary randomized π, positive N and δ in (0,1), let S be the actual state cardinality and V its true trajectory value. The proved error threshold is exactly

`γ ‖V‖∞/(1−γ) * sqrt(log(2S/δ)/(2N))`.

Replacing ‖V‖∞ by its proved geometric bound gives exactly

`γ/(1−γ)^2 * sqrt(log(2S/δ)/(2N))`.

In both cases the good event has probability **strictly greater than** 1−δ. For every ε>0, the exact sufficient per-state sample condition is

`N ≥ log(2S/δ)/(2 ε^2 (1−γ)^4)`.

The final proof uses γ≤1, so this sufficient count conservatively drops a possible γ² improvement. It preserves the factor 1/2. There is no hidden universal constant, extra state factor outside the logarithm, or erroneous use of total sample count in place of per-state N. Total observations are NS. The bound has horizon exponent four, whereas source `thm:model-based-policy-eval` (`generative_model_model_based.tex:142–155`) has exponent three and a different logarithmic expression. No exact source-theorem closure follows from this weaker rate. The absence of the source precision upper bound in this independently valid conservative theorem is an extension of its own scope, not a substitute transcription of the source theorem.

## Actual samples and fixed-vector condition

I inspected the source direct policy-row algorithm (`generative_model_model_based.tex:78–130`), its analysis beginning at `:179–225`, and the imported integrated sample definitions. The experiment is the actual finite product indexed by (s,i), with coordinate law the true `M.policyTransition π s`. Each empirical row is the observed relative-frequency distribution. The estimator is the same integrated empirical Bellman solution, already identified with actual infinite discounted trajectory value in its empirical model.

`samplingLaw_stateRow` proves the pushforward of that whole experiment under restriction to one state is exactly the row's N-fold iid sample law. It uses proved global indexed independence restricted by the injective map i↦(s,i), and proved actual marginals. No row-law equality or concentration event is assumed by the final probability theorem.

The value vector being concentrated is `M.trajectoryExpectedValue π`, fixed before data are sampled. M and π are outer fixed inputs; neither reads the sample array. The true value's dependence on the unknown model is legitimate in a theoretical concentration argument and does not make it a data-dependent empirical value. Applying the theorem to π chosen from the same observations would require a separate uniform/decoupling argument and is not licensed here.

## Collapsed-model composition

The original true MDP and integrated empirical evaluation MDP need not have identical action-indexed rewards: the latter embeds the known π-averaged reward as action-independent. The proof correctly avoids assuming their tables equal. Instead it constructs a true collapsed model with the same action-independent π-averaged reward and true policy transition kernel. Its value Bellman operator equals the original model's operator, and uniqueness plus the actual trajectory/fixed-point bridge proves equality of their actual trajectory values.

The deterministic perturbation helper is then applied between that true collapsed model and the actual empirical model, whose reward and discount match definitionally. The residual expands to `(P̂π−Pπ)V` on the original true trajectory value. The estimator is converted to actual empirical trajectory value through its proved bridge. This supplies a term-level composition of the deterministic bound with the real algorithm; there is no unsupported equality of original and collapsed rewards or silent replacement of the estimated object.

## Union, constants, strictness and endpoints

The proof applies the singleton nonnegative-vector Hoeffding theorem at confidence η=δ/S in each state. Nonnegative V follows from actual return bounds. Source MDP nonemptiness gives S≥1, hence 0<η<1. The imported radius is exactly ‖V‖∞ sqrt(log(2/η)/(2N)), proved equal to the displayed log(2S/δ) form.

Each strict violation has probability <η. The finite union over all states is bounded by the sum of those probabilities, giving <δ. Independence across different states is not needed for that union step; it is already present in the actual experiment. The complement simultaneously supplies all residual inequalities; deterministic perturbation gives the value-error event by inclusion. Probability normalization and finite-domain measurability justify the complement identity and real-probability conversion.

The strict success probability is supported by the imported `familyViolation_lt`: in a finite sample space, a nonempty strict violation set has a strictly positive gap above its radius. Hoeffding applied at its minimum attained deviation gives a strict tail improvement. Empty violation sets are handled separately. Thus strict >1−δ is not inferred improperly from an ordinary ≤δ tail bound.

No division by γ occurs, so γ=0 is covered and the value-error threshold becomes zero. The known reward makes the estimator exact there. If ‖V‖∞=0 the imported zero-vector branch proves residual deviation zero directly, avoiding division by zero in the Hoeffding exponent. For zero statistical variance but nonzero norm (for example a constant V), the theorem remains a valid conservative bound; it does not assert a variance-sensitive zero radius. A zero-variance Bernstein refinement is not claimed or required here. N=1 is allowed; N=0 is explicitly excluded by the frequency construction.

## Input audit

Final probability theorems have only the finite state/action carriers, their Fintype instances, M and π, positive N, and δ in (0,1). Expanded M fields are nonempty state/action sets, probability transition rows (nonnegative masses and unit row sums), deterministic rewards in [0,1], and discount in [0,1). Expanded π fields are probability action rows. All are source standing/typing inputs. No approximation certificate, policy independence hypothesis, desired success event, variance bound or concentration conclusion is assumed.

The sample-size corollary additionally takes ε>0 and the exact displayed conservative N lower bound; these are explicit premises of that corollary. The intermediate `valueEstimator_perturbation` takes a nonnegative residual tolerance and a uniform residual inequality, but the probability theorem proves those inequalities on its constructed good event rather than importing them as theorem premises. All production uses are thereby supplied. Relative to these honestly scoped conservative statements, EXCESS=0. Relative to the sharp source theorem, the horizon-four sample condition cannot replace its horizon-three condition, so exact source certification would fail.

## Remaining work and evidence

The source sharp variance/resolvent analysis, its exact logarithm and universal-constant theorem remain open. The staged file imports `PolicyEvaluationPerturbation` by its local staging name; production integration must replace it with the actual integrated import and recheck the affected export. This review certifies the stable staged implementation, not a future integration diff.

Dependency hashes recomputed: `EmpiricalHoeffdingFamily.lean` `0b8bf547984a749623012f9a6a19ffe92ffa9c10f8a69d6b4abf139c794dc12d`; `EmpiricalHoeffding.lean` `fd8be9002c7e5c6e418461818e7842c96520ca604e10e466f8431b1307798b55`. The staged perturbation dependency is the previously reviewed `eb8844a5cb2f05a5ea44c2b48a9f9182947731e86ec66d57890e2cf800dfff38`.

The first independent exact-copy check through `scripts/lean-local.sh` failed at import resolution because that wrapper does not include the staging directory in its search path. This was a staging-path failure, not a theorem error. I then independently compiled the exact reviewed perturbation source to a fresh temporary directory as `PolicyEvaluationPerturbation.olean`, and ran `.local/lean .local/HoeffdingIndependentAudit.lean` with that directory plus the ordinary project/dependency artifact paths in `LEAN_PATH`. This used no preexisting staged dependency artifact and modified no dependency artifact.

The exact Hoeffding source copy with nine appended `#print axioms` commands exited 0 without diagnostics. `policyCollapsedModel_bellman`, `policyCollapsedModel_trajectoryValue`, `valueEstimator_perturbation`, `samplingLaw_stateRow`, `policyHoeffdingRadius_eq`, `valueEstimator_hoeffding`, `truePolicyValue_norm_bound`, `valueEstimator_hoeffding_uniform`, and `valueEstimator_hoeffding_sample_bound` each report exactly `propext`, `Classical.choice`, `Quot.sound`. The temporary source and temporary compiled dependency were deleted. Compiler slots were coordinated within the limit of two.

## Integrated export check

Independently reviewed `Formalization/Generative/PolicyEvaluationHoeffding.lean`, SHA-256 `95779576e3078fbc7bd44c0e3d774e1abca99dd24fdaa2f622cf5d1b2975da3e`. An exact byte comparison against the staged source proved the **only** change is `import PolicyEvaluationPerturbation` becoming `import Formalization.Generative.PolicyEvaluationPerturbation`. All declaration and proof bytes are unchanged. The earlier source/semantic verdict therefore carries over to this exact integrated file.

The first import-based audit found the new integrated object's `.olean` did not yet exist. With the lead confirming no concurrent project build, I compiled the exact integrated source to its own project artifact:

`bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/Generative/PolicyEvaluationHoeffding.olean Formalization/Generative/PolicyEvaluationHoeffding.lean`

This exited 0 without diagnostics. I then ran `bash scripts/lean-local.sh .local/IntegratedHoeffdingAudit.lean`; that temporary file imported **only the integrated module** and printed axioms for all nine reviewed theorem exports. It exited 0 without diagnostics, and each imported declaration reported exactly `propext`, `Classical.choice`, `Quot.sound`. This confirms the actual integrated export artifact, rather than merely recompiling a copied declaration. The temporary import audit source was deleted. Compiler use was coordinated within the two-compiler limit. This closes this module's integration/export audit, while the source's sharp theorem remains open as stated above.
