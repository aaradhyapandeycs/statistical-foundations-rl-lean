# Independent audit: staged printed policy-evaluation theorem

Reviewed 2026-11-02. Exact staged `.local/PolicyEvaluationSourceTheorem.lean` SHA-256 `5203c0716ed90521be7ce2a9448b2a8f1b5c68e958ccb37fb274af52c80fc73a`, independently recomputed. Builder handoff: `docs/builder-policy-evaluation-source-theorem.md`. This reviewer owns only this report.

## Verdict and certification boundary

**DECLARATION FIDELITY: PASS for the source theorem with the explicit universal witness 720 and stronger strict probability. STAGED COMPOSITION/AXIOMS: PASS. INTEGRATED EXPORT: NOT CERTIFIED by this staged audit.**

The exact staged theorem matches `thm:model-based-policy-eval` (`generative_model_model_based.tex:140–155`) on its actual algorithm, fixed stationary randomized policy, true trajectory value, probability law, full parameter range and printed logarithm. It has no excess mathematical premise. Positive N is derived, not assumed. The proof supplies the reviewed high-sample prerequisites and covers the one-state/zero-discount endpoints. This is ordinary staged source/proof evidence, not a frozen author approval or whole-monograph completion claim.

The reviewer authored the high-sample assembly dependency. Its independent review was performed by the distinct critic and recorded in `docs/critic-policy-evaluation-high-sample.md`, tied to staged hash `b8f4dd90e9571d730eb0203752e3299c8d4ee3c0cbabdfdd6961037f096ac601`. This audit checks the differently authored top-level statement/composition and relies on that separate review for independence of the dependency. It does not substitute self-certification for that review. Source/sample arithmetic also has its separate independent review.

The builder reports production local-instance name collisions being repaired. Those integration changes and actual imported top-level export must receive a separate exact-diff/build/axiom check; a staged compilation does not certify an as-yet repaired production version.

## Independent source reconstruction

The source uses finite nonempty stationary MDPs with deterministic known reward in [0,1], discount γ∈[0,1), and a given stationary policy π mapping states to action distributions (`prelim.tex:31–45,66–76`). Actual value is the expectation of the discounted reward sum (`:94–105`).

The algorithm draws N independent next states from Pπ(·|s) at every state and uses their frequency matrix in `(I−γP̂π)⁻¹rπ` (`generative_model_model_based.tex:78–106`). The main theorem states existence of a sufficiently large universal positive c₀ so that, for 0<δ<1 and 0<ε≤1/(1−γ),

`N ≥ c₀ log(S/(δ(1−γ))) / ((1−γ)^3 ε²)`

implies probability at least 1−δ of simultaneous error ≤ε at every state. N is per state, with total NS observations; neither A nor N appears inside this theorem's logarithm.

The reviewed theorem uses exactly coefficient 720 at that location. Its conclusion supplies a proof hN:0<N and a **single** actual-law event whose finite sup norm error is ≤ε, with success probability >1−δ. The strict probability strengthens the source's weak inequality and does not alter the non-strict error threshold. The full closed upper accuracy endpoint is retained.

## Expanded binder audit

Repeated fields are listed once; the two explicit typeclass instances are the only supplied instances in the declaration's section. The discrete measurable structures are fixed local constructions, not user-supplied restrictions.

| Expanded input | Bin | Source basis |
|---|---|---|
| State : Type | TYPING | Finite state carrier |
| Action : Type | TYPING | Finite action carrier |
| Fintype State | STANDING | Source finite MDP |
| Fintype Action | STANDING | Source finite MDP |
| M.state_nonempty | STANDING | Nonempty source state set |
| M.action_nonempty | STANDING | Nonempty source action set |
| M.transition | STANDING | Stationary transition probability rows |
| Every transition mass nonnegative | STANDING | Probability row definition |
| Every transition row sums to one | STANDING | Probability row definition |
| M.reward | STANDING | Known deterministic reward |
| M.reward_nonneg | STANDING | Source [0,1] range |
| M.reward_le_one | STANDING | Source [0,1] range |
| M.discount | STANDING | Source known discount |
| M.discount_nonneg | STANDING | γ≥0 |
| M.discount_lt_one | STANDING | γ<1 |
| π | SOURCE | Given stationary randomized policy |
| π action-probability table | TYPING | Distribution-valued policy carrier |
| π row masses nonnegative | TYPING | Probability policy definition |
| π row sums to one | TYPING | Probability policy definition |
| N : ℕ | SOURCE | Per-state sample count |
| δ : ℝ | SOURCE | Confidence parameter |
| ε : ℝ | SOURCE | Accuracy parameter |
| hδ : 0<δ | SOURCE | Source confidence lower endpoint |
| hδ1 : δ<1 | SOURCE | Source confidence upper endpoint |
| hε : 0<ε | SOURCE | Source accuracy lower endpoint |
| hεmax : ε≤1/(1−γ) | SOURCE | Full source upper endpoint |
| hNbound : displayed bound with 720 | SOURCE | Concrete witness for universal source constant |

Inventory counts: TYPING 5, STANDING 13, SOURCE 9, RULED 0, EXCESS 0. No concentration, recurrence, growth, terminal estimate, β/log comparison, inverse, residual smallness, S≥2 or γ>0 premise occurs in the main declaration. Those are constructed/discharged inside its proof.

hN is **in the conclusion**, not an additional supplied premise. `source_sample_count_pos` proves the printed budget positive: S≥1 and δ(1−γ)<1 make the log strictly positive, and the denominator is positive for ε>0. Thus any natural N meeting the bound is positive. The existential proof witness is solely required to type the empirical frequency construction. Its position outside the probability event cannot select different mathematics per data point, and Lean proof irrelevance makes the estimator independent of which positivity proof is used.

## Universal constant and independent exact-interface probe

Although the staged export uses the concrete numeral rather than an existential c₀, it quantifies uniformly over all M,π,N,δ,ε at that same numeral. This supplies a universal witness; it is not a model-dependent existential constant hidden after M.

To verify the logical direction and exact source quantifiers, the independent transient probe additionally reconstructed a theorem with shape

`∃ c>0, ∀ S A N, ∀ M on Fin S/Fin A, ∀ fixed π, ∀ δ ε in the source ranges, printed_bound(c) → ∃ hN, P(error≤ε)≥1−δ`.

Its proof chooses **720 before all those mathematical inputs**, then applies the actual staged export and weakens strict probability to the printed weak inequality. This exact source-shaped interface compiled successfully. It uses the source's labeled finite carriers and no extra positivity premise on N. Thus the constant's universality is checked by a concrete term, not merely asserted in the handoff.

## Actual definitions and experiment

`samplingLaw M π N` is literally the product over (s,i) of the true policy-row measures. The integrated dependency proves normalization, true-coordinate marginals and full independence. The array has one state observation at each (s,i), matching the direct policy-row algorithm rather than the state-action experiment for policy learning. Randomized π is handled by the genuine policy-induced row Pπ, and is fixed before data. No estimator-independence assumption is present.

`valueEstimator M π N hN data` uses the exact empirical frequencies of those same observations, unchanged known policy reward rπ and unchanged discount. Its integrated inverse theorem identifies it with `(I−γP̂π(data))⁻¹rπ`, using proved nonsingularity, current-state rows and next-state columns. The total singular-inverse fallback is unreachable. The empirical model's action-independent embedding of rπ is the correct collapsed policy-evaluation construction, not a replacement of unknown rewards or an assumed equality with arbitrary action rewards.

The comparison target is the actual `trajectoryExpectedValue π` under M, not a fixed-point name without trajectory semantics. Its bridge and full [0,1/(1−γ)] bound are proved. The finite function-space norm is the actual sup norm, so the event equals source simultaneous pointwise absolute error because ε≥0. All events are measurable on the finite discrete sample domain. `Measure.real` is ordinary probability since the product law is a probability measure. No extra joint-measurability assumption in varying real model inputs is required.

Definition-body/carrier checks for the actual sample law, empirical estimator/inverse and true trajectory value pass on their already reviewed valid domains. There is no off-source zero/default construction or unproved arbitrary witness substituted for these objects.

## Exact proof consumption and endpoints

For S≤1, M's nonemptiness makes the source state space a singleton. The proof installs the corresponding subsingleton instance, then invokes the actual estimator exactness theorem at every sample. The target event is all data and has probability one. This handles the small printed-log regime without restricting δ, γ or ε or assuming a false universal additive-log absorption for S=1.

For S≥2, the proof derives 0<h=1−γ≤1 and real N>0, then applies `source_sample_budget_from_printed_log` at the actual cardinality and N. The returned β is rewritten by unfolding the actual depth/log definitions, including the m+1 cast; it yields exactly both the high-sample threshold N≥64β/h and radius≤ε. No β is silently renamed, and the factor 64 remains supplied rather than dropped at the final inference.

The actual `valueEstimator_high_sample` is applied with the same M,π,N,hN,δ and that threshold. A single event inclusion using radius≤ε produces the target event. The high-sample theorem has its own separately reviewed common all-level Bernstein-event proof for recursion and terminal control. The top proof introduces no new event intersection or independence claim.

For γ=0, the full-domain high-sample export handles exactness internally; the top theorem does not instantiate a 1/γ growth expression there. The S=1 branch also covers γ=0 independently. N=1 is allowed whenever the printed condition permits it; N=0 cannot satisfy its positive right side. ε=1/h is included by non-strict arithmetic. There is no unprinted S≥2 or positive-discount limitation on the exported theorem.

## Independent staged compilation and axioms

The lead explicitly allocated a separate compiler slot. I freshly rebuilt the exact staged terminal, high-sample and sample-assembly dependencies, sequentially, into an isolated project-owned temporary artifact directory; no preexisting staged object was trusted. Their source hashes matched the handoff:

- terminal: `29c50df335bf18e75083d8628817f16d5f076f6eb32e63465ed227752e306145`;
- high-sample: `b8f4dd90e9571d730eb0203752e3299c8d4ee3c0cbabdfdd6961037f096ac601`;
- sample assembly: `f408a6050eb96cfc7b4c5ab95ff1d22f0c556ad6b0a3a7783164642d03accc5b`.

Using that directory plus the ordinary built project/dependency paths in `LEAN_PATH`, I compiled `.local/SourceTheoremIndependentAudit.lean`, an exact unchanged copy of the reviewed source with two `#print axioms` commands and the independent existential-interface example described above. All compilations exited 0. Only the known nonsemantic `unnecessarySeqFocus` warning appeared in the sample-assembly dependency; the top source, two axiom commands and exact-interface example produced no diagnostics.

Both `source_sample_count_pos` and `valueEstimator_source_sample_bound` reported exactly `propext`, `Classical.choice`, `Quot.sound`. The transitive axiom closure therefore contains no `sorryAx` or custom project axiom. The exact source contains no `sorry` or `admit`. Temporary sources/artifacts were deleted, and the compiler slot was immediately released.

Pinned source hashes: model-based chapter `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`; prelim `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`. This evidence certifies the staged exact version and its source-shaped composition. Final production repairs/import closure, actual imported-export axioms and shared project build remain required before a completed integrated source result is reported.

## Integrated source and exported theorem recheck (2026-11-03)

Independently recomputed `Formalization/Generative/PolicyEvaluationSourceTheorem.lean` SHA-256 as `5aba4a6f67d4e1e49c265ab3aebd36fc9d26681f8d3b632e5e00285aa297fa18`. Exact byte comparison against the reviewed staged source passed: only `import PolicyEvaluationHighSample` and `import PolicyEvaluationSampleAssembly` became their corresponding `Formalization.Generative.*` imports. No definition, theorem statement, proof or local instance in this module changed. The staged semantic verdict therefore carries over to this precise integrated source.

Using the explicitly allocated compiler slot and the actual integrated dependency artifacts, I compiled the actual module to its own project object:

`bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/Generative/PolicyEvaluationSourceTheorem.olean Formalization/Generative/PolicyEvaluationSourceTheorem.lean`

Exit status 0 without diagnostics. I then ran `bash scripts/lean-local.sh .local/IntegratedSourceTheoremAudit.lean`; the temporary audit imported **only** the integrated source-theorem module and inspected both actual exported declarations. It exited 0 without diagnostics, and both `source_sample_count_pos` and `valueEstimator_source_sample_bound` reported exactly `propext`, `Classical.choice`, `Quot.sound`. Thus this audit verifies the actual integrated object/transitive axiom closure, rather than recompiling copied declarations against staged imports. The temporary probe was deleted. The main report's integrated-export reservation is superseded for this exact version, subject to the shared full-project check and the independently reviewed dependency repairs recorded by the lead.

## Retained exact universal-constant wrapper

At the lead's request, the previously transient existential interface has been written to a separate candidate `.local/PolicyEvaluationUniversalConstant.lean`. It imports **only the integrated source theorem**. Its named export `StatisticalRL.ModelBasedPolicyEvaluation.policyEvaluation_universal_constant` chooses c=720 before all source cardinalities S,A, sample counts N, MDPs, policies, confidence and accuracy inputs. It uses the exact printed sample expression, derives the positive-N witness from the integrated theorem, and has the source's non-strict ≥1−δ probability conclusion. The carriers are the source's finite labeled sets `Fin S` and `Fin A`, with fixed discrete measurable structure.

An exact copy of that wrapper with one appended `#print axioms` command was compiled via `bash scripts/lean-local.sh .local/UniversalConstantAxiomAudit.lean`. Exit status 0 without diagnostics; the wrapper reported exactly `propext`, `Classical.choice`, `Quot.sound`. This establishes the existential universal-constant claim against the actual integrated source export. The axiom probe was deleted, but the candidate wrapper source is intentionally retained for independent review and possible production inclusion. Its production landing is not certified merely by this candidate compilation. Compiler slot was released immediately after these checks.

Retained wrapper SHA-256: `6ed38db49bd227f1a083632ad3151955c9c96a4bbd6acccd96a5721e694ac625`. No source node or inventory status was changed by this review. Source-node completion remains gated on the shared full-project check and a distinct independent review/landing audit of the wrapper.
