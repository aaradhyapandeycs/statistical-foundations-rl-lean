# Independent review: deterministic policy-evaluation perturbation

Reviewed 2026-11-02. Exact staged file `.local/PolicyEvaluationPerturbation.lean`, SHA-256 `eb8844a5cb2f05a5ea44c2b48a9f9182947731e86ec66d57890e2cf800dfff38`. This is ordinary proved infrastructure, not an author-frozen anchor. Reviewer owns only this report.

## Verdict and source scope

**PASS for the stated deterministic pre-resolvent identity, residual identity, sup-norm bound and zero-discount endpoint. The displayed source inverse identity and the statistical theorem are not established by this file.**

I independently read `source/upstream/tex/chapters/generative_model_model_based.tex:179–203`, especially `eq:Vhatpi-Vpi-difference`, and the subsequent concentration discussion. The source uses the same known reward and discount in the true and empirical MDP and derives

`Vhat−V = γ (I−γ P̂π)⁻¹ (P̂π−Pπ)V`.

The staged identity is precisely its Bellman rearrangement before applying an inverse. It does not contain an inverse object, an invertibility proof, a geometric-series operator construction, or the displayed resolvent equation. Thus this is substantive deterministic progress toward that source step, not completion of the literal displayed formula. The builder report makes this distinction correctly.

The source chapter's policy evaluation treatment absorbs the fixed policy into an effective A=1 transition chain. The Lean result permits arbitrary stationary randomized π on the common finite action carrier and uses the corresponding mixed transition. Specializing to the source chain is immediate mathematically; the generalization does not change the tested quantity or hide an extra condition.

## Binders, kernels and known inputs

The following inventories all input families. Each field row applies separately to M and Mhat; neither model is supplied as an assumed approximation of the other.

| Expanded input | Bin | Source meaning |
|---|---|---|
| State | TYPING | Common state carrier |
| Action | TYPING | Common action carrier |
| Fintype State | STANDING | Finite source MDP |
| Fintype Action | STANDING | Finite source MDP |
| M.state_nonempty | STANDING | Nonempty source state set |
| Mhat.state_nonempty | STANDING | Same nonempty state set |
| M.action_nonempty | STANDING | Nonempty source action set |
| Mhat.action_nonempty | STANDING | Same nonempty action set |
| M.transition | STANDING | True stationary probability rows |
| M.transition nonnegative masses | STANDING | Probability normalization convention |
| M.transition row sums =1 | STANDING | Probability normalization convention |
| Mhat.transition | STANDING | Arbitrary second stationary probability rows |
| Mhat.transition nonnegative masses | STANDING | Empirical rows are probability rows |
| Mhat.transition row sums =1 | STANDING | Empirical rows are probability rows |
| M.reward | STANDING | Known reward table |
| M.reward_nonneg | STANDING | Source [0,1] range |
| M.reward_le_one | STANDING | Source [0,1] range |
| Mhat.reward | STANDING | Known reward table in second model |
| Mhat.reward_nonneg | STANDING | Source [0,1] range |
| Mhat.reward_le_one | STANDING | Source [0,1] range |
| M.discount | STANDING | Source discount |
| M.discount_nonneg | STANDING | 0≤γ |
| M.discount_lt_one | STANDING | γ<1 |
| Mhat.discount | STANDING | Second model discount |
| Mhat.discount_nonneg | STANDING | 0≤γhat |
| Mhat.discount_lt_one | STANDING | γhat<1 |
| π | SOURCE | Same evaluated stationary policy in both models |
| π-row mass nonnegative | TYPING | Randomized policy distribution |
| π-row sums =1 | TYPING | Randomized policy distribution |
| hr : Mhat.reward=M.reward | SOURCE | Source empirical model retains r |
| hγ : Mhat.discount=M.discount | SOURCE | Source empirical model retains γ |
| s | TYPING | Pointwise state query |
| ε (only residual corollary) | TYPING | Arbitrary deterministic residual tolerance |
| hε : 0≤ε (only residual corollary) | SOURCE | Nonnegative uniform residual tolerance |
| hres : ∀ s, |residual s|≤ε (only residual corollary) | SOURCE | Explicit antecedent of the conditional deterministic corollary |
| hzero : M.discount=0 (only endpoint theorem) | SOURCE | Endpoint specialization |

Counts across this expanded family inventory: TYPING 6, STANDING 24, SOURCE 6, RULED 0, EXCESS 0. The three corollary-specific premises do not occur in the unconditional perturbation bound. In particular, `hres` is not assumed in a claimed source sample-complexity theorem: it belongs to an explicitly conditional helper. It must be proved from an actual experiment before that helper can be used for a statistical guarantee.

Common reward-table equality is sufficient and matches the actual empirical construction. Equality merely of the π-averaged reward would also suffice for the algebra, but the stronger table equality is already part of the source algorithm's unchanged known reward, rather than a new restriction on its instances. No ordering, closeness, concentration, variance, or sampling property is required of either transition kernel. The arbitrary Mhat carrier broadens the deterministic step; an actual empirical-model substitution remains to be checked by integration.

## Actual trajectory semantics and the identities

I inspected the imported `PrefixValueBridge` theorem and its construction from finite prefixes and dominated-convergence limits. `trajectoryExpectedValue` is the expectation of the summable discounted reward on the actual Ionescu–Tulcea infinite controlled trajectory law. The proof replaces that actual value by the uniquely constructed Bellman state-value fixed point only through `trajectoryExpectedValue_eq_valueFixedPoint`, for each of M and Mhat separately. No fixed-point label is substituted as an unexplained meaning of value.

`policyTransition π` averages action-conditioned transition rows under π. The immediate reward in `valueBellman` is the same π-average of the corresponding reward table. Equal table reward and equal discount therefore cancel those terms even for randomized π.

The defined `policyValueResidual` is exactly `(P̂π−Pπ)V`, with V the **true** trajectory value. The difference order, the model supplying V, and the model acting on the value difference are all correct. Writing d=Vhat−V, the pointwise theorem proves `d=γ(P̂π d + residual)`. Expanding expectations with the proved finite-distribution subtraction identity yields exactly the subtraction of the two Bellman equations. `valueBellman_perturbation_residual` separately proves the operator discrepancy at V equals γ times the same residual.

For this literal residual definition: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.

The norm proof uses `‖P̂π d‖∞≤‖d‖∞`, encoded via the empirical model's value-Bellman contraction, and the triangle inequality. It correctly obtains `(1−γ)‖d‖∞≤γ‖residual‖∞` and divides by the strictly positive `1−γ`. The coefficient is exactly γ/(1−γ); there is no lost factor, substituted true kernel, changed norm, or inverse-norm assumption. The pointwise-residual corollary correctly converts absolute-value coordinate bounds to the finite sup norm. Its ε is a residual tolerance, not automatically the source theorem's final value-accuracy ε.

At γ=0, the bound has right side zero and implies equality of the two actual value functions. The proof never divides by γ. The model constraints and denominator argument remain valid, so the endpoint theorem is a meaningful semantic check rather than a vacuous impossible case.

## Open source obligations

The following remain open at this staged handoff:

- Construct or use a proved inverse of `I−γP̂π` and derive the source's displayed resolvent equality, with the intended finite-vector/matrix or linear-operator semantics.
- Instantiate Mhat with the algorithm's actual empirical transition model and discharge common reward/discount conditions using that construction.
- Prove a suitable residual concentration event under the actual independent sampling law. Randomized π is algebraically allowed here, but fixed-policy concentration cannot be applied to a data-dependent π without further justification.
- Establish the sharper variance/resolvent estimates and the source statistical sample-complexity theorem with its probability, constants and precision range. This coarse deterministic norm bound alone does not give the advertised sharp statistical rate.

No source theorem, inverse equation, probability bound or whole-chapter closure should be marked proved on the strength of these helpers alone.

## Independent verification

Dependency hashes match the builder handoff: `PrefixValueBridge.lean` `bd286567aa059c3e5fb293f1943eb06bd2e3d79c8dc9484d8a73195a2db16e89`; `DiscountedFiniteTrajectory.lean` `c6b25ae5dfc3dc38f1d4ae654524764e10474ba04d94a0925242de5d88ccbdd6`; `Basic.lean` `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088`. Source chapter hash is `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

After coordinating the second compiler slot while the lead project check ran, I copied the exact reviewed source to `.local/PerturbationIndependentAudit.lean`, appended five `#print axioms` commands and ran:

`bash scripts/lean-local.sh .local/PerturbationIndependentAudit.lean`

Exit status 0, without warnings or errors. The five theorem exports `trajectoryValue_perturbation_identity`, `valueBellman_perturbation_residual`, `trajectoryValue_perturbation_bound`, `trajectoryValue_perturbation_bound_of_residual`, and `trajectoryValue_eq_of_zero_discount` each report exactly `propext`, `Classical.choice`, `Quot.sound`. The temporary source was deleted. The staged file contains no `sorry`, `admit` or custom axiom declaration. This checks the exact staged source and transitive axioms; it does not replace production integration checks.
