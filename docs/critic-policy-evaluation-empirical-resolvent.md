# Independent review: empirical versus true variance resolvent

Reviewed 2026-11-02. Exact staged target `.local/PolicyEvaluationEmpiricalResolvent.lean` SHA-256 `2ad672efe62e102cdf654f95446fd884a4c9c0ab64b30b2cc38708ff205489a4`, independently recomputed. Reviewer owns only this report. This is an ordinary staged intermediate, not a frozen theorem or completed sharp source result.

## Verdict and exact scope

**PASS for the exact finite-matrix resolvent identity, deterministic norm estimates and actual-law first-auxiliary-vector Bernstein comparison. The higher auxiliary recursion and sharp horizon-three theorem remain open.**

I independently compared the implementation with source `generative_model_model_based.tex:379–405` (`eq:key-quantity-sharp-analysis-MB-PE`), auxiliary definitions at `:414–433`, and Bernstein/recursion steps at `:461–488`. The source's first auxiliary value is u=R sqrt(σ), with R=(I−γPπ)⁻¹ and σ=Var_{Pπ}(Vπ). The staged true vector is exactly that object. Its empirical counterpart is uhat=Rhat sqrt(σ), where Rhat=(I−γP̂π)⁻¹ uses the actual sampled frequency matrix and the **same fixed true variance vector**. It is not Rhat applied to empirical variance or the empirical value's variance.

The final theorem states that, under the actual direct policy-row product experiment and for N>0, 0<δ<1 and γ>0, with probability >1−δ,

`γ ‖uhat‖∞ ≤ ‖Vπ‖∞/sqrt(1−γ) + γ²/(1−γ) ‖r‖∞`,

where

`r_s = sqrt(2 log(4S/δ)/N) sqrt(Var_{Pπ(s)}(u)) + 2‖u‖∞ log(4S/δ)/(3N)`.

This is a genuine probability theorem without an assumed residual event. The explicit remaining variance is the next-level population variance of u, not a term already controlled by the sharp rate. No theorem-level sample complexity follows without bounding/unrolling that term.

## Literal matrices, sign and inverse semantics

The actual integrated matrices have current-state rows and next-state columns. Pπ averages M.transition under the fixed π; P̂π is the observed policy-row frequency matrix from the same N and data as the empirical evaluation algorithm. Matrix-vector multiplication is proved equal to the corresponding row expectation. Both inverses are nonsingular on every allowed input, by separately proved finite-matrix injectivity using stochastic-row contraction. No `Invertible` instance or residual estimate is supplied as an external premise.

Writing A=I−γP̂ and B=I−γP, the implementation proves B−A=γ(P̂−P), then uses the genuine nonsingular inverse-difference identity to obtain

`Rhat f − R f = γ Rhat (P̂−P) R f`.

The multiplication order and empirical-minus-true sign are correct. The theorem allows arbitrary finite f and every observation array; it does not require f≥0 for this algebra. Mathlib's singular-inverse fallback is excluded by the proved unit properties of A and B.

The generic empirical norm estimate derives u=f+γP̂u from A u=f, uses genuine normalized nonnegative empirical rows to show `‖u‖∞≤‖f‖∞+γ‖u‖∞`, then divides by positive 1−γ. This proves `‖Rhat f‖∞≤‖f‖∞/(1−γ)` with the correct constant for arbitrary signed f. Combining it with the identity yields

`‖Rhat f−Rf‖∞ ≤ γ/(1−γ) ‖(P̂−P)Rf‖∞`.

There is no stronger operator closeness or inverse positivity assumption hidden in this deterministic step.

The definitions of the two variance-resolvent vectors are literal matrix inverse applications on the declared valid MDP/positive-N domain. BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK (proved nonsingularity); CHARACTERIZATION OK (the imported budget/inverse and empirical inverse semantics justify actual inverses); CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.

## Fixed first auxiliary vector and actual probability law

Vπ is the actual true infinite-trajectory value through the reviewed integrated trajectory/Bellman bridge. σ is its actual true-row population variance. u uses only M and π, neither of which depends on the sample array. Thus u is a fixed vector for the subsequent Bernstein concentration even though it depends on the unknown true model. Its first-auxiliary interpretation agrees with the source; no fitted empirical vector is treated as independent.

For γ>0, pointwise nonnegativity of u is proved from γu equal to the nonnegative square-root variance budget. This supplies the nonnegative-vector hypothesis of the imported fixed-family Bernstein theorem. It is a produced fact, not a binder disguising an assumed inverse positivity theorem.

The actual law is `samplingLaw M π N`: N independent observations from each true policy row. The proof pushes this law to the N-vector for a fixed state and uses the previously proved exact row iid-law equality. It then applies the source-radius family theorem to the deterministic singleton {u}. No measurability/row-law/independence bridge is supplied as an unexplained premise.

Each row uses confidence η=δ/S, where source nonemptiness gives S≥1 and hence 0<η<1. The logarithm becomes exactly log(4S/δ), and the radius keeps the source coefficients sqrt(2) and 2/3 with denominator N, not N−1. This is the **population-variance Bernstein** radius; it must not be confused with the distinct empirical Bernstein lemma.

The imported Bernstein-family result actually has enough slack for strict success (its factor 4 logarithm yields a ≤η/2 singleton failure bound). The implementation only needs and correctly derives each row's failure <η, then a finite union gives total <δ. It requires no independence between row failure events or between separately derived theorem events. The complement gives simultaneous residual inequalities for all states. All data sets are measurable because the sample domain is finite.

## Probability composition and constants

The residual vector is exactly `(P̂−P)u`. On its derived simultaneous event the finite sup norm is at most ‖r‖∞; the proof bounds coordinates by r_s and then by |r_s|≤‖r‖∞. The deterministic comparison supplies

`‖uhat−u‖∞ ≤ γ/(1−γ) ‖r‖∞`.

The same event, without an additional union or independence claim, then gives

`γ‖uhat‖∞ ≤ γ‖u‖∞ + γ²/(1−γ)‖r‖∞`.

Finally the reviewed true-resolvent bound `γ‖u‖∞≤‖Vπ‖∞/sqrt(1−γ)` yields the final statement. The γ² multiplier on the remaining radius is correct: one γ comes from the difference identity and the second from scaling the final norm. No confidence budget is spent twice, no same-sample event is assumed independent, and no remaining term is silently absorbed.

## Endpoints, binders and remaining source obligations

Deterministic inverse identities and generic norm inequalities cover 0≤γ<1. At γ=0 both matrices are I, so the explicit zero-discount theorem proves equality of resolvent actions on every f and outcome. The three probability exports explicitly assume γ>0 to obtain u≥0 through the scaled budget. Their scope is honestly narrower; they do not assert an unscaled 1/γ theorem at zero. A probability-one zero-discount corollary could be added from the deterministic identity but is not exported here.

Zero population variance or zero u is allowed by the imported Bernstein theorem; neither the new proof nor radius divides by those quantities. N=1 is allowed; N=0 is excluded by empirical frequencies. π must remain fixed before data. The arbitrary-f deterministic identity may be specialized pointwise to data-dependent f, but its Bernstein application here is only to fixed u and cannot be generalized to such f without further arguments.

The expanded final probability inputs are finite nonempty state/action carriers, a true discounted MDP with normalized nonnegative transition rows, known rewards in [0,1], 0≤γ<1, a fixed stationary normalized randomized policy, N>0, 0<δ<1, and the displayed positive-discount specialization. These are source standing/typing inputs and explicit scoped domain restrictions. There is no supplied concentration event, variance control, empirical approximation or final error guarantee. EXCESS=0 for this scoped first-level comparison. It would fail fidelity if promoted as the full sharp policy-evaluation theorem.

The source continues through all required auxiliary levels, a simultaneous probability event across those levels, geometric unrolling, terminal control and exact sample/logarithm arithmetic. The current r still contains Var_P(u), so those steps remain substantive obligations. This is progress beyond the earlier heuristic approximation, not a proof that Rhat can universally be replaced by R without residual cost. Production integration and actual export audit also remain separate.

## Independent verification

The builder handoff was read and matches the implementation's scope, remaining higher-order term and constants. The Bernstein dependency hash was independently recomputed as `3f3d25c0953b629e7a8fba0921edf9a689a9818606e99e8eca7e64306299bcfe`, and its stated radius/success hypotheses were inspected locally. The remaining imported inverse, true-resolvent and sampling constructions are the previously independently reviewed integrated versions named in the builder report.

After the lead allocated the released compiler slot, I copied the exact stable source unchanged to `.local/EmpiricalResolventIndependentAudit.lean`, appended `#print axioms` for all nine theorem exports, and ran:

`bash scripts/lean-local.sh .local/EmpiricalResolventIndependentAudit.lean`

Exit status 0 without warnings or errors. All nine exports—`empirical_true_resolvent_identity`, `empirical_resolvent_norm_le`, `empirical_true_resolvent_norm_le`, `trueVarianceResolvent_nonneg`, `empirical_true_resolvent_eq_of_zero`, `trueVarianceResolventBernsteinRadius_eq`, `trueVarianceResolvent_residual_bernstein`, `empirical_true_varianceResolvent_bernstein`, and `empirical_varianceResolvent_scaled_bernstein`—reported exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs in the source. The temporary audit source was deleted, and the compiler slot was released immediately. This checks the exact staged implementation and transitive axioms, not a future integration diff.

## Integrated source and actual export recheck

Independently verified that `Formalization/Generative/PolicyEvaluationEmpiricalResolvent.lean` is byte-identical to the reviewed staged source, retaining SHA-256 `2ad672efe62e102cdf654f95446fd884a4c9c0ab64b30b2cc38708ff205489a4`. No import, statement, definition or proof change occurred. The semantic verdict above applies to this exact integrated version.

After waiting for the lead's explicit compiler-slot release, I compiled the actual integrated module to its own project object using:

`bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/Generative/PolicyEvaluationEmpiricalResolvent.olean Formalization/Generative/PolicyEvaluationEmpiricalResolvent.lean`

Exit status 0 without warnings or errors. I then ran `bash scripts/lean-local.sh .local/IntegratedEmpiricalResolventAudit.lean`; this temporary file imported **only** the integrated empirical-resolvent module and printed axioms for all nine actual theorem exports listed above. It exited 0 without diagnostics, and each imported theorem reported exactly `propext`, `Classical.choice`, `Quot.sound`. This checks the actual integrated object and built integrated dependencies rather than redeclaring copied proofs. The temporary probe was deleted and the compiler slot immediately released. This closes the integrated-export recheck for this version; all higher-order/statistical limitations remain.
