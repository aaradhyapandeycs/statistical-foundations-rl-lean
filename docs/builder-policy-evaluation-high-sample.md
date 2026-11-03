# Actual-law high-sample policy-evaluation assembly

`.local/PolicyEvaluationHighSample.lean` assembles the reviewed simultaneous Bernstein event, auxiliary growth, conditional residual recursion, newly proved terminal bound and final arithmetic into an **actual algorithm probability theorem**. It supplies every intermediate estimate; none is retained as a theorem premise. The printed source logarithm/sample-complexity conversion remains assigned to a separate worker. Independent review and production integration remain pending.

## Explicit depth, beta and result

Let h=1−γ. The file defines

`policyEvaluationDepth M = ceil_nat(log(exp(1)/h))`,

`policyEvaluationBeta M δ = 2 log(4 S (policyEvaluationDepth M+1)/δ)`.

Here S is the actual finite state cardinality. The depth is precisely the source-selected ceiling on its positive log argument; using the inclusive m+1 factor matches the actual simultaneous concentration event through level m.

`valueEstimator_high_sample` proves for every valid finite source MDP M, fixed stationary randomized π, N>0, 0<δ<1 and

`N ≥ 64 policyEvaluationBeta M δ / h`,

that under the actual direct policy-row product sampling law,

`P( ‖valueEstimator−Vπ‖∞ ≤ 3 sqrt(8 policyEvaluationBeta M δ/(h³ N)) ) > 1−δ`.

The value estimator is the actual integrated plug-in algorithm and Vπ is the actual infinite-trajectory true policy value. There is no confidence event, error recursion, growth bound, terminal estimate, inverse assumption or auxiliary construction supplied as an input. The sole sample condition is displayed explicitly.

The positive-discount proof is also named separately as `valueEstimator_high_sample_of_pos`. The full export handles γ=0 by the proved pointwise equality of true/empirical auxiliary values at level zero, so the success event is the entire sample space. No division by γ occurs in that endpoint branch.

## One shared event, not an intersection

The proof starts with **one** actual-law simultaneous Bernstein event from `auxiliaryValues_bernstein_explicit`, covering every state and auxiliary level 0..m. It does not intersect separate probability-recursion and terminal events, which would lose the claimed confidence.

On that same data event, the exact linear residual term β/(3N) is weakened to β/N using nonnegativity. For every level through m this proves the source-format residual

`|(P̂−P)V_l| ≤ sqrt(β/N) sqrt(Var_P(V_l)) + (β/N) ‖V_l‖∞`.

The proof then supplies the conditional source recursion at levels l<m. The reviewed scaled successor-growth theorem controls γ‖V_(l+1)‖∞; weakening its constant 1 to source sqrt(2) and γ≤1 in the linear term yields exactly the recursion required by the reviewed final arithmetic:

`e_l ≤ γ sqrt(β/N) e_(l+1) + [sqrt(2)sqrt(β/N)/sqrt(h) + (β/N)/h] ‖V_l‖∞`.

At l=m, the separately proved `auxiliary_terminal_error_conditional` supplies

`e_m ≤ γ/h [sqrt(β/N)+β/N] ‖V_m‖∞`.

The reviewed source geometric growth supplies all value inequalities, actual return bounds supply `0≤‖V₀‖∞≤1/h`, and the explicit ceiling supplies the depth condition. The sample inequality supplies the arithmetic threshold. `auxiliary_source_high_sample_radius` is then applied with every premise concretely discharged. Level-zero empirical auxiliary value equals the algorithm's estimator and its true counterpart equals actual Vπ. A final event inclusion transfers the one original strict probability bound.

All true auxiliary test vectors are fixed by M,π,level before sampling. No empirical/data-dependent vector is treated as independent. All empirical levels use the same observed matrix and true auxiliary rewards. No new confidence budget or cross-event independence assertion occurs.

## Source relation and remaining work

The result implements the source sharp analysis through its high-sample final radius (`generative_model_model_based.tex:410–634`), with the exact explicit β corresponding to the proved Bernstein constants and inclusive-level count. It is not yet the printed `thm:model-based-policy-eval` sample-complexity declaration: the displayed theorem's `log(S/(δh))`, universal sample constant and target ε range still need the separate logarithm/sample arithmetic bridge and a final source-facing statement. The separate worker is also handling the one-state case in that logarithm conversion.

The high-sample threshold is deliberately 64β/h, so this proof does not silently drop the source's factor 64. The previously reviewed deterministic small-sample repair is unnecessary here and is not assumed. No claim of whole-chapter completion or frozen author approval is made.

## Verification

The proof waited for an explicit lead compiler slot. The exact terminal-error dependency was freshly compiled into a temporary project-owned artifact directory, then the high-sample source compiled with that directory and the existing integrated dependencies. It compiled without warnings/errors after a routine addition-order adjustment. An exact unchanged-source copy `.local/HighSampleAxiomAudit.lean` with four appended `#print axioms` commands compiled without diagnostics. `policyEvaluationDepth`, `policyEvaluationBeta`, `valueEstimator_high_sample_of_pos` and `valueEstimator_high_sample` report only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs. The temporary probe and fresh terminal staging artifact directory were deleted, and the compiler slot was released immediately.

SHA-256:

- `.local/PolicyEvaluationHighSample.lean`: `b8f4dd90e9571d730eb0203752e3299c8d4ee3c0cbabdfdd6961037f096ac601`.
- `.local/PolicyEvaluationTerminalError.lean`: `29c50df335bf18e75083d8628817f16d5f076f6eb32e63465ed227752e306145`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

Current terminal import is the staging name `PolicyEvaluationTerminalError`; integration must qualify it after independently reviewed production integration of that dependency and recheck the import-only diff and actual exports. All other imports already target integrated project modules. This is builder evidence, not independent certification.
