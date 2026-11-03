# Actual-law auxiliary Bernstein recursion

`.local/PolicyEvaluationBernsteinRecursion.lean` connects the reviewed simultaneous auxiliary Bernstein event to the reviewed conditional residual recursion by an explicit event inclusion. It removes the pointwise concentration antecedent from the probability result; that antecedent is proved on the actual simultaneous good event. It does not assume or prove the sharp auxiliary growth bound or the final policy-evaluation theorem. Independent source/semantic review and integration remain pending.

## Source and exact result

The source is `generative_model_model_based.tex:461–495`, combining `eq:Bernstein-Vl` with steps (i)–(iii) of `eq:upper-bound-Vl-Vhatl`. The new theorem uses the actual direct policy-row sampling law and exact true/empirical auxiliary definitions from the reviewed staged modules.

Let h=1−γ, S=card State, `L=log(4S(m+1)/δ)`, and `e_l=‖Vhat_l−V_l‖∞`. For every valid finite MDP M, fixed stationary randomized π, N>0, m∈ℕ, and 0<δ<1, with probability **strictly greater than 1−δ** under the true policy-row product experiment, simultaneously for every `l : Fin (m+1)`,

`e_l ≤ γ sqrt(2L/N) (e_(l+1)+‖V_(l+1)‖∞) + γ (2L/(3N)) ‖V_l‖∞/h`.

The right side retains the exact Bernstein linear coefficient 1/3. Setting β=2L gives a=sqrt(β/N) and c=β/(3N), which is tighter than the source's absorbed-constant c=β/N. The logarithm counts m+1 actual levels (0 through m inclusive), in accordance with the reviewed simultaneous theorem. No m=0 or terminal-level issue is hidden: auxiliary level m+1 exists definitionally and is not itself asserted to satisfy concentration on this event.

The sole probability theorem assumes no sample-accuracy event, variance certificate, desired error bound, auxiliary growth estimate or target-shaped residual hypothesis. Its parameters are just the source finite MDP, fixed policy, positive sample count, finite level cutoff and valid confidence level.

## Term-level composition

The imported simultaneous event proves, for every state and level through m,

`|P̂V_l−PV_l| ≤ sqrt(2L/N) sqrt(Var_P(V_l)) + 2‖V_l‖∞L/(3N)`.

The file proves L>0 from source carrier nonemptiness, m+1≥1 and 0<δ<1. Thus the exact coefficients a and c are nonnegative. It rewrites the row-expectation difference as literal matrix residual `(P̂−P)V_l`, commutes the scalar product in the linear term, and supplies that term to `auxiliary_residual_recursion_conditional` at the same M,π,N,data and level. The output event contains all resulting recursions simultaneously. Monotonicity of probability then preserves the strict 1−δ success claim.

The fixed true auxiliary values depend on M,π and level but not the random data; their source nonnegativity, actual-law iid marginals and simultaneous Bernstein probability have already been proved by the imported event theorem. The composition introduces no new independence claim or confidence union and does not substitute an empirical auxiliary vector into a fixed-vector concentration theorem. Every empirical auxiliary vector uses the same observed empirical matrix and the source's same true auxiliary reward.

The scalar γ is allowed to be zero. No division by γ occurs; then all empirical and true auxiliary values coincide because both inverse matrices are I and the reward is the same, consistently with the zero right side. N=1 and m=0 are allowed. N=0 is excluded by empirical frequencies, and the source confidence domain is explicit.

## Remaining sharp growth and theorem work

This result supplies actual probability to steps (i)–(iii). It does not replace `‖V_(l+1)‖∞` by a sharp multiple of `‖V_l‖∞`, so source step (iv) is **not** yet a consequence of this module alone. The general nonnegative-forcing resolvent estimate provides a separately staged route for that growth fact, but it must be independently reviewed, integrated or imported with a precise bridge to these exact auxiliary objects before use.

Geometric unrolling, terminal remainder control, numerical sample/level arithmetic and the final sharp horizon-three value-error theorem remain separate. The previously reviewed low-sample deterministic repair of the source factor-64 transition is not assumed or invoked here. This is a bounded probability-recursion handoff, not a whole-theorem completion claim.

## Validation and identity

The new module was checked after the lead explicitly allocated a compiler slot. Its four staged dependencies (`PolicyEvaluationAuxiliary`, `EmpiricalResolventOrder`, `PolicyEvaluationAuxiliaryBernstein`, `PolicyEvaluationResidualRecursion`) were freshly compiled from their actual sources into a temporary project-owned staging artifact directory. The exact new source then compiled against those artifacts and existing integrated dependencies without warnings/errors. An exact unchanged copy of the final new source plus three `#print axioms` commands compiled with no diagnostics. `auxiliaryRecursionLog`, `auxiliaryRecursionLog_pos` and `auxiliaryValues_bernstein_recursion` all report only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs. The temporary probe and freshly compiled staging artifact directory were deleted; no dependency artifact was changed. The compiler slot was released immediately.

SHA-256:

- `.local/PolicyEvaluationBernsteinRecursion.lean`: `6b99d8f2a09a6d9efe09e687a213e879096726b692bb44eb6c65f432121ceb7f`.
- `.local/PolicyEvaluationAuxiliaryBernstein.lean`: `2a4a6df841a284b0db5a1b157d2240ee43e60ed060bd3b81bb47b03c95da3671`.
- `.local/PolicyEvaluationResidualRecursion.lean`: `860c81d21b55b58df3b9eefe66c341ee3a60f7edd9cfd67c66e1b089be0c8c4d`.
- `.local/PolicyEvaluationAuxiliary.lean`: `68a6bc19097ecc84a93583a39230b92b58b4a3ab8a2c0971ab50d084923bbb95`.
- `.local/EmpiricalResolventOrder.lean`: `bed62174679d0a11f0778702e29f77a004d144a26d5e8f5b4661644ffafd0bf5`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

Current imports are the staged modules `PolicyEvaluationAuxiliaryBernstein` and `PolicyEvaluationResidualRecursion`. Independent review should verify the exact dependency sources and event inclusion. Production integration needs those imports changed to the actual integrated module paths, an import-only diff check and actual export audit. This is builder evidence, not independent certification.
