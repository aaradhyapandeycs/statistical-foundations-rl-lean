# Deterministic policy-evaluation perturbation: staged handoff

`.local/PolicyEvaluationPerturbation.lean` proves the exact Bellman difference identity for **actual infinite-trajectory policy state values**, and a deterministic sup-norm error bound in terms of the empirical-minus-true policy-transition residual on the true value. It assumes two valid discounted MDPs share the reward table and discount and evaluates the same stationary randomized policy in both. Their transition kernels are otherwise arbitrary; no concentration, sampling law, desired error, or approximation guarantee is assumed. Independent source/semantic review and an integration build remain pending.

## Source and scope

The source describes the true and empirical policy values with the same known `r_π`, then displays

```text
Vhat^π − V^π = γ (I−γ P̂_π)⁻¹ (P̂_π−P_π) V^π
```

at `source/upstream/tex/chapters/generative_model_model_based.tex:179–203`, label `eq:Vhatpi-Vpi-difference`. The staged result proves its equivalent **pre-resolvent Bellman equation** and a direct deterministic consequence; it does not define a matrix inverse or yet prove the displayed resolvent equality itself. The estimated MDP is represented by an arbitrary valid `Mhat` with the same reward and discount. Applying it to the algorithm's actual empirical transition MDP, proving the concentration event for its residual, deriving the sharper variance/resolvent estimate, and the chapter's statistical sample-complexity theorem are separate work.

Both values are `trajectoryExpectedValue` from the real infinite-path law. Their use of Bellman equations is justified by the integrated `trajectoryExpectedValue_eq_valueFixedPoint` bridge, not assumed equality with a fixed point. `policyTransition π s` is the policy mixture of actual action-conditioned transition distributions, so arbitrary stationary randomized π is covered. `hr : Mhat.reward = M.reward` and `hγ : Mhat.discount = M.discount` are exactly the common-known-input conditions of this deterministic step. State and action carriers are finite, and both MDPs carry the source's nonempty, normalized-transition and bounded-reward fields. The results are valid for the full project discount range `[0,1)`, including γ=0.

## Exports

All are under `StatisticalRL.DiscountedMDP`:

- `policyValueResidual M Mhat π s` is exactly `(P̂_π−P_π)V^π` at s, using true trajectory value.
- `trajectoryValue_perturbation_identity` proves pointwise
  `Vhat^π−V^π = γ [P̂_π (Vhat^π−V^π) + (P̂_π−P_π)V^π]`.
  This is the rearranged Bellman form of the source resolvent identity; signs and the transition applied to the value difference are correct.
- `valueBellman_perturbation_residual` proves that the empirical-minus-true Bellman operator at the true value equals γ times the same residual.
- `trajectoryValue_perturbation_bound` proves the source-faithful deterministic estimate
  `‖Vhat^π−V^π‖∞ ≤ γ ‖(P̂_π−P_π)V^π‖∞/(1−γ)`.
  It uses the existing empirical Bellman contraction and triangle inequality; no matrix inverse bound or probabilistic premise is supplied as a hypothesis.
- `trajectoryValue_perturbation_bound_of_residual` derives `‖Vhat^π−V^π‖∞≤γε/(1−γ)` from an arbitrary uniform pointwise residual tolerance ε≥0. This ε is the *residual tolerance*, not automatically the source theorem's target value-error precision.
- `trajectoryValue_eq_of_zero_discount` checks the endpoint: with common rewards and γ=0 the actual trajectory values agree for arbitrary transition kernels.

## Verification and identity

The exact staged source was copied unchanged to a temporary probe and compiled with five appended `#print axioms` via `bash scripts/lean-local.sh`, against the integrated trajectory bridge. The source and all five checks compiled without diagnostics. Every export above other than the definitional residual was audited; each reports only `propext`, `Classical.choice`, and `Quot.sound`. This is a focused staged check, not an integrated project build.

SHA-256:

- `.local/PolicyEvaluationPerturbation.lean`: `eb8844a5cb2f05a5ea44c2b48a9f9182947731e86ec66d57890e2cf800dfff38`.
- `Formalization/MDP/PrefixValueBridge.lean`: `bd286567aa059c3e5fb293f1943eb06bd2e3d79c8dc9484d8a73195a2db16e89`.
- `Formalization/MDP/DiscountedFiniteTrajectory.lean`: `c6b25ae5dfc3dc38f1d4ae654524764e10474ba04d94a0925242de5d88ccbdd6`.
- `Formalization/MDP/Basic.lean`: `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
