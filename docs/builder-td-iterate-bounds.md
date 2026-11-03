# Synchronous TD pathwise bounds

Staged `.local/TDIterateBounds.lean` SHA-256 `76f62a155ac303d82bea3395487e9c54cb729eceba3ba84042414bc499bfb637` compiles using the project-local Lean wrapper. It formalizes the source update `eq:iteration-rule-td` and both assertions in `lemma:TD-bounded` (`generative_model_model_free.tex:270–302`).

The actual update starts at `V₀` and uses the realized next-state array at time `t+1`; `policyReward` averages the model reward under the stationary policy. The bounds apply to every sample array, so they require neither an independence assumption nor a product-law construction. The learning-rate premise ranges only over indices through the time being bounded. The first result places every iterate in `[0,1/(1−γ)]`; the second bounds the sup-norm error against the actual infinite-trajectory expected policy return by the same effective horizon. Nonnegative rewards, reward ≤1, and `0≤γ<1` come from the actual model structure.

The pathwise claim does not construct the sampling experiment or prove the high-probability TD learning theorem. The independent semantic review, exact-source axiom audit, production export compilation, and full project check subsequently passed; see `critic-td-iterate-bounds.md` for evidence.
