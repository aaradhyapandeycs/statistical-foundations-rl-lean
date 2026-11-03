# Independent source/semantic audit: bounded TD iterates

Verdict: PASS for the entire deterministic source `lemma:TD-bounded`, not a sampling-law or convergence-rate theorem. Exact reviewed staged `.local/TDIterateBounds.lean`, SHA-256 `76f62a155ac303d82bea3395487e9c54cb729eceba3ba84042414bc499bfb637`. No Lean source was edited.

Authoritative local source: `generative_model_model_free.tex:270–300`, including `eq:defn-Pt-TD-proof-generative`, `eq:iteration-rule-td` and `lemma:TD-bounded`.

## Update, indexing and policy semantics

`policyReward` is exactly the known policy-averaged reward rπ(s)=E_{a~π(s)}r(s,a), with bounds derived from the actual probability simplex and [0,1] reward assumptions. It does not replace the source update by an action-reward sample or assume its desired range.

`tdIterate 0=V₀`; update t+1 uses η(t+1), samples(t+1,s), and **the previous iterate t at every coordinate**, including the sampled next state. This is the synchronous source update at time t+1, not an in-place sequential-state update. Source's one-hot Pt multiplication is exactly selection of Vt at the observed next state. Neither η0 nor samples0 is used. The source recursion starts at1; the code agrees.

The sample array is arbitrary. Since this is a pathwise convexity invariant, a stochastic sampling assumption is unnecessary and omitting it only strengthens this deterministic conclusion. The file's header correctly avoids claiming the source iid/generative law. A later TD concentration theorem must still construct samples with actual Pπ-induced row laws and fresh-time independence; these are not established here. Similarly it makes no measurability/concentration/rate assertion for TD itself.

## Finite horizon of rate assumptions

`hη` requires 0≤ηk≤1 only for k≤the requested iterate t. It does not require every future rate to be admissible. Given the source assumptions through T, every t≤T satisfies this prefix condition by transitivity, yielding all source iterates0…T. The code's per-t formulation is a faithful local strengthening of the source horizon formulation, not a silently global rate restriction. η0 is unnecessarily required by the implementation proof's prefix predicate but is also explicitly included by the printed source assumption0≤t≤T, so this introduces no source mismatch.

No specific logarithmic learning-rate schedule, T≥2, γ≥1/2 or other later convergence-theorem condition is smuggled into this elementary lemma. It remains valid on the full MDP discount domain0≤γ<1, including γ=0 and learning rates0/1.

## Actual range and full norm statement

`tdIterate_bounds` proves both0≤Vt(s) and Vt(s)≤effectiveHorizon for every state and arbitrary sample realization, using the actual update, bounded policy reward and effective-horizon identity1+γH=H. It does not define the iterates by assuming their range.

`effectiveHorizon` is the proved value1/(1−γ). `tdIterate_error_norm_le` proves the full finite-state function supremum norm of Vt−M.trajectoryExpectedValue π, not just one coordinate or an initial-distribution average. Its reference is the actual integral of discounted return under the constructed infinite trajectory law (`MDP/InfiniteReturn.lean`), with its independently proved return bounds. No assumed Bellman fixed point or renamed estimator substitutes for Vπ. Coordinate absolute differences are bounded using the two actual [0,H] intervals; taking the Pi norm gives exactly the printed result.

## Independent compiler and imported axioms

Compiled the **exact original file** with `bash scripts/lean-local.sh -o .local/td-independent-review/TDIterateBounds.olean .local/TDIterateBounds.lean`: exit0 without diagnostics. A fresh, separate import-only `.local/td-independent-review/ImportAudit.lean` imported that newly generated module using an isolated search path followed by actual production/pinned package artifacts. All five exports (`policyReward`, `tdIterate`, `policyReward_bounds`, `tdIterate_bounds`, `tdIterate_error_norm_le`) reported only `propext`, `Classical.choice`, `Quot.sound`; both public theorem signatures were independently checked. Import probe exit0 without diagnostics. The source hash was verified directly, dependency artifacts preserved, and the compiler slot released immediately after completion.

Actual production integration/export audit remains a separate gate. This verdict does not certify the source TD high-probability theorem, its rate, martingale identities, natural filtration or sample law.

Production integration: the production module is byte-for-byte identical to the independently reviewed staged file. The full project check compiled the actual export and audited 2,220 project declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
