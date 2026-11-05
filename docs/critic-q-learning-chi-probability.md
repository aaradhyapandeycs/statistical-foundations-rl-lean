# Independent review: robust-comparator fluctuation probability drafts

## Bound scope and source

Reviewed the four exact staged sources at the supplied hashes:

| Draft | SHA-256 |
|---|---|
| `QLearningChiFixedValueFreedmanDraft.lean` (private staged draft, not shipped) | `8b578842cb8dc020c7f9115a542f374a14cc84f6fe15825634be55ceeae639c9` |
| `QLearningChiFixedValueUnionDraft.lean` (private staged draft, not shipped) | `ce8eb1eb355b5e9e5609f3a5916f70da6ce6a7817deb3d28c719763da06b8f28` |
| `QLearningChiSourceRadiusDraft.lean` (private staged draft, not shipped) | `de81a6b1b1db00bc7a887430871615b18968c92dd13f49b2ec94a8790152745b` |
| `QLearningChiSourceRadiusUnionDraft.lean` (private staged draft, not shipped) | `794fbda069f78d05b226eadb2bc7116ad85d26e31ec994ecb0b96a2984f1f777` |

The authoritative source is `source/upstream/tex/chapters/generative_model_model_free.tex`, SHA-256 `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`, especially the Q-comparison parameters and weights at lines 1090–1110, rho and reward shift around 1390–1410, comparator range at 1490–1540, and fluctuation/radius/absorption calculation at lines 1618–1684. The project indexing and sampling semantics are those in `Formalization/ModelFree/QLearningCausality.lean` and the qualified production Q-learning stochastic chain.

## Source constants, indexing, and confidence

The source parameters are

`etaBar = min(1, 2 log(T)^3 / (c₂(1−γ)T))`,
`rho = 8 etaBar log(4SAT/δ)`, and `b = 2rho/(1−γ)`.

The final draft uses `qSourceLateCap` for the exact first expression, `qChiSourceRadius` for the exact rho, and `2*rho*M.effectiveHorizon` for the reward shift. The source-parameter bridge proves `effectiveHorizon=1/(1−γ)` and matches that shift. Thus the radius and robust fixed-point parameters agree with the source.

The source update `i=n+1` is represented by the project sample coordinate `data((s,a),n)`. The increment guard `n<T ∧ T/2<n+1 ∧ n+1≤u` is exactly the late source window through terminal `u`; all inactive terms are zero, and the terminal is fixed in each sum. The sampling law is the actual synchronous product law with each fresh row distributed as `M.transition s a`; centering and variance are proved by the imported actual-row conditional-moment/history chain. No nominal row or data-selected comparator is substituted.

The final union counts two signs, all `S*A` rows, and at most `T` terminal times: `2SAT` scalar events. Each gets `epsilon=delta/(2SAT)`. The finite union bound therefore gives failure probability at most delta, without assuming inter-event independence. This matches the source's per-sign `delta/2` allocation. Non-late indices are assigned empty bad events. For the K=1 source radius, `log(2/epsilon)=log(4SAT/delta)`; the raw Freedman square-root and linear terms simplify respectively to `gamma*sqrt(rho*Var)` and `gamma*rho*H/6`, with `H=1/(1−gamma)`. The residual lemma then supplies the deterministic radius-to-residual absorption for both signs.

The generic Freedman theorem retains arbitrary positive K, its actual random predictable variance, and explicit `epsilon∈(0,1)`. The source-radius theorem fixes K=1, uses the previously derived almost-everywhere variance cap to enlarge the event, and transfers the a.e. inclusion by measure monotonicity. It does not assume a pointwise variance cap.

## Assumptions and hidden-premise check

The final `qChi_actualComparatorAbsorption_probability` requires the actual finite MDP, `T≥2`, `c₁,c₂>0`, `0<δ<1`, and the exact source finite rate-schedule predicate. The model's `0≤γ<1` and nonempty finite state/action types come from the actual MDP structure. The theorem proves positivity of the deterministic source radius and returns a proof witness `hρ`; it does not assume radius nonnegativity as an extra estimate. Comparator values are the actual fixed points for source radius and source shift, are independent of sample data, and their range bound is derived from the robust-range theorem.

I found no target-shaped assumption supplying a probability bound, variance budget, fixed-point identity, comparator span, radius event, or absorption result. These are derived through imported modules. Source comparator span is proved for the constructed `Q⁺/Q⁻` family. `rho` and the reward shift are deterministic functions of model, horizon, schedule parameters, and confidence only.

## Independent fresh isolated build and axiom probe

All four exact sources compiled serially with exit 0 and empty per-module compile logs into an isolated local audit directory (not shipped). The first draft imports the qualified production module `Formalization.ModelFree.QLearningChiFixedValueVariance`; this avoids mixing same-named staged variance declarations with production declarations. The three consumers import only the local probability drafts. The imported dependencies were the current built project oleans; this review did not rebuild the entire production dependency chain.

Fresh output hashes:

| Output | SHA-256 |
|---|---|
| `QLearningChiFixedValueFreedmanDraft.olean` | `f527051b3e582661bd7bc4376f20ffdf1702c6607e47238b62e5c433fc50e3d5` |
| `QLearningChiFixedValueUnionDraft.olean` | `1094897829af6a4999411daf62ab44a01fdc293c361411fde819e1f9d8053eaa` |
| `QLearningChiSourceRadiusDraft.olean` | `96e9af128129989aeb3b2eaf14b55b0d2d65f197d88e0fc99307f4c974b1472a` |
| `QLearningChiSourceRadiusUnionDraft.olean` | `4dd8a3ebd9957a1a5d646f76acc126d129268517665cf2cdeed25f71b402cb91` |

The combined fresh audit `CombinedAudit.lean` (in an isolated local audit directory, not shipped), SHA `88dd241c62488dfab580b12491b234dfc52fe5c2fcfcf1685bb5cba64f8c2970`, imports both union branches together and probes all sixteen exports. Its `.olean` SHA is `48c34da21ffcedc34be810db5f9c429a860ab25a116cd000fd4dbdf6b06ab045`; the probe output SHA is `376a7a8711a25e4650defc3dcc3cccca0c1e782bae68ebd3c3e192594661afa3`. All sixteen declarations depend only on `[propext, Classical.choice, Quot.sound]`. The source drafts contain no `sorry`, `admit`, or custom `axiom` declaration. This probe covers the sixteen named exports and their transitive dependencies, not every declaration in the project.

The independent variance-helper fresh build/probe evidence has also been added to `docs/critic-td-variance-pairwise-source.md`.

## Limitations and disposition

The four exact drafts compile and the stated source absorption probability is supported by the reviewed constants, actual sampling, and assumptions. This is only the source's robust-comparator fluctuation/absorption step. It does not prove Lemma 4.10(ii) comparator closeness, propagate comparison through Q-learning iterates, simplify the complete sample budget, or establish the final Q-learning accuracy theorem. The helper chain was compiled using existing actual production oleans rather than independently rebuilding those dependencies in this run; production landing and integrated checks remain the integration gate. The compiler slot is released.

## Production integration

The four reviewed comparator Freedman, union, source-radius and absorption-event modules are now integrated as corresponding `Formalization/ModelFree/QLearningChi*.lean` modules. The stability estimate and final Q-learning theorem remain separate. Declaration and proof bodies match the reviewed staged source; imports and status comments were updated where required. The complete project check compiled 263 modules and audited 3,454 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
