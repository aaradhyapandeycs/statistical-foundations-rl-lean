# Independent source review: statement-index backfill

Date: 2026-11-03
Scope: source/statement review only. No Lean process was run and no Lean source
was edited for this review. The root agent owns compilation. This review covers
the current Chapter 2 through Chapter 5 index files, including the six Chapter
3 entries added after the first review snapshot.

## Pinned snapshot

| File | SHA-256 |
|---|---|
| `Formalization/Statements/Ch2.lean` | `cd82b63af573a044be7e44423c5165e51b1215e57809199e89da49cc992b1d80` |
| `Formalization/Statements/Ch2Proofs.lean` | `eb0a74fb0e0fce6221ae36af55f67bb82450206ba9b9c2af108839b5d2eb333e` |
| `Formalization/Statements/Ch3.lean` | `f4104fe1cc8131125845af1a4f809d6f116042b25d78a202c063ac5e9e5dd6bd` |
| `Formalization/Statements/Ch3Definitions.lean` | `5fbbcacc9f0052f71a07ee5af9b4c4d89f63813a177bdb939e96ec8d464c5950` |
| `Formalization/Statements/Ch3Proofs.lean` | `b9fa4dad0fcb4d16665301b941c5dc1cfb8eb9e625dd655ec95307b837c326b1` |
| `Formalization/Statements/Ch4.lean` | `edb1867b9b4edb4a4df6c3504bd3bfa5277e9b5a52e02b2d40a76185229ece52` |
| `Formalization/Statements/Ch4Proofs.lean` | `8c591e4e7bbb1d2fd0b38ce3d01bb4d9b5f309e008983e55875ed54f45176045` |
| `Formalization/Statements/Ch5.lean` | `2fa1805f9c3ea796b43e75154b5c9bf8d801b5fdf4b8bb48528a91fb0dcc36bb` |
| `Formalization/Statements/Ch5Proofs.lean` | `f4a2d5ccae2554e37f2aff787bce9917bc1f0bf406e7b4a16e1be8dd5dea051b` |

The source is pinned by `source/provenance.json`. The ranges below use the
restored source at `source/upstream/tex/chapters/`.

## Chapter 2

### Lemma 2.2: variance perturbation

`Lemma2_2` at `Ch2.lean:14–24` matches `lem:variance-perturbation-var-P-V`,
`prelim.tex:458–467`: both value functions lie in `[0, 1/(1−γ)]`, and the
supremum norm difference of the transition-row variance vectors is bounded by
`4/(1−γ)` times their supremum distance. The Lean function norm is over
`State × Action`, matching the source's `SA`-coordinate variance vector.
`DiscountedMDP` supplies the source discount domain `0 ≤ γ < 1` and normalized
transition rows. `Ch2Proofs.lean:8–11` applies the existing perturbation result
directly.

### Lemma 2.9: Freedman

The current `Lemma2_9` at `Ch2.lean:28–49` matches `lem:Freedman-prelim`,
`prelim.tex:1056–1075`:

- Its pointwise deterministic increment bound `∀ n ω, |X n ω| ≤ B` matches
  the source's deterministic `|X_k| ≤ B` for all source indices.
- Its variance-cap premise is `∀ ω, W_n(ω) ≤ σ²`, matching the source's
  deterministic bound. The conclusion retains the random `W_n` inside the
  maximum, the `σ²/2^K` floor, the logarithm `log(2K/δ)`, and the `4B/3` term.
- The Lean index begins at zero and uses `Finset.range n`; the docstring's
  source-index shift maps Lean `X 0,…,X(n−1)` to source `X₁,…,X_n`. Its
  generated sigma-algebra uses exactly the strict past `j < k`.
- `0 < K`, `0 < δ < 1`, measurability, and the conditional-mean-zero condition
  are all represented. The conditional-expectation equality is appropriately
  almost everywhere.

The earlier a.e.-only increment and variance-cap version is superseded by the
hash above. The current `Lemma2_9_holds` wrapper converts the deterministic
premises to the a.e. helper inputs with `Eventually.of_forall`; it derives the
helper-only `B ≥ 0` from the source pointwise bound and represents the source
scale by an actual square `σ ^ 2` (`Ch2Proofs.lean:15–25`). The current index
therefore has no extra nonnegativity premises for `B` or `σ`.

**Chapter 2 verdict:** no source/statement mismatch found in the pinned
statements. The wrappers consume existing results rather than restating their
proofs.

## Chapter 4

The source domains were checked against `generative_model_model_free.tex`.
`DiscountedMDP` supplies finite nonempty carriers, rewards in `[0,1]`, and
`γ ∈ [0,1)`. The direct imports of `Ch4.lean` are the five definition modules
listed at lines 1–5; they contain the data/value/sampling definitions used by
the index and no theorem declarations. Proof-facing modules are imported by
`Ch4Proofs.lean`, not directly by the statement file.

| Entry | Source comparison |
|---|---|
| `Lemma4_2` (`Ch4.lean:15–25`) | Matches `lemma:TD-bounded`, `generative_model_model_free.tex:293–302`: bounded initial values, rates in `[0,1]` on indices `0,…,T`, and both the iterate range and error bound for every `t≤T`. The result is pathwise for arbitrary sample arrays, as the source lemma is deterministic once the samples are fixed. Its true value is `M.trajectoryExpectedValue π`. |
| `Lemma4_4` (`:27–42`) | Matches the one-step square-energy relation `lemma:TD-square`, `:643–659`, including the factors `ηₖ(1−ηₖ)γ²`, the conditional expectation of the next squared iterate, and `2ηₖ/(1−γ)`. It is represented under the finite actual TD sample law and a.e. conditional expectation. The finite `T`/prefix formulation specializes the source's `k≥1` statement to the sample window actually used; the proof wrapper supplies the stated finite-prefix rates. The product law has one unused time-zero coordinate, while updates use positive indices, so that coordinate does not change the source law or the conditional past. |
| `Lemma4_5` (`:44–65`) | Matches both simultaneous bounds in `lemma:TD-variance-proxy-bound`, `:727–743`: probability `≥1−δ/(2T)`, the `16\barη/(1−γ)²` proxy norm (written as `16\barη·H_eff²`), and the `33 log³T/((1−γ)³T)` original-variance bound. It includes the surrounding source conditions: `γ≥1/2`, `T≥2`, `δ∈(0,1)`, `ε∈(0,H_eff]`, the exact positive-index schedule from `:183–187`, the sample budget, `t≤T`, and eligible-terminal lower bound `T/(c₂ log T)≤t` from `:489–490`. Constant order `0<c₂≤c₁` and `c₃>0` is right. The selected witness `c₁=c₂=1/4,c₃=4096` is disclosed. |
| `Lemma4_8` (`:67–79`) | Matches `lemma:non-negativity-Qt-Vt`, `:1052–1071`: the source requires `ηₜ∈[0,1]` for every `t≥0`, and the statement has that global condition. It includes the `Q_t` and `V_t` ranges and the optimal-Q error bound, with `Q₀` in the source interval. The synchronous sample-array update and `qLearningValue=max_a Q` match the algorithm at `:800–832`. |
| `Lemma4_10` (`:81–98`) | Matches both clauses of `lemma:Q-comparison-facts`, `:1338–1373`: the support-constrained χ² set, the two-sided upper/lower expectation deviations, and the same-reward/same-discount optimal-Q perturbation bound. `qChiBall` explicitly enforces zero mass on nominal zero cells. The first substatement includes the source's standing `0≤γ<1` domain; its nonnegativity premise is not an extra restriction. |
| `Lemma4_11` (`:100–108`) | Captures both `γ`-contraction inequalities in `lemma:robust-Bellman-contraction`, `:1422–1438`, with the source's positive radius and specified reward shift `b=2ρ/(1−γ)`. The index fixes that source value rather than quantifying over arbitrary `b`. |
| `Thm4_6` (`:109–128`) | Matches `thm:infinite-horizon-simple`, `:891–912`: `γ∈[1/2,1)`, `A≥2`, `T≥2`, `δ∈(0,1)`, `ε∈(0,H_eff]`, the exact schedule for `0≤k≤T` (`:883–889`), initialization, `c₃ log⁴T log(SAT/δ)/((1−γ)⁴ε²)≤T`, and probability `≥1−δ` for all state-action Q errors. The source's universal constants are quantified before the model parameters. |

`Lemma4_5` and `Thm4_6` do not add the proof's convenience witness condition
`c₁≤1` to their existential statement. The wrappers may project the existing
proof's stronger constant witness; this does not alter the source-facing
conclusion. `Lemma4_10` and `Lemma4_11` retain the source discount domain and
the source's fixed reward-shift definition.

**Chapter 4 verdict:** no substantive conclusion, probability, sample-law,
time-index, or rate-schedule mismatch found in the current seven entries.
`Lemma4_4`'s finite-window presentation is a source-prefix specialization, and
the source-facing wrapper must preserve the global source conclusion if one is
later indexed separately. No source lemma is inferred from an unproved helper
premise in the statement files.

## Chapter 5

`Lemma5_5_corrected` (`Ch5.lean:9–38`) corresponds to `lemma:opt`,
`onlineRL.tex:765–775`, with the two disclosed implementation corrections:
the explicit `N=0` branch `Q=H` (Candidate C8) and one deterministic maximizing
tie rule. The confidence-factor discrepancy in the printed proof remains
separately disclosed as Candidate C6; the statement keeps the printed
factor-two conclusion and does not silently substitute the proof's factor
four. The `δ'` denominator is the active source equation's `100S²A²H²K²`
(`onlineRL.tex:413–421`); the commented-out 200 expression is not used.

The source event is simultaneous for all states, actions, stages, and episodes.
The statement uses `Fin H`/`Fin K`, pre-episode tables from exactly the first
`kH` completed observations, the true optimal finite-horizon suffix values,
and forced-first-action suffix Q values. The corrected planner's known reward
and true transition rows remain fixed; its empirical rows use the observed
history. The sequential law draws independent reset states and then draws each
successor from the row chosen from the revealed history, matching the online
sampling protocol (`onlineRL.tex:17–53`, `286–339`). Its event is the actual
finite-trajectory value/Q event, not a Bellman surrogate.

The fallback state is now chosen locally from the model's nonempty state
carrier, so it is not an extra theorem parameter. The proof wrapper uses that
same choice. Direct imports of `Ch5.lean` are the extracted episode-law and
planner-definition modules; the proof module alone imports the source optimism
theorem. No indexed result theorem is imported into its own statement.

**Chapter 5 verdict:** the corrected statement matches the disclosed corrected
implementation and its source event. It is not presented as the exact printed
`lemma:opt` because the printed zero-count operation is undefined and its proof
has the separate confidence-factor discrepancy.

## Chapter 3

The six current entries in `Formalization/Statements/Ch3.lean` were compared
with `source/upstream/tex/chapters/generative_model_model_based.tex`. The
statement file directly imports only `Ch3Definitions`; proof applications are
in `Ch3Proofs`. That definition module contains the sample spaces, product
sampling laws, empirical models, actual trajectory values, absorbing models,
and finite-horizon selector/event definitions used by the statements.

| Entry | Source comparison |
|---|---|
| `Thm3_1` (`Ch3.lean:14–25`) | Matches `thm:model-based-policy-eval`, `:140–156`: the universal `c>0` precedes S,A,N, model, policy, δ,ε; ranges and sample threshold match; the event uses the actual product law of policy-induced transition rows and plug-in trajectory-value estimator with known policy reward. The explicit `hN : 0<N` follows from the source threshold (`S≥1`, `δ<1`, `γ<1` make its logarithm and threshold positive) and is needed by the empirical-frequency definition. |
| `Thm3_2_positiveN` (`:28–51`) | Restricted positive-sample version of `Thm:sample-compl-main`, `:900–923`, as disclosed in `SOURCE-ISSUES.md#statement-index-scope-disclosures`. It preserves the source constant quantifier, confidence/accuracy domains, N-dependent logarithmic sample bound, and both V/Q inequalities. Its event quantifies over every deterministic empirically optimal policy under the actual independent product law of state-action transition rows, at least as strong as the source guarantee for any returned optimal deterministic policy. The wrapper converts the existing strict probability bound to the displayed weak `≥1−δ`. |
| `Lemma3_3` (`:53–62`) | Matches `LemAbsToNormalV`, `:1254–1263`: the model absorbs at x and replaces its reward there by `(1−γ)V*(x)`. `optimalTrajectoryValue` is the actual trajectory value of the optimal greedy policy; the wrapper applies the existing absorbing-model preservation result. |
| `Lemma3_4` (`:64–77`) | Matches `LemValueCover`, `:1292–1300`: for each state and positive-size empirical data, one of N+1 grid points gives value-function distance at most `1/[N(1−γ)]`. `absorbingGridValue` is the actual optimal trajectory-value function of the empirical absorbing model; the wrapper applies the existing covering result. |
| `Lemma3_5_positiveN` (`:79–107`) | Restricted positive-sample version of `lem:policy-learning-evaluation`, `:1306–1326`, as disclosed in `SOURCE-ISSUES.md#statement-index-scope-disclosures`. `leaveOneOutBeta` is the source `β₁=2 log(16SAN/((1−γ)δ))`; the sample threshold is `N≥c₀β₁/(1−γ)`. The event retains the simultaneous empirical-versus-true policy-value norm bound and pointwise `0≤V*−V^{π̂*}` and upper bound. Its product law and empirical model retain known rewards. The wrapper projects the source export's stronger event and probability to these clauses. |
| `Thm3_9_causal_positiveN` (`:109–137`) | Restricted positive-sample, fixed-selector version of `Thm:sample-compl-finite`, `:2552–2570`; the restrictions are disclosed in `SOURCE-ISSUES.md#statement-index-scope-disclosures`. It preserves source domains `δ>0`, `0<ε≤H`, the `H³ log(HSA/δ)/ε²` sample threshold, and simultaneous V/Q loss bounds. The actual product law is over stage/state/action/sample coordinates; empirical stages retain known rewards; V/Q are actual finite-trajectory suffix and forced-first-action Q values. The entry fixes a deterministic backward-greedy selector and fallback because the source does not specify a tie rule. The wrapper applies the existing theorem to that selector and projects its nonnegative-loss clauses to the indexed upper bounds. It is a causal-selector variant, not a claim that the source specifies this tie rule. |

The positive-N qualifiers match the current empirical-frequency definitions
and are disclosed for all three affected results. For Thm3_1, positivity
follows from its sample threshold: on the source range, its logarithm and
threshold are positive. For Thm3_2 and Lemma3_5, the explicit `N>0` restriction
remains necessary for these Lean empirical-frequency definitions; at `N=0`,
Lean's totalized real logarithm does not make the source's sample-size theorem
applicable. For Thm3_9, the source theorem treats `N` as a sample size and the
formalized experiment requires a positive count; that scope is disclosed
rather than generalized to `N=0`. The finite-horizon entry additionally fixes
a tie selector, as its docstring states. No source/export mismatch was found in
these six entries and their wrappers. This remains a source review, not
compilation or transitive-axiom evidence.

## Limits

This is a statement/source review, not compilation or axiom evidence. The root
agent owns the focused build and full integration check. The hashes above bind
the exact source-facing statement, definition, and wrapper files reviewed.
