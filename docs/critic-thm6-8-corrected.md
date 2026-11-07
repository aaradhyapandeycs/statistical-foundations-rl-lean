# CRITIC: Theorem 6.8 (`theorem:lcbq`), proposed `Thm6_8_corrected`

Public copy of the independent critic report; local paths removed.

- Date: 2026-11-07 04:43 UTC (start)
- Reviewer: independent Claude critic subagent (did not build this code)
- git HEAD: 6d98f9582477ca46a5af71c2d729326362c263a6 (branch recovery-batch-ch5-online-lower-bound-20261106; WIP files untracked)
- Mode: source-only reading. No Lean, lake, compiler or LSP was run by this critic. Compilation evidence is taken from the lead's log (see "Post-comparison reading").

## SHA256

| File | sha256 |
|---|---|
| source/upstream/tex/chapters/offlineRL.tex | 67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4 (matches source/provenance.json) |
| <builder working folder>/Probe68.lean | ce8a1e04a4b3c1d1648d83f3812a8a4579aaa52c30e3dab7bd32bc82741dca31 |
| <builder working folder>/LCBQDecomposition.lean | be18af5e848096868989cb485c00c2665f549e9f1f3c60d6dfb46186c6829ef4 |
| Formalization/OfflineRL/LCBQDefinitions.lean | 1baec0102770ae977b805b7bbc22513ba3e9343c0863d0b4b98a648c6b14f39f |
| Formalization/OfflineRL/LCBQLemma612.lean | 5065016f015e13bc497356aff408b468d3d9a47cad612ced5b8c0ff709283047 |
| Formalization/OfflineRL/LCBQSeriesBasic.lean | 21fc53b241c25fcabe94b94c02b4c3bcab873dee8dd2dedaa2d72672b5d0ed2f |
| docs/SOURCE-ISSUES.md | 356b75b32d0dc114c5d1ce8f394703496a439e028c9e1cd7423c221afb88aefc |

`Probe68.lean` lines 1–844 are byte-identical to `LCBQDecomposition.lean` (checked with `diff`); lines 845–888 add the probe entry `Thm6_8_corrected`, its wrapper and two `#print axioms`.

## Reconstruction of the source (independent)

Theorem 6.8 (offlineRL.tex:1754–1772). For any `0<δ<1`, any `ε ∈ (0, 1/(1−γ)]`, any test distribution `ρ`: with probability exceeding `1−δ`, the output `π̂` of Algorithm `alg:q-infinite-lcb` (:1701–1745) with `H = ⌈4ι/(1−γ)⌉`, `η_n = (H+1)/(H+n)`, `b_n = c_b√(Hι/(n(1−γ)²))`, `ι = log(SAT/δ)` (:1666–1687, :1849–1852) satisfies `V⋆(ρ) − V^{π̂}(ρ) ≤ ε`, provided `c_b` is sufficiently large and `T ≥ c₂ S C⋆ log(SAT/((1−γ)δ))/((1−γ)⁵ε²)` for a large enough universal `c₂`. `C⋆` is Definition `assumption:concentrate-infinite-simple` (:127–137): `max_{s,a} d⋆(s,a;ρ)/d^b(s,a)`, `d⋆` the normalised discounted occupancy of "the optimal deterministic policy π⋆", `0/0 = 0`. Samples are i.i.d. `(s_t,a_t) ~ d^b`, `s'_t ~ P(·|s_t,a_t)`. Ties in the arg max: "an arbitrary deterministic rule".

Quantifier reading. `c_b` is a universal constant chosen large; `c₂` is "some large enough universal constant". Since `c_b` is itself universal, `c₂` may depend on `c_b`. The proof makes this dependence necessary: θ is bounded via `β_n = 3c_b√(…)`, so the final constant scales like `c_b²`. The C24 counterexample also needs `c₂` to grow with `c_b` (failure persists for `T ≲ c·c_b² C⋆ι²/ε²`). So the faithful order is `∃c_b₀ ∀c_b ≥ c_b₀ ∃c₂`. `∃c₂` and `∃c₂₀ ∀c₂ ≥ c₂₀` are equivalent here, because the condition is monotone in `c₂` (all other factors are ≥ 0).

Proof, Steps 3–6 (:1938–2353).
1. `eq:performance-to-alpha0` (:1944–1950): `V⋆(ρ)−V^{π_T}(ρ) ≤ ⟨ρ,Δ_T⟩ ≤ (1/T)Σ_t⟨ρ,Δ_t⟩`. This uses `V_T ≤ V^{π_T}` (Lemma 6.10) and monotonicity of `V_t`.
2. `eq:first_step_rewrite` (:1952–1962): `Δ_t(s) ≤ min{Q⋆(s,π⋆(s)) − Q_t(s,π⋆(s)), 1/(1−γ)}`, which is at most `γ F_t(s,π⋆(s)) + min{β_{n_t}, 1/(1−γ)}` by Lemma 6.9(a). For `n=0` the minimum is `1/(1−γ)`, and the bound also needs `F_t ≥ 0`, i.e. `Δ ≥ 0`.
3. Regrouping (:2103–2133): `Σ_t 1{(s_t,a_t)=(s,a)} Σ_{i≤n_t} η_i^{n_t} x_i = Σ_i (Σ_{m=i}^{n_T} η_i^m) x_i ≤ (1+1/H) Σ_i x_i`, with `x_i ≥ 0`.
4. The time shift and the flow `Σ_s[ρᵀP^j](s)P_{s,π⋆(s)}f = ρᵀP^{j+1}f` give `α_j ≤ α_{j+1}+ξ_j+θ_j+ψ_j+φ_j` for general j (:2232). Iterating gives `α_0 ≤ α + ξ + θ + ψ + φ`.
5. Lemma 6.12: `α = 0`, `ξ ≲ (1−γ)^{-2}`, `θ ≲ √(C⋆STι²/(1−γ)⁵)`, `ψ+φ ≲ C⋆ι²/(1−γ)³`.
6. Step 6 (:2326–2353): `(1/T)α_0 ≲ √(C⋆Sι²/((1−γ)⁵T)) ≤ ε`. This last step needs `T ≳ C⋆Sι²/((1−γ)⁵ε²)`, i.e. log² (C24). The printed condition has a single log.

Independent spot-check of the C24 counterexample sketch (one state, `γ=0`, `p = c₂/(64c_b²⌈4ι⌉)`, `T = ⌈c₂ι/(pε²)⌉`). It gives `T ≈ 4096c_b²ι²`, `N⋆ ≈ 16c₂ι` and `b_{N⋆} ≈ c_b√(ι/(4c₂))`, which exceeds `9/16` for `ι ≳ 1.27c₂/c_b²`. Meanwhile `b_T ≈ 1/32`, so `Q_T(a₂) ≥ 1/2 − 1/16 > sup_t Q_t(a⋆)`, and the last strict V increase selects `a₂`. The sketch is consistent; the printed single-log theorem is false for this algorithm. A `_corrected` entry is warranted.

The corner `ι < 1` (my reconstruction). `ι < 1 ⇔ SAT < eδ < e`, so `SAT ∈ {1,2}`. With `SAT = 1` we have `|A| = 1`: every deterministic policy is optimal, the gap is 0 surely, and `1 > 1−δ`. With `SAT = 2`, `T ≤ 2`. Under the log² condition, `T ≥ c₂ S C⋆ L²/((1−γ)⁵ε²) ≥ c₂L²` (using `(1−γ)ε ≤ 1` and `(1−γ) ≤ 1`). Here `L = log(2/((1−γ)δ)) > log 2`. This gives `2 ≥ c₂(log 2)²`, which is infeasible for `c₂ > 2/(log 2)² ≈ 4.16`.

## Lean statement under review (`Thm6_8_corrected`, Probe68.lean:855–875)

`∃ cb₀ > 0, ∀ cb ≥ cb₀, ∃ c₂ > 0, ∀ S A [Fintype] (M : DiscountedMDP S A) db (sel) (hsel: ∀ f a, f a ≤ f (sel f)) π₀ T δ, 0<δ<1 → 1 ≤ T → ∀ ρ πstar, (πstar Q⋆-greedy) → ∀ ε, 0<ε → ε ≤ 1/(1−γ) → C⋆ ≠ ⊤ → c₂·|S|·C⋆.toReal·log(|S||A|T/((1−γ)δ))²/((1−γ)⁵ε²) ≤ T → ∀ Ω μ [IsProbabilityMeasure], ∀ X measurable, iIndepFun coordinates, each marginal = Σ ofReal(db(s,a)P(s'|s,a))·dirac → 1−δ < μ.real {V⋆(ρ) − V^{pointMass ∘ (run M cb δ sel π₀ (X ω) T).policy}(ρ) ≤ ε}`.

Definitions checked: `iota` = `log(|S||A|T/δ)`; `horizon` = `⌈4ι/(1−γ)⌉₊`; `penalty` = `c_b√(Hι/(n(1−γ)²))`; `step` matches eqs. Q-lcb-update-rule-Q/V. It uses rate `onlineQRate H k` with the incremented count `k`, `V(s) ← max(V_old(s), max_a Q'(s,a))`, and policy update `sel(Q'(s,·))` only on strict increase. `init` has Q=V=n=0 and policy π₀. `concentrability` is `⨆ ofReal d⋆/ofReal d^b` in ℝ≥0∞, so `0/0=0` and `x/0=⊤`. `d⋆ = discountedJointOccupancy` = `(1−γ)Σγ^t·P(s_t=s,a_t=a)`, normalised as in the source. `DiscountedMDP` carries rewards in `[0,1]` and `γ ∈ [0,1)`. `V⋆` is `trajectoryExpectedValue optimalGreedyPolicy`.

## Comparison table

| Item | Source | Lean | Assessment |
|---|---|---|---|
| Sample-size condition | `c₂SC⋆ log(SAT/((1−γ)δ))/((1−γ)⁵ε²) ≤ T` | same with `log(…)^2` | the only substantive change (C24). See NOTE-1 on the `L<1` regime |
| `c_b` | "sufficiently large", universal | `∃cb₀>0 ∀cb≥cb₀` (cb₀=4) | faithful |
| `c₂` | "some large enough universal" | `∃c₂>0` after `cb` (c₂ = 16(400000+5600cb)²) | faithful. Dependence on `c_b` allowed, and necessary per C24. Monotone in c₂ |
| δ | `0<δ<1` | `0<δ<1` | faithful |
| ε | `(0,1/(1−γ)]` | `0<ε ∧ ε ≤ 1/(1−γ)` | faithful |
| T | iterations, implicitly ≥1 | `1 ≤ T` explicit | justified: with T=0, Lean's `log 0 = 0` makes the condition `0 ≤ 0` true and π̂ = π₀ arbitrary, so the claim would be false. In the source the condition is meaningless at T=0 |
| C⋆ | ≥1, `∞` when `d^b` misses π⋆'s support | ℝ≥0∞ with guard `≠ ⊤` | justified: `⊤.toReal = 0` would reduce the condition to `0 ≤ T` and the claim would be false (no coverage). In the source `C⋆=∞` makes the condition unsatisfiable, so the guard loses nothing |
| π⋆ | "the optimal deterministic policy" | any `πstar` with `Q⋆(s,πstar s) = max_a Q⋆(s,a)` | faithful. Q⋆-greedy deterministic policies are exactly the optimal deterministic ones. Universally quantified: the result holds for every choice used in C⋆ |
| ρ | any test distribution, same ρ in C⋆ and the gap | same ρ in both | faithful |
| Data | i.i.d. `(s,a)~d^b`, `s'~P` | `iIndepFun` coordinates, marginal `d^b(s,a)P(s'|s,a)` | faithful. Any probability space Ω |
| Algorithm parameters | H, η_n, b_n with `ι=log(SAT/δ)` using the run length T | `run M cb δ …` with `iota S A T δ`, same T | faithful |
| Tie rule | "arbitrary deterministic rule" | `sel : (A→ℝ)→A` depending only on the Q-row, with the argmax property | restriction (MINOR-1, disclosure) |
| Output | `π̂ = π_T` | `(run … (X ω) T).policy` as point masses | faithful |
| Probability | "exceeding 1−δ" (strict) | `1 − δ < μ.real {…}` | faithful |
| Conclusion | `V⋆(ρ)−V^{π̂}(ρ) ≤ ε` | `ρ.E[V⋆] − ρ.E[V^{π̂}] ≤ ε` | faithful |

Universes: S, A and Ω are universe-polymorphic. The measurable space on the finite sample type is ⊤. Neither adds a hypothesis.

## Proof-structure check (reading the compiled-claimed Lean, not re-running it)

- `delta_le_visit` (eq:first_step_rewrite, pointwise). It uses `hopt` for `V⋆(s) = Q⋆(s,π⋆ s)`, `Q_t(s,π⋆ s) ≤ max_a Q_t ≤ V_t`, and Lemma 6.9(a) through `upperRecursion` when `n>0`. The `n=0` branch uses `delta_le` (`Δ ≤ 1/(1−γ)`) and `F ≥ 0`. This matches the source, including the truncation by `1/(1−γ)`.
- `triangle_rate_le` and `visit_regroup_pair`. These are the regrouping `Σ_m Σ_{i≤m} η_i^m x_i ≤ (1+1/H)Σ x_i`, using `onlineQRateWeight_tail_sum` (`Σ_{m≥i} η_i^m = 1+1/H`) and `x ≥ 0` from pessimism. They match :2103–2133.
- `occ_flow` and `sum_dWeight` are the flow identity and the `d_j` collapse.
- `alpha_step` covers general `j` (`eq:alpha-recursion-offlineQ`). `alpha0_le` iterates it and passes to the limit with `α_N → 0` and the HasSum's of ξ, θ, ψ, φ. This is the source's `α_0 ≤ α + ξ + θ + ψ + φ` with `α = 0`.
- `performance_le_alpha0` gives `gap ≤ ⟨ρ,Δ_T⟩` from `V_T ≤ V^{π_T}`, then `T⟨ρ,Δ_T⟩ ≤ Σ_t⟨ρ,Δ_t⟩` by `run_V_mono`. This matches :1944–1950.
- Confidence. `lemma612_events_strict` intersects five events. Four are at `δ/5` (martingale, prefix count, an "ic" event for poorly covered π⋆-pairs, two gated Freedman events); see C29(1)–(3). `inter_five_prob_strict` gives a strict `1−δ` from one strict and four non-strict bounds. The algorithm still runs with δ, not δ/5. The δ/5 lives only in the proof, absorbed by `ι ≥ 1` and `cb ≥ 4`.
- Final arithmetic (`final_scalar`), checked by hand. Write `x = 1−γ`, `K = S C⋆ L² ≥ 1`, `16C²K ≤ T x⁵ε²`, with `ι ≤ L`, `xε ≤ 1`, `x ≤ 1`.
  - θ: `C√(C⋆STι²/x⁵) ≤ Tε/4` ⇔ `16C²C⋆Sι² ≤ T x⁵ε²`. This holds.
  - ξ: `C/x² ≤ Tε/16` ⇐ `16C ≤ 16C²K ≤ T x⁵ε² ≤ T x²ε`, using `x³ε ≤ 1`. This holds.
  - ψ+φ: `C C⋆ι²/x³ ≤ Tε/16` ⇐ `16C C⋆ι² ≤ 16C²K ≤ T x⁵ε² ≤ T x³ε`, using `x²ε ≤ 1`. This holds.
  - Total: `α_0 ≤ (1/4+1/8)Tε < Tε`. Correct, with room to spare.
- Corner `ι < 1` (`corner_subsingleton`). It derives `n = SAT < 3` from `n/δ < e < 3` (with `δ < 1`). If `n = 2`, then `T ≤ 2` and `L > log 2`, and `16L² ≤ c₂ S C⋆ L² ≤ c₂ S C⋆ L²/((1−γ)⁵ε²) ≤ T ≤ 2`. This gives `L² ≤ 1/8 < (log 2)² ≈ 0.48`, a contradiction. So `n = 1`, `|A| = 1`, `A` is a subsingleton, `π_T` is pointwise `optimalGreedyAction`, the gap is 0 ≤ ε surely, and the probability is 1 > 1−δ. This agrees with my reconstruction. Lean excludes all of `SAT = 2` (not only the nontrivial `S=1, A=2, T=1`), using `c₂ ≥ 16`, which `thm68Const` satisfies. Every input comes from the theorem's own hypotheses (`hT, hδ, hδ1, hc₂, C⋆ ≥ 1, ε > 0, (1−γ)ε ≤ 1, hcond`). No extra premise is used.
- Wrapper honesty. `Thm6_8_corrected_holds` supplies `cb₀ = 4` and `c₂ = thm68Const cb`, proves positivity, and applies `thm68_corrected_prob`. It does not reprove or restate the result. The entry spells out `fun x => pointMass (…policy x)` where the export has `detPolicy (…policy)`; these are definitionally equal (`detPolicy` is that lambda).
- Forbidden tokens. I computed the transitive project import closure of `Formalization.OfflineRL.LCBQLemma612` (90 project files) and added `Probe68.lean` and `LCBQDecomposition.lean`. After stripping comments, I grepped for `sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide|ofReduceBool|@[extern`: 0 hits. (`#print axioms` does not match `\baxiom\b`.)

## Findings

BLOCKING: none.

MAJOR: none.

MINOR-1 (tie-rule scope, disclosure). The source allows "an arbitrary deterministic rule" for ties. Lean's `sel : (A→ℝ)→A` may depend only on the current Q-row, not on `s`, `t` or history. The proof never uses this (only `Q_t(s,π_t s) = max`), so the theorem very likely holds for all rules. Still, the formal entry covers a sub-class of the printed algorithm, and its docstring and the SOURCE-ISSUES entry must say so. This is the same scope already disclosed for C20 and the Ch6 LCB-Q definitions. It is not a correctness issue.

MINOR-2 (index hygiene at landing). The probe `Thm6_8_corrected` has no docstring. AGENTS.md requires the landed entry in `Formalization/Statements/Ch6.lean` to carry a docstring that cites `theorem:lcbq`, `chapters/offlineRL.tex:1754–1772` (condition at :1767), states that log is replaced by log² and that the tie rule is restricted to Q-row selectors, and points to `docs/SOURCE-ISSUES.md#C24`. `Ch6.lean` must import definition modules only (`LCBQDefinitions` provides `run`, `concentrability`; check that nothing in the `Prop` needs a proof module). The proof goes in `Ch6Proofs.lean`. Remove the `#print axioms` lines and the `Ch6Probe68` namespace from the landed version.

MINOR-3 (C24 wording). C24 says the nontrivial corner (`A = 2`, `S = T = 1`) is "infeasible for `c₂ > 1/log 2`". That is correct for the printed single-log condition. Under the corrected log² condition, which the formal proof uses, the threshold for that case is `c₂ > 1/(log 2)² ≈ 2.08`. For all of `SAT = 2`, including the `A = 1` sub-cases, it is `c₂ > 2/(log 2)² ≈ 4.16`; Lean uses `c₂ ≥ 16`. The C24 entry for the corrected theorem should cite the log² threshold.

NOTE-1 (not a weakening concern). For `L = log(SAT/((1−γ)δ)) < 1`, `L² < L`, so the corrected condition is weaker than the printed one there, and the corrected theorem asserts more. That regime forces `SAT ≤ 2`, and the proof handles it as above. For `L ≥ 1` (all practical cases) the corrected condition is stronger. Disclosure "log replaced by log²" is accurate. No claim of being "implied by the print" should be made.

NOTE-2. `c₂ = 16(400000 + 5600 c_b)²` is enormous but universal given `c_b`. The source makes no claim about its size.

NOTE-3. The proof depends on the C28/C29 repairs (δ/5 budget, the poorly-covered-pair event, gated Freedman). These are already recorded, and the corrected statement is unaffected by them.

## Proposed SOURCE-ISSUES text

Append to C24, after "Proposed correction":

> **Formal entry:** `Thm6_8_corrected` (`Formalization/Statements/Ch6.lean`) states Theorem 6.8 with `log²(SAT/((1−γ)δ))` in place of `log(SAT/((1−γ)δ))` in `eq:sample-size-lcbq-T-thm`, quantified as `∃ c_b₀ > 0, ∀ c_b ≥ c_b₀, ∃ c₂ > 0` (the proof gives `c_b₀ = 4`, `c₂ = 16(400000 + 5600c_b)²`; `c₂` must grow with `c_b`, per the counterexample above). Other explicit hypotheses: `1 ≤ T`, `C⋆ < ∞` (when `C⋆ = ∞` the printed condition cannot hold, so nothing is lost), `π⋆` any Q⋆-greedy deterministic policy used in `C⋆`, `0 < ε ≤ 1/(1−γ)`, i.i.d. samples from `d^b ⊗ P`, conclusion with probability strictly greater than `1−δ` for the output `π_T`. Scope: arg-max ties are broken by a deterministic selector that depends only on the Q-row `Q(s,·)`; the source allows any deterministic rule. The corner `log(SAT/δ) < 1` is handled inside the proof: it forces `SAT ≤ 2`; `SAT = 2` contradicts the log² condition for `c₂ ≥ 16` (since then `T ≤ 2` and `log(SAT/((1−γ)δ)) > log 2`), and `SAT = 1` gives `|A| = 1`, where the gap is 0. (The `1/log 2` threshold above refers to the printed single-log condition; under log² the nontrivial case `S = T = 1, A = 2` is infeasible for `c₂ > 1/(log 2)²`.)

In C22, replace the "Open (formal coverage only)" sentence with:

> **Formal coverage (Theorem 6.8):** closed by a different route. `Thm6_8_corrected` does not apply Lemma 6.11 in the corner `δ > SAT/e`. The theorem's own hypotheses (log² condition, `c₂ ≥ 16`) force `|A| = 1` there, and the claim then holds surely (see C24). The `γ ≤ 2/c₂`, `κ ≤ 1/2`, constant-84 argument above concerns the printed single-log condition and is not formalized. It is no longer needed, because the printed Theorem 6.8 is itself refuted (C24). Lemma 6.11 as printed still fails in the corner; `Lemma6_11_restricted` remains the formal entry.

## VERDICT (pre-log)

ACCEPT the corrected statement and the proof structure, subject to MINOR-1 and MINOR-2 at landing. This is conditional on the compile and axiom evidence, which this critic did not produce.

## Post-comparison reading (after the above was written)

I read `the private independent check note (Thm6_8-log)` and `docs/critic-lemma6-12-restricted.md`.

- The CHECK log independently confirms that the printed single-log Theorem 6.8 is false for every `(c_b, c₂)`, and that ι² is sufficient given Lemmas 6.9–6.12. This agrees with my reconstruction and spot-check.
- Its corner analysis (`SAT = 1` is trivial, `SAT = 2` is infeasible) agrees with `corner_subsingleton`. That log is a source-level check made before any Lean existed. It contains no compile or axiom evidence for `LCBQDecomposition.lean` or `Probe68.lean`.
- docs/critic-lemma6-12-restricted.md accepts `Lemma6_12_restricted` (ι ≥ 1, C = 400000 + 5600c_b, events at δ/5) with no BLOCKING or MAJOR findings. Here that export is consumed exactly through `lemma612Conclusion` (Tendsto α → 0, the HasSum bounds, and the `C⋆ ≠ ⊤` guards). The guards are discharged by the theorem's `hCs`. The ι ≥ 1 premise is discharged by the case split, with the corner handled by `corner_subsingleton`.
- docs/critic-lemma6-12-restricted.md notes that the five sequences do not depend on `sel`. For Theorem 6.8, `sel` does matter, through the output policy and `V_T ≤ V^{π_T}` (pessimism, which uses `hsel`). So the Q-row tie-rule scope (MINOR-1) is a real scope disclosure for this entry, unlike for Lemma 6.12.

Compile and axiom status: NOT VERIFIED by this critic, per its brief. Before landing, the lead must show:
- a clean compile of the moved `Formalization/OfflineRL/LCBQDecomposition.lean` and of the `Ch6`/`Ch6Proofs` entries;
- `#print axioms` for `Thm6_8_corrected_holds` and `LCBQ.thm68_corrected_prob` reporting only `propext`, `Classical.choice`, `Quot.sound`;
- the `pointMass`-lambda vs `detPolicy` unification accepted by `exact` (expected, by delta reduction).

## VERDICT

ACCEPT-WITH-MINOR.
- The corrected statement differs from the print only by log² in the sample-size condition (C24). All other differences are faithful formal readings: `∃cb₀ ∀cb ∃c₂`, explicit `1 ≤ T`, the `C⋆ ≠ ⊤` guard, `π⋆` any Q⋆-greedy policy, the ε range, ρ, the output `π_T`, and the strict `> 1−δ`. The one restriction is the Q-row tie-rule scope, which must be disclosed (MINOR-1).
- The C22/C24 corner is handled from the theorem's own hypotheses, by a correct `SAT ≤ 2 → (SAT = 2 infeasible, SAT = 1 ⇒ |A| = 1)` argument.
- The decomposition steps and the final constant arithmetic match the source and check out by hand.
- The wrapper only applies the export. There are no forbidden tokens in the import closure or the WIP files.
- Landing conditions: MINOR-1 disclosure; MINOR-2 docstring, module placement and removal of the probe lines; MINOR-3 C24 threshold wording; compile and axiom evidence.
- C22's open formal-coverage item for Theorem 6.8 can be closed as "superseded by a different route" with the text proposed above.
