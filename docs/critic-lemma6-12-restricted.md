# CRITIC: Lemma 6.12 (`lem:lcbq-alpha-xi-psi-phi-bound`), proposed `Lemma6_12_restricted`

Public copy of the independent critic report; local paths removed.

- Date: 2026-11-07 04:12 UTC (report written ~04:30 UTC)
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `6d98f9582477ca46a5af71c2d729326362c263a6` (branch `recovery-batch-ch5-online-lower-bound-20261106`; the LCB-Q files are untracked working-tree files)
- Mode: source-only review. No Lean, lake, compiler or lean-lsp was run. Reconstruction and comparison (sections 1 to 4) were written before I read any PREFLIGHT, BUILD-LOG, PROGRESS, CHECK or other CRITIC file.

## SHA256

| File | sha256 |
|---|---|
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` (matches `source/provenance.json`) |
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` |
| `docs/SOURCE-ISSUES.md` | `0164803b2635a5ed9617df0b4f524e18bc95258b1a75ec0b723033f9aec56a97` |
| `Formalization/OfflineRL/LCBQDefinitions.lean` | `1baec0102770ae977b805b7bbc22513ba3e9343c0863d0b4b98a648c6b14f39f` |
| `Formalization/OfflineRL/LCBQSeriesBasic.lean` | `21fc53b241c25fcabe94b94c02b4c3bcab873dee8dd2dedaa2d72672b5d0ed2f` |
| `Formalization/OfflineRL/LCBQPsiPhi.lean` | `8ea87db78f709440960c55ebcf10f695aec3cef4a4469e7e581cb71cbe391161` |
| `Formalization/OfflineRL/LCBQLemma612Events.lean` | `bbaa1ac1c21da49ad0766250f3dbdab6d44ea76d43b33828f45c5b9c5ec78dc4` |
| `Formalization/OfflineRL/LCBQFreedman612.lean` | `e3b7627804bc298470ed9c796790fd67ecfca9218b16e85513477b57648d2e5e` |
| `Formalization/OfflineRL/LCBQLemma612.lean` | `5065016f015e13bc497356aff408b468d3d9a47cad612ced5b8c0ff709283047` |
| `<builder working folder>/Probe612.lean` | `71c0d8ef7b41dad61506a84b78eed82923ba5e5dae3f21ceedff247b70d94c56` |

The six library hashes and the probe hash agree with `<builder working folder>/sha.txt`. Each library `.olean` under `.lake/build` is newer than its source. That is consistent with a successful compile, but I did not compile anything.

## 1. Source reconstruction

**Setting.** This is Algorithm `alg:q-infinite-lcb` (`:1701–1745`), the fresh-sample model: `(s_t,a_t) ~ d^b` and `s_t' ~ P(·|s_t,a_t)`, i.i.d. over `t`. The parameters are `H = ⌈4 log(SAT/δ)/(1−γ)⌉` (`:1669–1672`), `η_n = (H+1)/(H+n)` and `b_n = c_b √(Hι/(n(1−γ)²))`, with `c_b` "some universal constant" (`:1682–1688`). The notation is fixed at `:1806–1852`: `Q_t, V_t` at the end of iteration `t`, `n_t` (visits among the first `t` iterations), `k_i(s,a)` (time of the `i`-th visit) and `ι = log(SAT/δ)`. The quantity `β_n = 3c_b√(Hι/(n(1−γ)²))` for `n ≥ 1`, with `β_0 = +∞` (`:1886–1891`). The source defines `Δ_t = V⋆ − V_t` (`:1922–1925`), and `C⋆ = max_{(s,a)} d⋆(s,a;ρ)/d^b(s,a)` with `0/0 = 0` (`:127–137`), so `C⋆ = ∞` when some pair has `d⋆ > 0 = d^b`.

**Sequences** (`:1970–2015`). The source sets `d_j(s,a) = [ρᵀP_{π⋆}^j](s)·1{a=π⋆(s)}` and `κ = γ(1+1/H)³`. Then:
- `α_j = κ^j Σ_{t=1}^T ρᵀP^jΔ_t`.
- `θ_j = κ^j Σ_{t=1}^T Σ_s [ρᵀP^j](s) min{β_{n_t(s,π⋆(s))}, 1/(1−γ)}`.
- `ξ_j = κ^{j+1} ρᵀP^{j+1}Δ_0`.
- `ψ_j = γκ^j Σ_t {Σ_{s,a} d_j(s,a) Σ_{i≤n_t(s,a)} η_i^{n_t} P_{s,a}Δ_{k_i−1} − (1+1/H)(d_j/d^b)(s_t,a_t) Σ_{i≤n_t(s_t,a_t)} η_i^{n_t} P_{s_t,a_t}Δ_{k_i−1}}`.
- `φ_j = γκ^j(1+1/H)² Σ_t {(d_j/d^b)(s_t,a_t) P_{s_t,a_t}Δ_{t−1} − (1+1/H) Σ_{s,a} d_j P_{s,a}Δ_{t−1}}`.

The five terms are `α = limsup α_j` and `ξ, θ, ψ, φ = Σ_j(·)` (`:2276`).

**Lemma 6.12** (`:2309–2324`). With probability at least `1−δ`: `α = 0`, `ξ ≲ 1/(1−γ)²`, `θ ≲ √(C⋆STι²/(1−γ)⁵)` and `ψ+φ ≲ C⋆ι²/(1−γ)³`. The statement has no explicit hypotheses. It sits inside the proof of Theorem 6.8, whose standing assumptions are `0<δ<1`, `c_b` "sufficiently large" and the sample-size condition (`:1767`). Here `≲` hides universal constants, and `c_b` is itself a universal constant.

**Proof** (`:4786–5496`). It runs in five parts:
- **α:** `κ<1` and `‖Δ_t‖∞ ≤ 1/(1−γ)` give the bound. (The proof's display sums over `t = 0..T−1`, while the definition sums over `1..T`. This is harmless.)
- **ξ:** Lemma 6.11 together with `‖Δ_0‖∞ ≤ 1/(1−γ)`.
- **θ:** Tonelli, then Lemma 6.11 with `W_t`, then the prefix-count event `max{n_t, 4ι/3} ≥ t d^b/12` (Lemma `sample-split` at `δ/T`, union over `t`). Next the two-case bound on `W_t`, then `Σ t^{-1/2} ≤ 2√T` and Cauchy–Schwarz. Step (iii) uses `H ≍ ι/(1−γ)` "and the condition on `T`".
- **ψ:** the decomposition `κ_1+κ_2+(1+1/H)κ_3+E f_1`. In `κ_1` the source splits pairs into well covered (`d^b ≥ δ/(ST)`), handled by Freedman ("with the condition on `T`") and AM–GM, and poorly covered, handled by nonnegativity and a deterministic bound. `κ_2` telescopes, `κ_3 ≤ 0` telescopes per pair, and `E f_1 ≲ 1/(1−γ)²`.
- **φ:** "handled analogously … more simply … We omit the details" (`:5483–5485`).

The probability events used are the Lemma 6.10 event (giving `0 ≤ Δ ≤ 1/(1−γ)`), the prefix-count event, the ψ Freedman event and an implicit φ event. Each is stated at confidence `1−δ`.

## 2. Definitions check (Lean vs source)

| Item | Lean | Verdict |
|---|---|---|
| `ι` | `log(card S · card A · T / δ)` | exact |
| `H` | `⌈4/(1−γ)·ι⌉₊` | exact (Nat ceiling; `ι ≥ 1` keeps it positive) |
| `η_i^n` | `onlineQRateWeight H n (i+1)`, `i ∈ range n` | exact (`η_{i}^n` for `i = 1..n`) |
| `k_i − 1` | `visitTime data (s,a) (i−1)` (zero-based index of the `i`-th visit) | exact; `Δ_{k_i−1}` is `delta … (visitTime …)` |
| `run`/`step` | Q/V/count/policy update, strict-increase policy rule, `sel` tie rule | faithful to `:1712–1736` |
| `Δ_t` | `optValue − (run t).V`, with `optValue` the true trajectory value of the greedy optimal policy | exact (`V⋆`) |
| `d_j`, `ρᵀP^j` | `occupancyStateAt (detPolicy πstar) ρ j s` (law of the state at time `j`), times `1{a = πstar s}` | exact |
| `α_j` | `κ^j Σ_{t∈Icc 1 T} Σ_s occ_j(s) Δ_t(s)` | exact (follows the definition, not the proof's `0..T−1`) |
| `θ_j`, `betaTrunc` | `n = 0 ↦ 1/(1−γ)` (= `min{+∞, 1/(1−γ)}`); else `min{3c_b√(Hι/(n(1−γ)²)), 1/(1−γ)}` | exact |
| `ξ_j` | `κ^{j+1} Σ_s occ_{j+1}(s) Δ_0(s)` | exact |
| `ψ_j` | sample `t` is `data ⟨t−1⟩`; `n_t` is `run (t.val+1)`; the ratio is real division | exact; the real `x/0 = 0` only affects sampled pairs with `d^b = 0` (a null event) |
| `φ_j` | `Δ_{t−1}` is `delta … t.val`; factors `γκ^j(1+1/H)²` and `(1+1/H)` placed as printed | exact |
| `C⋆` | `⨆_p ofReal(d⋆(p))/ofReal(d^b(p))` in `ℝ≥0∞` | exact: `0/0 = 0` and `x/0 = ⊤` for `x > 0`; `d⋆` is the normalised joint discounted occupancy `(1−γ)Σγ^t·occJoint` |
| `π⋆` | parameter `πstar`, required to be greedy for `Q⋆` (`optimalityFixedPoint`) | matches "optimal deterministic policy"; the export does not use the hypothesis (see N2) |
| MDP | rewards in `[0,1]`, `0 ≤ γ < 1`, nonempty `S, A` | matches the source model |
| Data law | `X : Ω → Fin T → (S×A)×S`, `iIndepFun`, each marginal `Σ ofReal(d^b(sa)P(s'|sa))•dirac` | exact i.i.d. fresh-sample model |

I found no indexing, junk-value or division discrepancy.

## 3. Statement comparison

| Aspect | Printed | `Lemma6_12_restricted` | Verdict |
|---|---|---|---|
| `c_b` | universal, "sufficiently large" (Thm 6.8 context, as in C28) | `∃ cb₀ > 0, ∀ cb ≥ cb₀` (proof gives `cb₀ = 4`) | faithful |
| constant | universal (hidden in `≲`) | `∃ C > 0` after `cb`, before every instance quantifier (proof gives `C = 400000 + 5600·c_b`) | faithful: `θ` scales like `c_b` (since `β_n ∝ c_b`), so `C` must depend on `c_b`, and `c_b` is universal |
| `δ` | `0<δ<1` | `0<δ<1` | exact |
| `ι` | none stated | added premise `1 ≤ ι` | disclosed restriction (C24); see N1 |
| sample size `T` | proof uses the Theorem 6.8 condition (θ step (iii), Freedman) | none | stronger than the printed context; good |
| `α` | `α = limsup α_j = 0` | `Tendsto α_j → 0` | implies the printed claim (stronger) |
| `ξ` | `Σ ξ_j ≲ (1−γ)^{-2}` | `∃ξ, HasSum ξ_j ξ ∧ ξ ≤ C/(1−γ)²` | exact, and adds convergence |
| `θ` | `≲ √(C⋆STι²/(1−γ)⁵)` | `HasSum` unconditionally; bound under `C⋆ ≠ ⊤` with `card S`, `T`, `ι²` | exact; the guard is needed because `⊤.toReal = 0`, and the printed bound is `+∞` (vacuous) when `C⋆ = ∞` |
| `ψ+φ` | `≲ C⋆ι²/(1−γ)³` | two separate `HasSum`s; bound under `C⋆ ≠ ⊤` | exact. The `ψ` and `φ` series are signed, so separate `HasSum` is the right reading of `ψ = Σψ_j`, `φ = Σφ_j` |
| probability | `≥ 1−δ`, one event for all four claims | `1−δ ≤ μ.real {ω | all four}` | exact (single event) |
| extra hypotheses | — | `sel` maximises and `πstar` is `Q⋆`-greedy | context assumptions of the source; not used by the export (N2) |

**Non-vacuity.** The hypotheses are jointly satisfiable, for example `S = A = 1`, `T = 3`, `δ = 1/2` (`ι = log 6 ≥ 1`), with the canonical product space for `X`. `T = 0` and empty types are excluded automatically, because `ι = log 0 = 0 < 1` in those cases.

## 4. Proof-gap claims T4, T5, T6

**T4 (confidence budget).** Real gap.
- The printed proof uses at least four events (the Lemma 6.10/6.9 event, the prefix-count event, the ψ-Freedman event and the implicit φ-Freedman event). Each is quoted at `1−δ`, yet the lemma concludes `1−δ`.
- The usual "rescale δ" fix is not free here. `δ` enters the algorithm through `H` and `b_n`, so a sub-event at `δ/k` changes the logarithm inside the bound and inside the penalty, and the penalty must still dominate the Azuma radius at `δ/k`.
- The Lean proof runs all five events at `δ/5`. It absorbs `log(2T/(δ/5)) ≤ ι + 3 ≤ 4ι` (`log_ratio_le`, using `ι ≥ 1`) and covers Lemma 6.9 at `δ/5` with `c_b ≥ 4`.
- Severity: routine but genuine. A one-line SOURCE-ISSUES note is warranted.

**T5 (φ on poorly covered pairs).** Real gap.
- In ψ, the poorly covered part is disposed of by sign. The sampled term `−(1+1/H)f^{Iᶜ}(X_t) ≤ 0` is dropped and only `E f^{Iᶜ}`, which is small, remains.
- In φ the signs are reversed. The sampled term `g_t(X_t)` enters positively, while the envelope `≲ C⋆/(1−γ)² + δ/(ST⁴(1−γ)² d^b)` (`eq:fg-envelope-offlineQ-B-defn`) is unbounded as `d^b → 0`.
- The envelope's second term is real, not an artifact. `d̃(s) = γΣκ^j[ρᵀP^j](s)` can exceed `d⋆(s)/(1−γ)` by `(1+1/H)^{3J}` when `s` is reached only at depth `J ≫ H`. So a poorly covered `(s,π⋆(s))` can carry a ratio `d̃/d^b` that is arbitrarily large.
- "Analogously" therefore fails as written. An extra argument is required: either the event that no sample hits a pair with `d^b < δ/(cST)` (probability `≥ 1−δ/c`; this is the Lean route, event `E₃` at `δ/(5ST)`), or a Markov bound on `Σ_t g^{Iᶜ}(X_t)`. Either way it consumes additional confidence budget.
- Severity: a genuine omitted step in an argument the source explicitly omits. A SOURCE-ISSUES note is warranted.

**T6 (nonnegativity of Δ via gated Freedman).** Real gap.
- Lemma `Freedman-prelim` (`prelim.tex`) needs `|X_k| ≤ B` and a deterministic bound `W_n ≤ σ²`. Both the conditional mean and the conditional variance are taken with respect to the summands' own past.
- The source applies the variance bound `E[Z_t²|F_{t−1}] ≲ (C⋆/(1−γ)²) E f_{t−1}` (`:5222`), which uses `f ≥ 0`, i.e. `Δ ≥ 0`. That holds only on the Lemma 6.10 event, which is not predictable as a whole.
- Off that event `f` can be negative, and `f² ≤ B f` fails. In addition, `W_n` in the cited lemma is relative to the natural filtration of the `Z`'s, not `F_{t−1}`.
- The repair is to gate each summand by the `F_{t−1}`-measurable predicate "`V_v ≤ V⋆` for all `v ≤ t−1`". The gated sequence is still a martingale difference sequence, the bounds then hold surely, and gated equals ungated on the pessimism event. The Lean `gateProp` with `freedman_gated_prob` does exactly this, with the data filtration.
- Severity: routine measure-theoretic gap, MINOR. Worth a note, together with the filtration mismatch.

**Related observation (not a gap in the statement).** The printed proof uses the Theorem 6.8 condition on `T` in two places, θ step (iii) and the Freedman step. In the Freedman step it is needed to make `log(2K₀/δ)` with `K₀ ≈ log₂(C⋆T/…)` at most of order `ι`. The Lean proof avoids it: peeling uses `K = T` with `L = log(2T/(δ/5))`, independently of `C⋆`. So the formal lemma holds without any sample-size hypothesis.

## 5. Proof honesty

- The wrapper `Lemma6_12_restricted_holds` takes `cb₀ = 4` and `C = lemma612Const cb` (positivity by `linarith` from `cb ≥ 4`), then `exact lemma612_prob …`. It does not restate the lemma or prove it again.
- `lemma612Conclusion` is syntactically the same conjunction as the entry's set predicate (same `let γ ι Cs`, with `C` replaced by `lemma612Const cb`), so `exact` closes by definitional unfolding.
- The wrapper discards the `sel` hypothesis and the `πstar` optimality hypothesis (`_`). This is honest: the export simply does not need them.
- I scanned the import closure of `Formalization.OfflineRL.LCBQLemma612`, which has 90 project modules, plus `Probe612.lean`, for `sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide|@[extern|ofReduceBool|decide := true`. There were no hits, apart from the probe's two `#print axioms` lines.
- I did not run `#print axioms`. `audit-integration.out` (22:16) reports "Axiom audit passed for 10285 project declarations", but it predates the 23:08 `LCBQLemma612.lean`. A post-integration audit is still required.

## 6. Findings

**BLOCKING:** none.

**MAJOR:** none.

**MINOR**
- **M1.** The proof gaps T4, T5 and T6 are real (section 4). The index entry is fine, but `SOURCE-ISSUES.md` should record them as printed-proof gaps that do not change the statement. Suggested text is below.
- **M2.** The probe is not yet in `Formalization/Statements/Ch6.lean` and `Ch6Proofs.lean`. Docstrings citing `offlineRL.tex:2309–2324` (label at `:2310`), definitions `:1970–2015` and `:2276`, and C24 still need to be added. The `Ch6.lean` entry must import only `LCBQDefinitions`, which suffices for the `Prop`. A post-integration axiom audit is required (the existing audit output predates the final library file).

**NOTE**
- **N1.** The premise `ι ≥ 1` is sufficient, not minimal.
  - I checked numerically (scratch grid over `γ ∈ (0,1)`). For `ι < 3/4` there are instances with `κ = γ(1+1/H)³ ≥ 1` (for example the C24 instance `γ = 1/2`, `ι ≤ 1/8`), and there `α = ∞` on a single instance.
  - For `ι ≥ 0.8`, `(1−κ)/(1−γ) ≥ 1/16` holds uniformly, so the printed lemma very plausibly holds for every `ι ≥ c` with any fixed `c > 3/4`, at a larger constant.
  - The restriction therefore also excludes `ι ∈ (3/4, 1)`. That region requires `SAT ≤ 2` and `δ ∈ (SAT/e, 1)` and plausibly satisfies the printed claim. It is degenerate, and `ι ≥ 1` matches the C22 premise, so this is acceptable. The disclosure should say "sufficient", not "exactly the false region".
  - The θ counterexample in C24 needs `ι → 0`, so no single threshold separates "true" from "false" under a universal-constant reading.
  - No other part of the printed claim is excluded: `T = 0` and empty `S` or `A` are outside the printed scope anyway (ι is undefined).
- **N2.** The entry carries the hypotheses "`sel` maximises" and "`πstar` is `Q⋆`-greedy", which the export does not use. They match the source context, so the entry is not weakened. Readers should know the formal result holds for any deterministic `πstar` (C⋆ then refers to that policy).
- **N3.** The source's α proof display sums over `t = 0..T−1`, while the definition `eq:alpha-j-offlineQ` sums over `1..T`. This is harmless (both are bounded by `T/(1−γ)`), and Lean follows the definition. No issue entry is needed.
- **N4.** The formal statement needs no sample-size condition, while the printed proof uses Theorem 6.8's condition (section 4, related observation). The entry is therefore at least as strong as the printed lemma in its context. This is not a discrepancy.
- **N5.** The entry is in the `_restricted` form only because of `ι ≥ 1`. The `∃cb₀ ∀cb` quantifier and the `C⋆ ≠ ⊤` guards are faithful readings, not restrictions, and should be described that way in the docstring.

## 7. Suggested SOURCE-ISSUES text

Disclosure bullet (under "Statement-index scope disclosures"):

> - Lemma 6.12 (`lem:lcbq-alpha-xi-psi-phi-bound`, `offlineRL.tex:2309–2324`) is indexed as `Lemma6_12_restricted`. It has the added premise `log(SAT/δ) ≥ 1`, which is sufficient for `κ < 1` and `H ≍ ι/(1−γ)`; the printed lemma fails for small `ι` (see [C24](#C24)). The premise is not minimal: any `ι ≥ c > 3/4` would do with a larger constant, and the excluded band requires `SAT ≤ 2`. The source's `c_b` "sufficiently large" is stated as `∃ c_b₀, ∀ c_b ≥ c_b₀` (`c_b₀ = 4`, as in [C28](#C28)). The `≲` constant is an existential `C` that depends only on `c_b` (`C = 400000 + 5600 c_b`). `α = 0` is stated as `α_j → 0`; `ξ, θ, ψ, φ` are stated as `HasSum` limits. The `θ` and `ψ+φ` bounds are stated under `C⋆ < ∞`, since otherwise the printed right sides are `+∞`. No sample-size condition on `T` is assumed, although the printed proof uses Theorem 6.8's. The hypotheses that `π⋆` is optimal and that ties are broken by a maximiser are carried as in the source but are not used.

Proof-gap note (new candidate, or appended to C24):

> **Candidate C29: Lemma 6.12 proof — confidence budget, φ on poorly covered pairs, and Freedman on a non-predictable event.** Source: proof of `lem:lcbq-alpha-xi-psi-phi-bound`, `offlineRL.tex:4786–5496`.
> (1) The proof combines the Lemma 6.10 event, the prefix-count event (`eq:prefix-count-lower-bound-lcbq`) and two Freedman events, each at confidence `1−δ`, but concludes `1−δ`. Rescaling is not free, because `δ` enters `H` and `b_n`. Repair: run each event at `δ/5`, absorb `log 5` into `ι ≥ 1`, and take `c_b` large enough for Lemma 6.9 at `δ/5`.
> (2) The `φ` bound is omitted as "analogous" (`:5483–5485`), but the sign that disposes of poorly covered pairs in `κ₁` is reversed in `φ`. The sampled term `g_t(X_t)` enters positively, with envelope `≲ C⋆/(1−γ)² + δ/(ST⁴(1−γ)²d^b)`, which is unbounded as `d^b → 0`, because `d̃` can exceed `d⋆/(1−γ)` by `(1+1/H)^{3J}` at depth `J ≫ H`. Repair: intersect with the event that no sample hits a pair `(s,π⋆(s))` with `d^b < δ/(5ST)` (probability `≥ 1−δ/5`).
> (3) Freedman (`lem:Freedman-prelim`) is applied with the conditional-variance bound `E[Z_t²|F_{t−1}] ≲ C⋆(1−γ)^{-2} E f_{t−1}`. That bound uses `Δ ≥ 0`, which holds only on the Lemma 6.10 event, not predictably. The cited lemma also conditions on the summands' own past rather than on `F_{t−1}`. Repair: gate each summand by the `F_{t−1}`-measurable predicate `V_v ≤ V⋆ ∀ v ≤ t−1` and apply Freedman with the data filtration; on the pessimism event, gated equals ungated.
> The statement of Lemma 6.12 (under `ι ≥ 1`) is unaffected. The formal proof follows these repairs and needs no sample-size condition (its Freedman peeling uses `log(2T/(δ/5)) ≤ 4ι`).

## VERDICT (pre-cross-check)

**ACCEPT the `Lemma6_12_restricted` statement and wrapper as a faithful restricted index entry**, conditional on:
- (a) adding the disclosure bullet;
- (b) recording the T4–T6 proof gaps (M1);
- (c) placing the entry in `Ch6.lean`/`Ch6Proofs.lean` and running the post-integration axiom audit (M2).

There are no blocking or major findings.

## 8. Cross-check (written after sections 1–7)

I read `the private independent check note (Thm6_8-log)` and `docs/critic-lemma6-9-6-10.md` only after writing the sections above.

- **the private independent check note (Thm6_8) §4(B).** Its small-ι counterexamples and its `ι ≥ 1` analysis (`κ ≤ γe^{3(1−γ)/4} < 1`, `1−κ ≳ 1−γ`, `H ≍ ι/(1−γ)`) agree with my N1. That checker explicitly left two points for this critic: "T-condition not needed once ι ≥ 1" and "ψ+φ under ι ≥ 1".
  - My contribution on those two points is at the level of proof structure. I confirmed that the formal Freedman uses `L = log(2T/(δ/5)) ≤ 4ι`, with no dependence on `C⋆`, and that the library export has no `T` premise.
  - I did not re-derive every line of `LCBQPsiPhi`/`LCBQFreedman612`. Their correctness rests on compilation, and the compile output and axiom audit for the final files were not observed by me (NOTE-3 of the Lemma 6.9/6.10 critic applies equally here).
- **docs/critic-lemma6-9-6-10.md MINOR-1 (tie-rule scope).** This does not affect Lemma 6.12. All five sequences depend only on `V_t`, `n_t` and `Δ_t`, which do not depend on `sel`. The export takes no `hsel`, so the result holds for every tie rule, including history-dependent ones.
- **docs/critic-lemma6-9-6-10.md §7 advisory on the Step-3 definitions.** It reaches the same conclusion as my section 2. I additionally checked `occupancyStateAt` (the state law at time `j` under the stationary policy), which settles that critic's caveat.

## VERDICT

**PASS WITH REQUIRED DISCLOSURE.**

`Lemma6_12_restricted` faithfully states Lemma 6.12 under the added premise `log(SAT/δ) ≥ 1`. The five sequences, `C⋆`, `β`/`betaTrunc`, the indexing and the ratio conventions all match the source exactly. The quantifier order `∃cb₀ ∀cb ∃C ∀instance` is the right reading of "c_b universal, sufficiently large" plus `≲`. The `HasSum` and `Tendsto` encodings and the `C⋆ ≠ ⊤` guards are at least as strong as the printed claims. No sample-size premise is hidden; the formal result is stronger than the printed proof's context. The wrapper only applies `lemma612_prob`, and the forbidden-token scan of the 90-module import closure is clean.

There are no BLOCKING or MAJOR findings. Before landing, three things are required:
1. the disclosure bullet;
2. a SOURCE-ISSUES note recording the confirmed printed-proof gaps T4 (confidence budget), T5 (φ on poorly covered pairs) and T6 (Freedman on a non-predictable event and filtration mismatch);
3. the post-integration compile and axiom audit.
