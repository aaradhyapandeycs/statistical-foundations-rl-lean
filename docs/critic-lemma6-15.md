# CRITIC — Lemma6_15 (`lem:transition-KL-bound-infinite`) and candidate C21 — brief B2, direct session

Public copy of the independent critic report; local paths removed.

- Report started (UTC): 2026-11-06T17:11:07Z. Part A (reconstruction + comparison) written before reading
  `docs/SOURCE-ISSUES.md`; Part B (C21) appended afterwards.
- Reviewer identity: fresh Claude Code desktop session (model `claude-opus-5-5`), opened directly by the human for brief B2.
  This session did not write or edit any Lean code under review, did not build any held proof, and spawned no agents.
- Mode: SOURCE-ONLY. No Lean, lake, lean-lsp, compiler or axiom probe was run. No proof, source, ledger, Git or dependency
  change. Only files written: this report, plus one appended notification line in `the lead's private progress log`
  (requested by the human in this session). A scratch numeric probe (Python, no project imports) lives outside the tree at
  (local scratch path omitted).
- Independence: before Part A was written, this session had NOT read `docs/PROGRESS.md`, `docs/COVERAGE.md`,
  `docs/SOURCE-ISSUES.md`, any critic report, or anything under `../`. It had read `the lead's private progress log`
  (operational log, mentions C21 only by name) and the provider file's module docstring (`LowerBoundFamilyKL.lean:14–16`),
  which itself states the mis-citation. The mis-citation was found independently from the TeX (see F1 and its timeline note)
  before the provider was opened.

## Inputs (SHA256, computed in this session at 2026-11-06T17:11Z)

Git HEAD `6bac672b2956953c2587c9785cda8de7a5b6eb72`, branch `batch-ch2-ch3-ch6-20261106`; held files uncommitted.

| File | SHA256 |
| --- | --- |
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` |
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` (= provenance pin) |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` (= provenance pin) |
| `Formalization/Statements/Ch6.lean` | `f9fb13de3797e0d240635b31e3ee12cca72eded02874ba03729eb21922eb7d5e` (= brief pin) |
| `Formalization/Statements/Ch6Proofs.lean` | `d80a704b5693f0181a8b6f2df3c9bd3169eadfc87506392e51995b169b147542` (= brief pin) |
| `Formalization/OfflineRL/LowerBoundFamilyKL.lean` (untracked) | `e9e75e8fcae3cd14f776c7b2ede0814677ca1387f8f6c6202a7375f737fef221` |
| `Formalization/OfflineRL/LowerBoundFamilyDefinitions.lean` | `66f9222bdcef5f5d48521d12b6900e165fc9dcebbe59c9a9f882fddd85ec6220` |
| `Formalization/Probability/FiniteSampleDefinitions.lean` | `baa436abfb5988ab409cec759899fe944a05a7cd64bcb07fd8a8899a85f1a772` |
| `Formalization/MDP/CoreDefinitions.lean` | `68bf277b85a22ce7f2e8aee6f4ebc2bb3e06c6eb8b047519a79f0a468c1d4102` |
| `Formalization/Generative/GenerativeLowerBoundBernoulli.lean` | `e448cc57b89ace8b91fd65d0cd2a7999c17970e7c58381ff78de073488fe74f1` |
| `Formalization/Generative/GenerativeLowerBoundKLAffinity.lean` | `15a65644d6489fec79dc127efe58ba00cb33ff03b0a3dfc9483e5c9daf35bded` |
| `Formalization/Generative/GenerativeLowerBoundProductKL.lean` | `4adc447c85e1b0366ec772ab590542163782eac775cfec6670b7f066adffa884` |
| `Formalization/Generative/GenerativeLowerBoundWeightedLog.lean` | `bf58dbfbfc577623377081a20d1b88577b69ee9bba6dc30429b642048ae5e764` |
| `Formalization.lean` | `697052168941c159e83d54a657a736da1d37e74290ab7f51ce6e04bf3b0e90a1` |
| `Audit.lean` | `29f6cd54e69586325be78af79809bda1f1d1c2b0c52f03ad3746eb6e8c3d06f3` |
| `AGENTS.md` | `1e28b54cc339575657234bd92b3e53f82c6d347ecd3bf37f0f000a4a4af12579` |
| `RECOVERY-HANDOFF.md` | `da38e5658271f22d79e7b9e1f8fc1ae38a44cb100a36b4f7b38c7a4bff0f22ab` |
| `the private review brief` | `f0aa72881558a78727fa58c76d57b6494a33723829840ad24dab7f8cf9bffa1a` (differs from the `ad4fdf6d…` recorded in PROGRESS at 17:00:14Z; the B2 section's input pins it lists still match the files above) |
| `skills/lean/skills/lean-workflow/SKILL.md` | `610ba087e203fef78d71da314dfbf144f5b76182fb71781ee2c64337d941cd07` |
| `skills/lean-research-practice/SKILL.md` | `b09387acb01b2b3873eb9129e29348020394a0fc2d6676c04e9498c68debc34c` |
| `skills/lean-probability-rl/SKILL.md` | `e5bb820c212ab27a780b6a442daca951c0c706c5ead29f29ebbb7f498c57f184` |
| `skills/lean-probability-rl/references/rl-models.md` | `27c746f2113ea489d501e8c0c311509a9c49d1b1b73649607291086d14c057e0` |
| `skills/lean/skills/lean-statement-audit/SKILL.md` | `2c315ad231e93a198ef2960dadc67234c263a0f4a4adf858aeb2d9270007dfab` |

`docs/SOURCE-ISSUES.md` hash is recorded in Part B (read only after Part A).

## Part A.1 — Source reconstruction from the pinned TeX alone

Locators (offlineRL.tex unless noted): standing assumptions `:2440–2445`; family `:2452–2457`; `S`, `A` `:2459–2462`;
`μ` and `C > 2` `:2468–2476`; `P_θ` `:2479–2489`; `p, q` `:2492–2495`; `p > q ≥ γ-(1-γ)/2 ≥ 1/2` `:2499–2502`;
`Θ` (Gilbert–Varshamov) `:2519–2529`; **Lemma 6.15 environment `:2835–2865`** (label `:2836`); proof `:5680–5791`;
cited `lem:KL-quadratic-lower-bound` prelim.tex `:1335–1346` (proof `:1349ff`).

Setting. `𝒮 = {0,…,S-1}`, `𝒜 = {0,1}`, `θ ∈ Θ ⊆ {0,1}^{S-1}` indexed by `s = 1..S-1`.
Standing: `2/3 ≤ γ < 1` and `224(1-γ)ε/γ ≤ 1/2` (`eq:infinite-epsilon-assumption`); `C > 2`.
`μ(s) = 1/(C(S-1))` for `s > 0`, `μ(0) = 1 - 1/C`. For `s > 0`:
`P_θ(s'|s,θ_s) = p·1{s'=s} + (1-p)μ(s')`, `P_θ(s'|s,1-θ_s) = q·1{s'=s} + (1-q)μ(s')`;
`P(·|0,0) = δ_0`, `P(·|0,1) = (2γ-1)δ_0 + 2(1-γ)μ`; rewards `1` at `s>0`, `4/7` at `(0,0)`, `0` at `(0,1)`;
`p = γ + 224(1-γ)²ε/γ`, `q = γ - 224(1-γ)²ε/γ`.

Statement (`:2838–2864`): for any `θ, θ̃ ∈ Θ` and any `s > 0`:
(i) if `θ_s = θ̃_s`, then for every `a ∈ {0,1}`, `KL(P_θ(·|s,a) ‖ P_θ̃(·|s,a)) = 0`;
(ii) if `θ_s ≠ θ̃_s`, then for every `a ∈ {0,1}`, `KL(P_θ(·|s,a) ‖ P_θ̃(·|s,a)) ≤ c₃(1-γ)³ε²`,
"where `c₃ > 0` is some universal constant" (`:2864`) — i.e. `∃ c₃ > 0` chosen before `S, γ, ε, C, θ, θ̃, s, a`.

Implicit domain facts. `S ≥ 2` (for `s > 0` to exist; Theorem 6.13 assumes `S > 12`, `:2371`). `ε` is an accuracy level;
neither `:2442` nor Theorem 6.13 (`:2369–2372`) states its sign, but `p > q` (`:2501`) and `p ≥ γ` (`:5774`) presuppose
`ε > 0` (resp. `ε ≥ 0`), and well-formedness of `P_θ` needs `q ≤ 1`.

Independent re-derivation (no Lean consulted). Rows at `s>0` differ only in the self-loop mass; with
`α = 1 - 1/(C(S-1))`, `P(s'=s) = αx + (1-α)` for `x ∈ {p,q}`, and conditionally on `s' ≠ s` both rows equal
`μ(·|𝒮∖{s})`. Chain rule ⇒ `KL(row_x ‖ row_y) = KL(Bern(u_x) ‖ Bern(u_y))`, `u_x = x + (1-x)μ(s)`. Full support holds
(`μ > 0` since `C > 2`, and `p, q < 1`), so every KL is finite. By the chi-square bound (clause 1 of the cited lemma),
`KL(Bern(u)‖Bern(v)) ≤ (u-v)²/(v(1-v))`; with `u-v = α(x-y)`, `1-v = α(1-y)`, `v ≥ 1/2`, `1-y ≥ (1-γ)/2` (both rows),
`KL ≤ (x-y)²/(v(1-y)) ≤ 4(p-q)²/(1-γ)`. Since `p - q = 448(1-γ)²ε/γ` and `1/γ ≤ 3/2`:
`KL ≤ 4·448²(1-γ)³ε²/γ² ≤ 9·448²·(1-γ)³ε² = 1,806,336·(1-γ)³ε²`. Note `9·448² = 16·336²` exactly.
Both orientations (`θ_s = 0, θ̃_s = 1` and the reverse; `a = 0, 1`) are covered by the same bound, so the source's
WLOG (`:5687–5689`) is harmless even though KL is asymmetric. Case (i) is trivial: the rows coincide.

## Part A.2 — Lean statement, wrapper and provider (as read; not compiled by this session)

- Statement `def Lemma6_15 : Prop` — `Formalization/Statements/Ch6.lean:175–188` (docstring `:168–174`).
- Wrapper `theorem Lemma6_15_holds` — `Formalization/Statements/Ch6Proofs.lean:97–99`:
  `⟨16 * 336 ^ 2, by norm_num, fun … => lb_transition_kl m hm γ ε C hγ hγ1 hε hεmax hC θ θ' i a⟩`. Pure application;
  no restatement, no extra premise, constant supplied explicitly. Both files imported by `Formalization.lean:704–705`;
  provider imported at `Formalization.lean:105`.
- Provider `lb_transition_kl` — `LowerBoundFamilyKL.lean:172–263`; its type (`:172–183`) is token-for-token the body of
  `Lemma6_15` with `c₃` instantiated to `16 * 336 ^ 2`.
- Family `lbMDP` — `LowerBoundFamilyDefinitions.lean:66–107`; `lbGap/lbP/lbQ` `:23–29`; `lbMu` `:32–34`; `lbRow` `:37–63`.
- KL objects: `InformationTheory.klDiv` (Mathlib, `ℝ≥0∞`); `FiniteDistribution.rowMeasure = toPMF.toMeasure`
  (`FiniteSampleDefinitions.lean:25–26`) with `toPMF` = `PMF.ofFintype (ENNReal.ofReal ∘ prob)` (`:13–17`), measurable
  space fixed in the type by `local instance finiteSampleStateMeasurable : MeasurableSpace State := ⊤` (`:21`).
- Proof chain: `lbRow_klDiv_eq` (`:65–124`, KL of two mixed rows = `bernoulliKLExpression(u, v)`, finite) via
  `finite_klDiv_eq_expression` (`GenerativeLowerBoundKLAffinity.lean:41–53`, oriented `∑ μ{x}·log(μ{x}/ν{x})`,
  `finiteKLExpression` at `GenerativeLowerBoundWeightedLog.lean:40–41`) and `finite_fullSupport_ac`
  (`GenerativeLowerBoundProductKL.lean:11–18`); `lb_bernoulli_mixed_le` (`:127–169`) via
  `bernoulliKLExpression_le_quadratic` (`GenerativeLowerBoundBernoulli.lean:12–24`, the chi-square bound, proved from
  `log t ≤ t - 1`); main case split `:248–263`; equal case via `klDiv_self` (`:188–191`).

## Part A.3 — Field-by-field comparison and binder table

Encoding (`LowerBoundFamilyDefinitions.lean`): states `Option (Fin m)`, `S = m+1`, `none ↔ 0`, `some i ↔ i+1`;
actions `Bool`, `false ↔ 0`, `true ↔ 1`; `θ : Fin m → Bool`, `θ i ↔ θ_{i+1}`.
- `μ`: `lbMu C m none = 1 - 1/C`, `lbMu C m (some _) = 1/(C*m) = 1/(C(S-1))` ✓ (`:32–34`).
- `P_θ` at `s>0`: `if a = θ i then lbRow (some i) p else lbRow (some i) q`, `lbRow o x = x·1{t=o} + (1-x)·μ(t)` ✓
  (`:84–90`, `:39`); the `else` branch is `a = !θ i = 1-θ_s` ✓.
- `P(·|0,0) = lbRow none 1 = δ_0` ✓; `P(·|0,1) = lbRow none (2γ-1) = (2γ-1)δ_0 + 2(1-γ)μ` ✓ (`:82–83`).
- `p = γ + 224(1-γ)²ε/γ`, `q = γ - 224(1-γ)²ε/γ` ✓ (`:23–29`). Rewards `1 / 4/7 / 0` ✓ (`:91–94`). Discount `γ` ✓.
- Same `m, γ, ε, C` for `M` (θ) and `M'` (θ') ✓; same `(some i, a)` on both sides ✓.
- KL direction: `klDiv (M…).rowMeasure (M'…).rowMeasure` = `KL(P_θ ‖ P_θ')` ✓ (and the statement is universally
  quantified over ordered pairs, so it would be orientation-robust anyway).
- σ-algebra: the row measures live on `⊤` (discrete) by their type, so `klDiv` is the full discrete KL; no coarsening
  that could make the bound vacuous. `ENNReal.ofReal` of the nonnegative real `c₃(1-γ)³ε²` is exact, and `≤ ofReal r`
  additionally certifies finiteness — the Lean conclusion is at least as strong as the printed real inequality.
- Quantifier order: `∃ c₃ : ℝ, 0 < c₃ ∧ ∀ m hm γ ε C … θ θ' i a, …` — constant precedes every parameter ✓ (universal).
- Both clauses (i) `= 0` and (ii) `≤` present, with the right antecedents `θ i = θ' i` / `θ i ≠ θ' i` ✓.

Binder table (15 logical inputs of `Lemma6_15`; project bundles expanded — `lbMDP` takes only these hypotheses):

| Binder | Bin | Source / reason |
| --- | --- | --- |
| `∃ c₃`, `0 < c₃` | SOURCE | `:2864` universal constant `c₃ > 0` |
| `m : ℕ` | TYPING | `S = m + 1` |
| `hm : 1 ≤ m` | TYPING | `S ≥ 2`, needed for `s > 0` and `1/(C(S-1))`; weaker than Thm 6.13's `S > 12` |
| `γ ε C : ℝ` | TYPING | carriers |
| `hγ : 2/3 ≤ γ` | SOURCE-standing | `:2442` |
| `hγ1 : γ < 1` | SOURCE-standing | `:2442` |
| `hε : 0 ≤ ε` | TYPING | implicit sign of the accuracy level; needed for `q ≤ 1`, used by the source at `:2501`, `:5774` |
| `hεmax : 224*(1-γ)*ε/γ ≤ 1/2` | SOURCE-standing | `:2442`, same form |
| `hC : 2 < C` | SOURCE-standing | `:2474` |
| `θ θ' : Fin m → Bool` | SOURCE (generalised) | `θ, θ̃ ∈ Θ ⊆ {0,1}^{S-1}` (`:2838`); Lean takes all of `{0,1}^{S-1}`, which implies the statement for every `Θ` |
| `i : Fin m` | SOURCE | `s > 0` |
| `a : Bool` | SOURCE | `a ∈ {0,1}` |

Counts (15 inputs, counting `γ`, `ε`, `C`, `θ`, `θ'` separately): SOURCE 5 (`c₃`, `θ`, `θ'`, `i`, `a`),
SOURCE-standing 4 (`hγ`, `hγ1`, `hεmax`, `hC`), TYPING 6 (`m`, `hm`, `γ`, `ε`, `C`, `hε`), RULED 0, EXCESS 0.
("SOURCE-standing" = printed standing assumption of the construction, not an independently audited project
standing-assumption record; no such record exists for this family.)

Forbidden-token text grep (`sorry admit axiom opaque implemented_by unsafe native_decide`) over the 11 chain files listed
in the input table plus `EmpiricalRow.lean`: no hits. A tree-wide grep finds only prose in three unrelated docstrings
(`QLearningLateRateSchedule.lean:63`, `QLearningRobustDefinitions.lean:19`, `SingletonAction.lean:58`). This is a
preliminary text check only; the transitive import closure of `GenerativeLowerBoundKLAffinity` was not read in full.
`Ch6.lean` contains no `theorem`/`by` lines (grep). `Audit.lean:9` allows exactly `propext`, `Classical.choice`,
`Quot.sound`.

Independent check of the provider's arithmetic (source reasoning, not compilation): `lbGap ≤ (1-γ)/2` from `hεmax`
(`:193–197`); `lbGap ≤ 336(1-γ)²ε` from `γ ≥ 2/3` (`:198–202`); `p, q ∈ (1/2, 1)` and `1-p, 1-q ≥ (1-γ)/2`
(`:240–247`); `4(2·lbGap)² ≤ 16·336²(1-γ)⁴ε²` (`:210–216`); Bool trichotomy for the second case (`:255–257`). All
consistent with Part A.1.

## Part A.4 — Findings (before reading SOURCE-ISSUES)

- **F1 — MINOR (source proof, not a formalization defect; candidate source issue).** offlineRL.tex `:5722–5733`
  (a = 0): "Applying Lemma~\ref{lem:KL-quadratic-lower-bound} then yields `KL ≤ (u-v)²/(u(1-v))`". The cited lemma
  (prelim.tex `:1337–1345`) gives only `(u-v)²/(v(1-v))` (clause 1, `0<p,q<1`) and `KL(u‖v) ≤ KL(v‖u) ≤ (u-v)²/(u(1-u))`
  (clause 2, `1/2 ≤ v < u < 1`). Since `v < u` and `1-v > 1-u`, `(u-v)²/(u(1-v))` is strictly smaller than both, so it
  does not follow from either clause. It is also false on clause 2's own range: `u = 0.99, v = 0.5` gives
  `KL ≈ 0.6371 > (u-v)²/(u(1-v)) ≈ 0.4851`. In the construction's regime, a random sweep (400,000 samples,
  `γ ∈ [2/3,1)`, admissible `ε ≥ 0`, `C ∈ (2,10⁴]`, `m ≤ 10⁶`) found `KL/((u-v)²/(u(1-v))) ≤ 0.909` — numerical
  evidence only, not a proof that the displayed step is true there. Either way the printed step is unjustified by its
  citation. The final per-action bound is unaffected: clause 2 gives
  `(u-v)²/(u(1-u)) = α(p-q)²/(u(1-p)) ≤ (p-q)²/(p(1-p))` directly, and clause 1 gives `(p-q)²/(q(1-q)) ≤ (p-q)²/(p(1-p))`
  because `x(1-x)` decreases on `[1/2,1]`. The a = 1 display `≤ (p-q)²/(q(1-p))` (`:5751–5759`) is valid via clause 1
  (`(u-v)²/(u(1-u)) ≤ (p-q)²/(q(1-p))`). Lemma 6.15's statement therefore stands; only the a = 0 intermediate step is
  mis-cited. Lean takes the clause-1 route (`LowerBoundFamilyKL.lean:142–143`), which is an alternative proof: the Lean
  result does **not** certify the printed a = 0 step, and should not be described as checking it.
  Timeline: the general counterexample was computed while reading the TeX and prelim lemma, before any Lean file was opened.
- **F2 — MINOR (locator).** `Ch6.lean:168` cites `chapters/offlineRL.tex:2833–2862`; the lemma environment is `:2835–2865`
  and the printed sentence fixing the quantifier of `c₃` ("where `c₃>0` is some universal constant") is at `:2864`,
  outside the cited range. The proof locator `:5680ff` should be `:5680–5791`. Same range is used in the provider
  docstring (`LowerBoundFamilyKL.lean:9`). Not a mathematical issue.
- **F3 — NOTE (domain).** `hε : 0 ≤ ε` is not printed in `:2442` or Theorem 6.13, but it is the implicit convention the
  printed argument uses (`p > q` at `:2501`, `p ≥ γ` at `:5774`) and is needed for `P_θ` to be a kernel in general. The
  Lean entry includes `ε = 0` (rows coincide, bound 0), so it is not narrower than the source's intended `ε > 0`.
  Classified TYPING, not EXCESS.
- **F4 — NOTE (generalisation, allowed by AGENTS "export implies printed").** Lean quantifies over all
  `θ, θ' ∈ {0,1}^{S-1}` (not only Θ) and all `S ≥ 2` (not only `S > 12`), and concludes finiteness of KL in `ℝ≥0∞`.
  All three strengthen the printed statement; none is a discrepancy.
- **F5 — MINOR (hygiene, outside the mathematics).** `Ch6.lean` imports `Formalization.Probability.FiniteSampleDefinitions`
  twice (`:7` and `:9`). Harmless. The two imports Lemma6_15 needs (`LowerBoundFamilyDefinitions`,
  `FiniteSampleDefinitions`) are definition modules (their only proofs are structure-field obligations inside defs).
  Whether `MDP.DiscountedOccupancy` / `MDP.OptimalTrajectoryValue` (imported for other entries) are definition-only was
  not checked (outside B2).
- **F6 — NOTE (needs Lean-side confirmation).** The provider elaborates under `local instance lbStateMeasurable :
  MeasurableSpace (Option (Fin m)) := ⊤` (`LowerBoundFamilyKL.lean:23`), while the statement's row measures carry
  `finiteSampleStateMeasurable := ⊤` in their type. Both are `⊤`, so the mathematics is identical and `exact` should
  succeed by unfolding; the actual elaborated types of `Lemma6_15` and `lb_transition_kl`, and whether `klDiv`'s
  measurable-space argument is implicit or instance-implicit in the pinned Mathlib, were not inspected (Mathlib not read
  locally; no LSP). Semantics of `InformationTheory.klDiv`, `klDiv_self`, `klDiv_ne_top_iff` and
  `toReal_klDiv_of_measure_eq` are assumed from their names and use, needing Lean-side confirmation.

Comparison verdict for the statement (Part A, before C21): no BLOCKING or MAJOR source-correspondence finding. The
statement, constant, domain, endpoints, KL direction, quantifier order and the hard-family encoding match the source.

## Part B — Candidate C21 judgement (read after Part A, at 2026-11-06T17:13Z)

Input: `docs/SOURCE-ISSUES.md` sha256 `3d113729e6b40874e1692cb9f3d55f02bf701c2ae5e95431f0791c3c28014b9a` (= brief pin),
section "Candidate C21" lines `757–773` (end of file). Nothing else in `docs/` was read.

Claim-by-claim:

| C21 claim (line) | Judgement |
| --- | --- |
| Proof bounds `KL(Bern(u)‖Bern(v))` by `(u−v)²/(u(1−v))` for `u > v ≥ 1/2`, citing Lemma 2.13 (`:762–763`) | CORRECT. offlineRL.tex `:5721–5733`; `u ≥ p > q` and `v ≥ q ≥ 1/2` give the stated range. `lem:KL-quadratic-lower-bound` is Lemma 2.13 per the project index (`Ch2.lean:147`) and is the 13th numbered statement environment in prelim.tex outside comments (count only, PDF numbering not checked). |
| Lemma 2.13 gives `(u−v)²/(v(1−v))` or `(u−v)²/(u(1−u))`; both are at least `(u−v)²/(u(1−v))` (`:764–765`) | CORRECT for `v < u` (prelim.tex `:1337–1345`). Matches F1. |
| Cited inequality false in general; `u=0.99, v=0.5`: `KL ≈ 0.637 > 0.485` (`:765–767`) | CORRECT; reproduced independently (0.6371 vs 0.4851). Note the counterexample lies inside clause 2's own range `1/2 ≤ v < u < 1`, i.e. inside the region the proof claims to use, which makes the point stronger than "as a general statement". |
| "An earlier independent source review found no violation on the proof's actual parameter region" (`:767–768`) | NOT VERIFIABLE from C21: no locator to that review. This session's own 400,000-sample sweep also found none (max ratio 0.909), but both are numerical evidence, not a proof that the printed step is true in-regime. The entry should cite that review's path and say "numerical" if it was. |
| Lemma conclusion unaffected; clause 1 with reference parameter `v` gives the same `(p−q)²`-type bound (`:768–770`) | CORRECT in substance (Part A.1 derivation). "Same `(p−q)²`-type bound" is loose: clause 1 yields `(p−q)²/(q(1−q))`, which reaches the printed `(p−q)²/(p(1−p))` only with the extra fact that `x(1−x)` decreases on `[1/2,1]`; it yields the final `c₃(1−γ)³ε²` form directly. C21 omits the more direct repair: clause 2 gives `(u−v)²/(u(1−u)) ≤ (p−q)²/(p(1−p))` exactly as printed next. |
| Formal proof takes that route with `c₃ = 16·336²` (`:770–772`) | CORRECT: `LowerBoundFamilyKL.lean:142–143` (clause-1 bound `bernoulliKLExpression_le_quadratic`), wrapper `Ch6Proofs.lean:98`. `16·336² = 9·448² = 1,806,336`, the constant obtained independently in Part A.1. |
| "Printed-proof gap, not an error in the lemma's statement" (`:772–773`) | CORRECT. Consistent with AGENTS: the export implies the printed statement, so the non-suffixed `Lemma6_15` entry (no `_corrected`) is the right form, and recording the proof gap as a Candidate is appropriate. |

C21 additional notes:
- C21-N1 (MINOR): C21 repeats the imprecise locator "lemma at lines 2833–2862"; the environment is `:2835–2865` (F2).
  The display it names, `eq:KL-single-action-bound-infinite-proof`, is correctly identified (label at `:5740`).
- C21-N2 (NOTE): C21 is silent on the a = 1 display (`:5751–5759`, label `:5757`); this session finds that display valid
  via clause 1, so nothing is missing there.
- C21-N3 (NOTE): since Lean uses an alternative route, C21 and any coverage wording should say the printed a = 0 step
  remains unvalidated (it is not "formally checked"). C21's wording does not claim otherwise.

C21 verdict: **CONFIRMED** — the mis-citation finding is correct and the harmlessness claim is correct; three minor
wording/locator improvements above (C21-N1, the missing evidence path for the "earlier review", and the loose
"same bound" phrasing). No change to the Lemma6_15 statement is warranted.

## Explicit limits

- Source inspection only. This is NOT a fresh compile, NOT an elaborated-type check and NOT a transitive axiom audit of
  `Lemma6_15_holds` / `lb_transition_kl`. Those remain open and belong to the exact-current-tree validation that is
  running in slot 1 (started 17:04:09Z per PROGRESS); this session did not inspect its log or the fullcheck2 receipt.
- Mathlib declarations (`klDiv`, `klDiv_self`, `klDiv_ne_top_iff`, `toReal_klDiv_of_measure_eq`, `PMF.toMeasure`) were
  not read; their semantics are assumed from use and need Lean-side confirmation (F6).
- The transitive import closure of `GenerativeLowerBoundKLAffinity.lean` was not read; the forbidden-token grep is a
  preliminary text check, not `#print axioms` evidence.
- The numerical sweep is evidence about the printed a = 0 step, not proof; nothing in the verdict depends on it.
- Not reviewed: Lemma 6.14, Theorem 6.13, the downstream use of Lemma 6.15 in `eq:single-sample-KL-infinite` /
  `eq:KL-bound-infinite`, the other B-briefs, and the printed number "6.15" against the PDF.
- Missing evidence is not a mathematical failure: no finding above shows the Lean statement or its provider to be
  mathematically wrong.

## Severity summary

BLOCKING 0 · MAJOR 0 · MINOR 3 (F1 source-proof mis-citation = C21; F2 locator; F5 duplicate import) ·
NOTE 3 (F3, F4, F6) · C21 notes: 1 MINOR, 2 NOTE.

VERDICT: PASS-WITH-FINDINGS (source correspondence of `Lemma6_15` and wrapper/provider chain, source-only); C21 CONFIRMED.
Lemma6_15 is NOT certified: compiled exact-current-tree type and allowed-axiom audit are still required. Whole monograph
remains INCOMPLETE.

Report completed (UTC): 2026-11-06T17:13:37Z.
