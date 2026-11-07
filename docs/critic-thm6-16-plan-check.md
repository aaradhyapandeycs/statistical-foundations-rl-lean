# CHECK: the builder's private plan (Theorem 6.16, `thm:finite-VI-LCB`)

Public copy of the independent critic report; local paths removed.

Independent paper-proof critic pass. Source only. No Lean was compiled or edited. The cited paper
(li2024settling) was not consulted. I reconstructed the printed statement before reading the plan.

- Source pins (re-hashed): `chapters/offlineRL.tex` sha256
  `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4`, `chapters/prelim.tex`
  `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`. Both match the plan.
- Locators read: setting `offlineRL.tex:2935–3007`, C⋆ `:2983–2993`, algorithm `:3011–3089`,
  Theorem 6.16 `:3091–3112`, post-theorem remark `:3114–3121`, infinite penalty `:811–822`,
  occupancy `prelim.tex:745–770`. Library interfaces read: `bernsteinInfinite_fixedRow`
  (`OfflineRL/BernsteinInfiniteFixedRow.lean:348`), `visitCount_lower_tail`
  (`OfflineRL/OfflineCountChernoff.lean:83`), `bernoulliTailBoundSource`
  (`Probability/BernoulliTailProofs.lean:16`), `EnvironmentStage` (rewards in `[0,1]`), `Thm6_3`
  entry shape (`Statements/Ch6.lean:579–602`).
- My checks: `<reviewer check folder>/check.py` (`python3 -I`, stdlib, exact
  rationals), output `check.out` alongside. 20/20 pass. The plan's own `checks.py` output was read,
  not relied on.

## 0. My reconstruction of the printed statement (before reading the plan)

For every `ε ∈ (0,H]`, `δ ∈ (0,1)`, `ρ ∈ Δ(S)`: there is a variant of VI-LCB (backward
`Q_h = max{r_h + P̂_h V_{h+1} − b_h(·;V_{h+1}), 0}`, `V_{H+1} = 0`, greedy output, penalty `b ≥ 0`
of Bernstein form `Θ̃(sqrt(Var_{P̂}(V)/N) + H/N)`; refined via "two-fold sample splitting",
`:3061`) and a numerical constant `c_k > 0` such that, whenever the `K` iid trajectories of
`eq:finite-batch-size-def` satisfy `K ≥ c_k H³ S C⋆ log(KH/δ)/ε²`, with probability `≥ 1 − δ` the
output `π̂` has `V⋆_1(ρ) − V^{π̂}_1(ρ) ≤ ε`. `C⋆ = max_{s,a,h} d⋆_h(s,a;ρ)/d^b_h(s,a)` with
`0/0 = 0` (so `C⋆ ∈ [1,∞]`). `log(KH/δ)` presupposes `K ≥ 1`. No proof in the book.

## 1. Verdicts

| # | Claim | Verdict |
|---|---|---|
| 1 | Transcription of the printed statement (§1) and quantifier reading | **Confirmed** (plan's reading is equal or stronger in every slot) |
| 2a | Two-fold split with aux-determined per-`(h,s)` trimming is a faithful, least-committal reading of `:3020–3062` | **Confirmed, with one disclosed interpretive step** (see §2) |
| 2b | "H-block splitting loses a factor H" | **Confirmed for the analysis; inherent loss not proved** (wording fix) |
| 3a | Entry name `Thm6_16_restricted` | **Confirmed** (acceptable; docstring wording fixes below) |
| 3b | `0 < K` is a domain premise, not a correction | **Confirmed** |
| 4a | Stage-wise conditional independence via tapes (Lemma T, ideal data, `G`) | **Confirmed** (re-derived; exact enumeration) |
| 4b | Union over `≤ HK/8` visited triples, log has no `S`, `A` | **Confirmed** |
| 4c | (Dom), D1 pessimism, D2 reduction, D3 variance telescoping | **Confirmed** (D3 constant can be sharpened) |
| 4d | Step 4 small/large split, count chain `N ≥ K d^b/54`, self-bounding, `c_k = 69120 c_b` | **Confirmed** |
| 4e | Event table E1–E5 and failure budget | **Confirmed, two minor gaps** (`p = 0` case in E1; conditioning on `G` atoms must be made explicit) |
| 5 | `‖V̂_{h+1}‖` clip; `K = H = 1` counterexample to an `H`-clip under ∀-greedy semantics | **Confirmed** |

No claim refuted. **Go** for a Lean build, subject to the corrections in §4.

## 2. Details by claim

### 2.1 Transcription (claim 1) — confirmed

- The plan's §1.2 text matches `:3093–3112` verbatim in content. The quantifier reading
  `∃ variant ∃ c_k ∀ (S, A, H, MDP, π^b, ρ^b, ρ, π⋆, ε, δ, K)` is at least as strong as the printed
  order (`ε, δ, ρ` before "there exists a variant"; `c_k` a universal numerical constant). The
  `∃ c_b₀ ∀ c_b ≥ c_b₀ ∃ c_k` shape (as `Thm6_3`) instantiates to the printed one with `c_b = c_b₀`.
- `∀ π⋆` (every deterministic `Q⋆`-greedy policy, with `C⋆` computed from it) implies the statement
  for the book's "the optimal deterministic policy" (`prelim.tex:762`). Proof use of `π⋆`: only
  `V⋆_h = r + P⋆_h V⋆_{h+1}` at every state (D2) and the flow `d_{h+1} = d_h P⋆_h`; both hold for any
  `Q⋆`-greedy `π⋆`. Confirmed.
- `C⋆ : ℝ≥0∞` with `C⋆ ≠ ⊤` is required, not optional: with `⊤.toReal = 0` the Lean condition would
  otherwise hold trivially. ENNReal gives `0/0 = 0`, `x/0 = ⊤` (`x > 0`), matching `:2992`.
  `C⋆ ≥ 1` when finite (both occupancies sum to 1 at each `h` along `a = π⋆_h(s)`).
- "Commentary" classification of `:3114–3121` (minimax optimality, no burn-in) is right: it is cited
  and not part of the theorem.

### 2.2 Variant choice (claim 2)

Alternatives I considered:

1. **The displayed algorithm verbatim (all data, no split).** The theorem explicitly speaks of "a
   variant" and `:3061` says the refined variant is what gives sample optimality, so the entry is not
   obliged to use it. There is a genuine obstacle: `V̂_{h+1}` depends on stage-`(h+1)` counts, which
   are functions of the stage-`h` next states. My exact enumeration (S=2, A=1, H=3, K=2, penalty
   `min(1/N, ‖V‖)`) gives `E[(P̂_1 − P_1)V̂_2 ; N ≥ 1] = 0.0227 ≠ 0`, so the fixed-row Bernstein
   lemma cannot be applied directly. A leave-one-out / net argument puts `S` into the log, i.e.
   `H³S²`-type rates. Not a viable least-committal option without the cited paper.
2. **Two halves without trimming** (aux only for something else, main used in full). Does not
   decouple: main stage-`(h+1)` counts still depend on main stage-`h` next states. So "two-fold
   splitting" only helps when the aux half *fixes the counts* used from the main half. This is the
   one interpretive step of the plan: reading `:3061` as "aux-determined subsampling of the main
   half". It is the natural (and as far as I can see the only working) reading of "two-fold sample
   splitting that decouples dependency along each trajectory", but it is ours, and the docstring
   must say so (the plan's §2.4 wording already does).
3. **Different trim rules** (e.g. `max{X_a − c sqrt(X_a ι), 0}`): equally valid, better constants.
   `⌊X_a/4⌋·1{X_a > 16ι}` is fine; it only costs constants.
4. **Per-`(h,s,a)` trimming:** needs the trimming event over `HSA` triples; `A` is not bounded by
   `K`, so the printed `log(KH/δ)` would not suffice. Per-`(h,s)` trimming is the right choice.
   Confirmed.
5. **H-way split:** per-stage counts become `≈ K d^b_h/H`; in the plan's Step 4 this replaces
   `Y = H²SC⋆ι/K` by `H³SC⋆ι/K` and `HY` by `H⁴SC⋆ι/K`, i.e. `K ≳ H⁴SC⋆/ε²`. So the *analysis*
   loses a factor `H`, as claimed. That the loss is *inherent* is plausible (only `K` transitions are
   used in total, against the cited `KH ≍ H⁴SC⋆/ε²` transition rate at `:3116–3121`) but is not
   proved in the book or the plan. **Wording fix:** say "this route only yields `H⁴`" rather than
   "loses a factor H" as a fact.

### 2.3 Entry name and `K` domain (claim 3)

- `_restricted` is acceptable. The printed object ("a variant") is undefined, so per AGENTS.md
  ("concerns a different object") a suffixed entry with a C32 pointer is right. The entry is in fact
  an *instantiation* of the existential (stronger), not a weakening; the docstring should say
  "instantiated with one explicit variant" in addition to "restricted". Not adding a plain `Thm6_16`
  (`∃ alg`) is right: `∃ alg` drops "of VI-LCB" and is strictly weaker than the printed claim.
- `0 < K`: the printed text describes the data as "a collection of `K` independent sample
  trajectories", indexes `1 ≤ k ≤ K` (`:2942–2946`), and uses `log(KH/δ)` in the condition; `log 0`
  is undefined, so the printed formula presupposes `K ≥ 1`. It is a domain premise, not a
  correction. It must be explicit: under Lean's `log 0 = 0` (and also under an extended-real
  `log 0 = −∞` reading) the condition holds at `K = 0`, where every algorithm fails (plan check 5d;
  an empty dataset gives a fixed policy). Disclose in the docstring; a sentence in the C32 update is
  enough, no new SOURCE-ISSUES entry.

### 2.4 Paper proof (claim 4)

**Tapes (re-derived).** Main trajectories built sequentially; the `j`-th visit to `(h,s)` reads
`T^A_{h,s}(j)`, the `i`-th visit to `(h,s,a)` reads `T^S_{h,s,a}(i)`. Since a trajectory visits
stage `h` once, visits to `(h,s)` are ordered by `k`. A dataset determines exactly which tape cells
were read (each index is a function of earlier reads), distinct reads use distinct cells, and
unread cells integrate to 1, so the dataset's probability is the iid trajectory product. Tapes of
length `K` suffice. **Exact check:** iid law = tape pushforward on three instances
(`(S,A,H,n) = (2,2,1,2), (2,1,3,2), (2,2,2,1)`), equality as rationals.

**Ideal data.** Among the first `m` visits to `(h,s)` (in `k` order), those with action `a` are the
first `#{j < m : T^A_{h,s}(j) = a}` visits to `(h,s,a)`, which read `T^S_{h,s,a}(0..N^id − 1)`.
So on `E = {m_h(s) ≤ X_m(h,s) ∀h,s}` the kept data equal the ideal data. **Exact check:** for every
tape configuration and every `m ≤ visits`, kept = ideal (same three instances). The ideal dataset
does not read the initial states at all; given `G = σ(aux, T^A)`, `m` and `N^id` are fixed and
`V̂^{id}_{h+1}` is a function of `T^S` at stages `> h` only, which are product-independent of
`T^S_{h,·,·}`. **Exact check:** for fixed `m`, `E[(P̂_1 − P_1)V̂_2] = 0` exactly on tapes (contrast
with 0.0227 for unsplit data). Confirmed.

**Union over visited triples.** Given an atom of `G`, the positive-count triples are a fixed set of
size `≤ Σ_{h,s} m_h(s) ≤ Σ_h Σ_s X_a(h,s)/4 = H n_a/4 ≤ HK/8`. Each row: Lemma 6.18
(`bernsteinInfinite_fixedRow`, failure `< 8δ'`) at `δ' = δ/(4HK)` (`< 1/8` iff `HK ≥ 2`). Union:
`≤ δ'·HK = δ/4`. `S` enters only through `S ≤ K` (from the condition when `H ≥ 2`), `A` never.
Confirmed.

**Lemma 6.18 at `γ = 0` on `V/H`.** The library statement is generic in `γ < 1`; `hrange` becomes
`0 ≤ V/H ≤ 1`, valid since `V̂_{h+1} ≤ H − h`. Rescaling gives
`|(P̂−P)V| ≤ sqrt(4 Var̂(V) L/N) + 5HL/N` and `Var̂(V) ≤ 2Var(V) + 5H²L/(3N)` with
`L = log(1/δ') ≤ ι`. (Dom) then follows from `max{x,y} ≥ (x+y)/2` with `c_b ≥ 16`
(`c_b/4 ≥ 4`, `c_b/2 ≥ 5`); clip and `N = 0` cases are sure. Confirmed.

**D1/D2/D3.** Re-derived. D1: backward induction, at `a = π̂_h(s)`, uses `r ≥ 0` for the `0` branch.
D2: `V⋆_h − V̂_h ≤ P⋆_h(V⋆_{h+1} − V̂_{h+1}) + 2b⋆_h`, unrolled with `d_{h+1} = d_h P⋆_h`, `d_1 = ρ`.
D3: `V̂_h − P⋆V̂_{h+1} + 2b⋆_h ≥ 0` (uses `r ≥ 0`); `x·y ≤ (x + 2b)y ≤ 2H(x + 2b)` for
`y = V̂_h + P⋆V̂_{h+1} ∈ [0, 2H]`; telescoping gives
`Σ_h⟨d_h, v_h⟩ ≤ −⟨ρ,V̂_1²⟩ + 2H⟨ρ,V̂_1⟩ + 4HB ≤ H² + 4HB`. The plan's `2H² + 4HB` is valid but loose
(optional sharpening).

**Step 4.** Count chain re-derived analytically: with `x = K d^b_h(s,π⋆) ≥ 288ι`, `n_a ≥ K/3`
(`K ≥ 2`): `μ_a ≥ x/3 ≥ 96ι` so E3 gives `X_a ≥ 48ι > 16ι`, `m ≥ μ_a/8 − 1`, `mq ≥ x/24 − 1 ≥ 8ι`
(E4 premise, needs `ι ≥ 1/4`), `N ≥ x/48 − 1/2 ≥ x/54` iff `x ≥ 216` (holds: `288 log 32 ≈ 998`).
Small/large sums, Cauchy–Schwarz over `≤ HS` pairs, `sqrt(432c_bYB) ≤ B/2 + 216c_bY`: re-derived,
correct. Final constant: with `c_k = 69120 c_b`, `c_b ≥ 16`: linearised bound
`20(288 + 324c_b)/c_k + 4 sqrt(1080c_b/c_k) ≤ 1/192 + 0.09375 + 0.5 < 0.6` (my 200k-sample grid
max 0.596; exact quadratic max 0.302). Confirmed. `ι ≤ 5 log(KH/δ)` iff `log 16 ≤ 4 log(KH/δ)`,
true for `KH ≥ 2`. `H = 1` sure branch: `V̂_2 = 0 ⇒ b_1 ≡ 0 ⇒ Q̂_1 = r_1`. Confirmed.

**Events.** E1 via `bernoulliTailBoundSource` upper part (`τ ≥ 2pn`, bound `2e^{−0.19τ}`,
`0.19·16 = 3.04`); E2–E4 via `visitCount_lower_tail` (`e^{−μ/8} ≤ e^{−ι}` for `μ ≥ 8ι`). E1 ∩ E2 ⇒ E
re-derived (`X_a > 16ι ⇒ μ_a ≥ X_a/2 > 8ι ⇒ X_m ≥ μ_m/2 ≥ μ_a/2 ≥ X_a/4 ≥ m`). Budget:
`2HSe^{−3.04ι} + 3HSe^{−ι} + δ/4 ≤ δ(tiny + 3/16 + 1/4) < δ` using `HS ≤ HK`; my grid max ratio
0.4375. Gaps (minor, not refutations):
- **G1.** `bernoulliTailBoundSource` requires `0 < p`; the case `d^b_h(s) = 0` (then `X_a = 0`
  surely) must be split off. `visitCount_lower_tail` already allows `p = 0`.
- **G2.** "Lemma 6.18 applies row by row, conditional on `G`" must be realised as: `G` is finite-valued;
  for each atom `g` with positive mass, under `μ(·|g)` the next-state tapes keep their product law
  (they are independent of `G`), `N^id` is constant, and `IndepFun V̂_{h+1} row` holds; then
  integrate over atoms. This is a Lean-effort item for modules 7/9, not a mathematical gap; state it
  as its own lemma.
- **G3.** Assembly: the good event depends on the data `X` only, so `μ(good) = law(X)(good)` =
  tape-law(good ∘ build); E1–E3 (aux + main counts) and E4–E5 (tapes) must live on one product
  space (aux trajectories × initial states × tapes). The plan's inequality
  `P(bad) ≤ P(E1ᶜ ∪ E2ᶜ ∪ E3ᶜ) + P(E4ᶜ ∪ E5ᶜ)` is right on that space; say so explicitly.
- **G4.** Notation: §3 uses `L_h := ‖V̂_{h+1}‖` and also `L = log(1/δ')` (in (Dom) and E5). Rename one.

### 2.5 Penalty clip (claim 5) — confirmed

`K = H = 1`, `δ` close enough to 1, `ε < 1`: the printed condition holds; `n_a = 0` (and also
with no split: `N = 1` at the visited pair, `c_b Hι/1 ≥ H`) so an `H`-clipped penalty gives
`Q̂ ≡ max{r − 1, 0} = 0`, every action is greedy, and the ∀-tie-break claim has `P(good) = 0`.
With the `‖V̂_{h+1}‖` clip, `b_H ≡ 0` and `Q̂_H = r_H`. The counterexample is specific to the
∀-greedy output semantics, which the plan rightly keeps (stronger). **Disclosure needed:** with the
clip, `b_H ≡ 0`, which is not literally `Θ̃(H/N)` at the last stage; the docstring should state the
penalty exactly and note it is clipped at `‖V̂_{h+1}‖` (mirroring the `1/(1−γ)` clip of
`def:bonus-Bernstein-infinite`, `:811–822`).

## 3. Statement sketch (§5.3) remarks

- Add `letI : MeasurableSpace Traj := ⊤` (as `Thm6_3`) or a discrete instance.
- `V^{π̂}_1(ρ)` should be the trajectory expected return of the deterministic nonstationary `π̂`
  (as `Thm6_3` uses `trajectoryExpectedValue`), or a proved bridge to the backward-recursion value.
- `ε ≤ (H : ℝ)`; `qhat` must take only `c_b, δ`, rewards and data (check this in the definition
  review: no access to `transition`, `πb`, `ρb`, `ρ`, `ε`, `C⋆`).
- `C⋆` must be the max over all `(s,a,h)` of `d⋆_h(s,a;ρ)/d^b_h(s,a)` in `ℝ≥0∞`, with `d^b_h(s,a) =
  d^b_h(s)π^b_h(a|s)` from `ρ^b`; keep `≠ ⊤`.
- `c_b₀ = 16`.

## 4. Required corrections before/while building

1. §2.1: rephrase the H-split claim as an analysis statement (claim 2b).
2. §2.4 docstring: add "instantiated with", the exact penalty incl. `‖V̂_{h+1}‖` clip (`b_H ≡ 0`),
   `K ≥ 1` as domain of `log(KH/δ)`, `∀ π⋆`, `∀`-greedy, `C⋆ ≠ ⊤`; keep "not asserted to be
   li2024settling's algorithm"; state that aux-determined subsampling is our reading of `:3061`.
3. G1–G4 above (E1 `p = 0` split; explicit conditioning-on-atoms lemma; one product space for the
   assembly; notation).
4. Optional: D3 constant `H² + 4HB`.

## 5. Go / no-go

**GO** for a Lean build. Order: module 1 (definitions + statement) first, followed by a critic pass
on the definitions and the `Thm6_16_restricted` `Prop` before proofs; Lemma T (module 5) is the
main risk, and the exact finite enumeration above supports the atom-mass route. No source error
was found beyond C32 (undefined variant, outside proof) and the implicit `K ≥ 1` domain.
