# CHECK: plan for corrected Theorem 7.8 (`thm:lower-marl`), independent paper-proof review

Public copy of the independent critic report; local paths removed.

Reviewer: independent critic subagent, source only (no Lean compiled, no Lean edited). Date 2026-11-07.
Inputs: `source/upstream/tex/chapters/marl.tex` sha256
`8fadfab2c41ecad62349e27478adf2018047ad24a363c63a9918279238d12ffb` (matches the plan),
`generative_model_model_based.tex:31`, `docs/SOURCE-ISSUES.md#C40`, `Formalization/MultiAgent/LowerBound/PrintedStatement.lean`,
`Formalization/MultiAgent/LowerBound/SingletonActionRefutation.lean` (signatures only), the reused lemma statements in
`Online/LowerBound/{FamilyDefinitions,TestingTools}.lean`, `Probability/AdaptiveKL{,Definitions}.lean`,
`Probability/Fano/ReverseTest.lean` (statements read, not re-verified), and the plan
(the builder's private plan file).
Process note: the requested skill `skills/lean/skills/lean-paper-proof-checking/SKILL.md` does not exist in this tree
(no file matching `*paper*` under `skills/`); the review follows AGENTS.md and the brief instead.
Numeric checks: `<reviewer check folder>/check.py`, run with `python3 -I check.py`, output `ALL OK`
(details in section 5).

No author approval exists or is implied. Everything below is a critic finding, not certification.

---

## 0. Independent reconstruction of the printed statement (done before reading the plan)

`marl.tex:487–503`. Universal constants `c₁, c₂ > 0` ("small enough", "sufficiently small"). For every `m ≥ 2`, every
`S, H, A_1..A_m` (no ranges printed) and every `0 < ε ≤ c₁H`, there is a family `{MG_θ : θ ∈ Θ}` of "m-player
zero-sum" Markov games with `S` states, horizon `H`, `A_i` actions for player `i`, such that if the *total* number of
generative-model calls is `< c₂ H⁴ S max_i A_i / ε²`, then `inf_{π̂} max_θ P_θ{gap(π̂) > ε} ≥ 1/4`, with the infimum over
all **(joint)** policy estimators (`:502`).
* gap (`:332–340`): `max_s max_i (V^{⋆,π_{-i}}_{i,1}(s) − V^π_{i,1}(s))`; defined "for any policy π" and applied to joint
  (correlated) policies for CCE (`:346`); `π_{-i}` of a joint policy is the others' joint marginal (`:84–85`), the
  deviation `π'_i × π_{-i}` is played independently (`:119–126`). Policies are Markov (`:71–89`).
* Sampling (`:307–311`): each call chooses `(s, a, h)` with a joint `a` and returns `s' ~ P_h(·|s,a)`; the learner may
  choose adaptively (`:315`, Q-FTRL `:430`). Calls return transitions only.
* Rewards: deterministic (`:41`), normalised to `[0,1]` (`:42–43`); known to the learner by the book's standing
  convention (`generative_model_model_based.tex:31`) and, inside this chapter, by the plug-in estimator, whose empirical
  game uses the true `r` (`marl.tex:374`).
* "m-player zero-sum": defined only for `m = 2`: `r₂ = −r₁`, `r₁ ≥ 0` (`:50–53`), with the footnote allowing a constant
  shift of `r₂` (`:53`).
* Theorem 7.8 carries **no citation and no proof** (unlike 7.6 and 7.7). Only the commented remark at `:505` and the
  discussion at `:507–509` follow.

---

## 1. Claim (1): the plan's reading of the printed statement — CONFIRMED, with two small corrections

| Item | Plan | Verdict |
|---|---|---|
| Constants universal, quantified first | yes | confirmed (strongest reading; the construction delivers it) |
| `m ≥ 2`, no ranges on `S, H, A_i` | yes | confirmed |
| Estimator output: joint/correlated (covers NE and CCE learners) | yes | confirmed (`:502`, `:346`) |
| `π_{-i}` = marginal; deviation independent | `devProb π i π'_i a = π'_i(a_i) Σ_c π(update a i c)` | confirmed (`:84–85`, `:119–126`) |
| Adaptive generative sampling, total `N` | yes | confirmed (`:307–315`) |
| Known deterministic reward | yes | confirmed; add `marl.tex:374` as in-chapter evidence |
| Family may be fixed before `N` | yes (stronger order) | confirmed |
| "m-player zero-sum" undefined for `m ≥ 3`; violates `[0,1]` for `m = 2` | yes | confirmed |

Corrections:
* C1. §"Status" says "The monograph cites the result and gives no proof". Theorem 7.8 has **no citation**
  (`:487–488`); C40 already says "No proof or citation is given". Fix the wording.
* C2. Line locators drift slightly: Markov/product policies are `:71–91` (not `:60–83`), values `:96–106`,
  best response `eq:defn-optimal-V` `:119–126`. Use these.

---

## 2. Claim (2): existing `Thm7_8_printed` is too weak to be the corrected target — CONFIRMED; refutation unaffected — CONFIRMED

Direction. `Thm7_8_printed Adm` (`MarlPrinted78.lean`) differs from the printed text only by changes that make the
claim *easier*: extra hypotheses `S, H ≥ 1`, `A_i ≥ 1`; arbitrary `Adm`; existentially chosen `(Ω, law)` (the true
sampling law is one choice); the estimator ranges only over **data-independent product** policies `π₀` (a subclass of
all joint estimators); and `∀ q < 1/4, ∃ θ, q < P_θ` instead of `∃ θ, P_θ ≥ 1/4`. So printed ⟹ `Thm7_8_printed Adm`
for any `Adm` encoding the intended convention, and `¬ Thm7_8_printed Adm` ⟹ printed false. The weakness therefore
**strengthens**, not invalidates, `not_thm7_8_printed` (A_i = 1 gives gap ≡ 0, so every probability is 0). Confirmed.

Triviality under `max A ≥ 2`. Take `i*` with `A_{i*} ≥ 2`, one self-looping state, `r_{i*,h}(s,a) = 1[a_{i*} = θ]`,
partner `j₀ ≠ i*` with `−r_{i*}` (Σ = 0, |r| ≤ 1) or `1 − r_{i*}` (`sumConstant`), others 0. For fixed `π₀`,
`Σ_θ Σ_h π₀_{i*,h}(θ|s) = H`, so some `θ` has value `≤ H/A ≤ H/2` while the best response gets `H`; gap `≥ H/2 > c₁H ≥ ε`
for `c₁ < 1/2`, for every `N`, every law, `S, H ≥ 1`. False for `sumZeroNormalized` (rewards forced to 0). Confirmed.
The reward-blind version with the true law is equally degenerate: data are independent of θ, and for every output at most
one θ can have value `> H/2` (values over θ sum to `H`), so the θ-average failure probability is `≥ (A−1)/A ≥ 1/2`.
Confirmed. **Do not** register any such proof as `Thm7_8_corrected`; adding this observation to C40 is appropriate.

---

## 3. Claim (3): the corrected hypotheses — CONFIRMED necessary and sufficient, with one convention fix

* `max_i A_i ≥ 2`: necessary (Lean, `not_thm7_8_printed`).
* `S ≥ 2`: necessary under known reward. With `S = 1` every transition is the point mass, the game is determined by the
  known reward, and backward induction with constant continuation values gives an exact equilibrium: an exact **CCE**
  (enough, since the estimator class is joint) by stage-game CCE existence (LP/minimax), and an exact NE by Nash's
  theorem for the product-output Stage A. gap 0 with zero samples. Plan says "needs general-sum Nash existence"; for the
  joint-output target, CCE existence suffices. Prose only; agreed not to formalise now.
* `H ≥ 2`: necessary for the same reason (`H = 1`: `V_{·,2} ≡ 0`, per-state stage equilibria).
* `m ≥ 2`: as printed; used only to have a partner `j₀` for the zero-sum convention.
* Known shared reward: not a hypothesis but the modelling of the book's convention. In the Lean shape (`∃ family, ∀ rule,
  out`), the estimator already knows the family, so the shared-reward conjunct alone encodes "known reward"; the extra
  `Reward →` argument of `rule`/`out` is redundant (harmless). Either one suffices; keeping the conjunct is clearer.
* Sufficiency: by the proof in §4. Hence `{m ≥ 2, S ≥ 2, H ≥ 2, max A ≥ 2}` is the weakest set of size ranges (each one
  necessary, together sufficient), for the constants and rate as printed. Confirmed.

**Convention fix (C3, required).** For `m = 2` the book's convention is `r₂ = −r₁` **with `r₁ ≥ 0`** (`:50–53`). The
plan sets `r_{i*} = 1[s ≠ 0]`, `r_{j₀} = −r_{i*}`. If `A_2 > A_1` then `i* = 2` and player 1 (max-player) gets
`r₁ = −1[s≠0] ≤ 0`, violating the book's convention. Fix: when `i*` is not player 1, put `r₁ = 1[s = 0]` (player 1 is
`j₀`) and `r_{i*} = −1[s = 0] = 1[s≠0] − 1`. Per-player constant shifts change every value by the same amount `(H−h+1)·c`
for all policies, so gaps are unchanged and the proof is unaffected (one shift lemma, or redo the chain recursion with
`1[s≠0] − 1`). Recommended admissibility predicate for the zero-sum entry: `Σ_i r_i = 0`, `r_{player 1} ∈ [0,1]`, all
`|r_i| ≤ 1` (matches `:50–53` for `m = 2`, a disclosed choice for `m ≥ 3`). The `constSumNormalized` variant
(`r_{j₀} = 1 − r_{i*}`, all in `[0,1]`, the footnote's shift) needs no change.

Optional strengthening (C4): the output is a deterministic function of the history. A learner seed `ω ∈ Fin K` read by
both `rule` and `out` costs nothing in the proof (the Bayes bound holds for each `ω`, then average) and removes the
"deterministic output" limitation. Not required for go.

---

## 4. Claim (4): the paper proof (plan §2) — CONFIRMED step by step; rate `H⁴ S max A / ε²` is achieved

Checked by hand and numerically (section 5). Notation as in the plan; `λ = 1024ε ≤ H/2` from `ε ≤ H/2048`.

* §2.1 exit table = `onlineLBq H λ θ_c ·` (definition read): `θ_c ≠ 0`: `q(θ_c) = 1/H − λ/H²`, `q(0) = 1/H − λ/(2H²)`,
  others `1/H`; `θ_c = 0`: `q(0) = 1/H − λ/(2H²)`, others `1/H`. All in `[1/(2H), 1/H]` (needs `λ ≤ H/2`, `H ≥ 2`).
  Best action `θ_c`; margin `ℓ(σ) − q(θ_c) ≥ (1 − σ(θ_c)) λ/(2H²)` in both cases. **Confirmed.** Lower exit = better
  because reward is `1[s ≠ 0]` and the sink `0` is absorbing with value 0.
* §2.2 reduction: transitions and `r_{i*}` depend on the joint action only through `a_{i*}`, so `V^π_{i*}` is the
  single-agent value of the `a_{i*}`-marginal; the deviation `π*_{i*} × π_{-i*}` has `a_{i*}`-marginal `π*`; gap ≥
  player-`i*` term at state `x`. Holds for product and for correlated Markov `π`. **Confirmed.**
* §2.3 chain recursion `V_h = 1 + (1−ℓ_h)V_{h+1}`, `D_h = (ℓ_h − ℓ*_h)V*_{h+1} + (1−ℓ_h)D_{h+1}`; survival
  `≥ (1−1/H)^{h−1} ≥ 1/2` for `h ≤ ⌊H/2⌋`; `V*_{h+1} ≥ n − n(n−1)/(2H) ≥ n/2 ≥ H/4` with `n = H − h ≥ H/2`; per miss
  `≥ ½·λ/(4H²)·H/4 = λ/(32H)`; `W_x ≥ ⌊H/2⌋/4 ≥ H/16` gives gap `≥ λ/512 = 2ε > ε`. **Confirmed** (exact recursion vs
  bound: min ratio 2.84 over random and adversarial patterns, `H = 2..69`). Terms for `h > H'` vanish since all exits
  are `1/H` there.
* §2.4 per-coordinate adaptive testing. `P_0`, `P_j` differ only at queries `(x_c, h_c, a)` with `a_{i*} = j`
  (`onlineLBq_zero_eq_succ`); adaptive chain rule gives `KL(P_0‖P_j) = E_0[N_{c,j}]·kl(q₀(j)‖q_j(j)) ≤ E_0[N_{c,j}]κ`,
  `κ = 4λ²/H³` (absolute continuity holds: all exits in `(0,1)`). Event Pinsker; disjoint `hit_j`;
  `½(1−x) + x/(2M) ≤ ½` since `M ≥ 1`; Cauchy–Schwarz `Σ_j √n_j ≤ √(M Σ n_j)`; result `½ + √(E_0[N_c]κ/(8M))`.
  Jensen over `θ_{-c}` and `E_ρ[N_c] ≥ ½E_ρ[N_c | θ_c = 0]` give `E_ρ[miss_c] ≥ ½ − √(E_ρ[N_c]κ/(4M))`; summing,
  Cauchy–Schwarz and `Σ_c N_c ≤ N` give `E_ρ[W] ≥ |C|(½ − τ)`. **Confirmed.** Adaptivity is handled correctly: every
  count is an expectation under a law in the family's mixture, and the reference `θ_c = 0` has prior mass ½, which is
  exactly what lets the per-hybrid counts `E_{θ_c=0}[N_c]` be dominated by `2E_ρ[N_c]` and summed to `≤ 2N`. With an
  out-of-family null reference the hybrid counts live under different laws and do not sum to `N`; with a uniform prior
  the `A` factor cancels. The plan's remark on this is correct.
* §2.5 counting: `W ≤ |C|`, `E[W]/|C| ≥ 7/16` ⟹ `P(W ≥ |C|/4) ≥ (7/16 − 1/4)/(3/4) = 1/4`; pigeonhole over `S−1` chains;
  Bayes average ⟹ some θ. Constants: `κ = 2²²ε²/H³`, `M = A−1 ≥ A/2`, `|C| = (S−1)⌊H/2⌋ ≥ SH/8`; `τ ≤ 1/16` ⟸
  `N ≤ ASH⁴/(2³²ε²)`, implied by `N < c₂H⁴SA/ε²`, `c₂ = 2⁻³²`. **Confirmed**: the printed rate (all of `H⁴`, `S`,
  `max A`, `ε⁻²`) is achieved, with `c₁ = 1/2048`. Nothing uses `N ≥ 1`.
* §2.0 two-point remark. The adaptive part (learner concentrates on the difference set, so Le Cam caps at roughly
  `N·max_d kl_d ≲ 1`, and value separation `ε` forces `max_d kl_d ≳ ε²/H³` by a variance/simulation argument) is a
  sound **heuristic**, not a proof, and is not load-bearing. The uniform-allocation sentence ("`n ≲ H²/ε²`, i.e.
  `H³S∏A_i/ε²`") is unsupported and irrelevant to an adaptive lower bound (a quick calculation with two hypotheses
  differing on two `a_{i*}` values at every `(x,h)` gives a different expression). **Gap (minor): delete the
  uniform-allocation sentence and label the rest as heuristic motivation.**

No mathematical error found in §2.

---

## 5. Numeric checks (`python3 -I <reviewer check folder>/check.py` → `ALL OK`)

1. Exit range `[1/(2H), 1/H]` and margin inequality: `H = 2..59`, `A ∈ {2,3,5}`, random `σ`.
2. `kl(q_θ(a)‖q_θ'(a)) ≤ 4λ²/H³`: `H = 2..199`, three `λ` values, all instance pairs.
3. Exact chain loss vs `W λ/(32H)`: min ratio 2.844 (bound valid, conservative).
4. `⌊H/2⌋ ≥ H/3 ≥ H/4` (`H ≤ 1999`), `(S−1)⌊H/2⌋ ≥ SH/8`.
5. `λ ≤ H/2`, `τ ≤ 1/16` at the supremum of admissible `N`, and `(⌊H/2⌋/4)·λ/(32H) > ε`, over a grid of `S, H, A, ε`.
6. Single coordinate, exact Bayes-optimal hit probability under the ½ / `1/(2M)` prior for every allocation with ≤ 6
   queries per action (`H ∈ {2,3,4}`, `A ∈ {2,3}`): always `≤ ½ + √(nκ/(8M))` (max normalised ratio 0.5).

---

## 6. Corrections to the plan (summary)

* C1. "cites the result" → "states the result without citation or proof".
* C2. Fix the line locators (§1).
* C3 (**required before building**). Zero-sum predicate and construction must respect `r₁ ≥ 0` for `m = 2`
  (`:53`): if `i* ≠ 1`, use `r₁ = 1[s = 0]`, `r_{i*} = −1[s = 0]`, plus a constant-shift invariance lemma (or a shifted
  chain recursion). State the predicate in the docstring as a disclosed convention for `m ≥ 3`.
* C4 (optional). Learner seed for randomised outputs.
* C5. §1.2: `S = 1`/`H = 1` necessity for the joint-output target needs only CCE existence; NE existence only for
  Stage A. Still prose.
* C6. §2.0: drop the uniform-allocation sentence; mark the two-point paragraph as heuristic.
* C7. Lean shape: the `Reward →` arguments are redundant given `∃ family ∀ rule` plus the shared-reward conjunct; keep
  the conjunct, drop or keep the arguments, but say which one encodes "known reward" in the docstring.
* C8. Stage A alone must be registered as `Thm7_8_restricted_product` with a SOURCE-ISSUES note (plan already says so);
  only Stage B (joint outputs, `gapJ` reducing to `gap` on products) may be called `Thm7_8_corrected`.
* Engineering note: `onlineLBq_zero_eq_succ` is stated on `Fin (M + 1)`; `A_{i*}` must be cast to `M + 1` with
  `M = A_{i*} − 1` (a `Fin.cast`/`subst` step to plan for).

---

## 7. Go / no-go

**GO** for a Lean build of Stage A then Stage B, conditional on applying C3 (zero-sum convention for `m = 2`) to the
admissibility predicate and the hard family before writing `Marl78Hard.lean`, and C1/C6 to the plan text. The printed
reading, the triviality of the existing Prop, the validity of the A = 1 refutation, the necessity and sufficiency of the
hypotheses, and every step and constant of the proof check out. A builder must not certify its own source fidelity; a
post-build critic pass on the final Lean statement (estimator class, `gapJ`, admissibility predicate, constants) is still
required, and nothing here is author approval.
