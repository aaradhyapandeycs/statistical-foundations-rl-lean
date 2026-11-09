# CRITIC: independent check of the 2026-11-08 external audit findings F1–F5

Public copy of the independent critic check of an external review; local paths removed.

Post-review note (added to this public copy, 2026-11-09): the external review's findings F1–F4 were recorded in `SOURCE-ISSUES.md` on 2026-11-09 from the drafts below: F1 as [C47](SOURCE-ISSUES.md#C47); F2 as [C48](SOURCE-ISSUES.md#C48), with a pointer in C13; F3 as an addendum to C19 (no entry is renamed; the restricted/corrected naming mismatch it notes is recorded there); F4 as a scope note appended to C43 and one sentence in the Theorem 7.11 row of `COVERAGE.md`. F5 (Theorem 6.13 estimator quantifier) is resolved without reclassification: the randomized-estimator extension was proved and integrated on 2026-11-09 (`Thm6_13_randomized`, estimators with an independent seed on any probability space, no measurability premise; `Thm6_13` is its Dirac-seed case), independently reviewed in `critic-thm6-13-randomized.md`. The Theorem 6.13 ledger record now points to that entry; the reclassification drafted below was not needed and was not applied. Line references to `docs/COVERAGE.md`, `docs/SOURCE-ISSUES.md` and `docs/named-result-status.json` below are as of the review and may have moved. The external review itself is not published. The check text below is otherwise unchanged.


Date: 2026-11-09. Critic: independent agent (not a builder of any file named here).
Audit file tested (claims only): the external review dated 2026-11-08 (a private document, not published).

## Source pin

SHA-256 recomputed and compared with `source/provenance.json` (all match):

| file | SHA-256 |
|---|---|
| `chapters/inference.tex` | `82707713adb6c9296d9ee41faa84b2d0a12eaf1b34864a6d294de02132e648f2` |
| `chapters/onlineRL.tex` | `393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53` |
| `chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` |

Scripts (pure Python stdlib; `fractions` for exact arithmetic, Monte Carlo where noted), kept in the critic's private
working folder (not published):
- `check_findings.py` → `check_findings.out` (F1(a)–(d), F3, F4 arithmetic)
- `td_coverage_scan.py` → `td_coverage_scan.out` (F1 TD example, finite-T simulation)
- `mvp_literal_trigger.py` → `mvp_literal_trigger.out` (F2 literal-trigger MVP run)

No lake/lean run. No repository file other than this report and the scripts directory was written.

## Verdict table

| ID | Claim | Verdict | Proposed ledger slot |
|---|---|---|---|
| F1(a) | data-selected convex set with conditional Gaussian mass 1−α need not cover at 1−α | **CONFIRMED** (book text does say "any convex set") | new C47 |
| F1 TD | same failure asymptotically in the book's TD model (1 state, rewards 0/1, γ=1/2) | **CONFIRMED** (paper-level; CLT/Slutsky step not in Lean) | C47 |
| F1(b) | rectangle divides quantile by √T twice; coverage → 0 | **CONFIRMED** | C47 |
| F1(c) | ellipsoid compares squared statistic with R², R = χ² quantile | **CONFIRMED WITH CHANGES**: printed set is over-conservative for usual α; fails the book's own mass condition only when R<1 (α>0.317 for d=1, α>0.607 for d=2) | C47 |
| F1(d) | plug-in Ā_T⁻¹ undefined when a state is unsampled, prob ≥ (1−μ(s))^T>0 | **CONFIRMED** (also: Ā_T is invertible whenever every state is sampled) | C47 |
| F2 | literal consecutive-integer MVP trigger ⇒ regret K surely, refuting Thm 5.10's rate | **CONFIRMED** (needs an admissible adversarial tie rule; both printed δ′ allocations; any c₂>0) | new C48 + pointer in C13 |
| F3 | Lemma 6.5 false at N=1 (S=1, A=2, uniform, δ=31/32) | **CONFIRMED** (sharper: failure requires SN=1; proof breaks at `:3608`) | addendum to C19 (not a new C49) |
| F4 | C43 is stated as reading-dependent; corrected convex-set theorem open; citation gap witness −3/16 | **CONFIRMED** (arithmetic exact; external-paper facts checked only via fetched HTML) | qualifying text for C43/COVERAGE |
| F5 | Thm 6.13 Lean binder covers deterministic data→policy maps only; printed inf is over "all policy estimators" | **CONFIRMED WITH CHANGES**: the book never says "randomized"; the gap is a quantifier-scope ambiguity, already disclosed in ledgers, but the public category "printed result proved" overstates it | scope disclosure / reclassify to restricted, or prove seed extension (~150–200 lines finite seed) |

---

## F1 — Chapter 7 confidence regions (`inference.tex`)

**Exact source.** `\subsection{Statistical inference}` `\label{sec:inference}` (`inference.tex:150`).
Estimators Ā_T, Γ̂_T, w_{t,T}: `:160–175`; Λ̂_T = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ `eq:defn-hat-Lambda` `:179–181`.
Confidence-set paragraph and `eq:convex.Cdelta`: `:185–194`. Rectangles (i): `:196–203`. Ellipsoids (ii): `:205–213`.
Sampling model `eq:iid-samples`: `:49–64` (rewards r_t = r(s_t,a_t)).

**(a) What the book actually claims.** `:186`: "it suffices to choose *any* convex set C_α that contains at
least 1−α probability mass under the Gaussian distribution N(V̄_T, Λ̂_T/T)", stated as a conditional probability given
(V̄_T, Λ̂_T) in `eq:convex.Cdelta`, followed by (`:194`) "By the Gaussian approximation in Theorem 7.11, such sets serve
as approximate confidence regions for V^π." So the text does claim (approximate) coverage for an arbitrary convex set
satisfying a data-dependent conditional-mass condition, not only for the two listed constructions, which are introduced as
"Natural choices ... include, but not limited to". The claim is informal ("approximate"), but even the asymptotic
reading fails.

*Minimal witness (ideal Gaussian).* d=1, X ~ N(θ, 1/T) exactly, known variance, z = Φ⁻¹(1−α), 0<α<1/2.
C = [X − z/√T, ∞) if X ≥ 0, C = (−∞, X + z/√T] otherwise. Each choice has N(X,1/T)-mass exactly 1−α and is convex.
At θ=0: 0 ∈ C ⇔ |√T X| ≤ z, probability 2Φ(z)−1 = 1−2α for every T. Script: exact 0.900 at α=0.05, MC 0.8995.
Thm 7.11's fixed-set Berry–Esseen bound does not transfer to sets chosen from the same data; that is where the argument
breaks.

*TD-model version (audit's second paragraph).* One state, two actions with π uniform, r = (0,1), s′ = s, γ = 1/2,
η_t = η₀t^{-2/3}. Exact: V^π = 1; A = Ā_T = 1/2 identically; true residual variance Γ_true = 1/4; Λ_true = 1.
Under the C43 reading r(s) = r_π(s) the *printed* Γ is 0 (so Thm 7.11 is itself degenerate here; C43 already
notes Γ = 0 when S = 1); the counterexample does not use Thm 7.11, only the procedure, which uses Λ̂_T.
Γ̂_T = Σ w_t (V̄_T/2 − r_t)² = 1/4 + (V̄_T−1)Σw_t(1/2−r_t) + (V̄_T−1)²/4, with Σw_t = 1 and |Σw_t(1/2−r_t)| ≤ 1/2, so
Λ̂_T → 1 whenever V̄_T → 1 in probability. Selecting the half-line by sign(V̄_T − 1) with radius z√(Λ̂_T/T) gives
coverage P(|√TΔ̄_T| ≤ z√Λ̂_T) → P(|Z| ≤ z) = 1−2α, given the scalar Polyak–Ruppert CLT √TΔ̄_T ⇒ N(0,1) and Slutsky.
Checked: the Lean partial result `scaledError_smooth_gaussian_le` (`Formalization/Ch7Rest/TDInferenceSmooth711.lean:306`)
uses `trueGamma` (`TDInference711Defs.lean:121`, the true residual covariance), so applying it to x ↦ sin(ux), cos(ux)
(C², bounded derivative, Lipschitz Hessian) gives characteristic-function convergence and, by Lévy continuity, the CLT.
That corollary, Lévy continuity, and the Slutsky step are **paper-level, not Lean-checked**.
Simulation (V₀ = V^π, η₀ = 0.2, α = 0.05): sign-selected half-line coverage 0.750 / 0.797 / 0.865 at T = 10³/10⁴/4·10⁴
versus fixed one-sided 0.870 / 0.900 / 0.932 (limits 0.90 vs 0.95); sd(√TΔ̄_T) = 1.41/1.31/1.14 → 1 slowly, Λ̂ ≈ 1.000.
(With V₀ = 0 the O(1/T) transient dominates at moderate T; this is irrelevant asymptotically.)

**(b) Rectangles.** `:200`: half-width R̂/√T, where R̂ is the quantile of ‖·‖_∞ of N(0, Λ̂_T/T) (`:202`). So
R̂ = q_{1−α}(‖N(0,Λ̂_T)‖_∞)/√T and the half-width is O(1/T). V^π ∈ C ⇔ ‖√TΔ̄_T‖_∞ ≤ q/√T. Even with the oracle
Λ̂ = Λ and exact Gaussian errors (d=1, Λ=1): coverage = 2Φ(1.96/√T) − 1 = 0.95, 0.46, 0.16, 0.016, 0.0016 at
T = 1, 10, 100, 10⁴, 10⁶. → 0. The printed set also violates the book's own `eq:convex.Cdelta` for T > 1. Repair: half-width
R̂ with R̂ the quantile under covariance Λ̂_T/T, or R̂/√T with covariance Λ̂_T.

**(c) Ellipsoids.** Printed (`:209–212`): {V : T(V−V̄_T)ᵀΛ̂_T⁻¹(V−V̄_T) ≤ R²}, "R is the 1−α quantile of the χ²(d)
distribution". The statistic is χ²_d under the reference Gaussian, so the printed set has mass F_{χ²_d}(R²).
Since R² ≥ R iff R ≥ 1, the set satisfies `eq:convex.Cdelta` (conservatively, mass ≈ 1 at α = 0.05: 0.9999 for d=1)
exactly when R ≥ 1, and **violates it when R < 1**, i.e. α > 0.3173 (d=1) or α > 0.6065 (d=2); e.g. d=1, α=0.5:
R = 0.455, mass 0.351 < 0.5. So the audit's "compares squared statistic to squared χ² quantile" is accurate as a
transcription error; its consequence is over-coverage (not under-coverage) for conventional α. Also: `d` is undefined
in the chapter (dimension is S), the conditional display writes `\widehat{{\Lambda}/T}` (`:192`), and Λ̂_T⁻¹ requires
Λ̂_T ≻ 0, which fails e.g. when Γ̂_T has a zero diagonal entry (zero empirical residuals at a state).
Repair: compare with R where R is the χ²_d quantile (or R² with R its square root).

**(d) Singular Ā_T.** A_t = e_{s_t}(e_{s_t} − γe_{s′_t})ᵀ has only row s_t nonzero, so an unsampled state gives a zero
row of Ā_T. P(state s unsampled) = (1−μ(s))^T > 0 whenever S ≥ 2 (e.g. μ uniform, S=2: 2^{−T}). Converse (checked by
hand): if every state is sampled, row s of T·Ā_T has diagonal n_s − γc_ss and off-diagonal absolute sum γ(n_s − c_ss),
difference n_s(1−γ) > 0, so Ā_T is strictly row-diagonally dominant and invertible. So singularity occurs exactly on
the event "some state unsampled".

**Scope.** (a) and the TD example: any reading; the TD example is valid under both reward readings because it only uses
the procedure and the true dynamics. (b), (c), (d): literal printed formulas. Nothing here is Lean-checked; all items are
paper calculations. The Lean smooth-test result is not affected (it makes no confidence-region claim, as COVERAGE says).

**Proposed repair.** State a specific confidence rule with a data-independent shape given the pivot (e.g.
C = V̄_T + T^{-1/2} Λ̂_T^{1/2} K with K a fixed convex set of N(0,I)-mass 1−α), prove coverage for the oracle-covariance
version from a convex-distance bound, and add a covariance-perturbation argument for Λ̂_T; fix (b) and (c) as above;
define the procedure on the event that Ā_T or Λ̂_T is singular and charge that event's probability.

### DRAFT `docs/SOURCE-ISSUES.md` entry (C47)

```markdown
<a id="C47"></a>
## Candidate C47: Chapter 7 confidence sets — data-selected convex sets, rectangle scaling, ellipsoid radius, singular plug-in

Source: `\subsection{Statistical inference}` (`sec:inference`), `chapters/inference.tex:150–213`: plug-in
estimators `:160–181`, confidence-set rule `eq:convex.Cdelta` `:185–194`, rectangles `:196–203`, ellipsoids
`:205–213`; sampling model `eq:iid-samples` `:49–64`. Pinned chapter SHA-256:
`82707713adb6c9296d9ee41faa84b2d0a12eaf1b34864a6d294de02132e648f2`.

**(1) Arbitrary data-selected convex sets.** The text says it suffices to choose any convex set with conditional
mass ≥ 1−α under N(V̄_T, Λ̂_T/T), and that Theorem 7.11 makes such sets approximate confidence regions (`:186–194`).
This fails even for an exactly Gaussian estimator with known variance: X ~ N(θ,1/T), z = Φ⁻¹(1−α), 0<α<1/2, choose
[X − z/√T, ∞) if X ≥ 0 and (−∞, X + z/√T] otherwise. Both sets are convex with conditional mass exactly 1−α, but at
θ = 0 the coverage is P(|√T X| ≤ z) = 1−2α for every T. In the book's own TD model (one state, π uniform over two
actions with rewards 0 and 1, γ = 1/2) V^π = 1, Ā_T = 1/2, the true residual variance is 1/4, Λ̂_T → 1, and the same
sign-selected half-lines with radius z√(Λ̂_T/T) have limiting coverage 1−2α, given the scalar Polyak–Ruppert CLT.
The fixed-set bound of Theorem 7.11 is applied to a set chosen from the same data.

**(2) Rectangles.** R̂ is the ℓ∞ quantile under covariance Λ̂_T/T, and the half-width is R̂/√T, so the √T scaling is
applied twice: half-width O(1/T). Even with oracle covariance and exact Gaussian errors (S = 1, Λ = 1, α = 0.05) the
coverage is 2Φ(1.96/√T) − 1 → 0 (0.16 at T = 100). The printed set violates `eq:convex.Cdelta` for T > 1.

**(3) Ellipsoids.** The Mahalanobis statistic is compared with R², where R is the 1−α quantile of χ²(d). The printed
set has reference mass F_{χ²_d}(R²): conservative when R ≥ 1 and below 1−α when R < 1 (α > 0.317 for d = 1,
α > 0.607 for d = 2; d = 1, α = 1/2 gives mass 0.351). `d` should be S; Λ̂_T⁻¹ needs Λ̂_T ≻ 0.

**(4) Singular plug-in.** Row s of Ā_T is zero when state s is unsampled, an event of probability (1−μ(s))^T > 0
for S ≥ 2, so Λ̂_T (`:181`) is undefined there. If every state is sampled, Ā_T is strictly diagonally dominant and
invertible.

Proposed correction: prescribe a confidence rule whose shape given the pivot is fixed (e.g.
V̄_T + T^{-1/2}Λ̂_T^{1/2}K with K a fixed convex set of standard-Gaussian mass 1−α), prove its coverage with a covariance
perturbation bound, use half-width R̂ (not R̂/√T) in (2), the threshold R (not R²) in (3), and specify and charge the
singular event in (4). Status: paper calculations, not Lean-checked; the TD-model limit also relies on a CLT and
Slutsky argument not formalized (the Lean smooth-test bound `scaledError_smooth_gaussian_le` with sine/cosine test
functions and Lévy continuity would give the CLT; that derivation is paper-level). Raised by an external audit
(2026-11-08) and independently re-derived by a critic. Not author-approved.
```

---

## F2 — MVP literal trigger and Theorem 5.10 (`onlineRL.tex`)

**Exact source.** Algorithm `alg:main-mvp` `onlineRL.tex:1256–1310`; trigger `line:trigger-set-mvp` `:1280`
`N^all_h(s,a) ∈ {1,2,…,2^{log₂K}}`; stored count `N_h(s,a) ← Σ N_h(s,a,s̃)` `:1281`; reset `N_h(s,a,s̃) ← 0` `:1285`;
Q-update `eq:updateq-mvp` `:1298–1300` with min{·, H}; greedy `argmax_a` `:1268`; bonus `eq:bh-defn-Bernstein-ucbvi`
`:407–417` (`:409–410`); allocations δ′ = δ/(100S²A²H²K²) `eq:definition_delta_prime` `:416` and
δ′ = 100δ/(S²A²H²K²) `eq:assumption-K-proof-B-mvp` `:1386–1390`. (The 200SAH²K² variants at `:297`, `:552`, `:1265`,
`:1941` are commented out, not printed.) Theorem 5.10 `thm-mvp-regret` `:1339–1352`; doubling prose `:1215`.

**Step check** (S = H = 1, A = 2, r = (0,1) with action 0 the bad one, deterministic s₁, δ = 1/2):
1. Trigger: literal set {1,…,2^{log₂K}} = {1,…,K} for K a power of two (for other K, 2^{log₂K} = K as a real; the
   integer-floor reading also contains every count ≤ 2^{⌊log₂K⌋}, enough until that point). Every visit triggers. ✔
2. Batch reset: at each visit to (s,a) the per-successor counters hold exactly that visit (previous visit reset them),
   so N_h(s,a) = 1 after every visit. ✔ (Same mechanism as C13.)
3. Score: V_{H+1} = 0, so Var = 0 and ⟨P̂, V⟩ = 0; Q(bad) = min{0 + c₂·1·log(1/δ′)/1, 1} = 1 iff c₂ log(1/δ′) ≥ 1. ✔
4. Allocations: `:416` gives log(800K²) (≥ 6.68 at K = 1); `:1390` gives log(K²/12.5). For any fixed c₂ > 0 both exceed
   1/c₂ for K large. ✔ (Script: c₂ = 0.05 needs K ≈ 2^12 under `:416`; c₂ = 0.2 needs K ≈ 2^8 under `:1390`.)
5. Tie rule: the algorithm says only argmax (`:1268`); k = 1 has Q = (1,1); a lowest-index rule picks action 0. ✔
   admissible. It is *needed*: a tie rule preferring action 1 avoids the failure.
6. Zero-count completion: the good action keeps N = 0, the printed bonus divides by 0 (C8). Every completion that
   respects the clip (Q = H as in C8, or b = +∞ then min) gives Q(good) ≤ 1 = Q(bad). ✔
7. So the bad action is played every episode: regret exactly K surely (script: 16, 256, 4096, 65536).
   Thm 5.10 claims, with prob ≥ 1−δ = 1/2, regret ≤ Õ(min{√(SAH³K), HK}) = Õ(√(2K)); for any fixed polylog factor,
   K > C√(2K)·polylog(K/δ) for K large. Holds for every choice of c₁, c₂ > 0 ("suitably chosen" cannot help). ✔

**Relation to C13 and Lean.** C13 Lean-refutes the *auxiliary* Lemma 5.12 sum bound under the literal trigger
(`not_Lemma5_12_literalTrigger_printed`) and states the prose/display conflict. F2 extends this to the *main* theorem,
using additionally the clip, both δ′, and an adversarial tie. The proved `MVP_regret_corrected`
(`docs/COVERAGE.md:13`) uses the dyadic trigger and one fixed tie, so it is outside the counterexample's scope; no Lean
result is contradicted. F2 is **paper calculation, not Lean-checked** (the script is a simulation of the deterministic
trace, not a proof).

**Ledger choice: new C48, plus a one-line pointer in C13.** C13 is about the count lemma and the factor-two comparison;
F2 refutes a different printed result (Theorem 5.10), needs extra ingredients (tie rule, allocation, clip), and
changes how Theorem 5.10's "corrected" category should be read (the printed theorem is false under one of two readings
of its own algorithm). A separate ID keeps that result-level status traceable.

### DRAFT `docs/SOURCE-ISSUES.md` entry (C48)

```markdown
<a id="C48"></a>
## Candidate C48: Theorem 5.10 fails under the literal MVP trigger

Source: Theorem 5.10 (`thm-mvp-regret`, `chapters/onlineRL.tex:1339–1352`); Algorithm `alg:main-mvp` (`:1256–1310`),
trigger `:1280`, stored count and reset `:1281–1285`, clipped update `:1298–1300`, greedy step `:1268`; bonus
`eq:bh-defn-Bernstein-ucbvi` (`:407–417`); allocations `:416` and `:1386–1390`. Pinned chapter SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The displayed trigger `{1,2,…,2^{log₂K}}` contains every count up to K, while the prose (`:1215`) describes powers of
two ([C13](#C13)). Under the literal reading the main regret bound is false. Take S = H = 1, A = 2, rewards 0 and 1,
deterministic transitions, δ = 1/2, and a greedy rule that breaks the initial tie Q = (H, H) toward the reward-0
action (the algorithm specifies only argmax). Every visit triggers and resets the batch, so that action's stored count
is always 1. Since V_{H+1} = 0, its updated score is min{c₂ log(1/δ′), 1} = 1 as soon as c₂ log(1/δ′) ≥ 1, which holds
for all large K under both printed allocations δ′ = δ/(100S²A²H²K²) (`:416`) and δ′ = 100δ/(S²A²H²K²) (`:1390`),
for every c₂ > 0. The unvisited action has the undefined zero-count bonus ([C8](#C8)); every completion that respects
the clip at H gives it score at most 1. So the reward-0 action is played in every episode and Regret(K) = K surely,
contradicting Õ(min{√(SAH³K), HK}) = Õ(√K) for large K. A tie rule favouring the reward-1 action avoids this
instance, so the refutation is for the algorithm as printed (unspecified ties), not for every tie rule.

Not affected: the dyadic-trigger corrected theorem `MVP_regret_corrected` (power-of-two trigger, one fixed tie rule).
Status: paper calculation, not Lean-checked (a trace simulation is in the critic's working notes). Raised by an
external audit (2026-11-08) and independently re-derived by a critic. Not author-approved.
```

Pointer to append to C13: "Under the same literal reading the main Theorem 5.10 also fails; see [C48](#C48)
(paper calculation, not Lean-checked)."

---

## F3 — Lemma 6.5 at N = 1 (`offlineRL.tex`)

**Exact source.** Lemma 6.5 `lem:sample-split-infinite` `offlineRL.tex:1104–1115`: for any δ ∈ (0,1), with probability
exceeding 1−δ, max{N_{s,a}, (2/3) log(SN/δ)} ≥ Nρ(s,a)/12 for all (s,a) (`\infs` is the empty macro,
`commands.tex:223`). N_{s,a} is the raw count `eq:defn-Nsa-infinite` `:672–678`; sampling `:28–37`. Proof
`:3540–3615`; the failing inequality is `|N_large| ≤ N/(8L) ≤ N` at `:3607–3609`, which needs L = log(SN/δ) ≥ 1/8.
The lemma prints no restriction on N (any dataset size N ≥ 1).

**Witness (exact).** S = 1, A = 2, ρ = (1/2,1/2), N = 1, δ = 31/32. L = log(32/31) = 0.031749;
(2/3)L = 0.021166 ≤ 2/93 = 0.021505 (log(1+x) ≤ x) < 1/24 = 0.041667 = Nρ/12. The one sample leaves one action with
count 0, which then violates the inequality, so the event is empty: probability 0, whereas the claim is > 1−δ = 1/32.
Both actions are in N_large (Nρ = 1/2 ≥ 8L = 0.254), so |N_large| = 2 > N = 1, and the union bound gives 2δ/(SN) > δ.
Sharpening: for A = 2 uniform, S = N = 1 the lemma fails for every δ > e^{-1/16} ≈ 0.9394. If SN ≥ 2 then L > log 2 > 1/8
and the printed proof step is valid, so the failure needs SN = 1 (paper-level). The Lean entry assumes N ≥ 2, which is
sufficient; S ≥ 2 with N = 1 would also suffice for the printed proof.

**Relation to C19 / Lean.** `Lemma6_5_sampleSplit_actualData_corrected` (`Formalization/Statements/Ch6.lean:85–108`)
assumes `2 ≤ N` and is Lean-proved; it is unaffected. C19 currently says the omission is "not a counterexample";
F3 upgrades it to a counterexample to the standalone printed lemma (still not to Theorem 6.3, whose regime implies
N ≥ 2). Small inconsistency: COVERAGE/named-result-status call it a "restricted variant" while the Lean name has
`_corrected`; with a printed counterexample, `_corrected` is the accurate suffix and the ledger wording should follow.

**Ledger choice: addendum to C19 (no new C49).** Same lemma, same missing hypothesis, same Lean correction; only the
status changes from "omitted domain" to "printed lemma false at its endpoint".

### DRAFT addendum to C19

```markdown
**Addendum (2026-11-09): the printed lemma is false at N = 1.** Take S = 1, A = 2, ρ uniform, N = 1 and δ = 31/32.
The single sample leaves one action with N_{s,a} = 0, and for that action
(2/3)log(SN/δ) = (2/3)log(32/31) ≤ 2/93 < 1/24 = Nρ(s,a)/12. The simultaneous event is therefore empty, although
the lemma claims probability greater than 1−δ = 1/32. The printed proof fails at `|N_large| ≤ N/(8L) ≤ N`
(`offlineRL.tex:3607–3609`), which needs L = log(SN/δ) ≥ 1/8; here both pairs are in N_large and N = 1. Whenever
SN ≥ 2, L > log 2 and that step holds, so the failure needs SN = 1. The formal `N ≥ 2` version
(`Lemma6_5_sampleSplit_actualData_corrected`) is unaffected, and so is Theorem 6.3, whose sample regime implies
N ≥ 2. The entry is now a correction of a false printed statement rather than a domain restriction; ledgers that call
it "restricted" should say "corrected". Paper calculation, not Lean-checked. Raised by an external audit
(2026-11-08) and independently re-derived by a critic. Not author-approved.
```

---

## F4 — Theorem 7.11 qualifier and citation gap

**C43/COVERAGE wording (checked).** `docs/SOURCE-ISSUES.md` C43 (line ~1225 ff.) states the refutation holds "under
the reading in which rewards depend on (s,a) as printed at `inference.tex:62` and the undefined r(s) in Γ is r_π(s)",
and lists as not refuted "the reading with state-only rewards (or deterministic π) ... and the corrected statement".
`docs/COVERAGE.md:25` says "Printed statement refuted; corrected theorem open", "Under the reading with action-dependent
rewards and r(s) = r_π(s) in Γ", "Not refuted: the state-only-reward reading", and that the smooth-test partial result
"does not imply the printed theorem, any convex-set or confidence-region statement". **Both already meet the audit's
requirement.** The audit's restatement of the C43 instance (V^π = (1,1/2), zero TD error, Γ = I/128, distance 1) matches C43.

**Citation-gap arithmetic (exact, `check_findings.py`).** μ = (15/16, 1/16), γ = 3/4, P_π rows (1/2,1/2), x = (1,3):
A = diag(μ)(I−γP_π) = [[75/128, −45/128], [−3/128, 5/128]], xᵀAx = **−3/16** ✔. So A + Aᵀ is not positive
semidefinite. However trace A = 5/8, det A = 15/1024, discriminant 85/256 > 0: both eigenvalues are real and positive
(A is a nonsingular M-matrix, Gershgorin), so the mean TD ODE is still stable; only a Euclidean-accretivity step
cannot be reused. This is a gap in *applying the cited proof*, not a counterexample.

**External source (checked only via a fetched HTML summary of arXiv:2410.16106v6, not quoted from the PDF).** That
paper samples s_t i.i.d. from "μ, the stationary distribution", and its estimator is
Γ̂_T = Σ w_{t,T}(A_tθ̄_t − b_t)(·)ᵀ with time-specific θ̄_t, whereas the book (`inference.tex:166–169`, verified)
evaluates every residual at V̄_T and allows any μ with min μ > 0 (`:64`). Treat these two external facts as
**UNCLEAR pending a direct read of the cited paper** by the lead.

### DRAFT qualifying text (append to C43; mirror one sentence in COVERAGE row for Theorem 7.11)

```markdown
**Scope note (2026-11-09).** The machine-checked refutation depends on the reading r(s) = r_π(s) with action-dependent
rewards; under state-only rewards (or deterministic π) the printed statement is neither proved nor refuted. The
corrected statement (Γ replaced by the true residual covariance, assumed nonsingular) remains open, and the cited
proof may not transfer directly: the cited analysis (Wu et al., arXiv:2410.16106v6) samples states from the stationary
distribution, while the book allows any full-support μ. With μ = (15/16, 1/16), γ = 3/4 and both rows of P_π uniform,
xᵀdiag(μ)(I−γP_π)x = −3/16 at x = (1,3), so a Euclidean accretivity estimate is unavailable, although
diag(μ)(I−γP_π) still has positive eigenvalues. The book's Γ̂_T evaluates all residuals at V̄_T, while the cited
estimator uses the running averages. A corrected bound may still hold by another argument. Paper calculation, not
Lean-checked; the external-paper facts need a direct check against the cited version. Not author-approved.
```

COVERAGE sentence: "The corrected statement is open; the cited proof assumes stationary sampling and a different
covariance estimator, so it is not imported ([C43](SOURCE-ISSUES.md#C43))."

---

## F5 — Theorem 6.13 estimator quantifier

**Exact source.** Theorem 6.13 `thm:infinite-lwoer-bound` `offlineRL.tex:2367–2402`; infimum display
`eq:infinite-lower-bound-theorem` `:2381–2391`; "the infimum is taken over all policy estimators π̂, and P_{M_θ}
denotes the probability under M_θ" (`:2398–2401`). The chapter does not mention randomized estimators or seeds
(grep "randomiz" in offlineRL.tex: no hit in this theorem).

**Lean.** `Formalization/Statements/Ch6.lean` (Thm6_13, binder around `:283`):
`∀ πhat : (Fin N → (State × Bool) × State) → StationaryPolicy State Bool, ∃ θ, 1/4 ≤ (Measure.pi …).real {…}`.
So estimators are deterministic maps from data to (action-randomizing) stationary policies; the hard instance θ is
chosen after π̂ (correct order for an inf–max). With an independent seed U, P_θ(event) = E_U[f(θ,U)], and
"∀u ∃θ_u, f(θ_u,u) ≥ 1/4" does not imply "∃θ, E_U f(θ,U) ≥ 1/4" in general. The audit's claim is therefore correct
as a scope point. "Changes" relative to the audit: the book does not say "randomized"; the reading is the standard
minimax convention, not an explicit printed quantifier; and the ledgers already disclose it (`docs/COVERAGE.md:122`
"randomized estimators not covered literally"; `docs/named-result-status.json:449` "externally randomized estimators are
not covered literally"), while the category "Printed result proved" is what overstates. A further (not audited)
scope point: the Lean output class is stationary policies; the book does not restrict π̂'s output class either.

**Effort for the seed extension (estimate, no Lean run).** The infrastructure exists:
- `lb_fano_core` (`Formalization/OfflineRL/LowerBoundMinimax.lean:159`) already derives the *average* bound
  `1/4 ≤ (1/(M+1)) Σ_j P_j(ψ ≠ j)` (`hlow`, ~`:226`) before taking a maximum.
- `finiteSeed_averageTesting_to_oneRisk` (`Formalization/Generative/GenerativeLowerBoundSeededAveraging.lean:11`) turns
  a per-seed average-testing bound into ∃i with risk ≥ c under `independentSeedLaw` (= `μ.prod σ`,
  `GenerativeLowerBoundRandomSeed.lean:15`), for finite seed spaces; `GenerativeLowerBoundKernelQuarter.lean:16–53`
  is a ~40-line template doing exactly this for Chapter 3.
Plan: (1) extract `lb_fano_core_average` returning the averaged inequality (~40 lines, moved from the existing proof);
(2) `lb_minimax_core_seeded` for πhat : Data × Ξ → StationaryPolicy, finite Ξ: D(θ) = decoder error, R(θ) = gap event,
D ⊆ R pointwise by the existing `lbDecode_eq`/`lb_gap_ge_score` argument, then apply the averaging lemma (~50–70 lines);
(3) top-level seeded export reusing the instance construction of `offline_minimax_lower_bound` (~40 lines);
(4) statement entry `Thm6_13_randomized` (or strengthen the index entry) + proof wrapper (~40 lines).
Total ≈ 150–200 lines, finite seed, low risk. A general probability-space seed needs Fubini on `Measure.prod` (the data
space is finite with ⊤ σ-algebra, so P(E) = Σ_D p(D)·σ(E_D), only needing measurability of each seed section) plus a
measurability hypothesis on the estimator: roughly +100–150 lines.

### DRAFT scope disclosure / reclassification (append to "Statement-index scope disclosures")

```markdown
- Theorem 6.13 (`thm:infinite-lwoer-bound`, `offlineRL.tex:2367–2402`) takes the infimum over "all policy
  estimators" (`:2398–2399`). The index entry `Thm6_13` quantifies over deterministic maps from the N samples to
  stationary policies (which may randomize actions), with the hard instance chosen after the estimator. Estimators
  that use independent randomness to choose the output policy are a different quantifier: a hard instance found for
  each fixed seed may depend on the seed. Under the usual minimax reading, which includes such estimators, the entry
  is a restricted variant; it is reported as "restricted" until the seed extension (averaging the existing Fano
  average-error bound over an independent seed before choosing θ) is proved. Output classes other than stationary
  policies are also not covered. This is a scope limitation of the formalization, not an asserted source error.
  Not author-approved.
```

Matching COVERAGE row change: "**Restricted variant proved** (deterministic estimators; printed hypotheses and constants) ...
Estimators with independent internal randomization are not covered ([scope](SOURCE-ISSUES.md#statement-index-scope-disclosures))."
and `named-result-status.json` category for Theorem 6.13 → restricted (or keep "printed" only if the project explicitly
adopts and discloses the deterministic-estimator reading).

---

## What is Lean-checked vs paper-level (summary)

- Lean-checked and unaffected: C13 literal-trigger refutation of Lemma 5.12; `MVP_regret_corrected` (dyadic);
  `Lemma6_5_sampleSplit_actualData_corrected` (N ≥ 2); C43 refutations of Theorem 7.11; `scaledError_smooth_gaussian_le`;
  `Thm6_13` (deterministic estimators).
- Paper-level only (this review): all of F1 (incl. CLT/Lévy/Slutsky for the TD example), F2, F3 counterexample,
  F4 accretivity witness and the citation comparison, F5 effort estimate.
- External facts about arXiv:2410.16106v6 were read via a fetched-HTML summary only: UNCLEAR until directly checked.
