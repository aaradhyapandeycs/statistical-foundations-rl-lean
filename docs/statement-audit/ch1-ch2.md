> Public copy of an independent five-bin statement audit (2026-11-09/10), scrubbed of local paths and agent identifiers. Auditors were independent of the builders. No result here is author-approved. Method and totals: [README](README.md).

# Five-bin statement audit, batch ch1-ch2 (2026-11-09)

Auditor: independent statement auditor (no edits made outside this file; nothing compiled; no git/lake).
Source: `source/upstream/tex/chapters/intro.tex`, `prelim.tex`; upstream tar sha256 `54f8f7d096bc98e5ccebefeea59792296ad87c716a0ccf81b889b650758c0a92`, `source/provenance.json` sha256 `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51`.
Targets: `Formalization/Statements/Ch1.lean`, `Ch2.lean`, wrappers `Ch1Proofs.lean`, `Ch2Proofs.lean`.
No entry in these files carries a `_corrected`/`_restricted` suffix and `docs/SOURCE-ISSUES.md` has no entry for them, so the DISCLOSED bin is empty everywhere
and any deviation from the printed text would be a FAIL.

## Shared expansions (used by the tables below)

**M-bundle** = `M : DiscountedMDP State Action` (`MDP/CoreDefinitions.lean:28-38`), `[Fintype State] [Fintype Action]`. Expanded:
| field | Lean | bin | citation |
|---|---|---|---|
| Fintype State, Fintype Action | instances | TYPING | prelim.tex:34,36 (finite S, A) |
| state_nonempty, action_nonempty | `Nonempty` | TYPING | `{1..S}`, `{1..A}`, :34,36 |
| transition : S -> A -> FiniteDistribution S | prob vector, sum 1 | STANDING | prelim.tex:38-40 (P : S x A -> Delta(S)) |
| reward + reward_nonneg + reward_le_one | r in [0,1] | STANDING | prelim.tex:42 |
| discount + discount_nonneg + discount_lt_one | gamma in [0,1) | STANDING | prelim.tex:45 |
Counts for the bundle: SOURCE 0, STANDING 3, TYPING 3 (instances+nonempty counted as one TYPING group each: Fintype, Nonempty-state, Nonempty-action).

**pi-bundle** = `π : StationaryPolicy State Action` = `State -> FiniteDistribution Action` (`CoreDefinitions.lean:42`): STANDING (prelim.tex:66, stationary randomized policies; the chapter's policy class), 1 binder.

**Definitions relied on, checked for faithfulness (not just type inhabitants):**
- `trajectoryExpectedValue`, `trajectoryExpectedQ` (`MDP/InfiniteReturn.lean:~40`, `ForcedActionReturn.lean:~30`): Bochner integral of the actual `tsum` return under Ionescu-Tulcea laws
  `infiniteTrajectoryLaw` (`InfiniteTrajectory.lean:~66`: first step a0~pi(s0), s1~P; history kernel acts from last state) and `forcedActionTrajectoryLaw` (`ForcedActionTrajectory.lean:~17`: first action forced via pointMass, then pi). Matches eq:defn-Vpi-inf / eq:defn-Qpi-inf-horizon. Not junk (integrable, proved).
- `policyFixedPoint`, `optimalityFixedPoint` (`FixedPointDefinitions.lean`): `Classical.choose` of proved `∃!` solutions of `qBellman`/`qOptimality` (`FixedPointExistence.lean:40,46`). This is a characterization-defined object with the existence-and-uniqueness theorem proved first, so choice is not arbitrary. Identification with the trajectory Q is the content of index entries `Eq_bellman_consistency_V` (2nd conjunct) and `Eq_bellman_fix_point` plus library `trajectoryExpectedQ_eq_policyFixedPoint`; entries that use these objects (2.1, 2.1-count, 2.3 data, (2.24), (2.27), (2.28)) are faithful only modulo that bridge, which is proved in the library and appears in the index. Judged acceptable (the source itself states that Q^pi is the unique Bellman fixed point, prelim.tex:209, and uses Bellman forms to define the matrix identities), flagged as NOTE N1.
- `qOptimality` uses `actionMaximum` = `Finset.sup'` over a nonempty finite set (genuine max).
- `empiricalRow`, `sampleMeasure`, `rowMeasure` (`Probability/FiniteSampleDefinitions.lean`): empirical frequency vector `N^{-1} Σ 1{ω_i = s}` and `Measure.pi` of the row law. Faithful to prelim.tex:918-934.
- `finiteFamilyBorel` (`RandomFamilyBorel.lean`): σ-algebra on `Finset (State -> ℝ)` = infimum over n of pushforwards of Borel σ-algebras of injective n-tuples; sets measurable iff measurable preimage under every enumeration. A standard Borel structure on unordered finite families; includes the empty family. `rowVectorSpace` / `marginalMatrixVectorSpace`: comap of the real coordinate vector / Pi of it. Natural choices; the source leaves "independent" unspecified, so these are a TYPING-level choice (NOTE N2).
- `PrelimFano.averageErrorInfimum/minimaxErrorInfimum` (`Fano/TestRiskDefinitions.lean`): `sInf` of the range of average/worst-case error over measurable tests `Ω -> Fin (M+1)` (range nonempty and bounded in [0,1], so not junk); denominators `Fintype.card I = M+1`. Matches eq:defn-minimax/avg-prob-error.
- `FiniteDistribution.variance d f = E f² - (E f)²` matches eq:defn-Var-Psa-V.
- `bernoulliRealLaw p` = Bernoulli PMF pushed to {0,1} ⊂ ℝ.

---

## Ch1

### E1. `Eq_KL_ub_chi2` (Ch1.lean:30)  — source `eq:KL-ub-chi2`, `chapters/intro.tex:216–247` (read :210-250)
Reconstruction: for probability measures P ≪ Q on a common measurable space (Ω,F): 2·TV(P,Q)² ≤ KL(P‖Q) ≤ χ²(P‖Q), TV = sup_{A∈F}|P(A)-Q(A)|, KL = ∫log(dP/dQ)dP, χ² = ∫(dP/dQ-1)²dQ. P≪Q is the stated condition for KL, χ² (:229). Quantifiers: all Ω, P, Q.
| binder | Lean type | bin | citation |
|---|---|---|---|
| Ω, MeasurableSpace Ω | `Type u` | TYPING | :216 common measurable space |
| P Q | `Measure Ω` | SOURCE | :216 |
| IsProbabilityMeasure P, Q | instances | SOURCE | :216 "probability measures" |
| P ≪ Q | `P ≪ Q` | SOURCE | :229 |
Counts: SOURCE 3, STANDING 0, TYPING 1, DISCLOSED 0, EXCESS 0.
Other checks: TV is `⨆` over the subtype of measurable sets of |P.real A - Q.real A|, bounded by 1 and nonempty (∅), so a genuine sup. KL = Mathlib `klDiv` (equals ∫log dP/dQ dP when integrable, ⊤ otherwise, agrees with printed where defined). χ² as `∫⁻ ofReal((rnDeriv.toReal-1)²)`; since P≪Q, rnDeriv<⊤ Q-a.e., so `toReal` is not a junk-value problem; the lintegral reads the printed integral of a nonnegative function with value ∞ when not L². Conclusion `ofReal(2 TV²) ≤ klDiv ≤ χ²` in ℝ≥0∞ is the printed chain. Self-contained, not defined via a theorem type. Wrapper `Eq_KL_ub_chi2_holds` is a single application of `two_mul_sq_tv_le_klDiv_le_chiSquared`. Hypotheses satisfiable. Docstring accurate.
**Verdict: PASS**

---

## Ch2

All Ch2 entries below use the M-bundle (where they mention `M`), counted as STANDING 3 / TYPING 3, in addition to the listed rows.

### E2. `Lemma2_2` (Ch2.lean:35) — `lem:variance-perturbation-var-P-V`, `prelim.tex:458–467` (read 435-495)
Reconstruction: for V, V̂ ∈ R^S with 0 ≤ V, V̂ ≤ 1/(1-γ): ‖Var_P(V̂) - Var_P(V)‖_∞ ≤ 4/(1-γ)‖V̂-V‖_∞, Var_P(V)∈R^{SA} with entries P_{s,a}V² - (P_{s,a}V)².
| binder | Lean | bin | citation |
|---|---|---|---|
| State, Action, Fintype instances | | TYPING | :34,36 |
| M | M-bundle | STANDING (3), TYPING (3) | :34-45 |
| V Vhat | `State -> ℝ` | SOURCE | :459 |
| 0 ≤ V s ≤ 1/(1-γ) | hyp | SOURCE | :460 |
| same for Vhat | hyp | SOURCE | :460 |
Counts: SOURCE 3, STANDING 3, TYPING 3(+instances), EXCESS 0.
Other: norm on `State -> Action -> ℝ` is the Pi sup norm = max|.|, norm on `State -> ℝ` same; constant 4/(1-γ) exact; the Var vector built by `fun s a ↦ ...` matches (2.?) eq:defn-Var-Psa-V. Wrapper applies `transitionVariance_perturbation`.
**Verdict: PASS**

### E3. `Lemma2_9` Freedman (Ch2.lean:49) — `lem:Freedman-prelim`, `prelim.tex:1056–1075` (read 1050-1078)
Reconstruction: X_k real, |X_k| ≤ B, E[X_k | {X_j}_{j<k}] = 0, W_n = Σ E[X_k²|{X_j}_{j<k}] ≤ σ² deterministically; then for any integer K_0 ≥ 1 and 0<δ<1, w.p. ≥ 1-δ: |Y_n| ≤ sqrt(8 max{W_n, σ²/2^{K_0}} log(2K_0/δ)) + (4/3)B log(2K_0/δ). Order: (X,B,σ) fixed, then n, K_0, δ.
| binder | Lean | bin | citation |
|---|---|---|---|
| Ω, μ prob | | TYPING | prob. space |
| X : ℕ → Ω → ℝ, ∀n Measurable | | TYPING (random variables) | |
| B σ | ℝ | SOURCE | :1058-1066 |
| ∀ n ω, |X n ω| ≤ B | hyp | SOURCE | :1060 |
| cond. mean = 0 a.e. w.r.t. σ(X_j, j<k) (⨆ of comaps, empty ⨆ = ⊥ for k=0) | hyp | SOURCE | :1060 |
| n, K, 0<K | | SOURCE | :1066 |
| `∀ ω, Σ_k μ[X_k²|F_k] ω ≤ σ²` | hyp | SOURCE (but see issue) | :1062-1065 |
| δ, 0<δ<1 | | SOURCE | :1058 |
Counts: SOURCE 6, STANDING 0, TYPING 2, EXCESS 0 (one strength issue below).
Issue F1 (hypothesis strength): the printed hypothesis "W_n ≤ σ² holds deterministically" concerns a conditional expectation, which is defined only up to null sets. The Lean Prop requires `∀ ω` of one fixed Mathlib representative of `μ[·|·]`, which is strictly stronger than the a.s. reading (and the library theorem `freedman_natural_history` takes only `∀ᵐ`; the wrapper inserts `Filter.Eventually.of_forall`). The index Prop is therefore a weaker statement than the natural printed one: an instance whose W_n ≤ σ² only a.s., or only for another representative, is not covered. All other points check: strict/non-strict `1-δ ≤` matches "at least"; `max(W, σ²/2^K)`, `8`, `4/3`, `2K/δ` exact; sums over `range n` = k=1..n.
Fix: replace `(∀ ω, ∑ ... ≤ σ ^ 2)` by `(∀ᵐ ω ∂μ, ∑ ... ≤ σ ^ 2)` and have the wrapper pass the hypothesis directly (removing `Filter.Eventually.of_forall hcap`).
**Verdict: FAIL (minor: hypothesis `∀ ω` on a conditional-expectation representative instead of `∀ᵐ`)**

### E4. `Lemma2_8` Azuma-Hoeffding (Ch2.lean:77) — `lem:azuma-hoeffding`, `prelim.tex:1038–1052`
Reconstruction: |X_k| ≤ B_k deterministic, E[X_k|{X_j}_{j<k}]=0 ⇒ w.p. > 1-δ, |Σ_{k≤n}X_k| ≤ sqrt(2 Σ B_k² log(2/δ)).
| binder | Lean | bin | citation |
|---|---|---|---|
| Ω, μ prob | | TYPING | |
| X, B : ℕ → ℝ, X measurable | | TYPING/SOURCE (B_k is source) | :1040-1044 |
| |X k ω| ≤ B k | hyp | SOURCE | :1042 |
| cond. mean a.e. 0 | hyp | SOURCE | :1042 |
| n, δ, 0<δ<1 | | SOURCE | :1039 |
Counts: SOURCE 5, TYPING 2, EXCESS 0.
Other: conclusion `1-δ < μ.real` matches "exceeding"; bound exact. `condExp` is not junk (σ-algebra generated by measurable X_j is ≤ ambient). n=0 holds (prob 1). Wrapper applies `azuma_natural_history_source`.
**Verdict: PASS**

### E5. `Lemma2_3` (Ch2.lean:104) — `lem:basic-property-matrix-notation-inf`, `prelim.tex:544–574` (+ `intro.tex:204–209`)
Reconstruction: 0≤γ<1, any policy π: (I-γP_π)^{-1} = I + Σ_{i≥1}(γP_π)^i; (I-γP_π)^{-1}1_S = 1/(1-γ)1_S; ‖(I-γP_π)^{-1}‖_1 (max row abs sum) = 1/(1-γ); entrywise ≥ 0. Same for P^π with 1_{SA}.
| binder | Lean | bin | citation |
|---|---|---|---|
| M | M-bundle | STANDING/TYPING | |
| π | pi-bundle | STANDING | :544 "any policy" |
| Classical decEq (letI) | | TYPING | needed for `1` matrix |
Counts: SOURCE 0 (γ and π are the M, π binders), STANDING 4, TYPING 4, EXCESS 0.
Other: P_π(s,t)=Σ_a π(a|s)P(t|s,a) and P^π((s,a),(t,b))=P(t|s,a)π(b|t) match `P Π`, `Π P` (:~520). `Matrix.inv` is genuine since the matrix is invertible and equality with the series would fail on a junk 0 except trivially; `∑'` of a non-summable series would also be junk but the identity is proved (so it is a real convergent sum). ‖·‖ on `State -> ℝ` is sup norm applied to the vector of row sums = max row sum since entries are nonnegative. Wrapper uses `policyMatrices_resolvent_properties`.
**Verdict: PASS**

### E6. `Eq_Qpi_Vpi_matrix_notation_inf` (Ch2.lean:134) — eqs (2.24a–d), `prelim.tex:496–531`
Reconstruction: for every policy: Q = r+γPV; V = Π Q = r_π+γP_πV; V=(I-γP_π)^{-1}r_π; Q = r+γP^πQ; Q = (I-γP^π)^{-1}r.
Binders: M-bundle; π-bundle; Classical decEq (TYPING). Local lets define Q := policyFixedPoint, V := ΠQ, r, r_π, P (SA×S), P_π, P^π — all definitional abbreviations, not premises.
Counts: SOURCE 0, STANDING 4, TYPING 4, EXCESS 0.
Other: V is defined as Π^π Q^π (so the printed "V=ΠQ" equality is built in rather than concluded; V^π identification to the trajectory value is the separate printed identity eq:Vpi-a-function, covered by `Eq_defn_Qpi_inf_horizon`). Inverse is invertible by Lemma 2.3. See NOTE N1 (Q^π denoted by the unique Bellman solution).
**Verdict: PASS**

### E7. `Lemma2_1` (Ch2.lean:161) — `prelim.tex:339–343` with `eq:value_iteration` :317–319, `eq:policy_iteration` :328–330
Reconstruction: VI: Q_k = T(Q_{k-1}) from any Q_0, k≥1: ‖Q_k-Q*‖ ≤ γ^k‖Q_0-Q*‖. PI: π_0 arbitrary, π_k(s) = argmax_a Q^{π_{k-1}}(s,a), Q_k = Q^{π_k}: same bound.
| binder | Lean | bin | citation |
|---|---|---|---|
| M | M-bundle | STANDING/TYPING | |
| Q₀, k with 1≤k | | SOURCE | :341-343 |
| π : ℕ → policy, f : ℕ → S → A | | SOURCE (π_0 arbitrary initializer; f the argmax choice) | :328-330 |
| π(n+1) = pointMass(f n s) | hyp | SOURCE | :330 |
| f n s attains max of Q^{π_n}(s,·) | hyp | SOURCE | :330 |
Counts: SOURCE 5, STANDING 3, TYPING 3, EXCESS 0.
Other: iterate is `qOptimality^[k]`; ties allowed arbitrarily (stronger than a fixed tie rule). Q*, Q^{π} are the Bellman solutions (NOTE N1). `Nonempty Action` supplied from M. Wrapper = two library theorems (`value_iteration_error`, `arbitraryGreedyPolicyIteration_error`).
**Verdict: PASS**

### E8. `Lemma2_1_iterationCount` (Ch2.lean:189) — `prelim.tex:357–360`
Reconstruction (prose claim): to reach ‖Q_k-Q*‖ ≤ ε it takes no more than (1/(1-γ)) log(‖Q_0-Q*‖/ε) iterations, for VI and PI. Natural formalization: every k ≥ that quantity gives the bound.
Binders as Lemma2_1 plus ε>0 (SOURCE), no k≥1 hypothesis. Counts: SOURCE 6, STANDING 3, TYPING 3, EXCESS 0.
Other: junk value `log 0 = 0` when Q_0=Q* is disclosed in the docstring and harmless (conclusion true). γ=0 and ‖Q_0-Q*‖≤ε (log ≤ 0, k=0) fine since conclusion then trivial. The reading uses `log(x)/(1-γ) ≤ k` which implies γ^k ≤ ε/x since log(1/γ) ≥ 1-γ. The claim as printed is informal; this is the only precise reading. Wrapper uses `value_iteration_count`, `arbitraryGreedyPolicyIteration_count`.
**Verdict: PASS**

### E9. `Lemma2_7` (Ch2.lean:213) — `lem:tail-bound-sum-Bernoulli`, `prelim.tex:1001–1015`
Reconstruction: Z_i iid Bern(p), 0<p≤1, 1≤i≤n. ∀a>0: P(Σ(Z_i-EZ_i) < -an) ≤ exp(-a²n/(2p)); ∀τ ≥ 2pn: P(ΣZ_i>τ) ≤ 2exp(-0.19τ).
| binder | Lean | bin | citation |
|---|---|---|---|
| Ω, μ prob | | TYPING | |
| p, 0<p, p≤1 | | SOURCE | :1003 |
| n, Z : Fin n → Ω → ℝ | | SOURCE | |
| Measurable Z i | | TYPING | |
| iIndepFun Z μ | | SOURCE | :1003 |
| HasLaw (Z i) (bernoulliRealLaw p) μ | | SOURCE | "Bern(p)" |
| a>0 (lower tail) ; τ ≥ 2pn (upper) | | SOURCE | :1004-1013 |
Counts: SOURCE 6, TYPING 2, EXCESS 0.
Other: E Z_i = ∫ Z_i ∂μ (= p; integrable, bounded). n=0 fine. Both inequalities exact (0.19, factor 2). Wrapper applies `bernoulliTailBound_source`.
**Verdict: PASS**

### E10. `Lemma2_13` (Ch2.lean:233) — `lem:KL-quadratic-lower-bound`, `prelim.tex:1335–1346` (def. `eq:defn-KL-bern` :1326–1329)
Reconstruction: 0<p,q<1: KL(p‖q) ≤ (p-q)²/(q(1-q)); if 1/2 ≤ q<p<1: KL(p‖q) ≤ KL(q‖p) ≤ (p-q)²/(p(1-p)), KL(p‖q)= p log(p/q)+(1-p)log((1-p)/(1-q)).
Binders: p, q ∈ ℝ with the printed ranges (SOURCE 2+4 range hyps); no other premises. Counts: SOURCE 6 (range hypotheses), others 0, EXCESS 0.
Other: no junk (all logs of positive arguments). Wrapper applies the existing quadratic bound twice with arguments swapped and `bernoulliKL_le_reverse`, no substantive second proof.
**Verdict: PASS**

### E11. `Lemma2_11` reverse Fano (Ch2.lean:251) — `lem:reverse-Fano-bound`, `prelim.tex:1209–1229` (defs :1113–1128)
Reconstruction: P_0..P_M prob. measures on a common space; p_e ≥ p̄_e ≥ 1-1/(M+1) - sqrt(M/(2(M+1)²) Σ_{j=1}^M KL(P_0‖P_j)).
| binder | Lean | bin | citation |
|---|---|---|---|
| Ω, MeasurableSpace | | TYPING | |
| M : ℕ | | SOURCE | |
| P : Fin (M+1) → Measure Ω, IsProbabilityMeasure | | SOURCE | :1209-1212 |
Counts: SOURCE 2, TYPING 1, EXCESS 0.
Other: ℝ≥0∞ form `ofReal(1-1/(M+1)) ≤ ofReal(p̄_e) + (ofReal(M/(2(M+1)²))·ΣklDiv)^(1/2)` is equivalent to the printed inequality when the KL sum is finite (1-1/(M+1) ≥ 0, so no truncation) and is trivially true when infinite; for M≥1 the coefficient is positive so ∞ is not killed by `0*∞`; M=0 sum is empty. Mathlib's `klDiv` is ⊤ when P_0 ⋠≪ P_j, where the printed KL is undefined, so the Prop covers strictly more. `p̄_e ≤ p_e` included as first conjunct. Wrapper: `reverseFano_infimum_lower`.
**Verdict: PASS**

### E12. `Lemma2_6` empirical Bernstein (Ch2.lean:274) — `empirical bernstein`, `prelim.tex:985–997` (setting :916–934)
Reconstruction: P_{s,a} row d, N≥2 iid draws, P̂ empirical row; 𝒱 finite ⊂ R_+^S independent of P̂, 0<δ<1; w.p. >1-δ, ∀V∈𝒱: |(P̂-P)V| ≤ sqrt(2log(4|𝒱|/δ)/(N-1)) sqrt(Var_{P̂}(V)) + 7‖V‖ log(4|𝒱|/δ)/(3(N-1)).
| binder | Lean | bin | citation |
|---|---|---|---|
| State (Fintype), Ω, μ prob | | TYPING | |
| d : FiniteDistribution State | | SOURCE (P_{s,a}) | :919 |
| N, 2 ≤ N | | SOURCE | :988 |
| δ, 0<δ<1 | | SOURCE | :987 |
| draw : Ω → Fin N → State, Measurable | | TYPING | random sample |
| μ.map draw = d.sampleMeasure N | | SOURCE (iid draws from P_{s,a}) | :918-920 |
| family : Ω → Finset (State→ℝ), Measurable (finiteFamilyBorel) | | TYPING (random finite set) | N2 |
| IndepFun family (empiricalRow ∘ draw) | | SOURCE | :989 |
| ∀ω V∈family ω, ∀s, 0 ≤ V s | | SOURCE | 𝒱 ⊂ R_+^S |
Counts: SOURCE 6, STANDING 0, TYPING 4, EXCESS 0.
Other: empty family allowed (event vacuous, `log 0` junk unused). `‖V‖` sup norm; variance is `E_{P̂}V² - (E_{P̂}V)²` literally Var_{P̂}. Wrapper converts the library's radius `empiricalBernsteinFamilyRadius` to the printed form with algebra (`sqrt` product split) and monotonicity of measure; no re-proof of concentration.
**Verdict: PASS**

### E13. `Lemma2_4` Hoeffding (Ch2.lean:306) — `lem:Hoeffding-prelim`, `prelim.tex:939–950`
Reconstruction: as E12 with N>0, bound sqrt(‖V‖²log(2|𝒱|/δ)/(2N)), prob > 1-δ.
Binder table identical to E12 minus `2 ≤ N` (N>0 is typing for `empiricalRow`, TYPING). Counts: SOURCE 5, TYPING 5, EXCESS 0.
Other: constants exact (2|𝒱|, 2N). Wrapper applies `randomBorelFamily_empiricalRow_success_gt`.
**Verdict: PASS**

### E14. `Lemma2_5` Bernstein (Ch2.lean:331) — `lem:Bernstein-prelim`, `prelim.tex:956–978`
Reconstruction: (a) row: bound sqrt(2log(4|𝒱|/δ)/N) sqrt(Var_{P_{s,a}}V) + 2‖V‖log(4|𝒱|/δ)/(3N); (b) whole matrix P̂ ∈ R^{SA×S} independent of 𝒱: simultaneously for all (s,a) with 4SA|𝒱|/δ.
Part (a) binders as E13. Part (b):
| binder | Lean | bin | citation |
|---|---|---|---|
| State, Action : Type u, Fintype, Nonempty State, Nonempty Action | | TYPING | :34,36 |
| d : State × Action → FiniteDistribution State | | SOURCE (P) | :914 |
| draw : Ω → State×Action → Fin N → State, Measurable | | TYPING | |
| ∀ i, μ.map (draw · i) = (d i).sampleMeasure N | | SOURCE (each row iid P_{s,a}); cross-row independence NOT required, a weaker hypothesis than the setting at :916-920 | |
| family measurable; IndepFun family (whole empirical matrix) | | TYPING; SOURCE | :968 |
| nonneg | | SOURCE | |
Counts (b): SOURCE 6, TYPING 6, EXCESS 0.
Other: `Fintype.card State * card Action` = SA exact. Both parts conjoined as printed. Slight note: part (b) fixes Action and State in the same universe `Type u`, harmless for finite types (N3). Because the Prop assumes less (no independence across rows) it implies the printed result. Wrapper uses `randomBorelFamily_bernstein_source` and `randomBorelFamily_matrixBernstein_of_rowMarginals`.
**Verdict: PASS**

### E15. `Lemma2_12` KL tensorization (Ch2.lean:355) — `lem:KL-tensorize`, `prelim.tex:1313–1319`
Reconstruction: KL(P_1⊗…⊗P_n ‖ Q_1⊗…⊗Q_n) = Σ KL(P_i‖Q_i).
| binder | Lean | bin | citation |
|---|---|---|---|
| ι finite, α i, MeasurableSpace | | TYPING | |
| P Q : ∀ i, Measure (α i), IsProbabilityMeasure each | | SOURCE | :1313-1315 |
Counts: SOURCE 2, TYPING 2, EXCESS 0.
Other: equality in ℝ≥0∞ with Mathlib `klDiv`; where the book's KL is defined (P_i ≪ Q_i) values agree; elsewhere both sides are ⊤ (a non-ac coordinate makes the product non-ac), so no vacuity or false claim; ι empty gives 0 = 0. Docstring discloses the convention. Wrapper: `klDiv_pi_eq_sum`.
**Verdict: PASS**

### E16. `Lemma2_10` Fano (Ch2.lean:381) — `lem:fano`, `prelim.tex:1141–1168` (setting :1106–1132)
Reconstruction: (i) M=1: KL(P_1‖P_0) ≤ β < ∞ ⇒ p_e ≥ p̄_e ≥ max{e^{-β}/4, (1-√(β/2))/2}. (ii) M≥2, (1/(M+1))Σ_{j=1}^M KL(P_j‖P_0) ≤ β log M for some 0<β<1 ⇒ p_e ≥ p̄_e ≥ (log(M+1)-log2)/log M - β.
Binders (i): Ω, P : Fin 2 → Measure Ω prob (SOURCE), β ∈ ℝ (SOURCE), `klDiv (P 1)(P 0) ≠ ⊤` and `toReal ≤ β` (SOURCE, "≤ β < ∞"). (ii): M, 2≤M, P : Fin (M+1) → …, β, 0<β<1, ENNReal form of the KL hypothesis (all SOURCE). Counts: SOURCE 6 + 7, TYPING 2, EXCESS 0.
Other: in (ii) an infinite KL makes the hypothesis false, consistent with the printed requirement; `ofReal(1/(M+1))·Σ ≤ ofReal(β log M)` is the printed inequality (log M>0). Index of KL arguments `j.succ` runs over 1..M. Part (iii) is in a `comment` environment in the source (lines 1170–1199) and is correctly excluded. Wrappers: `fano_binary_infimum_lower`, `fano_multi_infimum_lower`.
**Verdict: PASS**

### E17. `Eq_QV_pi_perturbation_r_inf` (Ch2.lean:419) — eqs (2.27) `prelim.tex:613–631`
Reconstruction: M, M̃ same S,A,P,γ, different r̃ ∈[0,1]; every policy π: ‖Q^π-Q̃^π‖_∞ ≤ ‖r-r̃‖_∞/(1-γ), ‖V^π-Ṽ^π‖_∞ ≤ same.
Binders: M, M' (M-bundles; M' constrained), `M'.transition = M.transition`, `M'.discount = M.discount` (SOURCE, :606), π-bundle. Counts: SOURCE 2, STANDING 6, TYPING 6, EXCESS 0.
Other: norms are sup norms; V^π(s) = E_{a∼π} Q^π(s,a). NOTE N1. Wrapper: `policyFixedPoint_sub_norm_le_of_reward`, `policyValue_sub_norm_le_of_reward`.
**Verdict: PASS**

### E18. `Eq_QV_star_perturbation_r_inf` (Ch2.lean:446) — eq (2.28) `prelim.tex:633–653`
Reconstruction: same setting; ‖Q*-Q̃*‖ = ‖max_πQ^π - max_πQ̃^π‖ ≤ max_π‖Q^π-Q̃^π‖ ≤ ‖r-r̃‖/(1-γ); ‖V*-Ṽ*‖ ≤ ‖r-r̃‖/(1-γ).
Binders as E17 without π. Counts: SOURCE 2, STANDING 6, TYPING 6, EXCESS 0.
Other: `⨆ π` over all stationary randomized policies realizes `max_π`; bounded (proved; first conjunct shows the Q-sup equals `optimalityFixedPoint`, so sups are attained values, no junk); `⨆ π ‖…‖` bounded by `‖r-r̃‖/(1-γ)`; V⋆ represented as `⨆ π E_{a∼π(s)}Q^π(s,a)` which equals V^{π*} since π* maximizes V^π. Extra first conjunct is a conclusion, not a premise. Wrapper: `optimal_reward_perturbation`.
**Verdict: PASS**

### E19. `Eq_defn_Vpi_inf` (Ch2.lean:474) — `prelim.tex:94–106`
Reconstruction: V^π(s)=E[Σγ^t r(s_t,a_t)|s_0=s] well defined (the return is integrable under the trajectory law) and 0 ≤ V^π(s) ≤ 1/(1-γ).
Binders: M-bundle, π-bundle, s : State (SOURCE). Counts: SOURCE 1, STANDING 4, TYPING 3, EXCESS 0.
Other: `trajectoryExpectedValue` is the Bochner integral of the genuine `tsum` return under `infiniteTrajectoryLaw` (checked above). Wrapper: `integrable_infiniteDiscountedReturn`, `trajectoryExpectedValue_bounds`.
**Verdict: PASS**

### E20. `Eq_defn_Qpi_inf_horizon` (Ch2.lean:489) — `prelim.tex:117–129`
Reconstruction: Q^π(s,a) = E[Σγ^t r | s_0=s, a_0=a, then π]; V^π(s) = E_{a∼π(s)}Q^π(s,a).
Binders: M, π, s, a. Conjuncts: integrability, 0≤Q≤1/(1-γ) (extra, not premise), identity V=E Q. Counts: SOURCE 2, STANDING 4, TYPING 3, EXCESS 0.
Other: forced-action law is a genuine intervention. Wrapper: `integrable_infiniteDiscountedReturn_forced`, `trajectoryExpectedQ_bounds`, `trajectoryExpectedValue_eq_policyAverageQ`.
**Verdict: PASS**

### E21. `Eq_optimal_Vstar_Qstar_defn` (Ch2.lean:505) — `prelim.tex:132–143`
Reconstruction: there exists a deterministic stationary π* simultaneously maximizing Q^π(s,a), V^π(s) over (all stationary randomized) π at all (s,a); V*:=V^{π*}, Q*:=Q^{π*}.
Binders: M-bundle; ∃f; ∀π s a; second conjunct ∀ f g maximizers ⇒ same Q and V (shorthand independent of choice). Counts: SOURCE 3+, STANDING 3, TYPING 3, EXCESS 0.
Other: Q^π, V^π are the actual trajectory expectations. The second conjunct is an added, true consequence (conclusion side). Wrapper: `exists_stationary_trajectory_optimal` and antisymmetry.
**Verdict: PASS**

### E22. `Eq_defn_dpi_occupancy_discounted_dist` (Ch2.lean:539) — `prelim.tex:145–176`
Reconstruction: d^π(s;ρ)=(1-γ)Σγ^tP(s_t=s|s_0∼ρ), d^π(s,a;ρ)=(1-γ)Σγ^tP(s_t=s,a_t=a|s_0∼ρ); both normalized; for deterministic π*, d(s,a)=d(s)1{a=π*(s)}.
Binders: M-bundle, `[DecidableEq Action]` (TYPING), ρ (SOURCE), then ∀π (normalization), ∀ f s a (deterministic). Counts: SOURCE 1, STANDING 3, TYPING 4, EXCESS 0.
Other: events `{path | trajectoryState x path t = s ∧ (path t).1 = a}` correct since path t = (a_t, s_{t+1}); `∑'` is summable (proved sums = 1, so not junk). Deterministic claim for every deterministic f (⊇ π*). Wrapper uses `discountedStateOccupancy_eq_source`, `discountedJointOccupancy_*`.
**Verdict: PASS**

### E23. `Eq_bellman_consistency_V` (Ch2.lean:565) — `prelim.tex:191–223`
Reconstruction: Q^π = T^π Q^π, unique fixed point, V^π = T_π V^π with T^π(Q)(s,a) = r+γE_{s'}E_{a'∼π(s')}Q(s',a'), T_π(V)(s)=E_{a∼π}r(s,a) + γ E_{s'∼P(·|s,π)}V(s').
Binders: M, π. Counts: SOURCE 0, STANDING 4, TYPING 3, EXCESS 0.
Other: `P(s'|s,π)` written as `E_{a∼π(s)} P(s'|s,a)` (eq:defn-P-s-pi-inf) ✓. Wrapper: `trajectoryExpectedQ_bellman`, uniqueness via `policy_fixedPoint_exists_unique`, `valueFixedPoint_spec`.
**Verdict: PASS**

### E24. `Eq_bellman_fix_point` (Ch2.lean:586) — `prelim.tex:233–246`
Reconstruction: Q* = Q^{π*} is the unique fixed point of T, T(Q)(s,a)=r+γE_{s'}max_{a'}Q(s',a').
Binders: M, f : State → Action (SOURCE), hypothesis "f optimal" (SOURCE: π* optimal deterministic, :132). Counts: SOURCE 2, STANDING 3, TYPING 3, EXCESS 0.
Other: `⨆ a'` over a finite nonempty type = max (Nonempty from M, though not syntactically in the Prop; the junk value of ⨆ on an empty type cannot occur). Quantified over every optimal f, which is stronger than for the chosen π*. Wrapper uses `trajectoryExpectedQ_eq_optimalityFixedPoint_of_optimal`, `optimality_fixedPoint_exists_unique`.
**Verdict: PASS**

### E25. `Eq_gamma_contraction_preliminary_inf` (Ch2.lean:603) — `prelim.tex:251–261`
Reconstruction: ∀π, Q_1,Q_2: ‖T^πQ_1-T^πQ_2‖_∞ ≤ γ‖Q_1-Q_2‖_∞, ‖TQ_1-TQ_2‖_∞ ≤ γ‖Q_1-Q_2‖_∞.
Binders: M, π, Q₁, Q₂ (SOURCE). Counts: SOURCE 2, STANDING 4, TYPING 3, EXCESS 0.
Other: sup norm on `State → Action → ℝ`; `⨆` as in E24. Wrapper rewrites `T` to `qOptimality` and applies `norm_qBellman_sub_le`, `norm_qOptimality_sub_le`.
**Verdict: PASS**

### E26. `Eq_dh_pi_defn` (Ch2.lean:625) — `prelim.tex:749–774`
Reconstruction: finite-horizon nonstationary MDP, randomized Markov π; d_h^π(s;ρ)=P(s_h=s|s_1∼ρ), d_h^π(s,a;ρ)=P(s_h=s,a_h=a|s_1∼ρ)=d_h(s)π_h(a|s); d_1=ρ; for deterministic π*, d_h(s,a)=d_h(s)1{a=π*_h(s)}.
Binders: State, Action Fintype, DecidableEq both (TYPING), `stages : List (DecisionStage State Action)` (each stage: nonempty, kernel, r_h∈[0,1], policy π_h: STANDING :675-682, SOURCE policy), ρ (SOURCE). Conjuncts: product formula for all i,s,a; d at i=0 equals ρ; deterministic f with `policy = pointMass (f i x)` ⇒ `dj = d·1{a=f i s}` (SOURCE hypothesis). Counts: SOURCE 3, STANDING 3, TYPING 5, EXCESS 0.
Other: stage i ↔ h=i+1; `stages.take i` generates s_h by trajectoryLaw (action/transition path law), final-state event; joint adds one stage. Genuine probability events (not the product formula assumed). Wrapper uses `stateOccupancy_eq_trajectory_event`, `stateActionOccupancy_eq_trajectory_event`, `stateActionOccupancy_eq`.
**Verdict: PASS**

### E27. `Eq_Bellman_finite_pi` (Ch2.lean:652) — `prelim.tex:784–794`
Reconstruction: V_{H+1}=Q_{H+1}=0; ∀h∈[H]: Q_h=r_h+E_{s'∼P_h}V_{h+1}, V_h=E_{a∼π_h}Q_h.
Binders: stages list as E26. Conjuncts as above, with V_h, Q_h = `trajectoryValue`/`trajectoryQ` of the suffix `stages.drop i`, defined from actual path laws and cumulative path reward. Counts: SOURCE 0, STANDING 3, TYPING 3, EXCESS 0.
Other: terminal conjuncts trivial by `drop length`=[]. Wrapper: `trajectory_bellman_at` plus `simp`.
**Verdict: PASS**

### E28. `Eq_Bellman_finite_opt` (Ch2.lean:681) — `prelim.tex:798–806` with `:738–746`
Reconstruction: deterministic Markov optimal π* exists (maximizing V_h^π(s), Q_h^π(s,a) over all randomized Markov π at all (s,a,h)); for every optimal one: V*_{H+1}=Q*_{H+1}=0, Q*_h=r_h+E V*_{h+1}, V*_h=max_aQ*_h.
Binders: State, Action, `[Nonempty Action]` (TYPING, A≥1), `es : List (EnvironmentStage …)` (STANDING: nonstationary P_h, r_h∈[0,1]). Lets V,Q,det,IsOptimal are definitions; IsOptimal over all π : ℕ → policy and n<H (SOURCE). Counts: SOURCE 1, STANDING 3, TYPING 4, EXCESS 0.
Other: `⨆ a'` is a genuine max (finite, nonempty). Policies index from 0 ↔ h=1. Wrapper: `greedyDetSeq_dominates`, `finite_det_optimal_eq`, `trajectory_bellman_at`, `actionMaximum_eq_ciSup`.
**Verdict: PASS**

---

## Wrapper review
All 28 `_holds` theorems apply library theorems (names listed per entry). Wrappers that contain non-trivial lines: `Lemma2_6_holds` (algebraic conversion of the radius, monotonicity), `Lemma2_9_holds` (derives B≥0, passes ∀ᵐ), `Eq_Bellman_finite_opt_holds` (unfolding `controlled`/`drop`). None re-proves a concentration, Bellman or Fano result; no second proof of substance.

## Notes (do not change verdicts)
- N1 (update 2026-11-13: `Lemma2_1`, `Lemma2_1_iterationCount`, (2.24), (2.27), (2.28) now carry the identification with `trajectoryExpectedQ`/`trajectoryExpectedValue` as conjuncts, so they no longer rely on the bridge only in prose): Entries 2.1, 2.1-count, (2.24), (2.27), (2.28) denote Q^π, Q* by `policyFixedPoint`/`optimalityFixedPoint` (Classical.choose of proved ∃!), not by the trajectory integrals. Their equality with the trajectory Q is proved (`Eq_bellman_consistency_V`, `Eq_bellman_fix_point`, library `trajectoryExpectedQ_eq_policyFixedPoint`), so these entries read faithfully only together with those entries; acceptable but worth keeping visible.
- N2: σ-algebras on the random family (`finiteFamilyBorel`) and on empirical rows are the natural Borel choices; the source does not specify. A finer σ-algebra on the family would make independence a stronger premise, but this one is the standard Borel structure on unordered finite sets.
- N3: `Lemma2_5` part (b) uses `Action : Type u` (same universe as State).
- N4 (process, not statement fidelity): `Statements/Ch2.lean` imports several non-definition proof modules (e.g. `Probability.RandomFamilyBorel`, `EmpiricalHoeffdingRandomFamily`, `BernsteinMatrixMarginals`, `MDP.InfiniteReturn`, `FiniteOccupancy`) for the definitions it needs, whereas AGENTS.md asks for definition modules only; I did not check `scripts/gates/g2_statement_imports.txt`.

## Summary table
| # | Entry | Verdict |
|---|---|---|
| E1 | Eq_KL_ub_chi2 | PASS |
| E2 | Lemma2_2 | PASS |
| E3 | Lemma2_9 | FAIL (minor): `∀ ω` on condExp representative instead of `∀ᵐ` |
| E4 | Lemma2_8 | PASS |
| E5 | Lemma2_3 | PASS |
| E6 | Eq_Qpi_Vpi_matrix_notation_inf | PASS |
| E7 | Lemma2_1 | PASS |
| E8 | Lemma2_1_iterationCount | PASS |
| E9 | Lemma2_7 | PASS |
| E10 | Lemma2_13 | PASS |
| E11 | Lemma2_11 | PASS |
| E12 | Lemma2_6 | PASS |
| E13 | Lemma2_4 | PASS |
| E14 | Lemma2_5 | PASS |
| E15 | Lemma2_12 | PASS |
| E16 | Lemma2_10 | PASS |
| E17 | Eq_QV_pi_perturbation_r_inf | PASS |
| E18 | Eq_QV_star_perturbation_r_inf | PASS |
| E19 | Eq_defn_Vpi_inf | PASS |
| E20 | Eq_defn_Qpi_inf_horizon | PASS |
| E21 | Eq_optimal_Vstar_Qstar_defn | PASS |
| E22 | Eq_defn_dpi_occupancy_discounted_dist | PASS |
| E23 | Eq_bellman_consistency_V | PASS |
| E24 | Eq_bellman_fix_point | PASS |
| E25 | Eq_gamma_contraction_preliminary_inf | PASS |
| E26 | Eq_dh_pi_defn | PASS |
| E27 | Eq_Bellman_finite_pi | PASS |
| E28 | Eq_Bellman_finite_opt | PASS |

Counts: PASS 27, PASS-DISCLOSED 0, FAIL 1, UNSURE 0.

## Re-audit after fix (Lemma2_9 only)

Read: Ch2.lean:51-69 (docstring :~44-50), Ch2Proofs.lean:31-38, FIX-LOG.md line 4; source `prelim.tex:1056–1075` re-read.
Reconstruction unchanged (see E3). Binder table:
| binder | Lean | bin | citation |
|---|---|---|---|
| Ω, μ prob | | TYPING | |
| X : ℕ → Ω → ℝ, ∀n Measurable | | TYPING | |
| B σ | ℝ | SOURCE | :1058-1066 |
| ∀ n ω, \|X n ω\| ≤ B | hyp | SOURCE | :1060 |
| cond. mean =ᵐ 0 given σ(X_j, j<k) | hyp | SOURCE | :1060 |
| n, K, 0<K | | SOURCE | :1066 |
| `∀ᵐ ω ∂μ, Σ_k μ[X_k²\|F_k] ω ≤ σ²` | hyp | SOURCE (now a.s., matches the natural reading of "deterministically" for a conditional expectation) | :1062-1065 |
| δ, 0<δ<1 | | SOURCE | :1058 |
Counts: SOURCE 6, STANDING 0, TYPING 2, DISCLOSED 0, EXCESS 0.
Conclusion unchanged and exact (`1-δ ≤`, max{W_n, σ²/2^K}, 8, 4/3, 2K/δ). Wrapper now passes `hcap` directly to `freedman_natural_history` (no `of_forall` on that hypothesis; the remaining `of_forall` is for the pointwise bound |X_k| ≤ B, which is correct). Docstring explains the a.s. reading accurately.
**New verdict: PASS.** Updated totals for this batch: PASS 28, FAIL 0, UNSURE 0.
