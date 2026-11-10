> Public copy of an independent five-bin statement audit (2026-11-09/10), scrubbed of local paths and agent identifiers. Auditors were independent of the builders. No result here is author-approved. Method and totals: [README](README.md).

# Five-bin statement audit — batch ch7b (2026-11-09)

Auditor: independent statement auditor (read-only; no Lean compiled, no project files edited).
Targets: 19 entries in `Formalization/Statements/Ch7.lean`, wrappers in `Formalization/Statements/Ch7Proofs.lean`.
Source read: `source/upstream/tex/chapters/{RLHF.tex:15–215, marl.tex:15–245, 300–480, robust_RL.tex:20–135, 255–270,
inference.tex:45–190, intro.tex:214–236, prelim.tex:58–72}`.
Definitions expanded: `TDInference/Definitions.lean` (whole plug-in section), `RLHF/VPO/Definitions.lean`,
`RLHF/VPO/PrintedStatement.lean` (`IsPositivePolicy`, `vpoObjective`, `IsVPOMinimizer`), `MultiAgent/LowerBound/Definitions.lean`,
`MultiAgent/ModelBased/Definitions.lean`, `MultiAgent/LowerBound/PrintedStatement.lean`, `RobustRL/LowerBounds/Ch7Definitions.lean`,
`MDP/CoreDefinitions.lean` (`FiniteDistribution`, `DiscountedMDP`, `StationaryPolicy`),
`Generative/FiniteHorizonSamplingDefinitions.lean`, `Probability/FiniteSampleDefinitions.lean` (`empiricalRow`),
`RobustRL/DRVI/RowSets.lean` (`RowAttains`).
SOURCE-ISSUES entries checked: C39, C43 (incl. plug-in paragraph), C44, C45, C47(4), "Statement-index scope
disclosures" (RLHF bullet, lines 469–491).

Common TYPING conventions used below: `Fintype`/`DecidableEq`/`Nonempty` instances on finite carriers;
`DiscountedMDP` bundles reward ∈ [0,1], 0 ≤ γ < 1, nonempty S, A (prelim conventions; reward/discount fields are
STANDING, `robust_RL.tex:24–28`, `prelim.tex`); `FiniteDistribution` = actual probability vector.

---

## 1. Eq_defn_hat_Lambda_restricted — Ch7.lean:822 (wrapper Ch7Proofs.lean:445)

Source: `eq:defn-hat-Lambda`, `inference.tex:180–184` (Ā_T, Γ̂_T :160–170, weights :173–177, Λ⋆ = A⁻¹ΓA⁻ᵀ :99–117,
sampling :49–64, step sizes :133–134).

Reconstruction: TD with η_t = η₀t^{-2/3}, 0 < η₀ < 1/4, i.i.d. tuples s ∼ μ (min μ > 0), a ∼ π, s' ∼ P; V̄_T the PR
average; Λ̂_T = Ā_T⁻¹Γ̂_TĀ_T⁻ᵀ "is the final estimator of Λ⋆". No explicit theorem is printed; the only
mathematical content is that Λ̂_T estimates Λ⋆, i.e. (read) consistency Λ̂_T → Λ⋆ in probability, for every V₀.

Lean: ∀ finite instance, π, μ, η₀, V₀, [r(s,·) constant on supp π(·|s)] → μ > 0 → 0 < η₀ < 1/4 → ∀ ε > 0,
P(∃ s s', |Λ̂_T(s,s') − Λ⋆_printed(s,s')| > ε) → 0.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action + Fintype/DecidableEq/Nonempty | Type | TYPING | finite S, A |
| M | DiscountedMDP | SOURCE | `inference.tex:47` MDP (P, r, γ) |
| π | StationaryPolicy | SOURCE | :47 fixed policy |
| μ | FiniteDistribution State | SOURCE | :63 |
| η₀ | ℝ | SOURCE | :133 |
| V₀ | State → ℝ | SOURCE (universal init) | :70–74 (init unspecified; ∀ is the strong reading) |
| reward const on supp π | ∀ s a a', … | DISCLOSED | name `_restricted`, docstring, SOURCE-ISSUES C43 plug-in paragraph |
| ∀ s, 0 < μ s | Prop | SOURCE | :63 λ₀ > 0 |
| 0 < η₀, η₀ < 1/4 | Prop | SOURCE/STANDING | :133 |
| ε, 0 < ε | conclusion quantifier | — | consistency reading |

Counts: SOURCE 6, STANDING 0 (η₀ range counted SOURCE), TYPING 1 group, DISCLOSED 1, EXCESS 0.

Other checks: `printedLambda` uses `(tdA)⁻¹`; tdA = diag(μ)(I − γP_π) is invertible under μ > 0, γ < 1, so no junk.
`lambdaHat` junk 0 on singular Ā_T is disclosed (C47(4)) and only affects an event of vanishing probability.
`pathProb` is the exact i.i.d. product weight. Wrapper applies `eq_defn_hat_Lambda_restricted` (η₀ < 1/4 ⇒ η₀ ≤ 1).
Consistency is an interpretive reading of "estimator", stated in docstring and C43. Not vacuous (all hypotheses
satisfiable, e.g. state-only rewards).

Verdict: **PASS-DISCLOSED**.

## 2. Thm7_12_corrected — Ch7.lean:879 (wrapper :233)

Source: `thm_online`, `RLHF.tex:208–215`; algorithm :182–203; assumption :146–153; J, J⋆ :41–45, :92–102.

Reconstruction: under linear rewards (‖φ‖ ≤ 1, r⋆ = ⟨φ, θ⋆⟩), ‖θ⋆‖ ≤ r_max and ‖θ^{(t)}‖ ≤ r_max ∀t, with the printed
α (depends on T, κ, d, r_max, β), w.p. 1 − δ, Regret := Σ_{t=1}^T [J⋆(r⋆;π_cal) − J(r⋆,π^{(t)};π_cal)] ≤
Õ(e^{2r_max + r_max/β}√(κdT)); κ = sup π_cal/π_ref; π^{(t+1)} = argmin of the online VPO objective over D^{(t)}.

| binder | Lean type | bin | citation |
|---|---|---|---|
| X, Y, Fintype | Type | DISCLOSED | (ii); C44 "finite context and response sets" |
| d, 0 < d | ℕ | SOURCE/TYPING | :149 ℝ^d |
| T, 1 ≤ T | ℕ | DISCLOSED | (iii); C44 |
| ρ, ρ ≥ 0, Σρ = 1 | X → ℝ | SOURCE | :43 x ∼ ρ |
| π_ref, IsPositivePolicy | X→Y→ℝ | STANDING | log π_ref in objective (:62–66, :196), κ ratio :214; scope-disclosures bullet |
| π_cal, IsCondPolicy | X→Y→ℝ | SOURCE | :92–96 |
| φ, ‖φ‖ ≤ 1 | features | SOURCE | :149–151 |
| θstar, ‖θ⋆‖ ≤ r_max | EuclideanSpace | SOURCE | :151, :210 |
| β, 0 < β | ℝ | SOURCE | :46 |
| r_max, 0 < r_max | ℝ | SOURCE | :210 |
| α, 0 < α | ℝ | DISCLOSED (generalized: all α) | (iii); C44 |
| δ, 0 < δ | ℝ | SOURCE | :211 |
| sel, IsBallSelection | selection rule | DISCLOSED | (i); C44 (replaces ‖θ^{(t)}‖ ≤ r_max and argmin) |

Counts: SOURCE 8, STANDING 1, TYPING (in d), DISCLOSED 4, EXCESS 0.

Other checks: round indexing (0-indexed round k uses sel(D of rounds < k) = source π^{(k+1)} from D^{(k)}) matches
:194–198; round-0 sample unused as printed (C44). `vpoTrajWeight` is the exact product law. `vpoKappa` iSup over
a finite type: genuine max. `optCalValue` sSup over a nonempty bounded set (Y nonempty forced by IsCondPolicy).
Conclusion is an explicit bound, not the printed rate — disclosed (v). Wrapper: applies `vpo_regret_both` and
weakens the conjunctive indicator with `split_ifs` — no second proof. Non-vacuous: existence of a ball selection is
part of the conclusion.

Verdict: **PASS-DISCLOSED**.

## 3. Thm7_12_corrected_local — Ch7.lean:907 (wrapper :242)

Same source, same binders and bins as entry 2 (counts SOURCE 8, STANDING 1, DISCLOSED 4, EXCESS 0). Conclusion: the
κ-free local-curvature bound; differs from printed rate, disclosed (docstring, C44 "also at most a local-curvature
bound"). Wrapper identical pattern (`h1.2`).

Verdict: **PASS-DISCLOSED**.

## 4. Eq_DPO_restricted — Ch7.lean:953 (wrapper :255)

Source: `eq:DPO` with `eq:reward-policy-eq`, `RLHF.tex:52–74`.

Reconstruction: π_DPO = argmin_π −Σ log σ(β(log π(y₊|x)/π_ref(y₊|x) − log π(y₋|x)/π_ref(y₋|x))); claims: obtained by
substituting r = β(log π_r − log π_ref + log Z) into ℓ (so DPO(π_r) = ℓ(r)), Z cancels; hence DPO argmin ↔ reward MLE.

| binder | Lean type | bin | citation |
|---|---|---|---|
| X, Y, Fintype | Type | DISCLOSED | scope-disclosures bullet (finite X, Y) |
| π_ref, IsPositivePolicy | — | DISCLOSED/STANDING | scope bullet (implicit full support) |
| β, 0 < β | ℝ | SOURCE | :46 |
| D | List | SOURCE | :30 |

Argmin domain = full-support policies: DISCLOSED (name, docstring, scope bullet). Counts: SOURCE 2, DISCLOSED 2,
EXCESS 0. Conclusions (i)–(iv) are the printed cancellation, correspondence, non-identifiability (:90) and the
argmin equivalence; existence of minimizers not claimed (consistent with C44). Wrapper: four library applications.

Verdict: **PASS-DISCLOSED**.

## 5. Eq_policy_RBMLE_restricted — Ch7.lean:987 (wrapper :263)

Source: `RLHF.tex:105–141` (`eq:RBMLE`, `eq:Jstar`, `eq:policy_RBMLE`, KL remark :137–140).

Reconstruction: ℓ(r) − sign·α·J⋆(r;π_cal) equals the policy objective at π_r; argmin over π_r = argmin over π;
replacing π_ref by π_cal in the last term does not change minimizers and equals −E KL(π_cal‖π).

| binder | bin | citation |
|---|---|---|
| X, Y finite | DISCLOSED | scope bullet |
| ρ, ρ ≥ 0 | SOURCE (weakened: no normalization) | :43 |
| π_ref positive | DISCLOSED/STANDING | scope bullet |
| π_cal IsCondPolicy | SOURCE | :92 |
| sign ∈ {±1} | SOURCE | :111 |
| α > 0 | SOURCE | :111 |
| β > 0 | SOURCE | :46 |
| D | SOURCE | :30 |

Counts: SOURCE 6, DISCLOSED 2, EXCESS 0. Conclusion (iv) ∃K shift identity matches :137; (iii) KL identity matches
:138–140 (0 log 0 = 0 via Lean log 0 = 0, fine for full-support π). Wrapper supplies K explicitly (a witness term,
not a substantive proof) and applies library lemmas.

Verdict: **PASS-DISCLOSED**.

## 6. Eq_online_RBMLE_restricted — Ch7.lean:1030 (wrapper :272)

Source: `RLHF.tex:158–198` (`eq:RBMLE_online`, `eq:RLHF-policy`, combination claim :177, `eq:online_RBMLE`).

Reconstruction: two-step update (r^{(t+1)} = argmin ℓ − αJ⋆; π^{(t+1)} = argmax J(r^{(t+1)}, ·)) can be replaced by the
single policy update `eq:online_RBMLE`.

Binders: X, Y finite (DISCLOSED), ρ ≥ 0 (SOURCE), π_ref positive (DISCLOSED/STANDING), π_cal (SOURCE), α, β > 0
(SOURCE), D arbitrary (SOURCE: covers D^{(t)}), r with ∀r', obj r ≤ obj r' (SOURCE: r^{(t+1)} is a minimizer).
Counts: SOURCE 6, DISCLOSED 2, EXCESS 0.

Other checks: (a) uses the printed uncalibrated J of `eq:KL_reward` inline; (b) `IsVPOMinimizer` with coefficient α
is exactly the :194–198 objective. Only the direction "two-step output solves the one-step update" is stated; the
converse (every one-step minimizer is some π_r) is in entry 5 (ii) with sign = 1 — acceptable, and the docstring
says what is claimed. Uniqueness not claimed (disclosed). Wrapper: one library application.

Verdict: **PASS-DISCLOSED**.

## 7. Eq_reward_policy_eq_restricted — Ch7.lean:1058 (wrapper :282)

Source: `RLHF.tex:52–66`. Reconstruction: r = β(log π_r − log π_ref + log Z(r,x)) for all (x, y).
Binders: X, Y finite (DISCLOSED), π_ref positive (DISCLOSED/STANDING), β > 0 (SOURCE), r, x, y (SOURCE). Z written
out per :56–59, π_r = `gibbsPolicy` (literal :54). Counts: SOURCE 4, DISCLOSED 2, EXCESS 0.

Verdict: **PASS-DISCLOSED**.

## 8. Eq_Jstar_restricted — Ch7.lean:1077 (wrapper :288)

Source: `eq:Jstar`, `RLHF.tex:115–124`, with J⋆ of :99–102. All four printed lines are reproduced term-for-term
(line 1 :118–119, line 2 :120, (i) :121, (ii) :122). ρ ≥ 0 only (assumes less). Binders: X, Y (DISCLOSED), ρ ≥ 0,
π_cal cond, β > 0, r (SOURCE), π_ref positive (DISCLOSED/STANDING). Counts: SOURCE 4, DISCLOSED 2, EXCESS 0.
`optCalValue` = sSup over a nonempty bounded set; not junk.

Verdict: **PASS-DISCLOSED**.

## 9. Eq_RLHF_policy_closed_form_restricted — Ch7.lean:1107 (wrapper :295)

Source: `RLHF.tex:41–59`. Reconstruction: π_r := argmax_π J(r, π) has the Gibbs closed form.
Binders: X, Y (DISCLOSED), π_ref positive (DISCLOSED/STANDING), ρ ≥ 0 (SOURCE), β > 0 (SOURCE), r (SOURCE). J and π_r
written inline (KL via `klDiv`, correct for full-support π_ref). Conclusion characterizes the whole argmax set
(unique on supp ρ) instead of asserting uniqueness — disclosed (scope bullet). Counts: SOURCE 3, DISCLOSED 2,
EXCESS 0.

Verdict: **PASS-DISCLOSED**.

## 10. Eq_calibrated_value_shiftInvariant_restricted — Ch7.lean:1138 (wrapper :303)

Source: `RLHF.tex:86–102`. Reconstruction: for r₁ = r₂ + c(x): equal differences, ℓ(r₁,D) = ℓ(r₂,D),
J⋆(r₁) = J⋆(r₂) + E_ρ c, J(r₁,π;π_cal) = J(r₂,π;π_cal) ∀π, hence equal J⋆(·;π_cal).
Binders: X, Y (DISCLOSED), π_ref positive (DISCLOSED, scope bullet explains formal-KL reason), ρ ≥ 0, π_cal, β > 0,
r₂, c (SOURCE). Counts: SOURCE 5, DISCLOSED 2, EXCESS 0. With unnormalized ρ, Σρc is the stated weighted sum; for
a distribution it is E_ρ c (assumes less). Wrapper only reorders a library conjunction.

Verdict: **PASS-DISCLOSED**.

## 11. Thm7_6_restricted — Ch7.lean:1193 (wrapper :314)

Source: `thm:sample-complexity-plug-in-marl`, `marl.tex:384–399`; plug-in :355–378; NE :213–221; CCE :230–238;
gap :327–342; normalization :41–43.

Reconstruction: ∃ universal C₁ > 0: ∀ game, δ ∈ (0,1), 0 < ε ≤ √H, N ≥ C₁H³ε⁻² log(SHN∏A_i/δ) ⇒ w.p. ≥ 1 − δ,
gap(π̂_NE) ≤ ε ∧ gap(π̂_CCE) ≤ ε, π̂ = oracle equilibria of the empirical game (true reward).

| binder | bin | citation |
|---|---|---|
| ∃ C₁ > 0 (outermost) | SOURCE | universal constant, quantified before all sizes |
| m, S, H, A | SOURCE/TYPING | :15–30 |
| hS : 0 < S, hA : 0 < A_i | DISCLOSED | docstring "Added binders"; C45 |
| G | SOURCE | |
| rewards ∈ [0,1] on steps 1..H | STANDING | :41–43 |
| N, hN : 0 < N | DISCLOSED | C45 |
| 0 < δ < 1 | SOURCE | :386 |
| 0 < ε ≤ √H | SOURCE | :387 |
| sample-size condition | SOURCE | :394–396 (N inside log) |
| oracle causality (Occe, One) | DISCLOSED | C45 restriction |
| oracle returns CCE / NE of every empirical game | SOURCE | :376–378, defs :217–238 |

Counts: SOURCE 7, STANDING 1, DISCLOSED 3, EXCESS 0. Other checks: `empiricalGame` uses empirical frequencies at
steps 1..H and the true reward (:367–374); `gameSamplingLaw` = product of N i.i.d. draws per (h,s,a);
`gapJ`/`gap` are max over s, i of BR value minus value, BR via genuine iSup (bounded: finite horizon). (b),(c) not
shown non-vacuous in Lean (Nash existence) — disclosed; mathematically non-vacuous (backward-induction stage-Nash
oracle is causal). Wrapper is a direct library application.

Verdict: **PASS-DISCLOSED**.

## 12. Thm7_7_restricted — Ch7.lean:1286 (wrapper :322)

Source: `thm:Q-FTRL`, `marl.tex:441–467`; generative model :307–311.

Reconstruction: ∀ δ ∈ (0,1), ε ∈ (0,H]: ∃ model-based algorithm (Q-FTRL) that w.p. ≥ 1 − δ finds (a) ε-NE in two-player
zero-sum with Õ(SAH⁴/ε²) samples, (b) ε-CCE in general-sum with Õ(H⁴SΣA_i/ε²) samples.

| binder | bin | citation |
|---|---|---|
| ∃ C > 0 (outermost) | SOURCE (Õ read as universal constant × log) | C39 readings |
| m, S, H, A; 1 ≤ S, 1 ≤ A_i | TYPING / DISCLOSED | 𝒮 = {1..S}; C39 "added domain conditions" |
| 0 < δ < 1, 0 < ε ≤ H | SOURCE | :443 |
| rew ∈ [0,1] on 1..H (b) | STANDING | :41–43 |
| zero-sum rew (a) | SOURCE/STANDING | :50–54 |
| ∃ N, rule, out (depends on rew, δ, ε; not P) | SOURCE (existential) | known reward: generative_model_model_based.tex:31; C39 |
| ∀ P | SOURCE | |

Counts: SOURCE 6, STANDING 1, TYPING 1, DISCLOSED 1 (+ disclosed weakened conclusion), EXCESS 0. Deviation: the
witness is not shown to be Q-FTRL nor "model-based"; A read as max(A₁,A₂); Õ read with explicit log — all disclosed
in name, docstring, C39. Non-vacuity: H = 0 is excluded by 0 < ε ≤ H, so Query types are nonempty. Wrapper is a
direct library application.

Verdict: **PASS-DISCLOSED**.

## 13. Eq_mdp_value_Q — Ch7.lean:1346 (wrapper :332)

Source: `eq:mdp-value-Q`, `robust_RL.tex:88–98`, with the RMDP of :20–52 and robust V/Q :71–84.

Reconstruction: for the RMDP with (s,a)-rectangular set U^σ(P⁰) built from a **general "distance-like metric" ρ**
(:36–46; TV and χ² are "two popular instances", :52), σ > 0: ∃ deterministic π⋆ maximizing V^{π,σ} at every s
(resp. Q^{π,σ} at every (s,a)); V⋆ = max_π V^{π,σ}, Q⋆ = max_π Q^{π,σ}.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, Fintype | Type | TYPING | |
| M (nominal P⁰, r ∈ [0,1], γ < 1) | DiscountedMDP | SOURCE/STANDING | :24–28 |
| σ, 0 < σ | ℝ | SOURCE | :38 |
| ball ∈ {tvBall, chiBall} (hard-coded) | RowBall | **EXCESS (undisclosed domain narrowing)** | source: general ρ :36–46 |
| π over StationaryPolicy | — | STANDING | prelim.tex:66 |

Counts: SOURCE 2, STANDING 2, TYPING 1, DISCLOSED 0, EXCESS 1.

Other checks: robust V/Q are sInf over admissible kernels of actual trajectory values (static adversary), correct.
One f serving both V and Q is stronger (fine). The plain entry name and "Disclosures (none is a source issue)" do
not record that only the TV and χ² instances are covered; no SOURCE-ISSUES entry; COVERAGE.md:19 says "Printed
claim proved". The general-ρ claim is not implied by the Lean statement.

Verdict: **FAIL** (narrowed domain on a plain entry). Proposed fix: either (a) rename to `Eq_mdp_value_Q_restricted`,
state in the docstring that only the TV and χ² balls are covered (general distance-like ρ of :36–46 not claimed),
and add a bullet under "Statement-index scope disclosures" in `docs/SOURCE-ISSUES.md`; or (b) keep the plain name
and generalize to every `ball : RowBall State` whose rows at radius σ satisfy `RowAttains` (the library theorem
`exists_det_robust_value_Q_optimal` at `RobustRL/DRVI/RobustQ.lean:191` is already ball-generic), recording that
"distance-like" is read as "row sets on which the inner infimum is attained" — itself a reading that would then
need disclosure, so (a) is the simpler correct fix.

## 14. Eq_bellman_equ_infinite_all — Ch7.lean:1390 (wrapper :347)

Source: `eq:bellman-equ-infinite-all`, `robust_RL.tex:102–113`, objects :71–98.

Reconstruction: for the general-ρ RMDP, every policy π: Q^{π,σ} = r + γ inf_{P∈U(P⁰_{s,a})}⟨P, V^{π,σ}⟩, and
Q⋆ = r + γ inf ⟨P, V⋆⟩.

Binders: State/Action (TYPING), M (SOURCE/STANDING), σ > 0 (SOURCE), `ball` with hypothesis `ball = tvBall ∨ ball =
chiBall` (**EXCESS**: narrowing of general ρ; disclosed only in docstring prose "Scope … Other choices of ρ are not
claimed" while the docstring also says "No source issue"; name is plain; no SOURCE-ISSUES entry), πs with
domination hypothesis in (3) (SOURCE: π⋆ definition :90–92). Counts: SOURCE 3, STANDING 1, TYPING 1, DISCLOSED 0,
EXCESS 1.

Other checks: inner `⨅ q : ball …` over a nonempty bounded set (nominal row is in the ball); V⋆ = sSup over
stationary policies attains (by (3)); conclusions match both printed displays. Wrapper only applies library
lemmas after deriving `RowAttains` for the two balls.

Verdict: **FAIL** (scope narrowing on a plain entry; docstring discloses but name and SOURCE-ISSUES do not). Fix: as
entry 13 — rename `_restricted` + SOURCE-ISSUES scope bullet, or generalize over balls with `RowAttains` (the
library lemmas `robustPolicyQ_eq_reward_add_iInf` etc. take a general `ball` with `hU`).

## 15. Eq_robust_bellman_fixedPoint — Ch7.lean:1433 (wrapper :364)

Source: `robust_RL.tex:114–133` (T^σ, unique fixed point Q⋆, γ-contraction in ℓ∞, DRVI geometric convergence from
any initialization) and :261–262 (empirical operator).

Binders: TYPING (State, Action), M, σ > 0, πs dominating (SOURCE/STANDING), `ball = tvBall ∨ ball = chiBall`
(**EXCESS**, same narrowing). Counts: SOURCE 3, STANDING 1, TYPING 1, DISCLOSED 0, EXCESS 1.

Other checks: T written out with V(s) = ⨆_b Q(s,b) (finite nonempty Action via M); ‖·‖ is the sup norm on
State → Action → ℝ; (e) γ^t/(1 − γ) is a valid quantitative strengthening (Q₀ = 0, ‖Q⋆‖ ≤ 1/(1−γ)). The statement
is conditional on a value-maximizing πs, whose existence is entry 13 (fine, not vacuous). Wrapper: library lemmas
plus `drviIterate_error`.

Verdict: **FAIL** (same scope narrowing; fix as entry 13/14).

## 16. Marl_bestResponse_exists — Ch7.lean:1473 (wrapper :457)

Source: `marl.tex:96–143` (values, `eq:defn-optimal-V`, best-response existence :128–132, Bellman optimality
:135–143).

Reconstruction: V⋆_{i,h}(s) = max over Markov π'_i of V^{π'_i×π_{-i}}_{i,h}(s); ∃ π'_i attaining at all (h, s);
V⋆_{H+1} = 0; Bellman: V⋆_h(s) = max_{a_i} E_{a_{-i}∼π_{-i,h}}[r + ⟨P_h, V⋆_{h+1}⟩].

| binder | bin | citation |
|---|---|---|
| m, S, H, A | TYPING/SOURCE | :15–30 |
| G | SOURCE | (no reward bound assumed: assumes less) |
| π joint policy | SOURCE | :80–85 |
| i | SOURCE | |
| 0 < A i | TYPING | 𝒜_i = {1..A_i} |

Counts: SOURCE 3, TYPING 2, EXCESS 0. `deviate π i π'` = independent π'_i with the marginal π_{-i} (:119–122);
valueJ over steps h..H via k = H+1−h; iSup is shown to be a max by (1)+(2). Bellman expectation over a ∼ π_h with
a_i replaced equals the printed E over a_{-i} ∼ π_{-i,h}. Wrapper: four library applications.

Verdict: **PASS**.

## 17. Marl_NE_isCCE_not_converse — Ch7.lean:1500 (wrapper :467)

Source: `marl.tex:213–240` ("every Nash equilibrium is also a CCE, although the converse does not generally hold").

Reconstruction: (1) NE (product) ⇒ CCE; (2) ∃ game with a CCE that is not an NE.
Binders (1): m S H A G (SOURCE/TYPING), σ product policy (SOURCE), π with π_h(a|s) = ∏_j σ_{j,h}(a_j|s) (SOURCE: the
product policy viewed as joint), IsNE σ (SOURCE). (2) existential witness with rewards ∈ [0,1] (STANDING). Counts:
SOURCE 4, STANDING 1, TYPING 1, EXCESS 0. Since NE is defined only for products and CCE = NE on products (step-1
inequality vs. equality, BR ≥ value), "not a product law at step 1" is the right formal content of "not NE".
Wrapper: library applications.

Verdict: **PASS**.

## 18. Eq_convex_distance_le_TV — Ch7.lean:1527 (wrapper :480)

Source: `inference.tex:122–129` (d_cvx), `intro.tex:218–227` (TV = sup over the σ-algebra).
Binders: d (SOURCE), P, Q probability measures on (Fin d → ℝ, Borel) (SOURCE). Counts: SOURCE 3, EXCESS 0.
Convex sets need not be Borel; P.real C is the outer measure — a reasonable reading, disclosed; the inequality holds
under it (a measurable hull for P + Q is a hull for both). Both sSup sets are nonempty (∅) and bounded by 1, so not
junk. Wrapper: one library application.

Verdict: **PASS**.

## 19. Eq_tdWeights_sum — Ch7.lean:1539 (wrapper :490)

Source: `inference.tex:173–177`. w_{t,T} = t/Σu = 2t/(T(T+1)), weights sum to 1. Binder: T with 1 ≤ T (TYPING;
weights undefined at T = 0). 0-based index disclosed. Counts: SOURCE 1, TYPING 1, EXCESS 0.

Verdict: **PASS**.

---

## Summary

| # | Entry | Verdict | Note |
|---|---|---|---|
| 1 | Eq_defn_hat_Lambda_restricted | PASS-DISCLOSED | C43 restriction; consistency reading |
| 2 | Thm7_12_corrected | PASS-DISCLOSED | C44 (i)–(v) |
| 3 | Thm7_12_corrected_local | PASS-DISCLOSED | C44 |
| 4 | Eq_DPO_restricted | PASS-DISCLOSED | scope bullet |
| 5 | Eq_policy_RBMLE_restricted | PASS-DISCLOSED | scope bullet |
| 6 | Eq_online_RBMLE_restricted | PASS-DISCLOSED | one direction of combination claim; converse in #5 |
| 7 | Eq_reward_policy_eq_restricted | PASS-DISCLOSED | |
| 8 | Eq_Jstar_restricted | PASS-DISCLOSED | |
| 9 | Eq_RLHF_policy_closed_form_restricted | PASS-DISCLOSED | |
| 10 | Eq_calibrated_value_shiftInvariant_restricted | PASS-DISCLOSED | |
| 11 | Thm7_6_restricted | PASS-DISCLOSED | C45; (b),(c) non-vacuity not in Lean (disclosed) |
| 12 | Thm7_7_restricted | PASS-DISCLOSED | C39 |
| 13 | Eq_mdp_value_Q | FAIL | plain entry restricted to TV/χ² balls; source uses general ρ (:36–46) |
| 14 | Eq_bellman_equ_infinite_all | FAIL | same narrowing; prose-only disclosure, "No source issue" |
| 15 | Eq_robust_bellman_fixedPoint | FAIL | same narrowing |
| 16 | Marl_bestResponse_exists | PASS | |
| 17 | Marl_NE_isCCE_not_converse | PASS | |
| 18 | Eq_convex_distance_le_TV | PASS | outer-measure reading for non-Borel convex sets |
| 19 | Eq_tdWeights_sum | PASS | |

Totals: PASS 4, PASS-DISCLOSED 12, FAIL 3, UNSURE 0.

The three FAILs are a single scope issue (no mathematical error found): the robust-MDP displays are printed for an
(s,a)-rectangular set from a general "distance-like metric" ρ, while the plain entries cover only the TV and χ²
instances. Fix: rename to `_restricted` with a SOURCE-ISSUES scope-disclosure bullet (and update COVERAGE rows 19–21
from "Printed claim proved"), or generalize over `RowBall` families with `RowAttains` rows, which the library
already supports.

---

## Re-audit after fix (2026-11-09)

What I read: `Formalization/Statements/Ch7.lean:1317–1462`; the wrappers at `Ch7Proofs.lean:334–391`;
`docs/SOURCE-ISSUES.md:474–484` (the new scope bullet); `docs/COVERAGE.md` rows 19–21, now
"Restricted claim(s) proved"; `FIX-LOG.md`.

### Eq_mdp_value_Q_restricted (Ch7.lean:1352)
- **Binders:** State, Action (TYPING); M (SOURCE/STANDING); σ > 0 (SOURCE).
- **New ball premise:** `ball` with `tvBall ∨ chiBall ∨ (∀ s a V, ∃ q ∈ ball(P⁰_{s,a}, σ) minimizing ⟨q, V⟩)` is DISCLOSED.
  - The name has the `_restricted` suffix.
  - The docstring says that reading "distance-like" as implying attainment is an interpretation, and that families without attainment are not claimed.
  - The SOURCE-ISSUES scope bullet states the same thing.
- **Quantifier order:** `∀ ball, hyp → ∃ f, …`, so f is chosen per ball. That matches the source, where π⋆ depends on U^σ.
- **Other checks:**
  - The TV and χ² disjuncts are redundant, because both families satisfy the attainment disjunct. This is harmless.
  - The attainment premise implies the row sets are nonempty, so the sInf/iInf terms are not junk.
- **Wrapper:** derives `RowAttains` (the TV/χ² family lemmas, or the hypothesis itself, definitionally) and then applies `exists_det_robust_value_Q_optimal`. It contains no second proof.
- **Counts:** SOURCE 2, STANDING 2, TYPING 1, DISCLOSED 1, EXCESS 0.
- **Verdict: PASS-DISCLOSED.**

### Eq_bellman_equ_infinite_all_restricted (Ch7.lean:1398)
- The ball premise is the same and is DISCLOSED. "No source issue" has been removed.
- The conclusions are unchanged from the first audit.
- **Wrapper:** derives `RowAttains` as above, then applies the RobustBellmanDisplays lemmas only.
- **Counts:** SOURCE 3, STANDING 1, TYPING 1, DISCLOSED 1, EXCESS 0.
- **Verdict: PASS-DISCLOSED.**

### Eq_robust_bellman_fixedPoint_restricted (Ch7.lean:1446)
- The ball premise is the same and is DISCLOSED.
- **Quantifier order:** `∀ ball, hyp → ∀ πs, dominance → …`.
- **Wrapper:** applies the library lemmas plus `drviIterate_error`.
- **Counts:** SOURCE 3, STANDING 1, TYPING 1, DISCLOSED 1, EXCESS 0.
- **Verdict: PASS-DISCLOSED.**

### Residual note (not a failure)
The old unsuffixed names still appear only in historical `docs/critic-*.md` files. The fix log already records this.

### Updated totals for ch7b
PASS 4, PASS-DISCLOSED 15, FAIL 0, UNSURE 0.
