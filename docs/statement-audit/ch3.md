> Public copy of an independent five-bin statement audit (2026-11-09/10), scrubbed of local paths and agent identifiers. Auditors were independent of the builders. No result here is author-approved. Method and totals: [README](README.md).

# Five-bin statement audit — batch ch3 (2026-11-09)

Auditor: independent statement auditor (no edits outside this report; no compilation, no git, no lake).
Targets: all 19 `def … : Prop` in `Formalization/Statements/Ch3.lean` and their `_holds` wrappers in
`Formalization/Statements/Ch3Proofs.lean`.
Source read: `source/upstream/tex/chapters/generative_model_model_based.tex` (abbrev. MB) lines 1–160,
160–380, 440–500, 600–640, 780–790, 820–1010, 1200–1470, 1541–1640, 1715–1840, 2515–2590;
`chapters/prelim.tex` (abbrev. PR) :45 (γ ∈ [0,1)), :312–345 (VI/PI), :725–745 (finite-horizon optimal
deterministic policy). Standing conventions used: rewards in [0,1] and known (MB:31, PR:42–45),
γ ∈ [0,1) (PR:45), generative sampling i.i.d. per (s,a) / (s,a,h) (MB:20–30), A ≥ 2 in the
policy-learning section (MB:787).

Project definitions expanded (read in full): `DiscountedMDP`, `FiniteDistribution`, `expectation`,
`StationaryPolicy` (`MDP/CoreDefinitions.lean`); `policyTransition` (`MDP/Basic.lean:136`);
`FiniteDistribution.variance` (`Probability/VarianceDefinitions.lean`, E[f²]−(Ef)²);
`trajectoryExpectedValue` (`MDP/InfiniteReturn.lean:43`, integral of the actual infinite discounted
return); `trajectoryExpectedQ` (`MDP/ForcedActionReturn.lean:35`); `optimalGreedyAction/Policy`
(`MDP/OptimalTrajectoryValue.lean:21,33`, choice from the proved ∃! optimality fixed point, with
`trajectoryValue_le_optimalGreedy` proving genuine optimality); `policyFixedPoint`,
`optimalityFixedPoint` (choice from proved ∃!), `valueFixedPoint`, `qOptimality`, `actionMaximum`
(`Finset.sup'`); `rowMeasure`, `empiricalRow` (frequency vector, `Probability/FiniteSampleDefinitions.lean`);
all of `Statements/Ch3Definitions.lean` (both `samplingLaw`s are `Measure.pi` of the true rows,
`empiricalModel`s keep reward and discount, `EmpiricallyOptimal` = optimal against every stationary
policy at every state, `stateAbsorbingModel` = MB (eqn:transition-kernel-M-su-inf)/(eqn:reward-M-su-inf),
`absorbingGridStep = 1/(N(1−γ))`, `absorbingGridPoint i = i/(N(1−γ))`, `leaveOneOutBeta =
2log(16SAN/((1−γ)δ))`, `empiricalStage(s)`, `backwardGreedyActions`, `policyTrajectorySuffix/QSuffix`);
`EnvironmentStage`, `optimalValue`, `optimalQ` (backward induction, `MDP/EnvironmentDefinitions.lean`);
`controlled`, `greedyAction` (`MDP/PolicyEnvironmentDefinitions.lean`); `trajectoryValue`,
`trajectoryQ` (finite path laws); finite-horizon `Samples`/`samplingLaw`
(`Generative/FiniteHorizonSamplingDefinitions.lean`); `hardRow`/`hardMDP`
(`Generative/GenerativeLowerBoundTwoStateDefinitions.lean`: P(s₁|s₁)=p, s₂ absorbing, r = 1 at s₁).
No fallback/junk definitions found: every `Classical.choose` is from a proved ∃! or a proved
maximizer existence; empirical objects are only defined for `0 < N` (typed witness, no junk branch);
the matrix inverses `(1 − γ•P)⁻¹` are of genuinely invertible matrices (stochastic P, γ < 1).
Norms on `State → ℝ` / `State → Action → ℝ` are Pi sup norms = the source ‖·‖∞.

Bin abbreviations: SRC = SOURCE, STD = STANDING, TYP = TYPING, DIS = DISCLOSED, EXC = EXCESS.
Universal "carrier" binders (`State Action : Type*`, `[Fintype …]`, or `S A : ℕ` with `Fin S`, `Fin A`)
are TYP throughout (finite state/action spaces, PR standing). `M : DiscountedMDP …` is SRC/STD (its
fields: nonempty spaces TYP, reward ∈ [0,1] STD PR:42–45, γ ∈ [0,1) STD PR:45).

---

## 1. `Thm3_1` — Ch3.lean:24; source `thm:model-based-policy-eval`, MB:140–156 (algorithm MB:90–125)

Reconstruction: ∃ universal c₀ > 0, ∀ (finite S, A, MDP, policy π), ∀ ε ∈ (0, 1/(1−γ)], δ ∈ (0,1),
N ≥ c₀ log(S/(δ(1−γ)))/((1−γ)³ε²) ⇒ P(∀s |V̂^π(s) − V^π(s)| ≤ ε) ≥ 1−δ, where V̂^π = (I−γP̂_π)⁻¹ r_π
with P̂_π the frequency rows from N i.i.d. draws per state from P_π(·|s).

| binder | Lean type | bin | citation |
|---|---|---|---|
| c, 0 < c (∃, outermost) | ℝ | SRC | "some sufficiently large constant c₀" MB:153 |
| S A N | ℕ (Fin S, Fin A) | TYP | finite spaces; N sample size MB:94 |
| M | DiscountedMDP (Fin S) (Fin A) | SRC/STD | MB:62–74, PR:45 |
| π | StationaryPolicy | SRC | MB:66 |
| δ ε | ℝ | SRC | MB:142 |
| 0<δ, δ<1, 0<ε, ε ≤ 1/(1−γ) | Prop | SRC | MB:142 |
| sample threshold | Prop | SRC | MB:150–152 |

Counts: SRC 7, STD 0 (inside M), TYP 1, DIS 0, EXC 0.
Other checks: c chosen before everything. Conclusion `∃ hN : 0 < N, 1−δ ≤ P(‖V̂−V‖ ≤ ε)` is stronger
than printed (adds N > 0, which the premises force: S ≥ 1, δ(1−γ) < 1 ⇒ log > 0 ⇒ N > 0); docstring
correct. `samplingLaw` = product of true P_π rows; `valueEstimator` = Bellman fixed point of a model with
rows P̂_π and reward r_π = (I−γP̂_π)⁻¹r_π. No junk value (log argument > 1). Wrapper: direct library term.
Verdict: **PASS**.

## 2. `Eq_Vhatpi_Vpi_difference_decoupled_Hoeffding` — Ch3.lean:50; source `eq:eq:Vhatpi-Vpi-difference-decoupled-Hoeffding`, MB:270–276 (context 173–276)

Reconstruction: ∃ universal C₀ > 0 such that for any finite model, policy, N ≥ 1, δ ∈ (0,1): with
probability exceeding 1−δ, ‖V̂^π − V^π‖∞ ≤ C₀(√(log(S/δ)/((1−γ)⁴N)) + log(S/δ)/((1−γ)²N)).

| binder | Lean type | bin | citation |
|---|---|---|---|
| C₀, 0<C₀ (∃ outermost) | ℝ | SRC | "for some universal constant C₀" MB:218 |
| S A N | ℕ | TYP | |
| hN : 0 < N | Prop | TYP | display divides by N; N = per-state sample size ≥ 1 |
| M, π | | SRC/STD | MB:62–74 |
| δ, 0<δ, δ<1 | | SRC | MB:202–206, Bernstein with prob. 1−δ |

Counts: SRC 3, TYP 2, others 0. Strict "> 1−δ" as printed (MB:275). Wrapper: direct library term.
Verdict: **PASS**.

## 3. `Eqn_ice_cream` — Ch3.lean:71; source `eqn:ice-cream`, MB:619–634 (β₁ at :478, m at :624)

Reconstruction: for a large enough constant C₀, with β₁ = C₀ log(Sm/δ), m = ⌈log(e/(1−γ))⌉, for any
finite model/policy, δ ∈ (0,1) and N ≥ β₁/(1−γ): with probability exceeding 1−δ,
‖V̂^π − V^π‖∞ ≤ 3√(8β₁/((1−γ)³N)).

| binder | Lean type | bin | citation |
|---|---|---|---|
| C, 0<C; ∀ C₀ ≥ C | ℝ | SRC | "some large enough constant C₀" MB:478 |
| State Action, Fintype | | TYP | |
| M, π | | SRC/STD | |
| N, hN : 0 < N | | TYP | display divides by N |
| δ, 0<δ<1 | | SRC | Thm 3.1 context MB:142 |
| m, β₁ (let) | | SRC | MB:478, :624, :634 |
| β₁/(1−γ) ≤ N | | SRC | MB:633 |

Counts: SRC 5, TYP 2, others 0. Strict probability as printed. Intermediate chain expression is a proof
step (correctly omitted). C3 records the source proof gap; the stated bound is true (library proves it
for all N ≥ 1, C₀ ≥ 8). Wrapper: witness 8, ignores the N premise (export assumes less). Verdict: **PASS**.

## 4. `Thm3_2_positiveN` — Ch3.lean:89; source `Thm:sample-compl-main`, MB:900–923

Reconstruction: ∃ universal c₀ > 0: ∀ finite model, δ ∈ (0,1), ε ∈ (0,1/(1−γ)], N ≥ c₀
log(SAN/((1−γ)²εδ))/((1−γ)³ε²) ⇒ with prob ≥ 1−δ every optimal deterministic policy π̂⋆ of M̂ has
V^{π̂⋆} ≥ V⋆ − ε and Q^{π̂⋆} ≥ Q⋆ − γε.

| binder | Lean type | bin | citation |
|---|---|---|---|
| c₀, 0<c₀ (∃ outermost) | | SRC | MB:902 |
| State Action, Fintype | | TYP | |
| M | | SRC/STD | |
| N | ℕ | SRC | MB:916 |
| hN : 0 < N | Prop | DIS | name `_positiveN`, docstring, SOURCE-ISSUES "Statement-index scope disclosures" (Thm 3.2 item) |
| δ ε, 0<δ<1, 0<ε≤1/(1−γ) | | SRC | MB:902 |
| threshold | | SRC | MB:917–919 |
| ∀ f, EmpiricallyOptimal → … (inside event) | | SRC | "any optimal deterministic policy" MB:902, MB:840 |

Counts: SRC 6, TYP 1, DIS 1, EXC 0. V⋆ and Q⋆ are values of the proved-optimal greedy policy
(tie-independent). Policy quantified inside the event. At N = 0 the printed premise is degenerate
(log 0) and the algorithm undefined, so the disclosure is honest. Wrapper: library export with `.le`.
Verdict: **PASS-DISCLOSED**.

## 5. `Lemma3_3` — Ch3.lean:114; source `LemAbsToNormalV`, MB:1254–1263 (construction 1222–1252)

Reconstruction: for any MDP and state s, with u⋆ = V⋆(s), V⋆_{s,u⋆} = V⋆.

| binder | type | bin | citation |
|---|---|---|---|
| State Action, Fintype | | TYP | |
| M | | SRC | MB:1222 ("given any MDP") |
| x (absorbing state) | State | SRC | MB:1224 |
| s (pointwise evaluation) | State | TYP | function equality written pointwise |

Counts: SRC 2, TYP 2. `optimalValueAbsorbingModel` = `stateAbsorbingModel M x V⋆(x)` matches
(eqn:transition-kernel-M-su-inf)/(eqn:reward-M-su-inf) exactly; side proofs u ∈ [0,1/(1−γ)] are derived,
not assumed. Wrapper: direct library application. Verdict: **PASS**.

## 6. `Lemma3_4` — Ch3.lean:125; source `LemValueCover`, MB:1292–1300 (net at :1285–1290)

Reconstruction: with ε = 1/(N(1−γ)) and net {0, ε, …, Nε}, for each state s ∃ u₀ in the net with
‖V̂⋆ − V̂⋆_{s,u₀}‖∞ ≤ ε (V̂⋆ empirical optimal value; M̂_{s,u} absorbing modification of M̂).

| binder | type | bin | citation |
|---|---|---|---|
| State Action, Fintype | | TYP | |
| M, N | | SRC | MB:1275–1290 |
| hN : 0 < N | | TYP | ε = 1/(N(1−γ)) needs N ≥ 1; M̂ needs N ≥ 1 |
| data | Samples | SRC | statement holds for every realization (deterministic lemma) |
| x | State | SRC | "for each state s" |
| ∃ i : Fin (N+1) | | SRC | net of cardinality N+1 |

Counts: SRC 4, TYP 2. `absorbingGridValue M̂ … x i` = optimal value of `stateAbsorbingModel M̂ x (i/(N(1−γ)))`;
`absorbingGridStep M` uses M's discount = M̂'s. Wrapper: direct library application. Verdict: **PASS**.

## 7. `Lemma3_5_positiveN` — Ch3.lean:142; source `lem:policy-learning-evaluation`, MB:1306–1326

Reconstruction: ∃ large universal c₀, c₁ > 0: ∀ finite model, δ ∈ (0,1), β₁ = 2log(16SAN/((1−γ)δ)),
N ≥ c₀β₁/(1−γ) ⇒ w.p. ≥ 1−δ: ‖V̂^{π̂⋆} − V^{π̂⋆}‖∞ ≤ c₁√(2β₁/(N(1−γ)³)) and
0 ≤ V⋆ − V^{π̂⋆} ≤ 2c₁√(β₁/(N(1−γ)³)) entrywise.

| binder | type | bin | citation |
|---|---|---|---|
| c₀ c₁ > 0 (∃ outermost) | | SRC | MB:1324 |
| State Action, Fintype; M | | TYP / SRC | |
| N | | SRC | |
| hN : 0 < N | | DIS | `_positiveN`, docstring, SOURCE-ISSUES scope disclosures (Lemma 3.5 named) |
| δ, 0<δ<1 | | SRC | MB:1308 |
| c₀β₁/(1−γ) ≤ N | | SRC | MB:1324 |
| ∀ f EmpiricallyOptimal (inside event) | | SRC | π̂⋆ any optimal deterministic policy (MB:1003) |

Counts: SRC 5, TYP 1, DIS 1, EXC 0. β₁ matches `leaveOneOutBeta` exactly. Both displayed conclusions kept
(norm bound and the two-sided pointwise bound). Wrapper: library export, drops one extra conjunct
(export concludes more). Verdict: **PASS-DISCLOSED**.

## 8. `Thm3_9_causal_positiveN` — Ch3.lean:180; source `Thm:sample-compl-finite`, MB:2551–2570

Reconstruction: see entry 18 (`Thm3_9`).

| binder | type | bin | citation |
|---|---|---|---|
| c₀ > 0 (∃ outermost) | | SRC | MB:2553 |
| State Action, Fintype | | TYP | |
| H, E : Fin H → EnvironmentStage | | SRC | finite-horizon MDP, MB:2531 |
| hH : 0 < H | | TYP | implied by 0 < ε ≤ H (docstring says so); used only to name a fallback action |
| N | | SRC | |
| hN : 0 < N | | DIS | `_positiveN`, docstring, SOURCE-ISSUES scope disclosures (Thm 3.9 item) |
| δ ε, 0<δ, 0<ε≤H | | SRC | MB:2553 |
| threshold c₀H³log(HSA/δ)/ε² ≤ N | | SRC | MB:2566–2568 |
| tie rule fixed to `backwardGreedyActions` | (in conclusion) | DIS | `_causal` suffix, docstring, SOURCE-ISSUES scope disclosures ("earlier entry … for the concrete backward-greedy tie rule") |

Counts: SRC 5, TYP 2, DIS 2, EXC 0. `backwardGreedyActions` on `empiricalStages` is a genuine
backward-induction optimal policy of M̂ (fallback only beyond stage H). The general tie-free statement
is entry 17/18. Wrapper: library export + event monotonicity. Verdict: **PASS-DISCLOSED**.

## 9. `Eq_lemma_VarP_V_bound` — Ch3.lean:219; source `eq:I-gamma-P-Var-bound` MB:327–341 and `eq:lemma-VarP-V-bound` MB:346–352

Reconstruction: for any finite model and policy π: 0 ≤ (I−γP_π)⁻¹Var_{P_π}(V^π) ≤ (2‖V^π‖∞²/γ²)1
entrywise, and 0 ≤ ‖(I−γP_π)⁻¹√Var_{P_π}(V^π)‖∞ ≤ √(2/(1−γ))‖V^π‖∞/γ. (Both displays divide by γ;
the derivation at MB:318–327 multiplies by 1/γ², so the claim is only defined for γ > 0.)

| binder | type | bin | citation |
|---|---|---|---|
| State Action, Fintype, DecidableEq State | | TYP | matrix carrier |
| M, π | | SRC/STD | |
| 0 < γ | Prop | TYP (domain of definition) | printed RHS has /γ, /γ² (MB:341, :350); standing γ ∈ [0,1) PR:45; γ = 0 point undefined in print |

Counts: SRC 2, TYP 2, EXC 0. P, V, VarV, R literally as printed (`variance` = E[V²] − (EV)²; R a true
inverse). Intermediate chain steps omitted (proof steps). The γ > 0 exclusion is the domain where the
printed expressions are defined, so it is not a deviation; it is noted in COVERAGE.md but not in
SOURCE-ISSUES scope disclosures (recommendation only: add a one-line note there for consistency with how
Lemma 6.6's division-by-zero domain is handled). Wrapper: library bounds plus short algebra (deriving the
printed weaker constants from stronger exports); no second proof of substance. Verdict: **PASS**.

## 10. `Lemma3_6` — Ch3.lean:241; source `lem:empirical-value-residual`, MB:1395–1410, event `eq:Bernstein-empirical-optimal-value` MB:1373–1376

Reconstruction: on the event |(P̂_{π̂⋆} − P_{π̂⋆})V̂⋆| ≤ √(β₁/N)√Var_{P_{π̂⋆}}[V̂⋆] + 2β₁/(N(1−γ)) (all s):
γ‖(I−γP_{π̂⋆})⁻¹|(P̂_{π̂⋆} − P_{π̂⋆})V̂⋆|‖∞ ≤ 2√(2β₁/(N(1−γ)³)) + 6β₁/(N(1−γ)²), with β₁ = 2log(16SAN/((1−γ)δ)) ≥ 4.

| binder | type | bin | citation |
|---|---|---|---|
| State Action, Fintype; M | | TYP / SRC | |
| N, hN : 0 < N | | SRC / TYP | N ≥ 1 used at MB:1371 |
| data | | SRC | the event is a property of the realization |
| f, EmpiricallyOptimal | | SRC | π̂⋆ any optimal deterministic policy of M̂ |
| β, 0 ≤ β | | SRC (generalization) | source β₁ ≥ 4 (MB:1371) is a special case; export assumes less |
| event hypothesis (∀ s …) | | SRC | MB:1373–1376 / "On the event" MB:1399 |

Counts: SRC 6, TYP 1, EXC 0. V̂⋆ = `valueEstimator` = empirical optimal value (= V̂^f for every
empirically optimal f). Not vacuous (event satisfiable for large β). Wrapper: rewrites V̂⋆ to V̂^π then
applies library theorem. Verdict: **PASS**.

## 11. `Lemma3_8` — Ch3.lean:266; source `lem:properties-M01-lower-generative`, MB:1747–1767, parameters MB:1730–1735, MDPs MB:1575–1640

Reconstruction: for γ ∈ [2/3,1), 0 < ε < 1/(32(1−γ)), p = (4γ−1)/(3γ), α = 32(1−γ)²ε/(9γ²):
(i) 1/2 ≤ p < p+α < 1 and 1−p ≥ 2α; (ii) Q⋆_{M₁}(s₁,a) − Q⋆_{M₀}(s₁,a) > 2ε;
(iii) α²/(1−p) = 32²(1−γ)³ε²/(27γ³) ≤ 128(1−γ)³ε².

| binder | type | bin | citation |
|---|---|---|---|
| γ ε | ℝ | SRC | |
| 2/3 ≤ γ, γ < 1, 0 < ε, ε < 1/(32(1−γ)) | | SRC | MB:1752 |
| p, α (let) | | SRC | MB:1733 |
| hγ0 hp0 hp1 hq0 hq1 (clause ii) | Prop | TYP | well-formedness of `hardMDP` probabilities; all follow from clause (i) and γ ≥ 2/3, so clause (ii) is not vacuous |

Counts: SRC 4, TYP 1. `hardMDP` matches MB:1600–1625 (true = s₁). Wrapper: library facts + rewrite.
Verdict: **PASS**.

## 12. `Thm3_7_corrected` — Ch3.lean:300; source `theorem:azar`, MB:1443–1464

Reconstruction (printed): for 0 < ε < 1/(32(1−γ)), γ ∈ [2/3,1), SA ≥ 16, N ≤ c_N log(SA)/((1−γ)³ε²)
with small universal c_N: (i) ∀ (deterministic) policy estimator π̂ ∃ MDP with S states, A actions:
P(‖Q^{π̂} − Q⋆‖∞ > ε) ≥ 1/4; (ii) same for any Q estimator Q̂.

| binder | type | bin | citation |
|---|---|---|---|
| c_N > 0 (∃ outermost) | | SRC | MB:1450 |
| S A N, γ ε | | SRC/TYP | |
| 2 ≤ S | | DIS | `_corrected`, docstring item 1, SOURCE-ISSUES C2 + "Candidate repair of Theorem 3.7" |
| 16 ≤ S·A, 2/3 ≤ γ < 1, 0 < ε < 1/(32(1−γ)) | | SRC | MB:1446 |
| N bound | | SRC | MB:1448–1450 |
| 2 ≤ A (part i only) | | DIS | docstring item 2, SOURCE-ISSUES C1 (and MB:787 standing A ≥ 2) |
| piHat / QHat deterministic maps of (reward, γ, data) | | DIS | docstring item 3, SOURCE-ISSUES "Candidate repair" ("Each estimator is a deterministic map …") |
| ∃ M with M.discount = γ (after estimator) | | SRC | MB:1453, :1458 |

Counts: SRC 5, TYP 1, DIS 3, EXC 0. Strict "> ε", "≥ 1/4" as printed; Q^{π̂} = forced-first-action
trajectory Q of the returned deterministic policy. Docstring's three listed differences are exactly the
deviations found. Wrapper: witness 1/32768 + library theorem. Verdict: **PASS-DISCLOSED**.

## 13. `Thm3_2_burnInNecessary_restricted` — Ch3.lean:333; source prose claim MB:930–940 (claim :939)

Reconstruction: "N ≥ Ω̃(1/(1−γ)) is necessary for learning a policy that performs strictly better than a
random guess" — undefined notion; requires a reading.

| binder | type | bin | citation |
|---|---|---|---|
| c > 0 (∃ outermost) | | SRC | Ω̃ constant |
| S A N γ | | SRC/TYP | |
| 2 ≤ S, 2 ≤ A, 16 ≤ SA, 2/3 ≤ γ < 1 | | DIS | `_restricted`, docstring, SOURCE-ISSUES C49 |
| N ≤ c log(SA)/(1−γ) | | SRC | reading of Ω̃(1/(1−γ)) (log factor makes the lower bound stronger) |
| piHat deterministic map of (reward, γ, data) | | DIS | C49 |
| "strictly better than random guess" := gap ≤ 1/(64(1−γ)) | (conclusion) | DIS | C49 |

Counts: SRC 2, TYP 1, DIS 3, EXC 0. C49 states c = 1/8 form; wrapper converts and applies
`burnIn_necessary_valueGap`. Verdict: **PASS-DISCLOSED**.

## 14. `Thm3_2_approxPlanner_positiveN` — Ch3.lean:361; source prose MB:943 (after `Thm:sample-compl-main` MB:900–923)

Reconstruction: for any deterministic π̂ with ‖V̂⋆ − V̂^{π̂}‖∞ ≤ 1/(N(1−γ)), the guarantees of Thm 3.2 hold
after increasing c₀.

Binders as entry 4 except the inner hypothesis: `∀ f, ‖V̂⋆ − V̂^f‖ ≤ 1/(N(1−γ)) → …` — SRC (MB:943).
hN : 0 < N — DIS (`_positiveN`, docstring, SOURCE-ISSUES scope disclosures names this entry).
Counts: SRC 7, TYP 1, DIS 1, EXC 0. ∃ c₀ realizes "after increasing the universal constant". f inside
event covers data-dependent planners. Wrapper: library `.le`. Verdict: **PASS-DISCLOSED**.

## 15. `Thm3_2_planningIterations` — Ch3.lean:401; source prose MB:943; VI/PI definitions PR:312–345

Reconstruction: empirical VI and PI reach ‖V̂⋆ − V̂^{π̂}‖∞ ≤ 1/(N(1−γ)) within O((1−γ)⁻¹ log(N/(1−γ)))
iterations. VI (PR:316) "Initialize Q₀" (unspecified), Q_k = T(Q_{k−1}); PI (PR:323) π_k greedy w.r.t.
Q^{π_{k−1}}, π₀ unspecified.

| binder | type | bin | citation |
|---|---|---|---|
| C > 0 (∃ outermost) | | SRC | O(·) constant |
| State Action, Fintype; M; N | | TYP/SRC | |
| hN : 0 < N | | TYP | claimed slack 1/(N(1−γ)) divides by N; M̂ needs N ≥ 1 (scope note in SOURCE-ISSUES) |
| data | | SRC | deterministic claim for every realization |
| Q₀ with entries in [0, 1/(1−γ)] | | SRC (reading) | PR:316 leaves Q₀ open; with unbounded Q₀ no uniform C exists, so a bounded start is implicit; covers the canonical Q₀ = 0 |
| k ≥ C(1−γ)⁻¹log(N/(1−γ)) | | SRC | MB:943 |
| f greedy for Q_k (VI) | | SRC | VI output |
| π, g with π(n+1) = g n greedy for Q^{π n} (PI), π 0 arbitrary | | SRC | PR:323 |
| 1 ≤ k (PI) | | TYP | k counts PI iterations (PR:323 "k = 1, 2, …") |

Counts: SRC 7, TYP 3, EXC 0. The conclusion holds for every k above the threshold (stronger than
"within"). Note: the VI start-range reading is disclosed in docstring and COVERAGE.md but is not
recorded in SOURCE-ISSUES (recommendation only; it is a necessary reading of an underspecified claim,
not a narrowing of a true broader claim at fixed C). Wrapper: direct library term (identical type).
Verdict: **PASS**.

## 16. `Eq_P_Mi_Q_inaccurate_lower_generative` — Ch3.lean:444; source displays MB:1541–1556 (proof 1557–1835)

Reconstruction: for any 0 < ε < 1/(32(1−γ)), γ ∈ [2/3,1): ∃ two MDPs M₀, M₁, each two states and a
single action (sharing reward, γ), such that if N ≤ 0.003/((1−γ)³ε²), any estimator Q̂ (function of the
samples; MB:1806–1820 builds a deterministic test from it) satisfies P_{Mᵢ}(|Q̂(s₁,a) − Q⋆_{Mᵢ}(s₁,a)| > ε)
> 0.1 for some i.

| binder | type | bin | citation |
|---|---|---|---|
| γ ε, 2/3 ≤ γ < 1, 0 < ε < 1/(32(1−γ)) | | SRC | MB:1541 |
| ∃ M₀ M₁ : DiscountedMDP Bool Unit, same γ and reward | | SRC | MB:1544, 1575–1625 |
| N, N ≤ 0.003/(…) (after M₀, M₁) | | SRC | MB:1546–1549 |
| QHat : Samples → ℝ (deterministic) | | SRC | "any estimator"; source's test construction MB:1812 treats Q̂ as a function of data |

Counts: SRC 4, EXC 0. Strict > 0.1 kept (C4 documents the source's strictness gap). Randomized
estimators not covered — consistent with the source's own usage of "estimator" (deterministic test
built from Q̂); docstring and C4 say so. Wrapper: arithmetic (0.003 ≤ 9/2560) + library theorem.
Verdict: **PASS**.

## 17. `Thm3_9_minimaxLowerBound` — Ch3.lean:491; source prose MB:2585 (paragraph 2573–2585; display :2580–2583)

Reconstruction: "the sample complexity SAH⁴/ε² is provably minimax optimal" (citing domingues2021episodic):
there is a matching lower bound — no algorithm attains ε-optimality with constant probability using
o(SAH⁴/ε²) samples (up to logs), for ε ∈ (0, O(H)].

| binder | type | bin | citation |
|---|---|---|---|
| c c₁ > 0 (∃ outermost) | | SRC | constants of a lower bound |
| S A H N, ε | | TYP/SRC | |
| 2 ≤ S, 2 ≤ A, 2 ≤ H | | EXC (undisclosed by name) | docstring + SOURCE-ISSUES scope disclosures, but no `_restricted` suffix |
| 0 < ε | | SRC | |
| ε ≤ c₁H | | EXC (undisclosed by name) | narrows (0, H] range of MB:2578; same disclosure status |
| N ≤ cH³/ε² | | SRC | per-tuple form of SAH⁴/ε², protocol MB:2533–2540 |
| Seed : Type (universe 0), [MeasurableSpace], ν prob. | | EXC (undisclosed by name) | R3 restriction; library theorem itself is universe-polymorphic |
| piHat : Seed → rewards → data → ℕ → Fin S → Fin A (deterministic policy per seed) | | EXC (undisclosed by name) | R2: stochastic-policy outputs "not covered" |
| hmeas (measurable in seed for every reward table) | | EXC (undisclosed by name) | R1 |
| ∃ E (after estimator) | | SRC | |

Counts: SRC 4, TYP 1, DIS 0, EXC 5.
Other checks: quantifier order fine (c, c₁ first; instance after estimator); conclusion (prob ≥ 1/8 of
stage-1 failure at some state) is a genuine lower bound; not vacuous (estimator class nonempty, e.g.
Seed = Unit). The mathematical content and every narrowing are accurately described in the docstring and
in SOURCE-ISSUES "Statement-index scope disclosures" (R1–R4), and the docstring itself calls them a
"scope disclosure" listing what is "not covered" (stochastic-policy outputs, cited total-budget/adaptive
theorem). By the brief's rule a plain (unsuffixed) entry with self-declared narrowings fails: DISCLOSED
requires the `_restricted`/`_corrected` name. The narrowings S,A,H ≥ 2 are necessary (claim false
otherwise) and could be read as SOURCE, but R1–R3 and ε ≤ c₁H are genuine narrowings of a meaningful
broader claim.
Wrapper: witnesses 2⁻²⁸, 1/4096 + library `minimaxLowerBound` (measurable-level-set glue only).
Verdict: **FAIL** (naming/disclosure only; no mathematical error found).
Proposed fix: rename to `Thm3_9_minimaxLowerBound_restricted` (and `_holds`), update the SOURCE-ISSUES
scope-disclosure bullet, COVERAGE.md row 120, the line-223 reference, and named-result-status to the new
name; optionally generalize `Seed : Type*` (the library theorem already allows any universe) to drop R3.
No change to the library theorem.

## 18. `Thm3_9_positiveN` — Ch3.lean:527; source `Thm:sample-compl-finite`, MB:2551–2570 (algorithm 2524–2546; optimal deterministic policy PR:738–739)

Reconstruction: ∃ universal c₀ > 0: ∀ finite S, A, H, stages (P_h, r_h), δ > 0, 0 < ε ≤ H,
N ≥ c₀H³log(HSA/δ)/ε² ⇒ w.p. ≥ 1−δ the returned optimal (deterministic) policy π̂⋆ of M̂ satisfies
V_h^{π̂⋆}(s) ≥ V_h⋆(s) − ε ∀(s,h) and Q_h^{π̂⋆}(s,a) ≥ Q_h⋆(s,a) − ε ∀(s,a,h).

| binder | type | bin | citation |
|---|---|---|---|
| c₀ > 0 (∃ outermost) | | SRC | MB:2553 |
| State Action, Fintype | | TYP | |
| H, E | | SRC | |
| N | | SRC | |
| hN : 0 < N | | DIS | `_positiveN`, docstring, SOURCE-ISSUES scope disclosures (Thm 3.9 item) |
| δ ε, 0<δ, 0<ε≤H | | SRC | MB:2553 (δ > 0 only, as printed) |
| threshold | | SRC | MB:2566–2568 |
| ∀ f optimal for M̂ at every stage/state (inside event) | | SRC | MB:2541, PR:738–739 |

Counts: SRC 6, TYP 1, DIS 1, EXC 0. 0-based stages; `controlled … drop h` makes f h act at stage h.
Wrapper: direct library term. Verdict: **PASS-DISCLOSED**.

## 19. `Thm3_9` — Ch3.lean:571; same source as entry 18

Binders as entry 18 without hN; inside the event `∀ hN : 0 < N, ∀ f …` — TYP (empirical model typed only
for N > 0). At N = 0 the event is the whole space; the printed threshold then forces log(HSA/δ) ≤ 0 ⇒
δ ≥ HSA ≥ 1 (S, A, H ≥ 1 forced), so the printed claim is itself trivial there: no content is lost and
the Prop is not vacuous for N > 0. Counts: SRC 6, TYP 2, EXC 0. Wrapper: case split; N = 0 via
probability of univ, N > 0 via the library export (short glue, no second proof). Verdict: **PASS**.

---

## Wrapper check (Ch3Proofs.lean)

All 19 `_holds` theorems apply existing library exports (`policyEvaluation_universal_constant`,
`mainSample_policyLearning_universal_constant`, `optimalValueAbsorbingModel_preserves_optimalTrajectoryValue`,
`empirical_absorbingGrid_covers_valueEstimator`, `source_policyLearning_pointwise_universal_constants`,
`exists_universal_causalFinitePolicy_sample_constant`, `empiricalPolicyValue_source_residual_bound`,
`source_parameters_*`/`hardMDP_optimalQ_true`, `theorem37_corrected_fin_carriers`,
`mainSample_policyLearning_approx_universal_constant`, `empirical_planningIterations`,
`sourceHardMDP_full_Q_estimation_lower`, `minimaxLowerBound`,
`exists_universal_anyEmpiricalOptimalPolicy_sample_constant`, `decoupledHoeffding_universal_constant`,
`policyEvaluation_source_radius_all_states_positive_samples`,
`evaluationPolicyResolvent_variance_bound`/`_sqrtVariance_bound`, `burnIn_necessary_valueGap`) with only
glue (constant witnesses, `.le`, event monotonicity, arithmetic on constants). No restated or
duplicated proof of substance. No `sorry`/`admit`/axioms in either file (read). Not compiled in this audit.

## Summary

| # | Entry | Ch3.lean line | Verdict |
|---|---|---|---|
| 1 | Thm3_1 | 24 | PASS |
| 2 | Eq_Vhatpi_Vpi_difference_decoupled_Hoeffding | 50 | PASS |
| 3 | Eqn_ice_cream | 71 | PASS |
| 4 | Thm3_2_positiveN | 89 | PASS-DISCLOSED |
| 5 | Lemma3_3 | 114 | PASS |
| 6 | Lemma3_4 | 125 | PASS |
| 7 | Lemma3_5_positiveN | 142 | PASS-DISCLOSED |
| 8 | Thm3_9_causal_positiveN | 180 | PASS-DISCLOSED |
| 9 | Eq_lemma_VarP_V_bound | 219 | PASS (recommend SOURCE-ISSUES note for γ > 0 domain) |
| 10 | Lemma3_6 | 241 | PASS |
| 11 | Lemma3_8 | 266 | PASS |
| 12 | Thm3_7_corrected | 300 | PASS-DISCLOSED |
| 13 | Thm3_2_burnInNecessary_restricted | 333 | PASS-DISCLOSED |
| 14 | Thm3_2_approxPlanner_positiveN | 361 | PASS-DISCLOSED |
| 15 | Thm3_2_planningIterations | 401 | PASS (recommend SOURCE-ISSUES note for VI start range) |
| 16 | Eq_P_Mi_Q_inaccurate_lower_generative | 444 | PASS |
| 17 | Thm3_9_minimaxLowerBound | 491 | FAIL (self-declared scope narrowings without `_restricted` suffix) |
| 18 | Thm3_9_positiveN | 527 | PASS-DISCLOSED |
| 19 | Thm3_9 | 571 | PASS |

Totals: PASS 11, PASS-DISCLOSED 7, FAIL 1, UNSURE 0.

---

## Re-audit after fix (2026-11-09)

I re-read the following (read-only; nothing compiled by me): Ch3.lean:455–509 (the renamed def at :494), Ch3Proofs.lean:118–122,
FIX-LOG.md, SOURCE-ISSUES.md:552–590, COVERAGE.md rows 120 and 223, NEXT.md:146, PROGRESS.md:5 and :22,
named-result-status.json, docs/graph/nodes.json. I searched for stale references to the old name.

### `Thm3_9_minimaxLowerBound_restricted` (Ch3.lean:494)
The Prop is unchanged except that `Seed : Type*` (any universe) replaces `Seed : Type`. Binder table:

| binder | bin | citation |
|---|---|---|
| c c₁ > 0 (∃ outermost) | SRC | lower-bound constants |
| S A H N, ε, 0 < ε | TYP/SRC | |
| 2 ≤ S, 2 ≤ A, 2 ≤ H | DIS | `_restricted` name; docstring "Domain"; SOURCE-ISSUES scope disclosure (:573–588) |
| ε ≤ c₁H | DIS | same |
| N ≤ cH³/ε² (no log, fixed 1/8) | DIS | R4 |
| Seed : Type*, MeasurableSpace, ν probability | TYP | R3 removed: any universe |
| piHat: deterministic policy per seed | DIS | R2 |
| hmeas: measurable in the seed for every reward table | DIS | R1 |
| ∃ E after the estimator | SRC | |

Counts: SRC 3, TYP 2, DIS 4, EXC 0. The docstring states each narrowing accurately, and so does the
SOURCE-ISSUES bullet, which records the rename and that R3 was removed. The wrapper is the same glue as before: witnesses plus the
library `minimaxLowerBound`, which is universe-polymorphic, with the level-set measurability conversion.
**Verdict: PASS-DISCLOSED** (was FAIL).

### Notes and consistency
- SOURCE-ISSUES:555–559 now records the reading of the VI start range for `Thm3_2_planningIterations`.
  This matches the docstring and COVERAGE row 114. Accurate.
- SOURCE-ISSUES:560–563 now records the `0 < γ` domain for `Eq_lemma_VarP_V_bound`, stated as the
  domain of definition and not as a source error. Accurate.
- COVERAGE rows 120 and 223, NEXT.md, PROGRESS.md and nodes.json use the new name. The old name survives only in
  history text that also records the rename (SOURCE-ISSUES:575, PROGRESS:22) and in historical critic files. NEXT.md:146 labels the
  combined row "(corrected)". That is the row's strongest qualifier, coming from `Thm4_13_corrected`, so it is not an error.
- named-result-status.json: no entry. This is consistent, because the minimax claim is prose, not a numbered result
  (PROGRESS:22 says the ledger is unchanged).

Updated batch totals: PASS 11, PASS-DISCLOSED 8, FAIL 0, UNSURE 0.
