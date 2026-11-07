# Critic report: twelve previously unreviewed statement-index entries

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-07): required edit F6-1 was made on 2026-11-07; `Lemma6_7_restricted` now quantifies over every stationary policy π instead of `M.optimalGreedyPolicy`, and its docstring, scope disclosure and COVERAGE row were updated. Finding F4-3a was addressed by a minimality sentence in C5 (the retained premise is the one the appendix proof uses and is not claimed minimal). The review text below is unchanged.

- Date: 2026-11-07. Reviewer: independent critic subagent (did not write any of these entries or providers).
- git HEAD at review: `817b50144a025bb2c57127b52cde783fd79b5d43` (working tree, with uncommitted changes to Ch6/Ch7 statement files).
- Source pin: every `chapters/*.tex` hash recomputed against `source/provenance.json`: no mismatches.
- Method: for each entry, the printed statement was reconstructed from the `.tex` first, then compared binder by binder with the `Prop`. Every project definition the `Prop` depends on was opened. Wrappers were read, and an axiom probe was compiled.
- Files reviewed (sha256 prefix): Ch2.lean e30a8476dd0987b8, Ch2Proofs.lean c409f73c48197c1a, Ch3.lean 8c271156bf327a38, Ch3Proofs.lean ae547c237e212eb5, Ch4.lean 391f4708a0dd338b, Ch4Proofs.lean 51f47afeab15194e, Ch5.lean 19d52fa1fdd78bb9, Ch5Proofs.lean ea9884e4b8e43047, Ch6.lean ca8ba30ab2221c96, Ch6Proofs.lean c5564260404e8d43, prelim.tex 2d27bb720d49020c, generative_model_model_based.tex b7e7abfb2c2cb2c0, generative_model_model_free.tex 7f4eb058e00480bc, onlineRL.tex 393a4d26c228d833, offlineRL.tex 67cf0d1ce6a3d7c6, SOURCE-ISSUES.md 397b3df46fdbe494.

## Axiom probe

File `<reviewer probe folder>/Probe.lean` (`import Formalization`, then `#print axioms` for each `*_holds`), compiled with
`bash scripts/lean-local.sh <reviewer probe folder>/Probe.lean` (foreground, 61 s wall time, exit 0).
Before the run, I checked that the Statements ChN/ChNProofs `.olean` files for chapters 2 to 6 were newer than their sources.
All 12 wrappers depend only on `[propext, Classical.choice, Quot.sound]`:
Lemma2_6_holds, Lemma2_7_holds, Lemma2_11_holds, Lemma2_13_holds, Ch3.Lemma3_6_holds, Ch3.Lemma3_8_holds,
Ch4.Lemma4_3_corrected_holds, Ch4.Lemma4_9_holds, Ch4.Lemma4_14_holds, Lemma5_17_holds,
Ch6.Lemma6_7_restricted_holds, Ch6.Lemma6_14_restricted_holds.

## Summary of verdicts

| Entry | Verdict |
|---|---|
| Lemma2_6 | ACCEPT |
| Lemma2_7 | ACCEPT |
| Lemma2_11 | ACCEPT |
| Lemma2_13 | ACCEPT |
| Ch3.Lemma3_6 | ACCEPT |
| Ch3.Lemma3_8 | ACCEPT |
| Ch4.Lemma4_3_corrected | ACCEPT WITH DISCLOSURES |
| Ch4.Lemma4_9 | ACCEPT |
| Ch4.Lemma4_14 | ACCEPT WITH DISCLOSURES |
| Lemma5_17 | ACCEPT |
| Ch6.Lemma6_7_restricted | ACCEPT WITH DISCLOSURES (one required edit) |
| Ch6.Lemma6_14_restricted | ACCEPT WITH DISCLOSURES |

No entry has EXCESS hypotheses that change the printed mathematics. The only undisclosed narrowing found is in Lemma6_7_restricted (finding F6-1).

---

## Lemma2_6: empirical Bernstein (`empirical bernstein`, prelim.tex:985–997, setting 916–927)

Printed statement: fix (s,a) and a finite set 𝒱 ⊂ ℝ₊^S, 0<δ<1 and N≥2. If 𝒱 is independent of P̂_{s,a}, then with probability greater than 1−δ the following holds for all V∈𝒱: |(P̂−P)V| ≤ √(2 log(4|𝒱|/δ)/(N−1))·√Var_{P̂}(V) + 7‖V‖∞ log(4|𝒱|/δ)/(3(N−1)).

| Binder | Bin | Note |
|---|---|---|
| State, Fintype | TYPING | finite 𝒮 |
| Ω, μ probability | TYPING | the underlying probability space |
| d : FiniteDistribution | SOURCE | P_{s,a} |
| N, `2 ≤ N` | SOURCE | N≥2 |
| δ, 0<δ<1 | SOURCE | |
| draw measurable, `μ.map draw = d.sampleMeasure N` | SOURCE | N i.i.d. draws (`sampleMeasure` = `Measure.pi` of the row measure) |
| family : Ω → Finset, measurable (finiteFamilyBorel) | TYPING | a random finite set needs a σ-algebra. A deterministic 𝒱 is the constant special case |
| IndepFun family empiricalRow | SOURCE | "𝒱 independent of P̂_{s,a}" |
| V ≥ 0 | SOURCE | 𝒱 ⊂ ℝ₊^S |

Counts: SOURCE 6, STANDING 0, TYPING 3, EXCESS 0.

Conclusion: strict `1−δ < μ.real{…}`; the printed text says "greater than", so this matches. Var_{P̂}(V) is written out as E_{P̂}[V²] − (E_{P̂}V)², the plug-in variance of `eq:defn-Var-Psa-V`. ‖V‖ is the Pi sup norm. Junk values: N−1 ≥ 1 > 0. When |𝒱| = 0, log(0) = 0, but the ∀ over the empty family is vacuous. `empiricalRow` and `sampleMeasure` are the same definitions accepted in docs/critic-lemma2-4-hoeffding.md.
Wrapper: applies `randomBorelFamily_empiricalBernstein_success_gt`, then a set-inclusion step that rewrites √(2·Var·L/(N−1)) as √(2L/(N−1))·√Var. This derives the printed form from the export, as AGENTS.md allows, and does not re-prove the lemma.
Findings: none. Note (INFO): Maurer–Pontil's Theorem 4 uses the unbiased sample variance. The printed form uses the smaller plug-in variance, so it is a stronger statement, and that stronger statement is what is proved here.

## Lemma2_7: Bernoulli tails (`lem:tail-bound-sum-Bernoulli`, prelim.tex:1001–1015)

Printed statement: Z_i i.i.d. Bern(p), 0<p≤1. For every a>0, P(Σ(Z_i−EZ_i) < −an) ≤ exp(−a²n/(2p)). For every τ ≥ 2pn, P(ΣZ_i > τ) ≤ 2exp(−0.19τ).

| Binder | Bin |
|---|---|
| Ω, μ probability | TYPING |
| p, 0<p, p≤1 | SOURCE |
| n, Z : Fin n → Ω → ℝ | SOURCE |
| Measurable (Z i) | TYPING |
| iIndepFun Z μ | SOURCE (independent) |
| HasLaw (Z i) (bernoulliRealLaw p) | SOURCE (identically Bern(p)); the law is the PMF.bernoulli pushforward to {0,1} ⊂ ℝ, which I checked |

Counts: SOURCE 4, STANDING 0, TYPING 2, EXCESS 0. The conclusion matches exactly: strict `<` and `>`, the constant 0.19, and n=0 is allowed. The wrapper is the direct term `bernoulliTailBound_source`. Findings: none.

## Lemma2_11: reverse Fano (`lem:reverse-Fano-bound`, prelim.tex:1209–1229; definitions 1113–1128)

Printed statement: for probability laws P_0,…,P_M on a common measurable space, p_e ≥ p̄_e ≥ 1 − 1/(M+1) − √(M/(2(M+1)²) Σ_{j=1}^M KL(P_0‖P_j)).

Binders: Ω and its MeasurableSpace (TYPING); M (SOURCE); P with IsProbabilityMeasure (SOURCE). EXCESS 0.
Definitions: `averageErrorInfimum`/`minimaxErrorInfimum` (TestRiskDefinitions.lean:38–45) are real `sInf` over the range of measurable tests Ω → Fin (M+1) ("all tests"; measurability is implicit in the source). The range is nonempty (constant tests) and bounded below by 0, so `sInf` is not a junk value. The average is divided by |I| = M+1, and the worst case is `sup'` over the hypotheses.
Conclusion: the second inequality is moved into ℝ≥0∞ as ofReal(1−1/(M+1)) ≤ ofReal(p̄_e) + (ofReal(M/(2(M+1)²))·ΣKL)^{1/2}. Since p̄_e ≥ 0 and 1−1/(M+1) ≥ 0, this is equivalent to the printed real inequality whenever the KL sum is finite. When the sum is infinite, both forms are trivial. When M=0 the sum is empty, so 0·∞ cannot arise. Faithful. The wrapper is a direct application of `reverseFano_infimum_lower`. Findings: none.

## Lemma2_13: Bernoulli KL quadratic bounds (`lem:KL-quadratic-lower-bound`, prelim.tex:1335–1346; eq:defn-KL-bern 1328)

The entry is a literal transcription. The KL formula is written out exactly as in eq:defn-KL-bern. In the first part, 0<p,q<1 are SOURCE. In the second part, 1/2 ≤ q < p < 1 are SOURCE, and positivity follows from them. On these domains there are no junk-value risks: all logarithm arguments and denominators are positive. EXCESS 0.
Wrapper: part 1 and the first inequality of part 2 apply library lemmas directly. The second inequality of part 2 applies the part-1 library lemma with p and q swapped, rewriting (q−p)² = (p−q)². This derivation is allowed. Findings: none.

## Ch3.Lemma3_6: empirical value residual (`lem:empirical-value-residual`, generative_model_model_based.tex:1395–1410; event eq. 1373–1376)

Printed statement: on the event |(P̂_{π̂⋆} − P_{π̂⋆})V̂⋆| ≤ √(β₁/N)√Var_{P_{π̂⋆}}[V̂⋆] + 2β₁/(N(1−γ)) entrywise, γ‖(I−γP_{π̂⋆})⁻¹|(P̂_{π̂⋆}−P_{π̂⋆})V̂⋆|‖∞ ≤ 2√(2β₁/(N(1−γ)³)) + 6β₁/(N(1−γ)²). The source has β₁ = 2 log(16SAN/((1−γ)δ)) ≥ 4 (line 1311).

| Binder | Bin | Note |
|---|---|---|
| State, Action, M | TYPING | |
| N, hN : 0<N | TYPING | empirical rows need N>0. The source uses N≥1 (line 1359) |
| data | SOURCE | the sample array (the lemma is deterministic on the event) |
| f, EmpiricallyOptimal | SOURCE | π̂⋆ is an optimal policy of the empirical model, with any tie rule. `EmpiricallyOptimal` = trajectory optimality against all stationary policies |
| β, 0 ≤ β | SOURCE, weakened | β₁ ≥ 4 in the source. Lean assumes less |
| event hypothesis ∀ s | SOURCE | eq:Bernstein-empirical-optimal-value with the row at action f(s) |

Counts: SOURCE 4, STANDING 0, TYPING 2, EXCESS 0.
V̂⋆ = `valueEstimator`, the trajectory value of the canonical greedy empirical policy. It equals the value of f by `empiricallyOptimal_value_eq`, which the wrapper uses. This is a legitimate step deriving the printed form from the export. (I − γP)⁻¹ is the Matrix inverse, and I − γP is invertible because γ < 1. Findings: none.

## Ch3.Lemma3_8: hard-instance properties (`lem:properties-M01-lower-generative`, :1747–1767; parameters 1731–1734)

Printed statement: for p = (4γ−1)/(3γ), α = 32(1−γ)²ε/(9γ²), 0<ε<1/(32(1−γ)) and γ∈[2/3,1): (i) 1/2 ≤ p < p+α < 1 and 1−p ≥ 2α; (ii) Q⋆_{M₁}(s₁,a) − Q⋆_{M₀}(s₁,a) > 2ε; (iii) α²/(1−p) = 32²(1−γ)³ε²/(27γ³) ≤ 128(1−γ)³ε².
Binders γ, ε and their ranges: all SOURCE. Clause (ii) quantifies over the membership proofs hγ0, hp0, hp1, hq0, hq1. These are TYPING: the proofs are supplied by clause (i) and γ ≥ 2/3, so the clause is not vacuous, and proof irrelevance makes the choice of proofs harmless.
`hardMDP` (GenerativeLowerBoundTwoStateDefinitions.lean) matches the construction at :1590–1630: s₁ = `true` stays with probability p_M and otherwise moves to the absorbing s₂; the reward is 1 at s₁ and 0 elsewhere; there is one action. Q⋆ is the trajectory Q-value of the optimal greedy policy (project convention). EXCESS 0. The wrapper applies library lemmas and rewrites the two closed-form Q-values. Findings: none.

## Ch4.Lemma4_3_corrected: TD step size (`lemma:TD-step-size`, generative_model_model_free.tex:317–327; schedule 182–184; weights 307–313)

Printed statement: under schedule (eq:thm:eta-TD) for 1≤t≤T with c₁ ≥ c₂ > 0 and c₁c₂ ≤ 1/8, for every t ≥ T/(c₂ log T): η_k^{(t)} ≤ 1/T² if 0≤k≤t/2, and η_k^{(t)} ≤ η_k ≤ 2log³T/((1−γ)T) if t/2<k≤t.

| Binder | Bin | Note |
|---|---|---|
| γ, 0≤γ<1 | STANDING | discount convention |
| c₁, c₂ > 0; c₁c₂ ≤ 1/8 | SOURCE | c₁ ≥ c₂ is dropped, which assumes less |
| T, 2 ≤ T | TYPING/domain | log T > 0 is needed for the schedule to be defined. Disclosed |
| log²T ≤ c₁(1−γ)T | CORRECTION (C5) | not in the print. Disclosed with a formal counterexample |
| schedule for 1≤i≤T | SOURCE | |
| t ≤ T | CORRECTION (C5) | the schedule is unconstrained beyond T, so this is necessary. Disclosed |
| k ≤ t, t ≥ T/(c₂ log T) | SOURCE | |

Counts: SOURCE 5, STANDING 1, TYPING 1, disclosed corrections 2, EXCESS 0.
Weight `w` matches def:eta-k-t, including the k=t branch (an empty product) and the k=0=t case (value 1). `2k ≤ t` ⇔ k ≤ t/2. The conclusion matches the printed bounds.
Findings:
- F4-3a (LOW, docs/SOURCE-ISSUES.md:164–175): neither C5 nor the docstring says whether the added premise is the weakest one the evidence supports. The counterexample shows some γ-dependent premise is needed; it does not show that this exact premise is minimal. Required edit (documentation only): add one sentence to C5 saying the premise is the one the appendix proof uses and is not claimed minimal. Optionally mention T ≥ 2 and γ ≥ 0 in C5 as well (they already appear in the docstring and in COVERAGE).
The wrapper applies `tdRateWeight_corrected_step_size` directly.

## Ch4.Lemma4_9: Q-learning step size (`lemma:Q-step-size`, :1093–1112; schedule 882–886; η̄ 1087–1089; weights 1075–1083)

Binders: γ<1 (STANDING; γ ≥ 0 is dropped, which assumes less), c₁, c₂ > 0 (SOURCE; c₁ ≥ c₂ dropped), T ≥ 2 (TYPING/domain, disclosed), schedule for 0≤k≤T (SOURCE). EXCESS 0.
Conclusions: (a) for ⌊T/2⌋ < i ≤ t ≤ T, 0 ≤ w ≤ η_i ≤ η̄. This matches. (b) The square-sum bound is stated for every t ≤ T, which is stronger than printed; for t ≤ ⌊T/2⌋ the sum is empty. (c) The τ ≥ 1 telescoping identity and the τ = 0 sum identity are stated for every t, which is also stronger. The weights match def:eta-i-t-simple, including i = t and i = 0. `T / 2` is natural-number division, i.e. ⌊T/2⌋. The wrapper is a direct application. Findings: none.

## Ch4.Lemma4_14: hard-MDP values (`lem:optimal-V-Q-hardMDP`, :2797–2811; construction 2735–2781; p 2784–2788)

Binders: γ with 1/4 < γ < 1. This is TYPING/domain: it is exactly the range where p = (4γ−1)/(3γ) ∈ (0,1), the source's "p∈(0,1)". EXCESS 0.
`qHardMDP` (QLearningHardMDPDefinitions.lean) matches :2758–2773 in its transitions and rewards. Encoding: every state has the action set `Bool`, and at states 0, 2 and 3 both actions are copies of the source's single action. Copies of an action leave V⋆ and Q⋆ of the original actions unchanged, and the entry states the Q-claims for every action. The values are trajectory values of the optimal greedy policy. The identity 1/(1−γp) = 3/(4(1−γ)) checks out (γp = (4γ−1)/3).
Findings:
- F4-14 (INFO): the copied-action encoding is a carrier change, not the source's state-dependent action sets. The docstring discloses it and points to C31 item 5 for why it is not reused for the Q-learning dynamics. No edit required.
The wrapper is a direct application.

## Lemma5_17: UCB-Q learning-rate properties (`lemma:property_lr`, onlineRL.tex:2020–2041; rate 1898–1904; weights 1990–2000)

Binders: H with 0 < H (STANDING, horizon), N with 0 < N (SOURCE, "every N ≥ 1"), n with 0 < n (SOURCE). EXCESS 0.
`onlineQRateWeight H N n` (RateWeightDefinitions.lean:22) matches equ:learning_rate_notation for n ≥ 1: η_n ∏_{i=n+1}^N (1−η_i) when N ≥ n, with the empty product at N = n, and 0 when N < n. The n = 0 branch matches eq. -eta_0n. The rate is (H+1)/(H+n). The tail series is HasSum over N = n + k, so the infinite sum is not given a junk value.
The wrapper applies three library lemmas, and `ht ▸ hs.hasSum`. Findings: none.

## Ch6.Lemma6_7_restricted: occupancy-weighted variance (`lem:sum-d-Var-UB`, offlineRL.tex:1529–1537; P⋆, b⋆ 1038–1045; eq:infinite-v-lower 1311–1327; proof 4277–4335)

Printed statement, in the context of the Theorem 6.3 proof: Σ_s d⋆_ρ(s) Var_{P_{s,π⋆(s)}}(V̂) ≤ 2/(γ²(1−γ)) + 4/(γ²(1−γ))⟨d⋆_ρ, b⋆⟩. Here π⋆ is "the optimal deterministic policy" (offlineRL.tex:138), V̂ is the VI-LCB output, b⋆(s) = b(s, π⋆(s); V̂), and d⋆_ρ is the discounted occupancy of π⋆ from ρ.

| Binder | Bin | Note |
|---|---|---|
| S, A, M, ρ | TYPING/SOURCE | |
| V, b arbitrary | RESTRICTION (disclosed) | they replace V̂ and b⋆ |
| 0 < γ | STANDING | the printed bound divides by γ², and the chapter has γ ≥ 1/2 |
| 0 ≤ V ≤ 1/(1−γ) | RESTRICTION premise (disclosed) | consumed by the source proof at step (v) and in (ii) of eq:infinite-extra-lemma-au1 |
| b ≥ 0 | RESTRICTION premise (disclosed) | consumed at (i) |
| 0 ≤ V − γP⋆V + 2b | RESTRICTION premise (disclosed) | follows from eq:infinite-v-lower with r ≥ 0. Consumed at (ii) |

Definitions checked: `discountedStateOccupancy` = (1−γ)Σ_t γ^t P(s_t = s), which is the normalized occupancy. `policyTransition π s = (π s).bind (M.transition s)` reduces to P_{s,π(s)} for a point-mass policy. `variance` is the row variance.
The restriction is the weakest one the source proof supports: these are exactly the premises the printed proof consumes. It is disclosed in the docstring, in the SOURCE-ISSUES scope disclosures (~line 459) and in COVERAGE row 94.
Findings:
- F6-1 (MEDIUM, Formalization/Statements/Ch6.lean:123–135): π⋆ is fixed to `M.optimalGreedyPolicy`, a single tie rule. The source's π⋆ is "the optimal deterministic policy", and when optima are tied different choices give different d⋆_ρ and P⋆. The library export `occupancyWeightedVariance_mdp` (Formalization/OfflineRL/OccupancyWeightedVarianceMDP.lean:21) is proved for every `π : StationaryPolicy`. So the entry under-states the export, and the narrowing is not disclosed: the docstring says only "`π⋆` is the optimal greedy policy". Required edit: quantify the entry over an arbitrary `π : StationaryPolicy S A`, or at least over every deterministic optimal policy, replacing `M.optimalGreedyPolicy` in all three places. The wrapper becomes `occupancyWeightedVariance_mdp M π ρ V b …`. Alternatively, keep the current form and add the tie-rule restriction to the docstring and to the scope disclosure. The generalization is preferred, since it costs nothing.
The wrapper is a direct application of the library theorem specialized to the greedy policy.

## Ch6.Lemma6_14_restricted: hard-family values (`lemma:value-policy-LB-inf`, offlineRL.tex:2544–2583; construction 2432–2516; proof 5502ff)

Printed statement: for any θ ∈ {0,1}^{S−1}, under the standing assumptions (eq:infinite-epsilon-assumption: 2/3 ≤ γ < 1 and 224(1−γ)ε/γ ≤ 1/2; C > 2):
- the value-bound display holds for every π and every s > 0, with equality at π⋆;
- π⋆(0|0) = 1 and π⋆(θ_s|s) = 1;
- V⋆(0) = 4/(7(1−γ)), and V⋆(s) is given by the printed closed form.

| Binder | Bin |
|---|---|
| m, 1 ≤ m (S = m+1 ≥ 2) | STANDING |
| γ ∈ [2/3, 1) | STANDING (2437–2440) |
| ε ≥ 0 | STANDING (an accuracy level; keeps p, q ∈ [0,1]) |
| 224(1−γ)ε/γ ≤ 1/2 | STANDING |
| C > 2 | STANDING (2464) |
| θ | SOURCE |
| π (in clause 1) | SOURCE ("every policy" = stationary randomized, the book's convention) |

EXCESS 0.
`lbMDP` (LowerBoundFamilyDefinitions.lean:66) matches eq:defn-Ptheta-defn-inf row by row, including the (0,1) row (2γ−1)1{0} + 2(1−γ)μ. It also matches μ (with S−1 = m), p and q, and the rewards 1, 4/7 and 0.
Restriction: π⋆(θ_s|s) = 1 is stated only for ε > 0. When ε = 0, p = q, both actions are optimal at s > 0, and the fixed greedy tie rule need not pick θ_s. The disclosure is accurate (docstring; SOURCE-ISSUES ~line 452; COVERAGE row 95). For ε > 0 the optimal action is unique at every state, so fixing the greedy policy loses nothing. Every other clause is proved for ε ≥ 0.
Findings:
- F6-14 (LOW/INFO): at ε = 0 the printed clause can be read as being about *some* optimal policy, and it would hold for the policy that picks θ_s. A slightly stronger restricted form is possible: "for ε = 0 there exists an optimal policy with π(θ_s|s) = 1". Not required, since the current restriction is honest and disclosed. No edit required.
The wrapper is a direct application of `lb_value_policy`.

---

## Required edits (none blocks acceptance)

1. F6-1 (MEDIUM): `Lemma6_7_restricted` should quantify over an arbitrary policy π instead of `M.optimalGreedyPolicy`, since the export already supports it. Otherwise, disclose the fixed tie rule in the docstring and in the SOURCE-ISSUES scope disclosure.
2. F4-3a (LOW, documentation): C5 should say whether the added premise log²T ≤ c₁(1−γ)T is claimed minimal, and optionally list T ≥ 2 and t ≤ T as part of the correction.

Other checks: every docstring label and line range was checked against the pinned `.tex` and is correct. The COVERAGE rows for all 12 entries agree with the entries.
