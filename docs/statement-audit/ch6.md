> Public copy of an independent five-bin statement audit (2026-11-09/10), scrubbed of local paths and agent identifiers. Auditors were independent of the builders. No result here is author-approved. Method and totals: [README](README.md).

# Five-bin statement audit: batch ch6 (2026-11-09)

Auditor: independent statement auditor (read-only; nothing compiled; no edits outside this report).
Targets: every `def ... : Prop` in `Formalization/Statements/Ch6.lean` (26 entries) and the matching
`_holds` wrappers in `Formalization/Statements/Ch6Proofs.lean`.
Source read: `source/upstream/tex/chapters/offlineRL.tex` (ranges per entry below), standing conventions from
`prelim.tex:42` (rewards in [0,1]), `prelim.tex:45` (γ ∈ [0,1)), `prelim.tex:150–172` (discounted occupancy,
d⋆ of the optimal deterministic policy), `offlineRL.tex:28–37` (iid triple sampling), `:90` (ε ∈ (0,1/(1−γ)]),
`:127–140` (C⋆, 0/0 = 0), macros `commands.tex:221–244` (`\myrho = d^b`, `\infs` empty, `\Cstar = C⋆_ρ`).
Project definitions expanded: `DiscountedMDP` (`MDP/CoreDefinitions.lean:30`), `StationaryPolicy`,
`discountedStateOccupancy`/`discountedJointOccupancy`/`occupancyStateAt` (`MDP/DiscountedOccupancy.lean`),
`optimalGreedyPolicy`, `optimalityFixedPoint` (choice from proved ∃!), `OfflineVILCB.Input`
(`OfflineRL/VILCBDefinitions.lean`), `Params`, `Params.input`, `dataCount`, `dataPhat`, `uniformRow`
(`OfflineRL/VILCBDatasetDefinitions.lean`), `offlineBanditLaw`, `armCount`, `empiricalArmMean`, `armRadius`,
`lcbFallback` (`OfflineRL/BanditDefinitions.lean`), `LCBQ.iota/horizon/penalty/step/run/visitTime/
concentrability/kappa/betaTrunc/alphaSeq/xiSeq/thetaSeq/psiSeq/phiSeq` (`OfflineRL/LCBQDefinitions.lean`),
`onlineQRate(Weight)`, `FiniteDistribution.sampleMeasure/empiricalRow`, `lbGap/lbP/lbQ/lbMu/lbRow/lbMDP`
(`OfflineRL/LowerBoundFamilyDefinitions.lean`), `FiniteVILCB.Traj/trajMeasure/detPolicy/extPolicy/stageIndex/qhat`
(skimmed only: names, docstrings, data-only inputs).

Shared bins used below (to avoid repeating):
- `DiscountedMDP M`: fields `state_nonempty`, `action_nonempty` = TYPING; `reward ∈ [0,1]` = STANDING
  (`prelim.tex:42`); `discount ∈ [0,1)` = STANDING (`prelim.tex:45`); `transition` = SOURCE object (P).
- `OfflineVILCB.Input M` / `Params p`: `γ ∈ [0,1)` STANDING; `N > 0` TYPING (the algorithm divides by N in
  the `5/N` penalty term; and in Lean `log 0 = 0` would otherwise make sample-size premises trivially true);
  `r ∈ [0,1]` STANDING; `cb > 0` SOURCE (`:822`); `δ ∈ (0,1)` SOURCE (`:822`). In `Input`, `count` and `Phat`
  are free (not tied to data): a generalisation for deterministic lemmas, not a premise.
- `Fintype`, `Nonempty`, `DecidableEq`, `MeasurableSpace`/`⊤` σ-algebra on finite carriers, `Measurable X`,
  `IsProbabilityMeasure μ`: TYPING.
- iid data block `X, Measurable X, iIndepFun, marginal = Σ_t ofReal(d^b(t.1)·P(t.2|t.1))·δ_t`: SOURCE
  (`eq:sampling-offline-inf-iid`, `:28–39`); its finite-sum law is exactly d^b ⊗ P on the discrete space.

Wrappers (`Ch6Proofs.lean`): every `_holds` applies an existing library export, sometimes through
library bridge lemmas (`concentrability_eq_library`, `gap_bridge`, `isOptimal_of_optimal`,
`printed_size_imp_export_size`) or with `.le`/`measureReal_mono` weakening. The only non-trivial wrapper is
`Lemma6_5_sampleSplit_actualData_corrected_holds`, which identifies the triple law with
`jointRow.rowMeasure`, converts `iIndepFun` to a product law and rewrites the count; this is a law/notation
bridge, not a second proof of the result. No `sorry`/`admit`/`axiom` in either file. Both files are imported
by `Formalization.lean:1027–1028`. (Side note, not an entry verdict: `Ch6.lean` imports
`MDP.DiscountedOccupancy` and `MDP.OptimalTrajectoryValue`, which contain theorems as well as definitions;
AGENTS.md asks that statement files import definition modules only.)

---

## 1. Thm6_1_zeroCountFallback_corrected — `Ch6.lean:32`
Source: `thm:MAB_LCB_upper`, `offlineRL.tex:456–471`; setting `:243–258`; Alg. 6.1 `:383–445`
(commented fallback `:429–430`); `eq:defn-Cstar-bandits` `:264–281`.

Reconstruction: A arms, means r_a ∈ [0,1], optimal arm a⋆; data a_i iid d^b, R_i = r_{a_i} + z_i, z iid
N(0,1) independent; C⋆ = 1/d^b(a⋆). For δ ∈ (0,1) and N ≥ 8C⋆ log(2/δ): with prob ≥ 1−δ the LCB arm
(argmax of r̄_a − √(2log(4A/δ)/N_a)) has r⋆ − r_{a^lcb} ≤ 4√(C⋆ log(4A/δ)/N). Zero-count branch undefined in
active pseudocode.

| binder | Lean type | bin | citation |
|---|---|---|---|
| Arm, Fintype, DecidableEq, MeasurableSpace, MeasurableSingletonClass | types/instances | TYPING | `:245` |
| d, IsProbabilityMeasure d | Measure Arm | SOURCE | d^b `:250–255` |
| r | Arm → ℝ | SOURCE | `:245` |
| ∀b, 0 ≤ r b; ∀b, r b ≤ 1 | Prop | SOURCE | `:245` (r_a ∈ [0,1]) |
| aStar, ∀b, r b ≤ r aStar | Arm, Prop | SOURCE | a⋆ optimal `:246` |
| 0 < d.real {aStar} | Prop | TYPING | C⋆ = 1/d^b(a⋆) finite is needed for `N ≥ 8C⋆…` to be satisfiable |
| N, δ, 0<δ, δ<1 | ℕ, ℝ | SOURCE | `:395`, `:456` |
| 8·(1/d(a⋆))·log(2/δ) ≤ N | Prop | SOURCE | `:458` |
| zero-count convention mean 0, radius 1 (inside `lcbFallback`) | definition | DISCLOSED | name `_corrected`, docstring, SOURCE-ISSUES C18 |

Counts: SOURCE 7, STANDING 0, TYPING 2, DISCLOSED 1, EXCESS 0.
Checks: conclusion quantifies over every argmax `aL` (every tie rule) — implies the printed. Law
`offlineBanditLaw` = (⊗d) × (⊗N(0,1)), independent — matches. `Fintype.card Arm` = A. No junk: N ≥ 1 forced by
the premise. Verdict: **PASS-DISCLOSED**.

## 2. Lemma6_2_corrected — `Ch6.lean:52`
Source: `lem:monotone-contraction`, `offlineRL.tex:872–890`; operator `:714–746`, penalty `:808–824`.

Reconstruction: Q̂₀ = 0; Q̂_τ ≤ Q̂⋆_pe and ‖Q̂_τ − Q̂⋆_pe‖∞ ≤ γ^τ/(1−γ) for all τ ≥ 0, with Q̂⋆_pe the
unique fixed point of T_pess; τ ≥ log(N/(1−γ))/log(1/γ) ⇒ ‖·‖ ≤ 1/N. γ ∈ [0,1) only.

| binder | Lean type | bin | citation |
|---|---|---|---|
| S, A, Fintype, Nonempty A | types | TYPING | — |
| M : Input S A (γ∈[0,1), N>0, r∈[0,1], cb>0, δ∈(0,1), count, Phat) | structure | STANDING/TYPING/SOURCE as in shared bins | `:714–852` |
| 1/2 ≤ M.γ | Prop | DISCLOSED | `_corrected`, docstring, C10 |

Counts: SOURCE 2 (cb, δ), STANDING 2 (γ, r), TYPING 4, DISCLOSED 1, EXCESS 0.
Checks: fixed point existence and uniqueness are conclusions, not premises; order is pointwise Pi order;
norm is the sup norm; `log(1/γ) > 0` on γ ≥ 1/2 so no division junk. Verdict: **PASS-DISCLOSED**.

## 3. Lemma6_2_iterationCount_restricted — `Ch6.lean:72`
Source: prose `offlineRL.tex:892` (after `lem:monotone-contraction`).

Reconstruction: for every ε > 0, τ ≥ (1/(1−γ))·log(1/(ε(1−γ))) ⇒ ‖Q̂_τ − Q̂⋆_pe‖∞ ≤ ε.

Binders: as entry 2 plus `ε, 0 < ε` (SOURCE, `:892`), `τ` (SOURCE); `1/2 ≤ M.γ` DISCLOSED (`_restricted`,
docstring, `SOURCE-ISSUES.md#statement-index-scope-disclosures` item on `:892`, C10).
Counts: SOURCE 4, STANDING 2, TYPING 4, DISCLOSED 1, EXCESS 0.
Checks: when ε(1−γ) > 1 the log is negative and the condition is vacuous on τ, but the conclusion is still
true (‖·‖ ≤ 1/(1−γ) < ε); no vacuity. Verdict: **PASS-DISCLOSED**.

## 4. Lemma6_5_sampleSplit_actualData_corrected — `Ch6.lean:93`
Source: `lem:sample-split-infinite`, `offlineRL.tex:1104–1114`; sampling `:28–37`; counts `:676–678`.

Reconstruction: δ ∈ (0,1); with probability > 1−δ, ∀(s,a): max{N_{s,a}, (2/3)log(SN/δ)} ≥ N d^b(s,a)/12.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, Fintype, Nonempty | types | TYPING | — |
| ρ (= d^b), P | FiniteDistribution, kernel | SOURCE | `:28–37` |
| Ω, μ, IsProbabilityMeasure | probability space | TYPING | — |
| N | ℕ | SOURCE | — |
| 2 ≤ N | Prop | DISCLOSED | `_corrected`, docstring, C19 (+ addendum: printed false at N = 1) |
| δ, 0<δ, δ<1 | | SOURCE | `:1105` |
| X, Measurable, iIndepFun, marginal | iid triples | SOURCE | `:28–37` |

Counts: SOURCE 6, STANDING 0, TYPING 3, DISCLOSED 1, EXCESS 0.
Checks: strict `1 − δ <` matches "exceeding"; `\infs` is empty; count is the actual filter count.
Minor wording: the docstring still calls this a "restricted" result while the name is `_corrected` and the
C19 addendum says the printed lemma is false at N = 1; the deviation itself is accurately stated. Verdict:
**PASS-DISCLOSED**.

## 5. Lemma6_4 — `Ch6.lean:120`
Source: `lem:offline-prelim`, `offlineRL.tex:1078–1094`, stated inside the proof of Theorem 6.3 (`:1031–1071`),
whose hypotheses are γ ∈ [1/2,1) and τmax ≥ (1/(1−γ))log(N/(1−γ)) (`:901`).

Reconstruction (in that context): ‖V̂ − V̂⋆_pe‖∞ ≤ 1/N and |b(s,a;V̂⋆_pe) − b(s,a;V̂)| ≤ 2/N for all (s,a),
with V̂ = value of Q̂_{τmax}.

| binder | Lean type | bin | citation |
|---|---|---|---|
| S, A, Fintype, Nonempty A | | TYPING | — |
| M : Input | | shared bins | `:714–852` |
| 1/2 ≤ M.γ | Prop | STANDING | Thm 6.3 hypothesis `:901`, proof context `:1031–1071` |
| τ, (1/(1−γ))log(N/(1−γ)) ≤ τ | | STANDING | `:901`, `:1064–1068` |

Counts: SOURCE 2, STANDING 4, TYPING 4, DISCLOSED 0, EXCESS 0.
Checks: fixed point existence/uniqueness proved as conclusions; `value` = max_a; sup norm on S → ℝ; bonus
is the source penalty with zero-count convention. Verdict: **PASS**.

## 6. Lemma6_7_restricted — `Ch6.lean:145`
Source: `lem:sum-d-Var-UB`, `offlineRL.tex:1529–1537`; P⋆, b⋆ `:1038–1045`; `eq:infinite-v-lower` `:1311–1327`.

Reconstruction: inside Thm 6.3 proof on its event: Σ_s d⋆_ρ(s) Var_{P_{s,π⋆(s)}}(V̂) ≤ 2/(γ²(1−γ)) +
4/(γ²(1−γ))·⟨d⋆_ρ, b⋆⟩.

| binder | Lean type | bin | citation |
|---|---|---|---|
| S, A, Fintype | | TYPING | — |
| M | DiscountedMDP | shared | — |
| π (any stationary policy), ρ | | SOURCE (generalised from π⋆) | `:138`, `:1038–1045` |
| V, b | S → ℝ | SOURCE (V̂, b⋆) generalised | `:1038–1045` |
| 0 < γ | Prop | STANDING | Thm 6.3 `γ ≥ 1/2` `:901` |
| 0 ≤ V, V ≤ 1/(1−γ), 0 ≤ b, 0 ≤ V − γP⋆V + 2b | Prop | DISCLOSED | `_restricted`, docstring, scope-disclosures item "Lemma 6.7" |

Counts: SOURCE 4, STANDING 3, TYPING 2, DISCLOSED 4, EXCESS 0.
Checks: d⋆ normalised (1−γ)Σγ^t; policy generalised to every stationary π, covering every optimal π⋆.
Premises are satisfiable (V = 0, b = 0). Verdict: **PASS-DISCLOSED**.

## 7. Lemma6_14_restricted — `Ch6.lean:170`
Source: `lemma:value-policy-LB-inf`, `offlineRL.tex:2544–2583`; construction `:2432–2530`; standing
`eq:infinite-epsilon-assumption` `:2438–2443`.

Reconstruction: for every θ ∈ {0,1}^{S−1}: V^π_θ(s) ≤ (1 + γ(1−x)(C⁻¹V⋆(s) + (1−C⁻¹)V⋆(0)))/(1−γx) for all π,
s > 0, equality at π⋆; π⋆(0|0) = 1, π⋆(θ_s|s) = 1; V⋆(0) = 4/(7(1−γ)); V⋆(s) closed form.

| binder | Lean type | bin | citation |
|---|---|---|---|
| m, 1 ≤ m (S = m+1 ≥ 2) | | TYPING | state set {0,…,S−1} with positive states `:2470` |
| γ, 2/3 ≤ γ, γ < 1 | | STANDING | `:2440` |
| ε, 0 ≤ ε | | STANDING | positive accuracy `:90`; needed for p ≥ q |
| 224(1−γ)ε/γ ≤ 1/2 | | STANDING | `:2440` |
| C, 2 < C | | STANDING | `:2476` |
| θ | Fin m → Bool | SOURCE | `:2549` |
| clause `0 < ε →` on π⋆(θ_s|s)=1 | | DISCLOSED | `_restricted`, docstring, scope-disclosures "Lemma 6.14" |

Counts: SOURCE 1, STANDING 5, TYPING 1, DISCLOSED 1, EXCESS 0.
Checks: `lbMDP` matches `eq:defn-Ptheta-defn-inf` and the rewards exactly (false = action 0). V⋆ is the
trajectory value of `optimalGreedyPolicy`; equality clause uses that policy. Verdict: **PASS-DISCLOSED**.

## 8. Lemma6_15 — `Ch6.lean:198`
Source: `lem:transition-KL-bound-infinite`, `offlineRL.tex:2835–2865`.

Reconstruction: ∃ universal c₃ > 0: ∀θ, θ̃, s > 0, a: θ_s = θ̃_s ⇒ KL = 0; θ_s ≠ θ̃_s ⇒ KL ≤ c₃(1−γ)³ε².
Binders: m, hm (TYPING); γ, ε, C and the four standing hypotheses (STANDING, as entry 7); θ, θ', i, a (SOURCE).
Counts: SOURCE 4, STANDING 6, TYPING 1, DISCLOSED 0, EXCESS 0.
Checks: `∃ c₃` precedes every parameter (universal). θ, θ' range over all of {0,1}^{S−1} (implies Θ). KL is
Mathlib `klDiv` of the actual row measures; bound via `ofReal`. Verdict: **PASS**.

## 9. Lemma6_11_restricted — `Ch6.lean:224`
Source: `lemma:useful`, `offlineRL.tex:2292–2300`; H `:1667–1672`; κ `:2284–2287`; d_j/P_π⋆ `:1970–1973`.

Reconstruction: ∃ universal C: for all 0 < δ < 1, W ≥ 0:
Σ_j κ^j ρᵀ(P_{π⋆})^j W ≤ C(⟨d⋆_ρ, W⟩/(1−γ) + δ‖W‖∞/(ST⁴(1−γ))), with π⋆ "the" optimal deterministic policy
(`prelim.tex:160–172`, `offlineRL.tex:138`), i.e. any optimal deterministic policy the reader fixes.

| binder | Lean type | bin | citation |
|---|---|---|---|
| ∃ C, 0 < C | | SOURCE (`≲`) | `:2296` |
| S, A, Fintype; M; ρ; δ; W | | TYPING / shared / SOURCE | `:2294` |
| 0<δ, δ<1 | | SOURCE | `:2294` |
| 1 ≤ T | | TYPING | log(SAT/δ) domain |
| 1 ≤ log(SAT/δ) | | DISCLOSED | `_restricted`, docstring, C22, scope disclosures |
| ∀s, 0 ≤ W s | | SOURCE | `:2294` |
| π⋆ fixed to `M.optimalGreedyPolicy` (library tie choice) | — | EXCESS (undisclosed narrowed domain) | not flagged as a restriction in name/docstring/SOURCE-ISSUES |

Counts: SOURCE 5, STANDING 2, TYPING 3, DISCLOSED 1, EXCESS 1.
Checks: C universal (∃C outermost) — good; `tsum` junk not reachable since κ < 1 under the premise. Problem:
the printed lemma is about the book's π⋆, an arbitrary optimal deterministic policy (ties unresolved); the
entry covers only the library's greedy tie choice. The library export `lcbq_useful`
(`OfflineRL/LCBQUsefulSeries.lean:56`) already takes an arbitrary `π : StationaryPolicy`, so the narrowing is
gratuitous. The project treats single-tie-choice versions as restrictions elsewhere (Lemma 6.7 was
"generalized … after an independent review"; Remark 6.2/6.3 say so explicitly; Lemma 6.12/Thm 6.8/Thm 6.3
quantify over every Q⋆-greedy πstar). The docstring mentions "(the optimal greedy policy)" but does not
disclose it as a deviation and no SOURCE-ISSUES item covers it.
Verdict: **FAIL** (undisclosed domain narrowing).
Proposed fix: quantify `∀ (π : StationaryPolicy S A)` (or `∀ πstar : S → A` with Q⋆-greedy hypothesis and
`LCBQ.detPolicy πstar`) and replace both `M.optimalGreedyPolicy` occurrences; wrapper becomes
`fun S A _ _ M π ρ δ T W … => lcbq_useful M π ρ δ T W …`. Alternatively disclose the tie restriction in the
docstring and the scope-disclosures entry.

## 10. Thm6_13 — `Ch6.lean:262`
Source: `thm:infinite-lwoer-bound`, `offlineRL.tex:2367–2402`; construction `:2432–2634`.

Reconstruction: ∃ universal c₂ > 0: ∀ γ ∈ [2/3,1), S > 12, C⋆ > 2, ε ≤ 1/(672(1−γ)): ∃ class {M_θ} (S
states, 2 actions), ρ, data law with C⋆_ρ ∈ [C⋆, 2C⋆], such that for N ≤ c₂SC⋆/((1−γ)³ε²):
inf_π̂ max_θ P_θ(V⋆_θ(ρ) − V^π̂_θ(ρ) > ε) ≥ 1/4.

| binder | Lean type | bin | citation |
|---|---|---|---|
| ∃ c₂ > 0 | | SOURCE | `:2394` |
| γ, S, Cstar, ε and 2/3≤γ, γ<1, 12<S, 2<Cstar, ε ≤ 1/(672(1−γ)) | | SOURCE | `:2369–2371` |
| (inner ∃ State, Θ, M, ρ, db; ∀ N ≤ …; ∀ π̂) | conclusion side | — | `:2372–2398` |

Counts: SOURCE 9, STANDING 0, TYPING 0, DISCLOSED 0, EXCESS 0.
Checks: family/ρ/db chosen before N (stronger than printed). Shared discount and rewards are extra
conclusions. Estimators are deterministic maps dataset → stationary policy (standard meaning of
"estimator"; randomized ones in entry 11). C⋆ uses `optimalGreedyPolicy`, inside an existential
construction — harmless. ε ≤ 0 handled as in C9 (printed hypotheses kept; `x/0 = 0` reading disclosed).
Verdict: **PASS**.

## 11. Thm6_13_randomized — `Ch6.lean:312`
Same source. Same binders as entry 10 plus, inside the conclusion, `∀ Ω μ π̂` (seed space) — conclusion side.
Counts: SOURCE 9, others 0, EXCESS 0.
Checks: generalises entry 10 (Ω = Unit). No measurability of π̂ in the seed; probability of a possibly
non-measurable set is the outer measure, as the docstring states honestly. Verdict: **PASS**.

## 12. Lemma6_18 — `Ch6.lean:357`
Source: `lem:Bernstein-infinite-proof`, `offlineRL.tex:3635–3662`; conditional independence `:1126–1128`.

Reconstruction: δ ∈ (0,1/8), fixed (s,a) with N_{s,a} > 0, V independent of P̂_{s,a} with 0 ≤ V ≤ 1/(1−γ):
w.p. ≥ 1−8δ the two Bernstein bounds (constants 4, 5, 2, 5/3) hold.

| binder | Lean type | bin | citation |
|---|---|---|---|
| S, Fintype, Ω, μ, prob. | | TYPING | — |
| d (= P_{s,a}) | FiniteDistribution | SOURCE | `:3641` |
| γ, 0≤γ, γ<1 | | STANDING | `prelim.tex:45` |
| δ, 0<δ, δ<1/8 | | SOURCE | `:3640` |
| n, 0<n | | SOURCE | `:3640` (N_{s,a} > 0) |
| draw, Measurable, law = d^{⊗n} | | SOURCE | conditional-on-counts sampling `:1126–1128` |
| V, Measurable V | | SOURCE / TYPING | `:3641` |
| IndepFun V (empiricalRow) | | SOURCE | `:3641` |
| 0 ≤ V ≤ 1/(1−γ) | | SOURCE | `:3641` |

Counts: SOURCE 8, STANDING 1, TYPING 2, DISCLOSED 0, EXCESS 0.
Checks: conclusion constants match exactly; wrapper weakens a strict bound to `≤`. Verdict: **PASS**.

## 13. Lemma6_6 — `Ch6.lean:390`
Source: `lem:Bernstein-infinite`, `offlineRL.tex:1147–1163`; penalty `:808–824`; proof remark `:3632`.

Reconstruction: γ ∈ [1/2,1), δ ∈ (0,1): w.p. ≥ 1−δ, ∀(s,a), ∀Ṽ with ‖Ṽ − V̂⋆_pe‖∞ ≤ 1/N, ‖Ṽ‖∞ ≤ 1/(1−γ):
the two Bernstein bounds (8, 26; 2, 24) with log(4N/((1−γ)δ)) and denominators N_{s,a}.

| binder | Lean type | bin | citation |
|---|---|---|---|
| S, A, Fintype, Nonempty | | TYPING | — |
| ρ, P | | SOURCE | `:28–37` |
| p : Params (γ, N>0, r, cb, δ) | | shared bins | `:808–852` |
| 1/2 ≤ p.γ | | SOURCE | `:1149` |
| Ω, μ; X iid block | | TYPING / SOURCE | `:28–37` |
| inside event: ∀ Qstar fixed point | | SOURCE (V̂⋆_pe; all fixed points, unique for γ ≥ 1/2) | `:1036` |
| 0 < count s a | | TYPING (division domain; source `:3632` declares N_{s,a}=0 trivial, i.e. right sides +∞) | scope-disclosures "Lemma 6.6" |
| Ṽ bounds | | SOURCE | `:1160–1161` |

Counts: SOURCE 7, STANDING 2, TYPING 5, DISCLOSED 0, EXCESS 0.
Checks: the same δ is used in the penalty and the probability; the printed lemma uses one symbol δ and
V̂⋆_pe depends on the penalty's δ, so this is a faithful reading (the library export
`bernsteinInfinite_iid` is more general — independent event level). The `0 < count` guard is equivalent to
the printed claim under the source's own "+∞/trivial" convention; the docstring and scope-disclosures entry
describe it accurately. Verdict: **PASS** (note: the project labels the guard a "scope disclosure" yet keeps
the plain name; I judge it a faithful domain encoding, like β₀ = +∞ in Lemma 6.9).

## 14. Lemma6_9_restricted — `Ch6.lean:450`
Source: `lemma:Q-recursion-pessimistic-Q`, `offlineRL.tex:1866–1893`; algorithm `:1701–1745`; parameters
`:1663–1689`; notation `:1806–1852`.

Reconstruction: for c_b large enough, w.p. ≥ 1−δ, ∀ 1≤t≤T, (s,a), deterministic π: Q⋆ − Q_t ≤
γΣ_{i≤n} η_i^n P_{s,a}(V⋆ − V_{k_i−1}) + β_n, and Q^π − Q_t ≥ γΣ η_i^n P_{s,a}(V^π − V_{k_i−1}); β₀ = +∞.

| binder | Lean type | bin | citation |
|---|---|---|---|
| ∃ cb₀ > 0, ∀ cb ≥ cb₀ | | SOURCE ("c_b large enough") | `:1884` |
| S, A, Fintype; M | | TYPING / shared | — |
| db | | SOURCE | `:28–39` |
| sel, ∀f a, f a ≤ f (sel f) | | DISCLOSED (tie rule = function of the Q-row only) | `_restricted`, docstring, scope-disclosures "Lemma 6.9" |
| π₀ | S → A | SOURCE (arbitrary initial policy) | `:1707` |
| T, δ, 0<δ, δ<1 | | SOURCE | `:1663` |
| Ω, μ, X iid block | | TYPING / SOURCE | `:28–39` |

Counts: SOURCE 7, STANDING 2, TYPING 4, DISCLOSED 1, EXCESS 0.
Checks: `0 < n →` encodes β₀ = +∞ exactly; `visitTime` gives V_{k_{i+1}−1}; η via `onlineQRateWeight` =
source η_i^n; Q⋆ = optimality fixed point, V⋆ = optimal trajectory value. Verdict: **PASS-DISCLOSED**.

## 15. Lemma6_10_restricted — `Ch6.lean:506`
Source: `lemma:pessimistic-Q`, `offlineRL.tex:1907–1916`; π_t `:1825–1831`.

Reconstruction: w.p. > 1−δ, ∀ 1≤t≤T, (s,a): Q_t ≤ Q⋆ and V_t ≤ V^{π_t} ≤ V⋆ (no c_b condition printed).
Binders as entry 14, with `∃ cb₀, ∀ cb ≥ cb₀` = DISCLOSED (C28: printed lemma false for small c_b) and the
tie rule DISCLOSED.
Counts: SOURCE 6, STANDING 2, TYPING 4, DISCLOSED 2, EXCESS 0.
Checks: strict `1 − δ <` matches "exceeding"; π_t = `run … t`.policy. Verdict: **PASS-DISCLOSED**.

## 16. Lemma6_12_restricted — `Ch6.lean:547`
Source: `lem:lcbq-alpha-xi-psi-phi-bound`, `offlineRL.tex:2309–2324`; sequences `:1970–2015`; limits
`:2264–2276` (α = limsup α_j).

Reconstruction: w.p. ≥ 1−δ: α = 0, ξ ≲ 1/(1−γ)², θ ≲ √(C⋆STι²/(1−γ)⁵), ψ+φ ≲ C⋆ι²/(1−γ)³.

| binder | bin | citation |
|---|---|---|
| ∃cb₀ ∀cb≥cb₀ | SOURCE (Thm 6.8 context `:1764`, `≲` constants) | `:1764`, `:1884` |
| ∃ C > 0 (depends on c_b only) | SOURCE (`≲`) | `:2316` |
| S, A, M, db, π₀, T, δ, ρ, Ω, μ, X block | TYPING / shared / SOURCE | as entry 14 |
| sel + argmax property | DISCLOSED (tie scope) | scope-disclosures |
| πstar, Q⋆-greedy | SOURCE (π⋆ optimal deterministic) | `:138` |
| 1 ≤ ι | DISCLOSED | `_restricted`, docstring, C24 |

Counts: SOURCE 9, STANDING 2, TYPING 4, DISCLOSED 2, EXCESS 0.
Checks: `Tendsto α_j → 0` implies limsup = 0; HasSum asserts summability (stronger). `Cs ≠ ⊤ →` guards
are faithful (right sides +∞ otherwise). Real division by `db.prob` in ψ/φ only on a null set. Verdict:
**PASS-DISCLOSED**.

## 17. Thm6_8_corrected — `Ch6.lean:598`
Source: `theorem:lcbq`, `offlineRL.tex:1754–1772`.

Reconstruction: δ ∈ (0,1), ε ∈ (0,1/(1−γ)], ρ: w.p. > 1−δ, V⋆(ρ) − V^π̂(ρ) ≤ ε, provided c_b large and
T ≥ c₂SC⋆log(SAT/((1−γ)δ))/((1−γ)⁵ε²).

| binder | bin | citation |
|---|---|---|
| ∃cb₀ ∀cb≥cb₀ ∃c₂>0 | SOURCE (c_b large; c₂ universal) | `:1764–1768` |
| S, A, M, db, π₀, δ bounds, ρ, ε bounds, X block | TYPING / shared / SOURCE | `:1756–1758` |
| sel + argmax | DISCLOSED (tie scope) | docstring, C24 scope sentence, scope-disclosures |
| 1 ≤ T | TYPING (log domain; T = 0 would make Lean's log 0 = 0 condition trivial) | — |
| πstar Q⋆-greedy | SOURCE | `:138` |
| C⋆ ≠ ⊤ | TYPING (printed condition unsatisfiable at C⋆ = ∞; `⊤.toReal = 0` junk blocked) | — |
| log² sample condition | DISCLOSED | `_corrected`, docstring, C24 |

Counts: SOURCE 9, STANDING 2, TYPING 6, DISCLOSED 2, EXCESS 0.
Checks: output is π_T of `run`; strict probability as printed; c₂ depends on c_b (C24 counterexample shows
it must). Verdict: **PASS-DISCLOSED**.

## 18. Thm6_3 — `Ch6.lean:652`
Source: `thm:infinite-offline`, `offlineRL.tex:899–920`; Alg. `:827–852`; penalty `:808–824`.

Reconstruction: γ ∈ [1/2,1), δ ∈ (0,1), ε ∈ (0,1/(1−γ)], ρ, τmax ≥ (1/(1−γ))log(N/(1−γ)); for c_b large
and N ≥ c₁SC⋆log(NS/((1−γ)δ))/((1−γ)³ε²): w.p. ≥ 1−2δ, V⋆(ρ) − V^π̂(ρ) ≤ ε, π̂ greedy for Q̂_{τmax}.

| binder | bin | citation |
|---|---|---|
| ∃cb₀ ∀cb≥cb₀ ∃c₁>0 | SOURCE | `:913–916` |
| S, A, Fintype, Nonempty | TYPING | — |
| M, db | shared / SOURCE | `:28–39` |
| p : Params; p.γ = M.discount; p.r = M.reward; p.cb = cb | SOURCE (tying algorithm inputs to the MDP) | `:828` |
| p.N > 0 | TYPING | — |
| p.δ ∈ (0,1) | SOURCE | `:901` |
| 1/2 ≤ M.discount | SOURCE | `:901` |
| τmax condition | SOURCE | `:901` |
| ρ; πstar Q⋆-greedy | SOURCE | `:901`, `:138` |
| 0 < ε ≤ 1/(1−γ) | SOURCE | `:901` |
| C⋆ ≠ ⊤ | TYPING | as entry 17 |
| sample-size condition | SOURCE | `:911` |
| Ω, μ, X block | TYPING / SOURCE | `:28–39` |

Counts: SOURCE 13, STANDING 2, TYPING 5, DISCLOSED 0, EXCESS 0.
Checks: the event holds for every greedy π̂ (every tie rule), so it implies the printed claim for any tie
rule. "c₁ universal" read as depending on c_b; since c_b is itself a fixed numerical constant this implies
"∃ c_b, ∃ c₁". Same δ in penalty and 1−2δ, as printed. Verdict: **PASS**.

## 19. Thm6_16_restricted — `Ch6.lean:715`
Source: `thm:finite-VI-LCB`, `offlineRL.tex:3093–3112`; setting `:2943–2973`; C⋆ `:2983–2993`.

Reconstruction: ε ∈ (0,H], δ ∈ (0,1), ρ: there exists a VI-LCB variant such that w.p. ≥ 1−δ,
V⋆₁(ρ) − V^π̂₁(ρ) ≤ ε whenever K ≥ c_k H³SC⋆log(KH/δ)/ε².

| binder | bin | citation |
|---|---|---|
| ∃cb₀ ∀cb≥cb₀ ∃ck>0 | SOURCE (numerical c_k) | `:3109` |
| S, A, Fintype, Nonempty; 0 < H | TYPING | — |
| E, πb, ρb, ρ | SOURCE | `:2943–2973` |
| πs optimal at every stage/state | SOURCE (π⋆) | `prelim.tex:740–745` |
| ε, δ ranges | SOURCE | `:3097` |
| 0 < K | TYPING (log domain) | — |
| C⋆ ≠ ⊤ | TYPING | — |
| size condition | SOURCE | `:3107` |
| Ω, μ, X iid trajectories with `trajMeasure` | TYPING / SOURCE | `:2953–2958` |
| algorithm fixed to `FiniteVILCB.qhat` | DISCLOSED | `_restricted`, docstring, C32 |

Counts: SOURCE 9, STANDING 0, TYPING 5, DISCLOSED 1, EXCESS 0.
Checks: the algorithm reads only c_b, δ, rewards and data; holds for every greedy π̂; with c_b fixed this
gives the printed existential. Verdict: **PASS-DISCLOSED**.

## 20. Thm6_17_restricted — `Ch6.lean:794`
Source: `thm:lcbq`, `offlineRL.tex:3176–3192`; algorithm prose `:3126–3148`.

Reconstruction: δ ∈ (0,1), ε ∈ (0,H], ρ: w.p. ≥ 1−δ the LCB-Q output satisfies the gap ≤ ε when
K ≥ c_a H⁵SC⋆log³(SAK/δ)/ε² (algorithm under-specified).

Binders as entry 19, plus L with ι ≤ L ≤ max(ι, ι³), sel + argmax, π₀ (DISCLOSED: one explicit completion,
output rule differs from literal `:3145`, deterministic π⋆ in C⋆; C33).
Counts: SOURCE 9, STANDING 0, TYPING 5, DISCLOSED 3, EXCESS 0.
Checks: size condition is the printed log³ form; L-range never empty. Verdict: **PASS-DISCLOSED**.

## 21. Eq_defn_Cstar_bandits — `Ch6.lean:842`
Source: `eq:defn-Cstar-bandits`, `offlineRL.tex:264–281`.
Reconstruction: max_a d⋆(a)/d^b(a) = 1/d^b(a⋆) with d⋆ = 1{a = a⋆}, 0/0 = 0.
Binders: Arm, Fintype, DecidableEq, MeasurableSpace (TYPING); d (SOURCE, generalised to any measure);
aStar (SOURCE). Counts: SOURCE 2, TYPING 4, EXCESS 0.
Checks: ENNReal 0/x = 0 for b ≠ a⋆; holds also at d^b(a⋆) = 0 (= ∞). Verdict: **PASS**.

## 22. Remark6_4 — `Ch6.lean:853`
Source: `offlineRL.tex:357–359` (on Example 6.1 `:348–355`).
Reconstruction: in Example 6.1, C⋆ is "exceedingly close to 1".
Binders: N, 2 ≤ N (SOURCE, Example 6.1 `:350`). Counts: SOURCE 2, EXCESS 0.
Checks: reading d^b = empirical design frequency (design deterministic) stated in docstring; C⋆ = N/(N−1)
→ 1. Formal reading of an informal remark; implied content is correct. Verdict: **PASS**.

## 23. Remark6_2 — `Ch6.lean:867`
Source: `rem:Cstar_lower_bound_infinite`, `offlineRL.tex:142–151`.
Binders: S, A, Fintype (TYPING); M (shared); π any stationary policy (SOURCE, generalised from π⋆); ρ, db
(SOURCE). Counts: SOURCE 3, STANDING 2, TYPING 4, EXCESS 0.
Checks: ENNReal ratio with 0/0 = 0; covers every optimal π⋆. Verdict: **PASS**.

## 24. Remark6_3 — `Ch6.lean:888`
Source: `offlineRL.tex:175–185`.
Reconstruction: C_clipped ≤ C⋆; C_clipped can be as low as 1/S.
Binders: (i)/(iii) as entry 23; (ii) S, A, Fintype, Nonempty (TYPING) with existential witness.
Counts: SOURCE 3, STANDING 2, TYPING 6, DISCLOSED 0, EXCESS 0.
Checks: (ii) uses `optimalGreedyPolicy` on a degenerate witness (all policies optimal) — disclosed in the
docstring and scope disclosures; the printed sentence is existential, so this is a valid reading (a
non-degenerate witness also exists: absorbing state, unique optimal action, d^b a point mass). (iii) adds a
true lower bound. Citation sentence `:184` excluded, as stated. Verdict: **PASS**.

## 25. Remark6_5 — `Ch6.lean:917`
Source: `offlineRL.tex:413–415`; Alg. 6.1 `:383–445`; penalty `:400–402`; Example 6.1 `:348–355`.
Reconstruction: in Example 6.1, r₁^lcb ≈ r₁ for large N, r₂^lcb ≤ r₂, so LCB picks arm 1 w.h.p.
Binders: N, δ, 2 ≤ N, 0<δ<1 (SOURCE); 8log(8/δ) < N−1 (SOURCE: explicit "large enough N").
Counts: SOURCE 5, EXCESS 0.
Checks: radius √(2log(8/δ)/n) = printed with A = 2; both counts positive, so the fallback branch is never
used; quantitative "≈" reading stated in docstring. Verdict: **PASS**.

## 26. Example6_1 — `Ch6.lean:937`
Source: `example:offline-bandits`, `offlineRL.tex:348–355`; r̄, a^emp `:323–342`.
Binders: N, 2 ≤ N (SOURCE); sel with argmax property (SOURCE: a^emp ∈ argmax, any tie rule).
Counts: SOURCE 3, EXCESS 0.
Checks: lower Lebesgue integral of the nonnegative regret — the conservative direction for a lower bound
when the selector is non-measurable; equals the expectation for measurable selectors. Verdict: **PASS**.

---

## Summary

| # | entry | def line | verdict |
|---|---|---|---|
| 1 | Thm6_1_zeroCountFallback_corrected | 32 | PASS-DISCLOSED |
| 2 | Lemma6_2_corrected | 52 | PASS-DISCLOSED |
| 3 | Lemma6_2_iterationCount_restricted | 72 | PASS-DISCLOSED |
| 4 | Lemma6_5_sampleSplit_actualData_corrected | 93 | PASS-DISCLOSED |
| 5 | Lemma6_4 | 120 | PASS |
| 6 | Lemma6_7_restricted | 145 | PASS-DISCLOSED |
| 7 | Lemma6_14_restricted | 170 | PASS-DISCLOSED |
| 8 | Lemma6_15 | 198 | PASS |
| 9 | Lemma6_11_restricted | 224 | **FAIL** (π⋆ fixed to library tie choice, undisclosed) |
| 10 | Thm6_13 | 262 | PASS |
| 11 | Thm6_13_randomized | 312 | PASS |
| 12 | Lemma6_18 | 357 | PASS |
| 13 | Lemma6_6 | 390 | PASS |
| 14 | Lemma6_9_restricted | 450 | PASS-DISCLOSED |
| 15 | Lemma6_10_restricted | 506 | PASS-DISCLOSED |
| 16 | Lemma6_12_restricted | 547 | PASS-DISCLOSED |
| 17 | Thm6_8_corrected | 598 | PASS-DISCLOSED |
| 18 | Thm6_3 | 652 | PASS |
| 19 | Thm6_16_restricted | 715 | PASS-DISCLOSED |
| 20 | Thm6_17_restricted | 794 | PASS-DISCLOSED |
| 21 | Eq_defn_Cstar_bandits | 842 | PASS |
| 22 | Remark6_4 | 853 | PASS |
| 23 | Remark6_2 | 867 | PASS |
| 24 | Remark6_3 | 888 | PASS |
| 25 | Remark6_5 | 917 | PASS |
| 26 | Example6_1 | 937 | PASS |

Totals: PASS 12, PASS-DISCLOSED 13, FAIL 1, UNSURE 0.

Non-blocking notes: (a) Lemma 6.5 docstring still says "restricted" although the name is `_corrected` and C19's
addendum shows the printed lemma is false at N = 1. (b) Lemma6_6 keeps a plain name while the project calls its
`0 < N_{s,a}` guard a "scope disclosure"; I judge the guard faithful (source `:3632`), but the labelling is
inconsistent. (c) `Ch6.lean` imports two modules that also contain theorems (AGENTS.md: definitions only).
(d) FiniteVILCB/LCBQFinite internals (`trajMeasure`, `stageIndex`, `qhat`, `output`) and core MDP value
definitions were checked at docstring/signature level only, not re-audited line by line.
Method: reading only; no Lean compilation run by this auditor.

---

## Re-audit after fix (2026-11-09): Lemma6_11_restricted — `Ch6.lean:226`

Fix source: the fix log (local, not published):7`. Re-read the def, docstring and wrapper
(`Ch6Proofs.lean:114–117`); same source ranges as entry 9 (`offlineRL.tex:2292–2300`, `:1667–1672`,
`:2284–2287`, `:1970–1973`, `:138`, `prelim.tex:160–172`).

| binder | Lean type | bin | citation |
|---|---|---|---|
| ∃ C, 0 < C (outermost) | ℝ | SOURCE (`≲`, universal) | `:2296` |
| S, A, Fintype | types | TYPING | — |
| M | DiscountedMDP | shared (STANDING reward/discount, TYPING nonempty) | `prelim.tex:42,45` |
| ρ | FiniteDistribution S | SOURCE | `:2295` |
| πstar : S → A | deterministic policy | SOURCE (π⋆) | `:138`, `prelim.tex:160–172` |
| ∀ s, Q⋆(s, πstar s) = max_a Q⋆(s,a) | Prop | SOURCE (π⋆ optimal deterministic ⇔ Q⋆-greedy) | `:138` |
| δ, 0<δ, δ<1 | ℝ | SOURCE | `:2294` |
| T, 1 ≤ T | ℕ | TYPING (log domain) | — |
| 1 ≤ log(SAT/δ) | Prop | DISCLOSED | `_restricted`, docstring, C22, scope disclosures |
| W, ∀s, 0 ≤ W s | | SOURCE | `:2294` |

Counts: SOURCE 7, STANDING 2, TYPING 4, DISCLOSED 1, EXCESS 0.

Checks: the greedy hypothesis is character-for-character the form used in `Lemma6_12_restricted`
(`Ch6.lean:553–554`) and `Thm6_8_corrected`. For a finite discounted MDP, a deterministic policy is greedy for
Q⋆ at every state iff it is optimal, so this ranges over exactly the source's possible π⋆ (every tie rule). It is
satisfiable (`optimalGreedyAction`). `OfflineRL.LCBQ.detPolicy πstar = fun s ↦ pointMass (πstar s)`
(`LCBQDefinitions.lean`). This is the same object `concentrability`, `dWeight` and the Lemma 6.12 sequences use
for π⋆, and `occupancyStateAt (detPolicy πstar) ρ j` is ρᵀ(P_{π⋆})^j. C remains universal, quantified before
S, A, M and π⋆. The `tsum` junk is unreachable because κ < 1 under the premise. The wrapper only applies
`lcbq_useful M (detPolicy πstar) …` with C = 84. The docstring now states "every optimal deterministic policy;
no tie rule is fixed", which is accurate.

Verdict: **PASS-DISCLOSED** (supersedes the entry-9 FAIL). Updated totals: PASS 12, PASS-DISCLOSED 14,
FAIL 0, UNSURE 0. Side check: the Lemma 6.5 docstring (`Ch6.lean:86–93`) now says "corrected" and cites the
C19 N = 1 counterexample, which resolves non-blocking note (a).
