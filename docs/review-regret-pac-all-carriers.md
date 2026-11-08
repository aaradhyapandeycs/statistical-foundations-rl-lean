# REVIEW: the all-carriers refutation of the regret-to-PAC conversion (onlineRL.tex:113–183)

Public copy of the independent review of the critic's all-carriers refutation; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review covered the pre-integration snapshot (the builder's snapshot plus the critic's all-carriers probe module, reviewed in `critic-regret-pac.md`). The all-carriers refutation, written by the critic during the critic review, was adopted in its positive-constant form (F1 below) as the primary evidence for [C46](SOURCE-ISSUES.md#C46). The work was integrated into `Formalization/Online/RegretToPAC/{Definitions,StartState,Corrected,PrintedRefutation}.lean` (namespace `StatisticalRL.OnlineRL.RegretToPAC`), with statement-index entries `Eq_PAC_from_regret_conversion_corrected` and `Eq_PAC_from_regret_conversion_restricted` in `Formalization/Statements/Ch5.lean`. Names below are the integrated names, following the builder's rename list:
- the reviewed all-carriers Prop without a positivity hypothesis is called "the all-carriers Prop" below; it was not integrated as such;
- its positive-constant variant (F1) is the integrated main printed Prop `Eq_PAC_from_regret_conversion_printed`, refuted by `not_Eq_PAC_from_regret_conversion_printed`;
- the snapshot's fixed-carrier `_printed` is now `Eq_PAC_from_regret_conversion_printed_fixedCarrier`;
- counterexample algorithm `printedCexAlg`, constants `printedCexConst` (positivity `printedCexConst_pos`, non-monotonicity `printedCexConst_two_lt_one`), instance stage `printedCexStage`, reward argmax/argmin `rewardArgmax`/`rewardArgmin`;
- general lemmas `trajectoryValue_pointMass_nonneg`, `optimalValue_le_length`, `optimalValue_le_myopic_of_subsingleton`, `trajectoryValue_withPolicy_cons`, `expectation_of_subsingleton`; `value_le_optimal` → `trajectoryValue_pointMass_le_greedy`; `rowMeasure_real_setOf_false` → `rowMeasure_real_setOf_eq_zero`.

File hashes are those of the reviewed snapshot and probe files. The review text below is otherwise unchanged.

Independent reviewer, 2026-11-08. I read the source first. I wrote only this file and probes in the reviewer's
private probe folder (oleans in the reviewer's private olean folder). I did
not touch `Formalization/` or the project's `Formalization*` build outputs, and I fetched no paper.

**Verdict: ACCEPT WITH FIXES.** The mathematics is correct and the Lean proof is sound with a clean axiom
closure. The fixes concern packaging (positivity in the Prop), the honesty of the source-issue entry
(non-monotone constant), citations, and integration hygiene.

## 0. Integrity

- The critic's all-carriers probe module has sha256
  `4c28e2a1e5ed49232cd249dd134e50575b0fa2b735d0ea8391c40ef7234876e1`. This matches the brief.
- The builder's reviewed snapshot matches the builder's snapshot hash list (Corrected `2d622baf…`,
  Refutation `f79e631c…`, StartState `5c9329c4…`, Statements `de8c8962…`).
- My copies in the reviewer's private probe folder differ from the snapshot or critic files only in
  `import` lines, which I checked by diff after removing imports.
- Build. I ran `bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean <file>` in
  the foreground, one file at a time, in this order: Statements (6.5 s), StartState (2.4 s),
  Corrected (4.2 s), Refutation (2.7 s), the all-carriers module (2.2 s). Every run exited 0 with no errors. A plain
  re-run of the all-carriers module printed nothing.

## 1. Source reading (formed before reading the Lean)

- Protocol (:17–41). The MDP is nonstationary with finite S and A. The reward is **known** (:20), and by
  the book's convention r_h ∈ [0,1]. s₁ᵏ are i.i.d. from ρ. π^k is chosen from episodes 1..k−1.
- Claim (:113–141). An algorithm satisfies E Regret(K) ≤ C_{S,A,H} K^{1−α} "for any MDP with S states, A
  actions and horizon H", with α ∈ [0,1] and C_{S,A,H} "some quantity that may depend on (S,A,H)". Draw
  π̂ ~ Unif(π¹..π^K) from the deployed policies. Then w.p. ≥ 1−δ,
  V⋆₁(ρ) − V₁^{π̂}(ρ) ≤ C_{S,A,H+1} K^{−α} δ^{−1}.
- Proof (:145–183). For a singleton ρ, Markov gives C_{S,A,H}. For general ρ, the proof adds a step 0
  and runs the algorithm on the *augmented* MDP of horizon H+1.
- My reading. The deployed policies in the statement are those of the run on the given MDP. The
  augmented run appears only inside the proof. The hypothesis quantifies over all MDPs of a class, and
  most naturally over every (S,A,H), because C is indexed by all three and the conclusion evaluates C at
  H+1. Nothing in the source requires C ≥ 0 or C to be monotone.
- Consequence. Under the given-run reading, Markov plus start-state independence give the bound with
  C_{S,A,H}; the augmentation is not needed. The printed C_{S,A,H+1} therefore follows only when
  C_{S,A,H} ≤ C_{S,A,H+1}. If C may decrease in H, an algorithm that is deliberately bad at horizon H and
  good at horizon H+1 breaks the claim. That is exactly the probe's construction. I agree with
  CRITIC §3 and CHECK §(d) that this is a genuine but mild error in the constant's index.

## 2. Check 1: is the all-carriers Prop at least as weak as every reasonable reading?

All-carriers Prop `:= ∀ Seed ν alg C α, 0≤α → α≤1 → Hyp(all carriers) → Concl(all carriers, ∀δ>0)`.
A weaker Prop needs fewer algorithms, a stronger hypothesis or a weaker conclusion.

| Aspect | Lean | Direction / verdict |
|---|---|---|
| Carrier quantification | One `alg` family over every `(State : Type u) (Action : Type v)` with Fintype/Nonempty; Hyp holds for every carrier, H>0, K>0, E, ρ | This is the strongest hypothesis that can be read off "for any MDP with S states, A actions and horizon H". It covers both the fixed-class and the all-(S,A,H) readings. OK. |
| Algorithm class | Finite seed with law `ν H K`; deterministic Markov tables `planner(history.take(k*H))`; the algorithm sees H, K and r | This is fewer algorithms than the book allows, so the Prop is weaker, which is safe. The counterexample `printedCexAlg` ignores the seed, K, the history and the carrier cardinalities. It uses only H and the known reward, so it lies in every reasonable class. OK. |
| Constants | `C : ℕ → ℕ → ℕ → ℝ`, a function of (card S, card A, H) chosen after `alg` | Faithful. **The Prop has no positivity hypothesis**, although the critic advertises "strictly positive constants" (fix F1). |
| α | `0 ≤ α ≤ 1` | As printed. The instance uses α = 0. |
| δ | `0 < δ` only | As printed. Adding δ<1 would make the Prop stronger; it is absent, which is fine. The instance uses δ = 1/2. |
| π̂ | `ν.E[(1/K) Σ_k P_run(event_k)]` | This is exactly the joint probability over (seed, run, J ~ Unif). OK. |
| Values | `Vstar` = `greedyStages`, which equals `optimalValue` by `greedy_trajectoryValue`; V is the exact return of a deterministic table | OK. |
| Known reward / ρ | `alg … (fun h ↦ (E h).reward)`; ρ is not passed | OK. Rewards lie in [0,1] (`EnvironmentStage.reward_nonneg/le_one`), which is the book's convention. |
| Protocol | `onlineSequentialEpisodeLaw`: product reset law ∏ρ, π^k from `history.take(k*H)` | I checked this against `SequentialEpisodeDefinitions.lean:39–68` and `EpisodicSelectorDefinitions.lean:18–33`. Faithful. |
| Hyp domain | Only `0 < H` and `0 < K` | This hypothesis is narrower than "all H, K", which in principle makes the Prop stronger. However `printedCexConst > 0` makes H = 0 (regret 0) and K = 0 (empty sum ≤ C·0^{1−α}, which is ≥ 0) trivially true. Harmless. Mention it in the docstring (F4). |
| Universe | Refuted at `.{0,0}` | All constructions depend only on cardinalities. Acceptable. |

Two readings are **not** covered, and the SOURCE-ISSUES entry must disclose both (F2):

- **(R-mono)** C_{S,A,H} is nondecreasing in H. This is implicit in every use in the book, for example
  Õ(√(SAH³K)) at :186. Under (R-mono) the printed claim is **true**: the snapshot's
  `eq_PAC_from_regret_conversion_restricted` proves it at fixed carriers. `printedCexConst` is not monotone:
  `printedCexConst 1 2 2 = 1/4 < 2 = printedCexConst 1 2 1`, which my probe checks. The refutation depends on this.
- **(R-aug)** π̂ is drawn from the run on the augmented MDP. This reading changes the statement's object,
  and the proof essentially establishes it, so it is not a reasonable reading of the *statement*.

Neither gap is a defect of the refutation. They limit what the issue entry may claim. The correct claim
is: "false as printed, because the constant may decrease in H; true with C_{S,A,H}, and true with
C_{S,A,H+1} under monotone C."

## 3. Check 2: the instance and the regret hypothesis for every class

- **Case card S = 1, H ≠ 1, C = 1/4.** `printedCexAlg` plays `rewardArgmax ((E h).reward t)` at every step
  (`hf` by `simp [hc.2]`). `optimalValue_le_myopic_of_subsingleton` proves by induction on H that on a
  `Subsingleton` state type, V⋆ ≤ the return of myopic argmax. The proof uses `Finset.sup'_le` over
  actions and `expectation_of_subsingleton` to collapse every transition. This holds for arbitrary
  rewards in [0,1] and arbitrary (necessarily trivial) transitions. Each per-episode regret is therefore
  ≤ 0, so E Regret ≤ 0 ≤ K/4 for **every** one-state MDP with H ≥ 2 and every A, K, ρ and seed law. I
  find this genuinely proved and mathematically right: with one state and a known reward, the MDP is
  fully known and greedy play is optimal.
- **All other cases, C = H + 1.** Per episode, V⋆ ≤ H (`optimalValue_le_length`, using
  r ≤ 1) and V ≥ 0 (`trajectoryValue_pointMass_nonneg`, using r ≥ 0). So the regret is ≤ HK ≤ (H+1)K for any policy.
  This is trivially true, as expected. It covers card S = 1 with H = 1, where the algorithm
  deliberately plays argmin, and every card S ≠ 1, including card S = 0. That case is vacuous anyway,
  because `E 0` supplies `state_nonempty`.
- **Instance.** State = Unit, Action = Bool, H = K = 1, `printedCexStage` with reward(true) = 1,
  reward(false) = 0, ρ = point mass, δ = 1/2, α = 0, and `ν` = point mass on `()`. The printed bound is
  `printedCexConst 1 2 2 · 1^0 / (1/2) = 1/2`. The deployed action is `rewardArgmin`, whose reward is ≤ r(false) = 0, so
  V^{π̂} = 0. V⋆ ≥ r(true) = 1 (`trajectoryValue_pointMass_le_greedy`). The gap is ≥ 1 > 1/2 on every sample, so the event
  is empty (`rowMeasure_real_setOf_eq_zero`) and its probability is 0 < 1/2 = 1 − δ. Correct.
- The positivity of the constants is proved separately (`printedCexConst_pos`). I also checked it inside a Prop
  (see F1).

## 4. Check 3: axioms and tokens

My probe file in the reviewer's private probe folder (compiled, exit 0), with reviewed names mapped to the
integrated names:

```
refutation of the all-carriers Prop                  depends on axioms: [propext, Classical.choice, Quot.sound]
refutation of the positive-constant variant
  (now not_Eq_PAC_from_regret_conversion_printed)    depends on axioms: [propext, Classical.choice, Quot.sound]
printedCexConst_pos                                  depends on axioms: [propext, Classical.choice, Quot.sound]
```

`grep` over all five copied modules finds no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
`extern`, `unsafe`, `opaque`, `set_option`, `macro` or `elab`.

The probe also proves that the all-carriers Prop implies its positive-constant variant, so the variant is the
weaker Prop. It then proves the negation of the variant at `.{0,0}` by the same proof plus `printedCexConst_pos`.
This mechanically confirms "refuted even with strictly positive constants".

## 5. Required fixes

- **F1 (required).** Put positivity in the statement. Either add `(∀ S A H, 0 < C S A H) →` to the
  library Prop, or export both versions. My probe file already
  contains a compiled version (the positive-constant Prop, its refutation and the weakening lemma).
  The C = 0 escape then cannot be raised against the refutation.
- **F2 (required, docs).** The SOURCE-ISSUES (C46) entry must say:
  - the refutation exploits a C that is **non-monotone in H**, together with a deliberately bad H = 1
    behaviour and the known-reward convention;
  - the claim is true with C_{S,A,H}, which is the snapshot's `_corrected`;
  - the claim is true with C_{S,A,H+1} when C is nondecreasing in H, which is `_restricted`;
  - the augmented-run reading (R-aug) is a proof artifact;
  - the algorithm class is restricted: finite seed and deterministic deployed tables. This restriction
    only weakens the refuted Prop.
- **F3 (required).** Fix the citations. The probe docstring cites `onlineRL.tex:126–150`. The claim
  block is :113–141 (labels `eq:PAC-from-regret-conversion` :116, `-regret` :122, `uniform-policy-pihat`
  :129, `-pac` :138), the proof is :145–183, the protocol is :17–41 and the known reward is at :20.
  onlineRL is Chapter 5 (`StatisticalRL-nowplain.tex:218`), so any statement-index entry belongs in
  `Statements/Ch5.lean`.
- **F4 (integration).**
  - Rename the critic's and builder's working namespaces to `StatisticalRL.OnlineRL.RegretToPAC`.
  - Place the files under `Formalization/Online/RegretToPAC/`: definitions (Prop) in
    `Definitions.lean`, and generic lemmas plus the counterexample in `PrintedRefutation.lean`.
  - Name the all-carriers Prop `Eq_PAC_from_regret_conversion_printed` (or the `_allCarriers`
    variant) and its refutation `not_Eq_PAC_from_regret_conversion_printed`. The existing
    fixed-carrier `_printed` from the snapshot should be either renamed `…_printed_fixedClass` or dropped
    in favour of this one.
  - The Prop belongs to definitions-only imports, so it may live in `Statements/Ch5.lean`. Follow the
    project convention for refuted entries: a refutation is not "proved", so record it in SOURCE-ISSUES
    rather than as a proved `_holds`.
  - Deduplicate. The critic's generic lemmas subsume the snapshot Refutation's Unit-specific ones
    (`value_nonneg_unit`, `optimalValue_le_length`, `optimalValue_le_myopic`,
    `trajectoryValue_withPolicy_cons_unit`). Keep the general ones, with
    Mathlib-style names: `trajectoryValue_withPolicy_cons`, `trajectoryValue_pointMass_nonneg`,
    `optimalValue_le_length`, `optimalValue_le_myopic_of_subsingleton`.
  - Give the reward argmax/argmin helpers names such as `rewardArgmax`/`rewardArgmin`, or reuse an
    existing argmax helper if `MDP/FiniteOptimal.lean` provides one.
  - Mention the `0 < H`, `0 < K` hypothesis domain in the docstring.
  - Mark the counterexample algorithm and constants as counterexample-only, with docstrings.
- **F5 (minor).** The module docstring calls `C = 0` "allowed". After F1, state that the refuted Prop
  assumes C > 0.

## 6. Probe files

- Import-renamed copies of the four snapshot modules and the critic's all-carriers module, in the
  reviewer's private probe folder.
- A probe file in the same folder holds the positivity variant, the weakening lemma, the non-monotonicity
  check and the axiom prints.

Reviewed file sha256: `4c28e2a1e5ed49232cd249dd134e50575b0fa2b735d0ea8391c40ef7234876e1`.
