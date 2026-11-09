# CRITIC P3b (Chapter 7 MARL best response, NE ⇒ CCE, d_cvx ≤ TV, plug-in weights): independent review

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-09): this critic reviewed the pre-integration drafts. They were integrated on 2026-11-09 into `Formalization/Statements/Ch7.lean` and `Ch7Proofs.lean`. R1–R5 were applied before landing: R1 replaced the U19 context note by the informal, not-machine-checked remark quoted below; R2: `Eq_tdWeights_sum` keeps its own COVERAGE row, because the node generator maps the entry to its own display node (inference lines 174–176) and leaves the `eq:defn-hat-Lambda` node unchanged (checked on the regenerated graph; no double counting); R3 corrected the locators in `MarlBestResponse.lean` (:128–132, :135–143, CCE :232–238), so its hash differs from the one quoted below, and in the U17 and U18 rows and entry docstrings; R4 qualifies `Thm7_11_printed_allConvex` as the library definition in `TDInferencePrinted711.lean`; R5 adds the reward and action-set sentence to the U17 row. The wrapper docstrings name library exports unqualified, so the graph generator does not attribute them to a neighbouring node. Labels U17–U20 number the rows of the builder's draft; F-P3b-n refers to the independent completion check. The review text below is otherwise unchanged.

Critic: independent (not the builder). Date 2026-11-09. Brief: the completion plan, batch P3b, as
amended by the independent completion check, findings F-P3b-1, F-P3b-2.

**Overall verdict: ACCEPT WITH FIXES.** All four entries are faithful. The Lean is sound and the
axioms are clean. The required fixes are documentation-only (R1, R2). R3–R5 are recommended.

## Evidence (own runs, one Lean process at a time, guard `pgrep -x lean | wc -l` < 2)

Hashes verified equal to the builder's status notes:
`MarlBestResponse.lean d1fb11d0…`, `ConvexDistanceTV711.lean a9062ed5…`,
the statement draft `7247a448…`, the wrapper draft `f61a9ec0…`.

- a critic probe, run with the project's local Lean wrapper (≈44 s): clean.
  The probe imports `Formalization` + `MarlBestResponse` + `ConvexDistanceTV711` + `TDInferencePlugin711`,
  then pastes the drafts verbatim into `StatisticalRL.Statements.Ch7` (no name collision with the
  current `Formalization`). `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all four
  `_holds`. Critic extras that also compile:
  - `∀ σ, toJoint σ ≠ coordPolicy`;
  - `¬ ∃ σ, IsNE coordGame σ ∧ toJoint σ = coordPolicy`;
  - an instantiation of the U19 entry at d = 2.
- the statement draft, which has only the CURRENT `Statements/Ch7.lean` imports: clean. **No G2 edge.**
- `MarlBestResponse.lean` and `ConvexDistanceTV711.lean` checked without `-o`: both clean, no output.
  The project oleans are newer than the sources.
- grep for `sorry`, `admit`, `axiom` and `native_decide` in both modules and both drafts: none.
- The wrappers only apply library exports (`valueJ_deviate_le_starValue`, `brPolicy`/
  `valueJ_brPolicy_eq_starValue`, `starValue_terminal`, `starValue_bellman`,
  `isCCE_of_isNE_of_prob_eq`, `coord*`, `convexDistance_le_tv`, `pluginWeight_eq`,
  `sum_pluginWeight`). None of them restates or reproves a result.

## Per-entry verdicts

### U17 `Marl_bestResponse_exists` (marl.tex:119–143): ACCEPT

TeX re-read: deviation :119–121; `eq:defn-optimal-V` :122–126, which is a max over Markov
`π'_i : S×[H]→Δ(A_i)`; simultaneous attainment :128–130; "best among all policies … executed
independently" :131–132; Bellman display :135–143, with the expectation over `a_{-i} ∼ π_{-i,h}`,
max over `a_i`, terminal 0 and `(s,h,i) ∈ S×[H]×[m]`.

- **Per-step value (F-P3b-1).** `Vstar h s := ⨆ π', valueJ G (deviate π i π') i h (H+1-h) s` is defined
  inline for every h (steps h..H). ✓
- **BddAbove / no junk.** Conjunct (1) proves domination of every deviation. Conjunct (2) proves
  attainment. Together they make `Vstar` a genuine maximum. Neither is a hypothesis. ✓
- **Simultaneous attainment.** One μ works for all h ∈ [1,H] and all s. ✓
- **Bellman.** `∑ a', π_h(a'|s) · f(update a' i b)` is exactly `E_{a_{-i} ∼ π_{-i,h}}[f(a_{-i}, b)]`,
  because the marginal of `π_h` on −i is the law of `a'_{-i}` and `a'_i` is overwritten. The max is
  `⨆ b : Fin (A i)` over a nonempty finite type, so it is a genuine max. The terminal condition
  `Vstar (H+1) = 0` holds. ✓
- `deviate` uses the per-(h,s) marginal of a possibly correlated π, which matches π_{-i} at :84–85. ✓
- **Markov-only deviations.** This is the printed class. The section restricts to Markov policies at
  :71–73, and :122 maximises over `S×[H]→Δ(A_i)`. History-dependent deviations are not in the
  printed claim, so this is not a deviation. The draft COVERAGE disclosure is adequate.
- **Hypotheses.** `0 < A i` is implicit in `A_i = {1,…,A_i}` (:20). Rewards are arbitrary reals, while
  the source has [0,1]; the entry therefore assumes less. ✓

### U18 `Marl_NE_isCCE_not_converse` (marl.tex:240; NE :213–221, CCE :232–238): ACCEPT

- **(a)** The hypothesis is `∀ h s a, π_h(a|s) = ∏_j σ_{j,h}(a_j|s)` for every h ∈ ℕ. This is
  equivalent to `π = toJoint σ`, the natural embedding of the NE product policy as a joint policy
  (F-P3b-2 form). It is neither weaker nor stronger in substance. ✓
- **(b)** Witness: a two-player, one-state, one-step coordination game with rewards in [0,1], so it
  satisfies the :34–37 normalisation. π is uniform on {(0,0),(1,1)}, and `IsCCE` is proved: value 1,
  and every value is ≤ 1. The conclusion is that the step-1 law equals no product law. This implies
  `toJoint σ ≠ π` for every σ (critic probe). NE is defined only for product policies (:214), so π is
  not an NE. The probe also shows that no NE σ has `toJoint σ = π`.
- **Reading check.** Is "no product law at step 1" the right reading of "the converse does not
  generally hold"? Yes. The printed converse is "every CCE is an NE", so its failure needs one CCE that
  is not an NE. For product policies, CCE ⇔ NE (`isNE_iff_isCCE_toJoint`). A CCE that fails to be an
  NE must therefore be non-product, and the entry's conclusion is slightly stronger than "not product".
  Witnessing at step 1, the only step of a game with H = 1, is legitimate. ✓

### U19 `Eq_convex_distance_le_TV` (inference.tex:124–129; TV intro.tex:218–227): ACCEPT, entry warranted

- `P.real C` is `(P C).toReal`. For non-Borel convex C it is the outer measure. For Borel convex sets
  it coincides with the measure, so the outer-measure reading extends the measurable-convex reading.
  The common measurable hull lemma is correct: it intersects the two `toMeasurable` hulls.
- TV is written inline as the sSup over `MeasurableSet` A (Borel σ-algebra of `Fin d → ℝ`). This
  matches `eq:TV`'s `sup_{A∈𝓕}` with 𝓕 the Borel σ-algebra. "sup over convex ≤ sup over measurable"
  is literally `d_cvx ≤ TV` with both definitions unfolded. ✓
- Junk check: both sets are nonempty (∅ is convex and measurable) and bounded by 1. The `sSup`s are
  therefore genuine. ✓
- **Entry or note.** Use an entry. :129 asserts a mathematical inequality ("we have d_cvx ≤ TV"), and the
  convexity/measurability gap makes it non-trivial. The plan class is P.

### U20 `Eq_tdWeights_sum` (inference.tex:173–177): ACCEPT

- Conjunct 1 is the display at :175, with a 0-based index (t+1). Conjunct 2 is ∑w = 1, which the source
  does not print but which follows from it. The entry concludes more, which is allowed.
- **Duplicate?** The facts are already machine-checked and mentioned in the `eq:defn-hat-Lambda`
  COVERAGE row, but no statement entry exists. A tiny entry is fine and gives the display a named
  anchor. See R2 on row placement.

## Required fixes

- **R1 (U19 COVERAGE context note: unhedged and unchecked claim).** The draft says "P is the law of
  √TΔ̄_T, which is finitely supported … and Q is a nondegenerate Gaussian, so TV(P,Q) = 1". Nothing
  assumes or proves Λ⋆ nondegenerate, and the note is not machine-checked. Replace the sentence with:
  > Context remark (informal, not machine-checked; not a source issue): under the i.i.d. sampling of
  > `eq:iid-samples` with deterministic rewards, the law of √TΔ̄_T is finitely supported, while
  > N(0, Λ⋆) has no atoms whenever Λ⋆ ≠ 0. Then TV = 1 in that application, so the inequality is true
  > but uninformative there.
- **R2 (U20 row placement).** The existing `eq:defn-hat-Lambda` row (inference 156–185) already contains
  the weights 175–177 and has status "Printed reading refuted …". A second row for 173–177 overlaps it.
  Before integrating, the lead must check that the site generator (F-T-2 joint-entry rule) maps
  `Eq_tdWeights_sum` to its own node and does not relabel or double-count the `eq:defn-hat-Lambda`
  node. The simplest alternative is to drop the separate row and add to the existing row: "statement
  entry `Eq_tdWeights_sum` (display :175 and ∑w = 1)". Either choice is acceptable, provided the
  generated status of both nodes is checked.

## Recommended (non-blocking)

- **R3 (locators).**
  - `MarlBestResponse.lean` header and `valueJ_brPolicy_eq_starValue` docstring say ":128–131"; the
    prose runs to :132.
  - The header and `starValue_bellman` say ":134–141"; the display is :135–143 (as in the entry).
  - The draft COVERAGE U17 row says ":136–141"; use :135–143.
  - The CCE item begins at :232 (230–231 are blank). 230–238 is harmless, but 232–238 is exact.
- **R4.** In the U19 docstring and COVERAGE row, qualify `Thm7_11_printed_allConvex` as the library
  definition in `TDInferencePrinted711.lean`. It is not a `Statements` entry, and an unqualified
  reader search in `Ch7.lean` finds nothing.
- **R5.** In the U17 COVERAGE row, add: "rewards: the export holds for arbitrary real rewards (source
  [0,1]); A_i ≥ 1 is the source's nonempty action set."

## COVERAGE text approval

- U17 row: **approved with R3 (":135–143") and R5.**
- U18 row: **approved as drafted.**
- U19 row: **approved after R1** (and R4).
- U20 row: **approved after R2** (or fold it into the existing row).
- No SOURCE-ISSUES entry is needed. All four entries are printed claims, and none is `_corrected` or
  `_restricted`.
- Integration plan (Ch7.lean unchanged imports; Ch7Proofs.lean + Formalization.lean gain the two
  module imports): **approved.** After integrating, the lead must re-run `python3 scripts/check.py`
  (G2 list unchanged).

Probe: the critic probe described under Evidence (kept locally, not published).
