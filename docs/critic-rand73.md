# Critic report: randomized-estimator lower bounds for Theorems 7.3 and 7.5 (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/RobustRL/LowerBounds/RandomizedLowerBound.lean` (exports `thm7_3_corrected_randomized`, `thm7_3_corrected_knownReward_randomized`, `thm7_5_corrected_randomized`, `thm7_5_corrected_knownReward_randomized`) with drafted statement entries. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT-WITH-FIXES; all fixes applied. The four entries `Thm7_3_corrected_randomized`, `Thm7_3_corrected_knownReward_randomized`, `Thm7_5_corrected_randomized` and `Thm7_5_corrected_knownReward_randomized` landed in `Formalization/Statements/Ch7.lean` alongside the deterministic ones (kept as the `Ω = Unit` special cases, with docstrings pointing to the randomized entries), with `_holds` wrappers in `Ch7Proofs.lean` and the library import in `Formalization.lean`. Docstrings state the seed model, the outer-probability convention for non-measurable failure sets and the printed constant 1/8; the entries keep the `_corrected` name (A ≥ 2, and S ≥ 2 with shared reward for the known-reward reading, still deviate from the print). The SOURCE-ISSUES C7 and C38 "Estimator class" paragraphs, the COVERAGE rows for Theorems 7.3 and 7.5 and the named-result records were updated: randomized estimators are now covered.

Targets: Formalization/RobustRL/LowerBounds/RandomizedLowerBound.lean. Source: chapters/robust_RL.tex:377-391, 461-480; SOURCE-ISSUES C7, C38.


## Source (read independently)
- thm:l1-lower-bound, source/upstream/tex/chapters/robust_RL.tex:377-391: "inf over all estimators
  pi-hat" of max{P0(gap>eps), P1(gap>eps)} >= 1/8; c0 in (0,1/8], sigma in (0,1-c0], gamma in [1/2,1),
  eps in (0, c0/(256(1-gamma))], N <= c0 log2 / (8192 (1-gamma)^2 max{1-gamma,sigma} eps^2).
- thm:chi2-lower-bound, robust_RL.tex:461-480: same inf/max >= 1/8; gamma in [3/4,1), sigma in (0,inf),
  eps <= c3/(1-gamma), N <= c4/((1-gamma)^3 eps^2) (1+sigma/(1-gamma)), universal c3,c4>0.
- No estimator class is restricted in print ("all estimators"); randomized estimators are in scope.

## Findings
1. Constant: printed constant is 1/8 for both theorems. The randomized exports conclude 1/8 -- identical
   to the print and to the existing deterministic entries (which also state 1/8, not 1/4). The 1/4 is only
   the internal summed bound P0(E0)+P1(E1) >= 1/4, which yields max >= 1/8 with no loss. c0 ranges, budget
   and (for 7.5) the witnessed c3 = 1/512, c4 = 1/5308416 are the same as the deterministic exports, with
   the same exists-c3-c4-before-everything quantifier order. No constant weakening.
2. Estimator class: the new exports strictly extend the deterministic ones (Omega = Unit, nu = dirac gives
   the deterministic statement; Markov-kernel estimators on the finite data space are of seeded form).
   They therefore close the "randomized estimators are not covered" disclosure in SOURCE-ISSUES C7
   (docs/SOURCE-ISSUES.md ~line 258) and C38 (~line 1288). Remaining deviations are exactly the existing
   ones: A >= 2 (C7/C38), plus S >= 2 and shared reward for the known-reward reading.
3. Proof route checked: pair_sum_of_policy_gap (test 1/2 < pi(a0|s0); error events inside failure
   events because pi(a0|s0)+pi(a1|s0) <= 1 for a0 != a1) and max_prod_ge_of_sum via
   exists_prod_measureReal_ge_of_sum_sections' (I = Bool, c/2 * 2 = c) are correct. The primed lemma
   replaces each F_i by toMeasurable (nu x P_i) F_i, uses monotonicity of sections, then
   measure_toMeasurable: sound for non-measurable sets.
4. Measurability convention: (nu.prod P).real F for non-measurable F is the outer probability; for
   seed-measurable estimators it is the probability. Same convention as Thm6_13_randomized
   (Statements/Ch6.lean:300-318). Meaningful; must be stated in the entry docstrings (the library
   docstring already says it). An inner-probability version would be false in general.
5. Universes: Omega : Type u, State/Action : Type; entries must be universe-polymorphic defs used as
   X.{u} as in Thm6_13_randomized. Checked: compiles at arbitrary u.
6. No sorry/admit/axiom. Quantifier order: exists M0 M1 mu before forall Omega nu est (models do not depend
   on the seed law or estimator), matching "there exist M0, M1 ... inf over pi-hat".
7. FIX REQUIRED (index/docs): (a) add four entries ALONGSIDE the deterministic ones (do not replace;
   deterministic ones remain valid special cases, keep them): Thm7_3_corrected_randomized,
   Thm7_3_corrected_knownReward_randomized, Thm7_5_corrected_randomized,
   Thm7_5_corrected_knownReward_randomized. Suffix: keep `_corrected` (A >= 2 etc. still deviate from
   print) and append `_randomized` (an estimator-class extension, not a weakening; mirrors
   Thm6_13_randomized). Do NOT drop `_corrected`, and do not describe them "as printed".
   (b) Docstrings: cite robust_RL.tex:377-391 / 461-480, point to C38 / C7, state the seed model
   (Omega any universe, any sigma-algebra, nu probability, seed law independent of model i, joint law
   nu (x) P_i), the outer-probability convention, constant 1/8 as printed, and that the deterministic
   entry is the Omega = Unit case. (c) Update C7/C38 "Estimator class" paragraphs and the deterministic
   entries' docstrings to point to the _randomized entries. (d) Add the Proofs wrappers and import
   RandomizedLowerBound in Ch7Proofs.lean / Formalization.lean.

## Compilation evidence
- `bash scripts/lean-local.sh Formalization/RobustRL/LowerBounds/RandomizedLowerBound.lean`: no output (clean), 8.4s.
- Scratch `<local probe>`: the four drafted Props (bodies copied
  verbatim from the export types) with `X_holds : X.{u} := <export>.{u}`; all four print
  axioms [propext, Classical.choice, Quot.sound].

## Five-bin (all four entries; KR rows only for knownReward)
| binder | bin | citation |
|---|---|---|
| c0, 0<c0, c0<=1/8 (7.3) | SOURCE | :379 |
| exists c3 c4 >0 first (7.5) | SOURCE | :463,:476 |
| State Action : Type, Fintype, Nonempty, MeasurableSpace State := top | TYPING | finite S, A |
| gamma sigma eps N, all ranges, N budget | SOURCE | :379-386 / :463-476 |
| 2 <= card Action | DISCLOSED | C38 / C7 |
| 2 <= card State (KR) | DISCLOSED | C38 / C7 |
| M0.reward = M1.reward (KR) | STANDING (known reward, generative_model_model_based.tex:31, robust_RL.tex:25) + DISCLOSED by name |
| exists M0 M1 mu, discount = gamma | SOURCE | :380 |
| Omega : Type u, [MeasurableSpace Omega] | TYPING (seed carrier) | |
| nu, IsProbabilityMeasure | SOURCE ("all estimators" includes randomized) | :389 |
| est : Omega -> Samples -> StationaryPolicy | SOURCE | :389 |
| conclusion 1/8 <= max of (nu x P_i).real | SOURCE (outer-prob convention to disclose) | :383 |
EXCESS: 0. Per-entry verdict once docstrings + SOURCE-ISSUES are written as in 7: PASS-DISCLOSED.
