# CRITIC: Theorem 3.7 (`theorem:azar`), proposed `Thm3_7_corrected`

Public copy of the independent critic report; local paths removed.

- Date (UTC): 2026-11-06 23:0x
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `50555485a4c7b5aac4710965a63bbd5e86d6c73b` (branch `recovery-batch-fano-ch2-ch6-20261106`; reviewed modules are untracked working-tree files)
- Mode: source-only reading plus file inspection and Python numerics. No Lean, lake, compiler or LSP was run.
  `the private preflight note (Thm3_7)`, other `<builder working folder>/` files, PROGRESS files and other CRITIC files were not read.
  The reconstruction in sections 1 and 3 was done from the TeX before reading the Lean.

## SHA256

| File | sha256 |
|---|---|
| `source/upstream/tex/chapters/generative_model_model_based.tex` | `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d` (matches `source/provenance.json`) |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` (matches provenance) |
| `<builder working folder>/probe/Thm37Probe.lean` | `3beb29586da53239d2d80f4e896115d1819b57558bb51e3a8005152cc33f186a` |
| `Formalization/Generative/GenerativeLowerBoundTheorem37Fin.lean` | `e566e3e8eb27369f6e1a5b06cf2202905f8ed43d5fa4630d989715641b907716` |
| `Formalization/MDP/StateRelabel.lean` | `bcd85ca49a5af3a5de33b9efeba41b44a2e492b961939a2a16eb1038e5a93de3` |
| `Formalization/Generative/StateRelabelSampling.lean` | `d98fd812ea85ac65d1d09bea3cf715109e90e3c22efc23b9a32536fdb14d696c` |
| `Formalization/Generative/GenerativeLowerBoundQMixtureAnyAction.lean` | `f849dd787c1b2dfeac28532265233e8c3424f9c6728ac7a796df97c1d6ae4d72` |
| `Formalization/Generative/GenerativeLowerBoundCombinedRisk.lean` | `b09e11443edf778797d44bb592655a5d619b06af106650cd0c0a61a365bcdc7c` |
| `Formalization/Statements/Ch3Definitions.lean` | `8494b89e4a2c90c0ee41fd6fcc84796cfdb588b88320b352656e5dba5147b68c` |
| `docs/SOURCE-ISSUES.md` | `fe83f77b754a018199f81b5414d9434bbc142c604813c3c1fab9836fd560456c` |

## 1. Source reconstruction and the printed theorem's failures

Printed statement (`generative_model_model_based.tex:1443–1464`): for `0<ε<1/(32(1−γ))`,
`γ∈[2/3,1)`, `SA≥16`, `N` samples per state-action pair with
`N ≤ c_N log(SA)/((1−γ)^3 ε^2)` for some small universal `c_N>0`:
(i) for every (deterministic) policy estimator there is an `S`-state, `A`-action
γ-discounted MDP with `P(‖Q^{π̂}−Q^⋆‖∞>ε) ≥ 1/4`; (ii) the same for every Q estimator with
`‖Q̂−Q^⋆‖∞`. Rewards are deterministic and known (`prelim.tex:42`,
`generative_model_model_based.tex:31`).

- **C1 (A = 1, part (i)) confirmed.** With `S=16, A=1` there is one stationary policy, so
  `Q^{π̂}=Q^⋆` on every model and dataset; the event is empty. All printed hypotheses are
  satisfiable (pick ε small so the budget admits any fixed N ≥ 0). Part (i) is false.
- **C2 (S = 1, both parts) confirmed, under the known-reward convention.** With one state every
  transition returns to it, so `Q^⋆(a)=r(a)+γ max_b r(b)/(1−γ)` is a function of the known
  reward and γ: the estimator `Q̂ = that formula` has zero error and the reward-greedy policy is
  optimal. Both parts fail at `S=1, A=16`. (If rewards were unknown and unobserved, S=1 would
  not be a counterexample; the source convention makes them known, so C2 stands.)
- **Weakest corrections.** `S≥2` is necessary for both parts (C2), `A≥2` is necessary for part
  (i) (C1). `A≥2` is *not* necessary for part (ii): with `A=1, S≥16` the one-action
  baseline/alternative family on `S−1` active states plus an absorber gives ≥ `S` hypotheses
  each separated from the baseline by more than `2ε` in one coordinate, and the Lean
  `qMixtureSource_deterministic_Q_risk_of_pos` proves it. Since the proposed domain
  (`S≥2` both, `A≥2` only in (i), `SA≥16` retained from the print) is both necessary
  (counterexamples) and sufficient (proved), it is the weakest dimension domain.
  The constant: the printed theorem says "for some small universal constant `c_N>0`"; the
  proposed Prop keeps `∃ c_N > 0` *before* all `∀ S A N γ ε` (the strong, uniform reading),
  and `1/32768` appears only as the witness. No "weakest constant" question arises.

## 2. Field-by-field fidelity of `Thm3_7_corrected`

| Field | Printed | Prop | Verdict |
|---|---|---|---|
| constant | ∃ small universal `c_N>0` | `∃ c_N : ℝ, 0 < c_N ∧ ∀ …` | match (uniform) |
| γ range | `[2/3,1)` | `2/3 ≤ γ`, `γ < 1` | match |
| ε range | `0<ε<1/(32(1−γ))` | `0 < ε`, `ε < 1/(32(1−γ))` | match |
| size | `SA ≥ 16` | `16 ≤ S*A` plus `2 ≤ S`; `2 ≤ A` only in (i) | disclosed correction (C1, C2) |
| N bound | `N ≤ c_N log(SA)/((1−γ)^3ε^2)` | identical, `N : ℕ` (N = 0 allowed) | match (N=0 is extra strength) |
| data | N iid next-states per (s,a) | `Samples = ((Fin S×Fin A)×Fin N) → Fin S`, `samplingLaw = Measure.pi` of true rows | match |
| known inputs | reward known; γ given | estimator receives `M.reward`, `M.discount`, data; may depend on S,A,N,γ,ε through quantifier order | match the source convention |
| estimator class (i) | "(deterministic) policy estimator" | arbitrary (not even measurability required) function to deterministic stationary policies `Fin S → Fin A` | match the natural reading |
| estimator class (ii) | "any Q-function estimator" | arbitrary function data → `Fin S → Fin A → ℝ` | match the standard reading (see MINOR-2) |
| model | ∃ γ-discounted MDP with S states, A actions | `∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ` (rewards in [0,1]) | match; model chosen after estimator, as printed |
| risk (i) | `‖Q^{π̂}−Q^⋆‖∞ > ε` | `ε < ‖trajectoryExpectedQ (pointMass ∘ π̂) − trajectoryExpectedQ optimalGreedyPolicy‖` (sup norm on `Fin S → Fin A → ℝ`) | match; Q is the actual forced-first-action trajectory expectation and `optimalGreedyPolicy` is proved optimal |
| risk (ii) | `‖Q̂−Q^⋆‖∞ > ε` | `ε < ‖Q̂ − trajectoryExpectedQ optimalGreedyPolicy‖` | match |
| probability | `≥ 1/4` | `1/4 ≤ (samplingLaw M N).real {…}` | match (finite sample space, every set measurable) |
| separate witnesses | separate ∃M in (i) and (ii) | separate ∃M | match |

The Prop is written out in full and does not refer to any theorem's type.

## 3. Sharpening: printed separation (eq. at line 2075–2079) is false; midpoint estimator

Independent re-derivation for the printed family (`p=(4γ−1)/(3γ)`, `α=32(1−γ)^2ε/(9γ^2)`,
`x := 1−γp = 4(1−γ)/3`, so `γα = 2x^2ε/γ`). At an active state `s`, the optimal action stays
with probability `p+α`, so `Q^⋆(s,π^⋆(s)) = H := 1/(1−γ(p+α))`. A suboptimal first action
stays with probability `p` and then follows π^⋆, so
`Q^⋆(s,a) = 1+γpH = L := (1−γα)/(1−γ(p+α))`, **not** the printed `1/(1−γp)`
(eq. `Qstar-hard-instance-generative-policy-learning`, lines 1985–1993). Hence

`H − L = γα/(1−γ(p+α)) = 2xε/(γ − 2xε)`, and `H−L > 2ε ⇔ x(1+2ε) > γ`.

On the admissible domain `x ≤ 4/9` and `2xε < 8(1−γ)/(3·32(1−γ)) = 1/12`, so
`x(1+2ε) < 4/9+1/12 < 2/3 ≤ γ`. Thus `(H−L)/(2ε) = x/(γ−2xε) < 16/21 ≈ 0.762` at **every**
admissible `(γ,ε)`; the supremum 16/21 is approached at `γ=2/3, ε↑3/32`. Python check
(200k random admissible points plus the exact endpoint in rationals) gives max ratio
0.76187 and sup 0.761905; value iteration at γ=0.9, ε=0.5 reproduces H, L exactly.
So the printed claim `Q^⋆(s,π^⋆(s)) − Q^⋆(s,a) > 2ε` is false everywhere on the domain
(the two-state Lemma (ii) quantity `γα/((1−γp)(1−γ(p+α))) > 2ε` is a different difference).

**Midpoint estimator.** `Q̂(s_i,a) = (H+L)/2` for `i<S`, `Q̂(s_S,a_0)=0` (a function of γ, ε only;
H, L do not depend on the index (j,k)). Its error is `(H−L)/2 < (8/21)ε < ε` deterministically under
every member of `C_mdp` and every N, so `P(‖Q̂−Q^⋆‖∞>ε)=0`. Step 5 of the printed proof therefore
cannot be repaired by constants: the printed family does not witness part (ii). Confirmed.

For contrast, part (i) on the printed family survives with the corrected values: a wrong action at
`s` gives `|Q^{π̂}(s,π̂(s)) − Q^⋆(s,π̂(s))| = 1/(1−γp) − L = 2xpε/(x−γα) > 2pε > ε`, so Step 4's
logic holds once the Q-values are corrected (the policy loss uses a different coordinate than the
false gap). The Lean Q part correctly uses a different family (baseline with all rows `p`, single
perturbed row), where the relevant separation is the two-state Lemma (ii) quantity, which is true.

## 4. Proof honesty

- **Wrapper.** `Thm3_7_corrected_holds := ⟨1/32768, by norm_num, theorem37_corrected_fin_carriers⟩`.
  The export's body is textually the Prop with `c_N := 1/32768`. It applies the export only.
- **Export.** `theorem37_corrected_fin_carriers` converts the N bound to budget form
  (`theorem37_budget_of_sampleBound`, elementary) and calls `theorem37_policy_fin` /
  `theorem37_Q_fin`. These relabel `Option (Fin m) ≃ Fin (m+1)` via `(finSuccEquiv m).symm`,
  build the original-carrier estimator `est d s = piHat r₀ γ (relabelSamples e N d) (e s)` with
  `r₀` the reward of the relabeled baseline model, and apply the reviewed
  `sourceFamily_*` chain (Fano + decoder) and the new `qMixtureSource_deterministic_Q_risk_of_pos`.
  Feeding `r₀` instead of `M.reward` is sound because all family members share one reward table
  (`qMixtureMDP.reward` and the source family reward do not depend on the index); the closing `rfl`
  enforces this definitionally.
- **Relabeling lemmas.** `FiniteDistribution.relabel`, `relabelStates`, Bellman commutation,
  fixed-point transport via the uniqueness characterizations, trajectory-Q transport via
  `trajectoryExpectedQ_eq_policyFixedPoint`, `norm_comp_equiv_symm`, and
  `samplingLaw_relabelStates` (via `measurePreserving_arrowCongr'` with the correct index and value
  equivalences; sample at `(t,a,i)` is `e` of the original sample at `(e⁻¹ t,a,i)`) are all
  mathematically correct statements with no extra hypotheses.
- **AnyAction module.** A duplicate of the reviewed `qMixtureSource_deterministic_Q_risk` with
  `2 ≤ A` replaced by `1 ≤ A` and the cardinality inequality
  `log((m+1)A) ≤ 2 log(mA+1)` (true for `m,A≥1`); budget chain `N d ≤ 256 t ≤ log((m+1)A)/2 ≤ log(mA+1)` checks.
  The reviewed declaration is left unchanged.
- **Forbidden tokens.** Import closure of `GenerativeLowerBoundTheorem37Fin` (101 project modules)
  plus the probe grepped for `sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide|@[extern|ofReduceBool`,
  plus `elab/macro/syntax/run_cmd/#eval/import Lean`: **0 hits**.
- **Compilation.** Not run by this reviewer. `.lake/build` contains `.olean`s for the four new
  modules with timestamps equal to or after their sources (17:32–17:34), which is consistent with
  compilation but is not evidence of the probe's `#print axioms` output.

## Findings

**BLOCKING:** none.

**MAJOR:** none.

**MINOR**
1. The probe has no docstring. The `Ch3.lean` entry must cite `theorem:azar`,
   `chapters/generative_model_model_based.tex:1443–1464`, state the three differences from the
   print (`S≥2`; `A≥2` only in (i); known reward and discount passed explicitly to deterministic
   estimators), and point to the SOURCE-ISSUES entry.
2. The probe imports `Formalization.Generative.GenerativeLowerBoundTheorem37Fin`. Do not copy that
   into `Ch3.lean`: the Prop needs only `Ch3Definitions` (Samples, samplingLaw,
   trajectoryExpectedQ, optimalGreedyPolicy, pointMass), and the proof belongs in `Ch3Proofs.lean`.
   Also import both from `Formalization.lean` and re-run `scripts/check.py` and the axiom audit.
3. The estimator class is deterministic maps. That matches the standard reading of the print, and
   randomized estimators are a generalization, so this is not a fidelity defect. Disclose it,
   though: randomized estimator versions exist in the library only for `S,A≥2`
   (`sourcePolicyAndQ_risk_quarter_with_common_constant`), and not for the `A=1` Q case.
4. The existing "Candidate repair of Theorem 3.7" paragraph in `docs/SOURCE-ISSUES.md` still says the
   correction adds `S≥2` and `A≥2` to the combined statement. Update it to the per-part domain.

**NOTE**
- The hard models differ from the printed construction: the Q part uses a baseline/one-row family
  with all A actions at the absorber, and the action set is uniform `Fin A` rather than the print's
  singleton absorber. This is fine because the theorem is existential in M.
- The printed proof also misstates the non-optimal Q value and the Fano hypothesis count
  (`1/(M+1) Σ` over `M` models), and its Step 5 is unrepairable on its family (section 3). These are
  proof issues; the corrected *statement* is still proved by a different family.
- `N = 0` is admitted, which is stronger than the print requires.

## Suggested SOURCE-ISSUES wording

**Corrected entry (`Thm3_7_corrected`).** "Theorem 3.7 is false as printed (C1: part (i) at `A=1`;
C2: both parts at `S=1` under the source's known-reward convention). `Thm3_7_corrected` proves the
printed conclusion, with probability `≥1/4`, the printed γ and ε ranges, the printed sample bound and a
uniform constant (witness `c_N=1/32768`), on the domain `S≥2`, `SA≥16`, with `A≥2` required only in
part (i). Each estimator is a deterministic map from the known reward table, the known discount and the
full `N`-per-pair sample array. Both added conditions are necessary, by C1 and C2. Part (ii) is proved
for `A=1` as well, so no action restriction is imposed there. This is a corrected variant, not the
printed theorem, and it is not an author-approved erratum."

**Sharpening.** "The separation claim in the proof of Theorem 3.7 (`generative_model_model_based.tex:2073–2079`),
`Q^⋆(s,π^⋆(s)) − Q^⋆(s,a) > 2ε`, is false at every admissible `(γ,ε)`. With the printed `p, α` and
`x=4(1−γ)/3`, the true gap is `γα/(1−γ(p+α)) = 2xε/(γ−2xε) < (16/21)·2ε`. The displayed suboptimal
value `1/(1−γp)` should be `(1−γα)/(1−γ(p+α))`. Consequently the data-free estimator equal to the midpoint
`(H+L)/2` on active states and `0` at the absorber has error `< (8/21)ε` on every member of the printed
family, so that family cannot witness part (ii). Part (i)'s reduction survives with corrected values. The
formal proof of part (ii) uses a baseline-versus-one-row family instead."

VERDICT: PASS-WITH-FINDINGS
