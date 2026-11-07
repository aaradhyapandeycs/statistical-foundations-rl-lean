# CRITIC — Theorem 7.10 (`thm:lower_bound`), WIP `Thm710Wip`

Public copy of the independent critic report; local paths removed.

Critic: independent of the builder. Date 2026-11-07.
Source: `source/upstream/tex/chapters/federated_RL.tex`, sha256
`c9df1d9f6187d79644d6c55ae9be97cb68e5578fa2b963b490a3d94ef45b0320` (matches `source/provenance.json:33`).
Ranges (verified by `grep -n`): Algorithm 7.3 description :166–198 (parameters :174–181; update
`eqn:generic_algo_update` :183–188; averaging `eqn:generic_algo_averaging` :189–194; "any distributed mean
estimation routine", WLOG `t_{C_round} = T`, `N = BT` all on :196); algorithm box :200–220 (init `Q_0^k ← 0` :207,
return `Q̂ = Q_T` :219); Theorem 7.10 :227–239 (label :238); discussion :242–244ff.

Files reviewed (sha256 match BUILD-LOG):

| file | sha256 |
|---|---|
| `Thm710Wip/Defs.lean` | `2c930f97…f376` |
| `Thm710Wip/Statement.lean` | `1f3efb51…769b` |
| `Thm710Wip/LowerBound.lean` | `17b4f1a1…e142` |
| `Thm710Wip/Proofs.lean` | `2a8ee390…acba` |
| `Thm710Wip/InnerConstant.lean` | `4f6cfc19…73eb` |

## Verdicts

- `Thm7_10` (index entry, reading A) with wrapper `Thm7_10_holds`: **ACCEPT WITH DISCLOSURES** (plain name
  `Thm7_10` justified; required edits are docstring/citation/ledger disclosures, no signature change).
- `Thm7_10_innerConstant` / `not_thm7_10_innerConstant` (reading B refutation): **ACCEPT**
  (minor citation edits only).

## 1. Independent reconstruction (done before reading the Lean)

Printed: assume γ ∈ [5/6,1), S ≥ 4, A ≥ 2; 𝒜 an instance of Algorithm 7.3; T ≥ max{16, 1/(1−γ)}; learning rates
either η_t = 1/(1 + c_η(1−γ)t) or η_t ≡ η, 1 ≤ t ≤ T. "If C_round ≤ c₀/((1−γ)log²N) for some universal constant
c₀ > 0, then for any choices of communication schedule, batch size B, c_η > 0 and η ∈ (0,1), there exists an
instance of MDP such that E‖Q̂ − Q⋆‖_∞ ≥ C_γ/(√N log³N) for all K ≥ 2 and N = BT", C_γ > 0 depending only on γ.

Quantifier order I read: ∃ universal c₀ > 0 (a fixed numeric constant, as in "for some universal constant") —
∃ C_γ (function of γ only) — ∀ γ, S, A, T, schedule-family parameters, 𝒞 (with t_{C_round} = T), B — [hypothesis
on C_round = |𝒞| with N = BT] — ∃ MDP (S states, A actions, discount γ) — ∀ K ≥ 2 — E[sup-norm error] ≥ bound.
The MDP precedes K ("there exists an instance ... such that ... obeys ... for all K ≥ 2"); the algorithm
parameters (𝒞, B, c_η/η) precede the MDP ("for any choices of ... there exists an instance"). The hypothesis
"If C_round ≤ ..." is written before "for any choices of communication schedule, batch size B", but it involves
N = BT and C_round = |𝒞|, so it can only be read as a hypothesis on the already-chosen (𝒞, B, T); Lean's
`∀ T B 𝒞 η, … → hyp → …` is the only coherent formalization and is logically insensitive to the ∀ order.
Reading B ("for some c₀ > 0" existentially inside the antecedent) is grammatically possible but makes the
antecedent vacuous; reading A is the natural mathematical reading of "for some universal constant c₀", and
the book's companion results use "universal constant" for outer-fixed constants. Prior check
(`the private independent check note (Ch7-rest)` §1 row 3) agrees and records that a ∀c₀ reading with C_γ independent of c₀ is refuted, so the
outer ∃c₀ (with C_γ allowed to be chosen after c₀) is the right target.

## 2. Five-bin binder table for `Thm7_10` (`Statement.lean:37–51`)

| binder / hypothesis | Lean | bin | source |
|---|---|---|---|
| ∃ c₀, 0 < c₀ | :38 | SOURCE | :232 "for some universal constant c₀ > 0" |
| ∃ Cγ : ℝ → ℝ, chosen before γ | :38 | SOURCE | :237 "C_γ > 0 depends only on γ" |
| ∀ γ, 5/6 ≤ γ, γ < 1 | :38 | SOURCE | :228 |
| 0 < Cγ γ | :38 | SOURCE (conclusion) | :237 |
| State, Action Fintype | :39 | TYPING | finite MDP |
| 4 ≤ card State, 2 ≤ card Action | :40 | SOURCE | :228 |
| T, B : ℕ | :41 | TYPING | |
| 𝒞 : Finset ℕ | :41 | TYPING | :178 𝒞 = {t_r} |
| η : ℕ → ℝ | :41 | TYPING | :176 |
| 16 ≤ T, 1/(1−γ) ≤ T | :42 | SOURCE | :229 T ≥ max{16, 1/(1−γ)} |
| 1 ≤ B | :42 | TYPING | batch size |
| 𝒞 ⊆ Icc 1 T | :43 | TYPING | schedule of iterations 1..T |
| T ∈ 𝒞 | :43 | STANDING | :196 WLOG t_{C_round} = T |
| rate disjunction (c_η > 0 linear, or η₀ ∈ (0,1) constant) | :44–45 | SOURCE | :229, :232–233 (see F4) |
| card 𝒞 ≤ c₀/((1−γ) log²(BT)) | :46 | SOURCE | :230–231, C_round = |𝒞| :190, N = BT :196 |
| ∃ M, M.discount = γ | :47 | SOURCE (conclusion) | :233 |
| ∀ K, 2 ≤ K | :48 | SOURCE (conclusion) | :236 |
| Cγ γ/(√(BT) log³(BT)) ≤ ∫ supError(genericOutput …, Q⋆) d fedSamplingLaw | :49–51 | SOURCE (conclusion) | :234–235 |

Counts: SOURCE 11, STANDING 1, TYPING 6, RULED 0, **EXCESS 0**.

## 3. Findings

**F1 (Medium, disclosure) — Algorithm fidelity: exact averaging only.** `Defs.lean:48–52` (`genericStep`)
models the synchronization as exact averaging, the printed formula (:189–194). Line :196 says the averaging
"may be replaced by any distributed mean estimation routine, including ... compression". Direction: a lower
bound over a larger class of algorithms is a *stronger* claim, so the Lean result is formally narrower than a
reading in which Theorem 7.10 quantifies over all routines. I do **not** require `_restricted`: the theorem
says "as described in Algorithm 7.3", the algorithm box (:214) computes Q_t^k "according to
eqn:generic_algo_averaging", and "any distributed mean estimation routine" is not a mathematically specified
class (an unrestricted routine could be an arbitrary map of the local iterates, making the claim meaningless).
But a reader must be told. Required: one sentence in the `Thm7_10` docstring and the COVERAGE row: "𝒜 uses the
printed exact averaging (eqn:generic_algo_averaging); the remark at :196 allowing any distributed mean
estimation routine (e.g. compressed averaging) is not covered."

**F2 (Medium, disclosure) — The proved statement is degenerate, and the proof shows it.** As C42 says, `T ∈ 𝒞`
forces log²N ≤ c₀/(1−γ), so for each γ only boundedly many N qualify; the proof (`LowerBound.lean:176–243`) uses
the r ≡ 1 instance with deterministic error γ^T/(1−γ) and C_γ = γ^{⌊exp√(c₀/(1−γ))⌋}/(1−γ) — the √N log³N rate and
the dependence on K, B, sampling noise play no role. This is a faithful proof of the *printed* statement under
reading A, so plain `Thm7_10` is correct, but the docstring (Statement.lean:31–33) and COVERAGE must say plainly
that this does not establish the discussion at :242–248 (Ω̃(1/(1−γ)) rounds needed for any collaborative gain).
The present docstring nearly does; also reword ":32–33 exponentially small in exp(√(c₀/(1−γ)))" to "C_γ =
γ^{⌊exp √(c₀/(1−γ))⌋}/(1−γ), doubly exponentially small in √(c₀/(1−γ))".
Also note with c₀ = 1 (the wrapper's choice) the hypothesis is unsatisfiable for γ < 1 − 1/log²16 ≈ 0.870; this
is legitimate for an ∃c₀ statement and the export holds for every c₀ (`lowerBound_of_fewRounds` takes arbitrary
c₀), so no vacuity is exploited — state "the library export holds for every c₀" in the docstring so a reader
does not suspect it.

**F3 (Low) — Wrong source line citations.** Verified with `grep -n`: update eq. is :186–188 (described
:183–185), not :180–182; averaging eq. :191–194, not :185–189; mean-estimation/WLOG/N = BT sentence is :196, not
:191; `Q_0^k ← 0` is :207, not :206; `return Q̂ = Q_T` is :219, not :217; i.i.d. sampling description is
:183–184, not :177–179. Affected: `Defs.lean:13,17,19,20,22,25,39,46,64,79`, `LowerBound.lean:14`,
`Statement.lean:22`. (`SOURCE-ISSUES.md#C42` correctly cites :196.) `Defs.lean:102` names
`InnerConstant710.lean`; the WIP file is `InnerConstant.lean` — make consistent at integration.

**F4 (Low, optional) — Rate hypotheses over all t ∈ ℕ.** `Statement.lean:44–45` require η t = formula for every
t : ℕ (incl. t = 0 and t > T); the source fixes η_t only for 1 ≤ t ≤ T. Since 𝒜 reads η only on 1..T and any
1..T schedule extends to all t by the same formula, the two are equivalent, but as stated the entry's
hypothesis is formally stronger. Critic probe (below) proves my 1..T-only reconstruction `CriticRecon` directly
from the export (agreeing η with a [0,1]-valued extension and showing `genericRun` depends only on η on 1..T).
Optional edit: restrict to `∀ t, 1 ≤ t → t ≤ T → …` and adapt the wrapper (my probe contains a working proof).
Not a source-fidelity finding.

**F5 (Low, OK) — Remaining checks, no defect.**
- K ≥ 2 printed (:236); ∃M before ∀K matches "there exists an instance ... for all K ≥ 2".
- Quantity is E[‖Q̂ − Q⋆‖_∞]: Bochner integral of `supError` (max over (s,a) of |·|) against `fedSamplingLaw`.
  Sample space is finite with ⊤ σ-algebra, integrand integrable (`Integrable.of_finite`), so no junk-zero; a junk
  0 could only make the lower bound harder anyway.
- `Q⋆ = optimalityFixedPoint` = unique fixed point of `qOptimality` (`FixedPointExistence.lean:46`).
- `batchUpdate` (Defs:41–44): (1−η)Q + (η/B)∑_b (r + γ max_{a'} Q(s'_b,a')) = eqn:generic_algo_update with the
  generative-model sample Bellman operator; deterministic known reward, as elsewhere in the book.
- `genericStep`: averaging of the half-step iterates over j at t ∈ 𝒞, otherwise local — matches :191–194.
- Q_0 = 0 (:207) — `genericRun 0`. Output `(1/K)∑_k Q_T^k`; with T ∈ 𝒞 all agents coincide, = Q_T (:219).
- Sampling: `Measure.pi` over (iteration index t−1, agent, (s,a), slot b), each from P(·|s,a): fully
  independent, as "i.i.d. ... B samples from the generative model for each (s,a)" (:183–185). Iteration t+1 reads
  coordinate t (`fedSamplesExtend`, Defs:86–90, guarded 0 < t ≤ T): correct.
- Rate families: both exactly as printed; c_η > 0, η ∈ (0,1) open.
- MDP class `DiscountedMDP` has rewards in [0,1] (book convention, `generative_model_model_based.tex:54`);
  restricting the existential class only strengthens Thm7_10.
- Junk: log(BT) ≥ log 16 > 1 > 0, √(BT) > 0, so the bound's denominator is positive; 1 − γ > 0; c₀/(…) has
  positive denominator. No division-by-zero junk.

**F6 (Ledger) — C42 status.** `docs/SOURCE-ISSUES.md#C42` still says "no Lean evidence yet". On landing, update
it to cite `Thm7_10_holds` (reading A, as printed, degenerate) and `not_thm7_10_innerConstant` (reading B false).

## 4. Reading-B refutation (`Defs.lean:104–118`, `InnerConstant.lean:473–553`)

- Prop: textual diff against `Thm7_10` is exactly the move of `∃ c₀, 0 < c₀ ∧ …` from the outermost position
  into the antecedent (`Defs.lean:113` vs `Statement.lean:38,46`); every other line is identical. Correct.
- Witness: γ = 5/6, `Fin 4 × Fin 2` (S = 4, A = 2, the minimum sizes), T ≥ 16 chosen from
  T⁴(11/12)^T → 0 so that 18(11/12)^T T⁴ < C_γ (T ≥ 6 = 1/(1−γ) also checked, `by norm_num; linarith`),
  B = 1, η ≡ 1/2 (constant family, satisfies the ∀ t hypothesis), 𝒞 = Icc 1 T (⊆, ∋ T), and the antecedent's c₀
  witnessed explicitly. All printed hypotheses discharged honestly.
- Covers every MDP: the instance M is *received* from the hypothesis (`obtain ⟨M, hM, hK⟩`) and
  `expected_error_le` is stated for arbitrary M (section variable), using only M.discount = 5/6 and rewards in
  [0,1] (V⋆ ∈ [0, 1/(1−γ)]); K is then chosen (it depends only on C_γ, T), giving ¬(∀K ≥ 2 …). Since the Prop's
  rate hypothesis is over all t (F4), the refutation is of a formally stronger-hypothesis Prop and therefore also
  refutes the 1..T variant. If the book's MDP class allowed larger bounded rewards the same argument scales
  (K chosen after M), so the refutation is robust.
- Bound chain: E‖Q̂−Q⋆‖ ≤ (11/12)^T·6 + ηγ T·8·(w·36/K + 1/w)/2, with w = 3X/bnd, K > 54Xw/bnd; each of the three
  parts < bnd/3, bnd/6, bnd/3 — checked by the kernel.

## 5. Lean evidence (critic)

Probe `<reviewer probe folder>/CriticProbe.lean` (sha256
`87a9adaf5b4e76365cdc0a72fc4a821cee605674f76dab7b5093c9347df1a8af`), command
`bash scripts/lean-local.sh <reviewer probe folder>/CriticProbe.lean` (foreground, no -o), exit 0
(first attempt had a probe-side elaboration error, fixed in the probe only). Contents: independent
reconstruction `CriticRecon` (max-form T bound, explicit `let N`, rates only on 1..T, schedule as explicit
membership) proved from `lowerBound_of_fewRounds`; `example : Thm7_10 := Thm7_10_holds`;
`example : ¬ Thm7_10_innerConstant := not_thm7_10_innerConstant`. Output:

```
'StatisticalRL.Statements.Ch7.Thm7_10_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'StatisticalRL.Ch7Rest.FedGeneric.not_thm7_10_innerConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Builder's `axiom-probe.out` agrees. No sorry/admit/axiom in the WIP files (builder scan; I saw none in the parts read).

## 6. Required edits

1. (F1) `Thm7_10` docstring + COVERAGE row: disclose exact averaging; the :196 "any distributed mean estimation
   routine" generalization is not covered. Keep the name `Thm7_10` (no `_restricted`).
2. (F2) Docstring: state that the export holds for every c₀, give the explicit C_γ, and say the result does not
   establish the :242–248 discussion; reword "exponentially small in exp(…)".
3. (F3) Fix all line citations listed in F3; fix the `InnerConstant710.lean` file-name reference.
4. (F6) Update `SOURCE-ISSUES.md#C42` with the Lean evidence on landing (still "Not author-approved").
5. (F4, optional) Restrict the rate hypotheses to 1 ≤ t ≤ T in both Props (wrapper proof available in the probe).
