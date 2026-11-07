# CRITIC — Theorem 4.13 (`thm:finite-horizon-simple-Q-generative`)

Public copy of the independent critic report; local paths removed.

- Written: 2026-11-07, independent critic (did not build the formalization).
- Git HEAD: `9d04276f65872ed3a4b6ad3e3773fe6fc35f78f4` (branch `recovery-batch-vilcb-thm63-20261107`).
- Source: `source/upstream/tex/chapters/generative_model_model_free.tex`, sha256
  `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`. This matches `source/provenance.json`.
  Ranges: algorithm :2172–2200, schedule `eq:thm:finite-horizaon-eta` :2203–2209, theorem :2215–2236.
  Rewards in [0,1]: `prelim.tex:682`.
- Under review: `<builder working folder>/FiniteQWip/*.lean` and `<builder working folder>/StatementProbe.lean`. Every
  source sha256 matches the BUILD-LOG status table (Definitions `945400ef…`, Main `b3c9551c…`, StatementProbe
  `953b1074…`, and so on). The oleans are newer than the sources.
- Commands run (foreground, one at a time, all from the repo root, no `-o`, so nothing was written outside
  `<reviewer probe folder>/`):
  1. `bash scripts/lean-local.sh <builder working folder>/FiniteQWip/Main.lean`: exit 0, no output, 11.8 s.
     The export re-elaborates from source.
  2. `bash scripts/lean-local.sh <reviewer probe folder>/CriticProbe.lean`: exit 0, no errors.
     Probe sha256: `912676d687bdf7b527a48fc78826ee0a2e350137b1f3f790348efe3ff4231b31`.
  3. One `python3 -I -c` numeric check of whether the budget can be satisfied (no files written).
- Not run: `lake`, lean-lsp, `scripts/check.py`, and the full `Audit.lean`. The WIP is not in the library import closure yet.

## Verdict: ACCEPT WITH DISCLOSURES

The export `StatisticalRL.FiniteQLearning.finiteQLearning_sample_complexity` and my independent re-derivation of the
proposed wrapper depend only on `[propext, Classical.choice, Quot.sound]`. The proposed Prop states the printed theorem
faithfully, with one exception: the added premise `2 ≤ T`. That premise is necessary. I machine-checked that the same
Prop with `1 ≤ T` is **false**. The algorithm semantics match the source. I found no junk value that makes the
conclusion vacuous or the hypotheses unsatisfiable for H ≥ 1 and T ≥ 2.

The required edits concern naming and the documentation (F1, F2). None of them concerns the mathematics.

## Reconstruction from the source (done before reading the Lean)

- Algorithm. For t = 1..T, sweep h = H..1:
  Q_{t,h} = (1−η_t)Q_{t−1,h} + η_t(r_h + max_{a'} Q_{t,h+1}(s_{t,h}(s,a), a')).
  - Each (s,a,h) gets one independent draw per iteration, with s_{t,h}(s,a) ~ P_h(·|s,a).
  - The target uses the **current** iterate at h+1.
  - Q_{t,H+1} ≡ 0 is implicit.
  - The source asks for 0 < η_t < 1.
- Schedule, for 0 ≤ t ≤ T:
  1/(1 + c₁T/(H log²T)) ≤ η_t ≤ 1/(1 + c₂t/(H log²T)), with "sufficiently small universal constants c₁ ≥ c₂ > 0".
- Theorem hypotheses: δ ∈ (0,1), ε ∈ (0,1], T ≥ c₃H⁴ log³T log(SAT/δ)/ε² for a sufficiently large universal c₃, and
  0 ≤ Q_{0,h} ≤ H+1−h (h is 1-based).
- Conclusion: ∀(s,a,h), |Q_{T,h} − Q⋆_h| ≤ ε with probability **greater than** 1−δ. The source says nothing about T ≥ 2.
- Quantifiers. c₃ must be allowed to depend on c₂. Suppose c₃ were fixed while c₁ = c₂ → 0. Then for the T admitted
  by the budget, the lower bound forces η_t → 1, so Q_T becomes a single-sample target, which is not ε-accurate. So
  "∃c₀ ∀ 0<c₂≤c₁≤c₀ ∃c₃" is the strongest sensible reading. It implies the weakest reading "∃c₁,c₂,c₃".

## Findings

### F1 (Medium, naming/policy): the entry adds a premise but carries the plain name `Thm4_13`
`StatementProbe.lean:24,28`. The Prop assumes `2 ≤ T`. The printed theorem does not. AGENTS.md says: when the export
assumes more than the printed result, use a `_corrected`/`_restricted` entry pointing to `SOURCE-ISSUES.md`, and
"never … call a corrected statement the original theorem". C35 already records this as a source issue. A plain
`Thm4_13` name next to a recorded C35 is inconsistent.

**Required:** rename to `Thm4_13_corrected` (with wrapper `Thm4_13_corrected_holds`). The docstring should say that it
differs from the printed result only by `2 ≤ T`, and point to `docs/SOURCE-ISSUES.md#C35`.

The alternative reading is that `2 ≤ T` is the printed schedule's domain of definition, so no plain name is
over-claimed. If the lead adopts it, the lead must say so explicitly and keep C35 consistent. I recommend the suffix.

### F2 (Medium, documentation): the C35 text is stale
`docs/SOURCE-ISSUES.md:998–1001` cites `c₃ = 2000/c₂` and a CHECK Part B proof built on KL/Pinsker. The formal proof
differs in three ways:
- it uses `c₃ = 8000/c₂`;
- stability is deterministic, via a total-variance potential;
- the good event has probability ≥ 1−δ/2.

See the replacement text below.

### F3 (Confirmed, High importance for fidelity): `2 ≤ T` is necessary, and this is machine-checked
`CriticProbe.lean`, theorem `not_thm4_13_from_one : ¬ Thm4_13_from 1`. `Thm4_13_from T₀` is a verbatim copy of the
proposed Prop with `T₀ ≤ T` in place of `2 ≤ T`.

- At T = 1, Lean's `Real.log 1 = 0` and `x/0 = 0` make the schedule read `1 ≤ η t ≤ 1` (lemma
  `T1_schedule_forces_one`), and the budget is `0 ≤ 1` (lemma `T1_budget`).
- Instance:
  - H = 2, State = Bool, Action = Unit, r₁ ≡ 0, r₂(s) = [s], and P₁ = P₂ uniform;
  - η ≡ 1, Q₀ ≡ 0, δ = 1/2, ε = 1/4.
- Then Q⋆₁ ≡ 1/2 (`optQ_stage0`).
- For every data point, Q_{1,1}(s) = r₂(s_{1,1}(s)) ∈ {0,1} (`iterate_stage0`, proved from `sampledIterateAt_succ` and
  `_terminal`). So the accuracy event is ∅ (`T1_event_empty`), and the conclusion would read 1/2 < 0.
- Axioms of `not_thm4_13_from_one`: `[propext, Classical.choice, Quot.sound]`.

This confirms CHECK Part A(ii) and C35(1). Under the paper's semantics the statement is undefined at T = 1, not false.
In Lean it is false, so the premise is essential. T = 0 is also excluded, correctly: at T = 0, log 0 = 0 and Q₀ need
not be accurate. `2 ≤ T` is the **only** added premise. The Prop assumes neither `0 < η < 1` nor `A ≥ 2`. Rewards in
[0,1] and finite nonempty S and A are built into `EnvironmentStage` and match `prelim.tex:682`.

### F4 (OK): the statement matches the printed theorem, item by item
| Item | Source | Lean (`StatementProbe.lean`) | Status |
|---|---|---|---|
| constants | small c₁ ≥ c₂ > 0, large c₃ | `∃c₀>0, ∀c₁ c₂, 0<c₂ → c₂≤c₁ → c₁≤c₀ → ∃c₃>0, ∀ MDP …` (:25–26) | at least as strong as printed; c₃ is universal (chosen before State/Action/H/E/δ/ε/T); the dependence on c₂ is unavoidable (see above) |
| schedule range | 0 ≤ t ≤ T | `∀ t, t ≤ T` (:29) | exact; the export uses only 1 ≤ k ≤ T, which is weaker, so the wrapper restricts |
| schedule form | 1/(1+c₁T/(H log²T)) ≤ η_t ≤ 1/(1+c₂t/(H log²T)) | :30–31 | exact |
| log | log (natural) | `Real.log` | OK; under the ∀-small-c reading a change of base is absorbed into c₀ and c₃ |
| budget | T ≥ c₃H⁴log³T·log(SAT/δ)/ε² | :32–33, with `card State * card Action * T / δ` | exact |
| δ, ε | δ∈(0,1), ε∈(0,1] | :28 | exact |
| init | 0 ≤ Q_{0,h} ≤ H+1−h, h ∈ [H] 1-based | `0 ≤ Q₀ h s a ≤ (H:ℝ) − h`, h : Fin H 0-based (:35) | exact after the shift (cast is `((h:ℕ):ℝ)`, checked in the probe) |
| conclusion | ∀(s,a,h) \|Q_{T,h}−Q⋆_h\| ≤ ε | `∀ h s a, \|sampledIterate … h s a − optimalQ ((ofFn E).drop h) s a\| ≤ ε` | exact; `optimalQ (drop h)` is r_{h+1} + P_{h+1}V⋆_{h+2} with V⋆_{H+1} = 0 (`EnvironmentDefinitions.lean:26–35`) |
| probability | greater than 1−δ | `1 - δ < (samplingLaw E T).real {…}` (:36) | exact (strict) |
| η | deterministic | `η : ℕ → ℝ` fixed before the data | OK |

### F5 (OK): the algorithm semantics are correct (`FiniteQWip/Definitions.lean`)
- `headIterate` (:35–43) gives Q_{t+1,h} = (1−η_{t+1})Q_{t,h} + η_{t+1}(r_h + max_{a'} next(t+1)(sample t s a, a')).
  The target uses the **current** iteration's next stage, as in `eqn:q-learning-finite`.
- `iterate [] = 0` (:46–49) is the terminal convention Q_{t,H+1} ≡ 0.
- `sampledStages` (:55–61) gives stage h, iteration t+1, coordinate `data ((h,s,a), t)` for t < T. The junk branch
  `else s` is never reached for t < T: `sampledIterateAt_succ` (:111–122) needs `t < T`, and `sampledIterate` runs
  exactly T iterations.
- `samplingLaw` (`Formalization/Generative/FiniteHorizonSamplingDefinitions.lean:13–16`) is `Measure.pi` over
  (h,s,a,t) of `(E h).transition s a` as a PMF measure. So all SAHT draws are independent, there is one fresh draw per
  (h,s,a) per iteration, and each has law P_h(·|s,a). It is a probability measure, so `probReal_univ` is meaningful.
- `sampledIterateAt_succ` states the printed recursion literally. Its axioms are `[propext, Classical.choice, Quot.sound]`.

### F6 (OK): no junk value makes the theorem vacuous; the hypotheses can be satisfied
- **H = 0:** `Fin 0` is empty, so the event is `univ` and the conclusion is 1−δ < 1. This is true, and the source is
  vacuous here as well. It is the only degenerate case, handled at `Main.lean:124–131`.
- **Empty State or Action:** impossible when H ≥ 1, because `EnvironmentStage` carries nonemptiness.
- **H ≥ 1, T ≥ 2:** H log²T > 0, so the schedule involves no division by zero. For t ≥ 1 it forces η_t ∈ (0,1)
  (`Main.lean:52–66`).
- **Schedule:** it can always be satisfied. `CriticProbe.schedule_satisfiable` proves that the rescaled-linear schedule
  η_t = 1/(1+c₂t/(H log²T)) satisfies both bounds for every t ≤ T, given H ≥ 1, T ≥ 2 and 0 < c₂ ≤ c₁.
- **Budget:** with c₂ = c₁ = 1/64 and c₃ = 8000/c₂ = 512000, the smallest powers of two T that satisfy it are:
  - H=1, S=A=1, δ=1/2, ε=1: T ≈ 2.75·10¹¹;
  - H=2, S=10, A=5, δ=0.05, ε=0.5: T ≈ 7.0·10¹³;
  - H=5, S=100, A=10, δ=0.01, ε=0.1: T ≈ 1.4·10¹⁷.

  The right side grows only polylogarithmically, so every larger T also qualifies. So for every (H,S,A,δ,ε) the
  conclusion is a genuine probability statement about a non-empty hypothesis set. The constants are large but legal:
  the source says only "sufficiently large".

### F7 (OK, no trivialization): the internal departures are sound
The export compiles with standard axioms, so the departures cannot make the theorem false. I checked anyway that they
do not hide a trivialization:
- `plusV/minusV` (`Comparators.lean:21–47`) are backward recursions with an `sSup`/`sInf` over the χ²-ball
  `qRobustExpectations`. Non-emptiness and boundedness are proved (`sSup_robust_mem`, `sInf_robust_mem`, :116–141), so
  the junk value `sSup ∅ = 0` is never relied on. The comparators are **deterministic** functions of E, which is what a
  fixed-vector Freedman bound needs.
- `fluct` (`Propagation.lean:22–25`) is the weighted sum of V(sample) − PV over the window (t₀, t] with weights
  `weight η i t` = η_i^{(t)}.
- `GoodHead`/`AllGood` (:28–39) bound |fluct| by √(ρVar) + ρK, for both comparators, at every (s,a) and every t ≤ T.
- `AllGood` gets probability ≥ 1 − 2HSATδ′ from `coord_freedman` and a union bound (`GoodEvent.lean:105–207`). With
  δ′ = δ/(4SAHT) this is 1 − δ/2 (`Main.lean:172–178`).
- The conclusion is obtained on `AllGood` from the **actual** sampled iterate (`sampled_accuracy_of_allGood`) and then
  by `measureReal_mono`. It is not obtained from an auxiliary process.
- The stability step replaces KL/Pinsker with the total-variance potential. It needs ρH³ ≤ ε²/64
  (`Arithmetic.lean:181`), which is H⁴-consistent with the printed budget, and gives D ≤ 7ε/16. The propagation tail
  H·2^H·∏(1−η_j/2) ≤ H/T ≤ ε/6 uses the lower schedule bound through Σ_{(T/2,T]} η_j ≥ 16H log²T
  (`Main.lean:27–49`). The 2^H factor is absorbed because exp(−8H log²T) is tiny for T ≥ 2.

### F8 (Low, integration): `Definitions.lean` contains proofs
`FiniteQWip/Definitions.lean:79–122` holds theorems (`sampledStages_drop`, `sampledIterateAt_succ`, and others). AGENTS
requires `Statements/Ch4.lean` to import definition modules only. **Required on integration:** move the unfolding
lemmas into a separate module (BUILD-LOG note 6), or confirm that the project's convention allows small lemmas in
`*Definitions` modules. Also:
- delete the WIP oleans in `.lake/build/lib/lean/FiniteQWip/`;
- re-elaborate the entry inside `Ch4.lean`, whose own `local instance stateMeasurable … := ⊤` sits next to the ⊤
  instance fixed in `samplingLaw`'s type. I expect no conflict, because `Measure.real` unifies the σ-algebra from the
  measure, but this must be checked by compiling;
- run `python3 scripts/check.py` and the full axiom audit after integration. I did not run them.

### F9 (Low, docstring precision): `StatementProbe.lean:16–23`
The docstring calls `2 ≤ T` "the schedule's domain of definition". After the F1 rename it should also say that
without the premise the Lean statement is false (F3), not merely ill-posed.

## Required replacement text for `docs/SOURCE-ISSUES.md` C35 item (3)

> (3) The monograph cites li2021tightening-icml and gives no proof. The formal proof
> (`FiniteQLearning.finiteQLearning_sample_complexity`) is self-contained from monograph tools: Freedman with K₀ = 1
> along each (h,s,a) coordinate, robust χ²-ball comparators V^± (finite-horizon form of `lemma:Q-comparison-facts`),
> absorption of the fluctuation into the Bellman residual, and a triangular propagation recursion with
> super-solution H·2^k·∏_{(T/2,t]}(1−η_j/2). The χ² stability step is proved deterministically with the
> total-variance potential Ψ = 2K V⋆ − (V⋆)², not via the trajectory KL chain rule and Pinsker of
> `the private independent check note (Thm4_12-4_13)` Part B. Constants: every c₁ ∈ (0, 1/64] and c₂ ∈ (0, c₁] work with
> c₃ = 8000/c₂ (CHECK Part B's 2000/c₂ belonged to the KL route and is not what is formalized). The good event has
> probability ≥ 1 − δ/2, so the printed strict bound "> 1 − δ" holds. A ≥ 2 and 0 < η_t < 1 are not assumed; the
> schedule is used only for 1 ≤ t ≤ T.

Also append to item (1):

> Without `2 ≤ T` the Lean transcription is false; this is machine-checked in
> `<reviewer probe folder>/CriticProbe.lean` (`not_thm4_13_from_one`, same instance). The entry is
> `Thm4_13_corrected`.

The second sentence applies if F1 is adopted. If the probe is not kept, cite the instance only.
