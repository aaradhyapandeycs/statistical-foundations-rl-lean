# Critic report: Lemma 2.10 (Fano's lemma, `lem:fano`)

Public copy of the independent critic report; local paths removed.

- Date (UTC, `date -u`): Fri Nov  6 20:00:53 UTC 2026
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `6bac672b2956953c2587c9785cda8de7a5b6eb72`, branch `batch-ch2-ch3-ch6-20261106` (working tree dirty; `FanoLemma.lean` is untracked, `Ch2.lean`, `Ch2Proofs.lean`, `Formalization.lean` modified)
- Mode: source-only review; no Lean compiled by the critic (no lake, lean, lean-lsp, `scripts/check.py` or `scripts/lean-local.sh` run). Numeric sanity checks used `python3 -I` with a script in the session scratchpad, outside the project.
- Independence: the source reconstruction (section 2), the Lean comparison (section 3) and the proof audit (section 4) were written before reading any builder note. `private task notes`, `private preflight notes`, `<builder working folder>/` (except `BUILD-LOG.md`, read only after sections 1 to 8 were written), `PROGRESS.md`, other `critic reports` files, `docs/PROGRESS.md` and `docs/COVERAGE.md` were not opened.

## 1. Inputs and pins

| File | sha256 (recomputed) | Expected / pin | Match | Lines inspected |
|---|---|---|---|---|
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` | provenance pin | yes | 1090–1215 (focus 1106–1202); lemma counter check: every `\begin{lemma}` in the file |
| `source/upstream/tex/chapters/intro.tex` | `6bfa41c0bcb9df3aa613ebe2bce9a966caaa9942e6629d52dabee5e518d0c92a` | provenance pin | yes | 215–245 (`eq:defn-KL` at 232) |
| `source/upstream/tex/chapters/commands.tex` | `78f6f8b5f086797d195dc72df6426df96faf632b3687723cfbe405fe411f7df3` | provenance pin | yes | 61–64 (`\KL` macros) |
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` | n/a | n/a | whole |
| `Formalization/Statements/Ch2.lean` | `e30a8476dd0987b89d7658b0dd7c299e8ce198d4780764c809913ff56505fc5f` | e30a8476… | yes | 1–26, 225–329 (`Lemma2_10` at 292–327) |
| `Formalization/Statements/Ch2Proofs.lean` | `c409f73c48197c1ad1e09e96cddd325157107c843132a20bdad59f3a4c199cdd` | c409f73c… | yes | 1–13, 135–147 (`Lemma2_10_holds` at 140–145) |
| `Formalization/Probability/Fano/FanoLemma.lean` (450 lines) | `cd842c006dfc78af52f002f93733931ece6ba263bf335f2fced6006736fb758d` | cd842c00… | yes | 1–450 (all) |
| `Formalization/Probability/Fano/TestRiskDefinitions.lean` | `9d234d5295a50be1920ca293254ab9a670ae2b5fc3b80a237e84ff834c055978` | n/a | n/a | 1–50 (all) |
| `Formalization/Probability/Fano/TestTransports.lean` | `9b53eb6e881e326296f61339a18d75396b1b254549d4c5e24911311785257a2a` | n/a | n/a | 1–170 (all) |
| `Formalization/Probability/Fano/ReverseFanoInfimum.lean` | `faa8fea87b196e11ea079e13ea1ccc1f3ab593e280d717cf17428d2d8053c3a8` | n/a | n/a | 1–50 |
| `Formalization/Probability/Fano/ReverseTest.lean` | `098daa730f783a27953e426f52a31bfbb520fc9e1984fdcf0c530fa703d8e9d7` | n/a | n/a | 1–165 (all) |
| `Formalization/Probability/Fano/ReverseTestDefinitions.lean` | `aae0c13dc0fc8c1cbaf91fce02960617337bb80c1fa17e63b5f41ebc0539de5c` | n/a | n/a | 1–22 (all) |
| `Formalization/Probability/Fano/FinitePartitionKL.lean` | `d8c40813f949ccc95436aa7b8a9b621bc8305821a2e646485711f062cd1c9558` | n/a | n/a | 1–152 (all) |
| `Formalization/Probability/Fano/FiniteValuedMapDefinitions.lean` | `958f7664b8db0dda351aa466840723bef46e5929e2295fc8416f2cc04261bb66` | n/a | n/a | 1–15 (all) |
| `Formalization/Probability/Fano/FinitePartitionRestriction.lean` | `c1cb89b2d52fb4ef63fbb11b3df0a0690439cdeba1717f78d18350675d5c24dd` | n/a | n/a | declaration list only |
| `Formalization/Probability/Fano/BernoulliPinskerLaw.lean` | `e5799ec274f1a9310b367088dd18537db2ba772bc35a75152f04c2a67052a478` | n/a | n/a | 76–82 (statement of `bernoulli_klDiv_quadratic_lower`) |
| `Formalization/Generative/GenerativeLowerBoundFiniteDataProcessing.lean` | `9022df9d0638c5d1624c4f83934a1b72739021f5a49d82eddb19817ba05904e7` | n/a | n/a | 1–25 (all) |
| `Formalization/Generative/GenerativeLowerBoundFiniteKLDataProcessing.lean` | `471ec68b7d653a1bdace8e73097dbd5f85c5d7f9c5e6f4d714759a52b1c88aa9` | n/a | n/a | 1–45 |
| `Formalization/Generative/GenerativeLowerBoundWeightedLog.lean` | `bf58dbfbfc577623377081a20d1b88577b69ee9bba6dc30429b642048ae5e764` | n/a | n/a | 1–71 (all) |
| `Formalization/Generative/GenerativeLowerBoundAffinityOverlap.lean` | `17d6bea10441f5cf2cbbbc4a480cd122204008caf317073d6906473bf797ff71` | n/a | n/a | 1–34 (all) |
| `Formalization.lean` | `1ecb6f135e2feac432378c2653f19a16d0f2f54b8f4c19f042ef04c600a3804a` | n/a | n/a | grep: imports `FanoLemma` (124), `Statements.Ch2` (437), `Statements.Ch2Proofs` (438) |
| `Audit.lean` | `29f6cd54e69586325be78af79809bda1f1d1c2b0c52f03ad3746eb6e8c3d06f3` | n/a | n/a | 1–24 (allow-list `propext`, `Classical.choice`, `Quot.sound` over every `StatisticalRL.*` constant) |
| Mathlib `InformationTheory/KullbackLeibler/Basic.lean` (rev `32d24245c7a12ded17325299fd41d412022cd3fe`, same as `lake-manifest.json`) | `6ae68f0c2ecafbe5f7932b3d8f863539d4d9f6018c1905ed0e5664986ef6c23d` | n/a | n/a | 57–64 (`klDiv` definition), lemma names at 78, 100, 150, 157, 205 |
| Mathlib `MeasureTheory/MeasurableSpace/Instances.lean` | `845a0c7cff8ac19038946346b2630311ae1e7f354d49203d1e747bd3f4c488b3` | n/a | n/a | 34 (`Fin.instMeasurableSpace n := ⊤`) |

Numbering check: the uncommented `\begin{lemma}` environments of `prelim.tex` before line 1140 are at 339, 458, 544, 939, 956, 985, 1001, 1038, 1056 (the one at 1092 sits inside `\begin{comment}` 1081–1103), so `lem:fano` at 1140 is Lemma 2.10. Consistent with Lemma 2.11 = `lem:reverse-Fano-bound` at 1209.

## 2. Source reconstruction (written before reading any Lean)

Setting (`prelim.tex:1108–1128`). `P_0, …, P_M` are probability measures on a common measurable space `(𝒳, 𝒜)`. A test is a map `ψ : 𝒳 → {0, …, M}`; the text writes `P_i(ψ ≠ i)`, so `ψ` must be measurable (the event `{ψ ≠ i}` must lie in `𝒜`). This matches the cited Tsybakov §2.7.1 / §2.2, where a test is an `𝒜`-measurable function into `{0, …, M}`. The tests are deterministic; randomized tests are not mentioned.

- `p_e := inf_ψ max_{0≤i≤M} P_i(ψ ≠ i)` (`eq:defn-minimax-prob-error-prelim`, label at 1117, display 1118).
- `p̄_e := inf_ψ (1/(M+1)) ∑_{i=0}^M P_i(ψ ≠ i)` (`eq:defn-avg-prob-error-prelim`, label at 1124, display 1125).

Both infima range over a nonempty set (constant tests), and every value lies in `[0,1]`, so they are ordinary real infima.

KL (`intro.tex:229–232`, `eq:defn-KL`): `KL(P‖Q) = ∫ log(dP/dQ) dP`, defined when `P ≪ Q`. The log is natural (the book's `exp(−β)` in part (i) and `log 2` in part (ii) are in nats). Under `P ≪ Q` the negative part of `log(dP/dQ)` is `P`-integrable (since `∫_{p<q} p·log(q/p) ≤ ∫ (q−p)^+ ≤ 1`), so the integral is a well-defined value in `[0, ∞]`. It equals `+∞` exactly when `log(dP/dQ)` is not `P`-integrable. The book prints no convention for `P` not ≪ `Q`.

Lemma 2.10 (`prelim.tex:1140–1202`, label 1141):

- (i), lines 1145–1152: `M = 1`. If `KL(P_1‖P_0) ≤ β < ∞`, then `p_e ≥ p̄_e ≥ max{ (1/4)·exp(−β), (1 − √(β/2))/2 }`.
- (ii), lines 1154–1168: `M ≥ 2`. If `(1/(M+1)) ∑_{j=1}^M KL(P_j‖P_0) ≤ β·log M` for some `0 < β < 1`, then `p_e ≥ p̄_e ≥ (log(M+1) − log 2)/log M − β`.
- (iii), lines 1171–1199, is wholly commented out with `%`. It is not part of the printed lemma.

Implicit assumptions:

- Tests are measurable and deterministic.
- KL is natural-log KL. "KL ≤ β < ∞" forces `P_1 ≪ P_0`, finite KL and `β ≥ 0`, since KL is at least 0. A real `β` is enough.
- In (ii) the hypothesis forces every `KL(P_j‖P_0)` to be finite, so each `P_j ≪ P_0`.
- `β < ∞` in (i) only says that β is a real number.
- `0 < β < 1` in (ii) is not needed for truth:
  - If `β ≥ 1`, the right side is below `log((M+1)/2)/log M − 1 < 0`, because `(M+1)/2 < M` for `M ≥ 2`.
  - If `β ≤ 0`, all the KLs vanish, and the general bound below still applies.

Truth of each printed part:

- `p_e ≥ p̄_e`: for every test, the max is at least the average, and the inequality passes to the infimum over the same test class. True in both parts.
- (i), first branch (Bretagnolle–Huber). For a test `ψ`, let `A = {ψ = 1}`. Then `P_0(ψ≠0) + P_1(ψ≠1) = P_0(A) + P_1(Aᶜ) ≥ ∑ min ≥ (1/2)·exp(−KL(P_1‖P_0)) ≥ (1/2)·exp(−β)`. Halving gives `(1/4)·exp(−β)`. True.
- (i), second branch (Pinsker). `P_0(A) + P_1(Aᶜ) = 1 − (P_1(A) − P_0(A)) ≥ 1 − TV ≥ 1 − √(KL/2) ≥ 1 − √(β/2)`. Halving gives the claim. True; trivial when `β > 2`. Equality holds at `P_0 = P_1`, `β = 0`, where `p̄_e = 1/2`.
- (ii) (Fano). For a test `ψ`, let `a_j = P_j(ψ = j)` and `b_j = P_0(ψ = j)`, so `∑ b_j = 1`. Then:
  - Binary data processing gives `KL(P_j‖P_0) ≥ kl(a_j‖b_j)`.
  - The log-sum inequality on `(a_j)` and `(1−a_j)` gives `∑_j kl(a_j‖b_j) ≥ S·log S + T·log(T/M)`, where `S = ∑a_j` and `T = ∑(1−a_j) = (M+1)·p̄(ψ)`.
  - A second log-sum, on `(S, T)` against `(1, 1)`, gives `S·log S + T·log T ≥ (M+1)·log((M+1)/2)`.

  Hence `∑_{j=0}^M KL(P_j‖P_0) ≥ (M+1)(log(M+1) − log 2) − T·log M`. The `j = 0` term is 0. Dividing by `(M+1)·log M > 0` gives `p̄(ψ) ≥ (log(M+1) − log 2)/log M − β`. True (this is Tsybakov Cor. 2.6). The argument uses `P_0` as the reference measure directly; the mixture is not needed.

Numeric sanity check (`python3 -I`, random finite laws with zero atoms, using exact infima `p̄_e = (1 − TV)/2` for M = 1 and `p̄_e = 1 − (1/(M+1))∑_x max_j P_j(x)` for M ≥ 2, at the tightest admissible β):

- (i): 128,334 admissible samples, `min(p̄_e − bound) = 0.0`, attained at `P_0 = P_1`.
- (ii): 30,560 admissible samples with `0 < β < 1`, `min(p̄_e − bound) ≈ 0.0289`.

No violations in either part.

## 3. Lean statement versus source, field by field

`def Lemma2_10 : Prop` (`Ch2.lean:309–327`) is the conjunction of two universally quantified clauses.

| Item | Source | Lean | Verdict |
|---|---|---|---|
| Sample space | common measurable space `(𝒳,𝒜)` | `{Ω : Type u} [MeasurableSpace Ω]`, arbitrary σ-algebra and universe | exact |
| Laws | `P_0,…,P_M` probability measures | (i) `P : Fin 2 → Measure Ω`; (ii) `P : Fin (M+1) → Measure Ω`; `[∀ j, IsProbabilityMeasure (P j)]` | exact; (i) identifies `M = 1` with index type `Fin 2` |
| Test class | maps `𝒳 → {0,…,M}`, measurable (implicit), deterministic | `MeasurableTest = {ψ : Ω → I // Measurable ψ}` with `I = Fin (M+1)`; σ-algebra on `Fin n` is Mathlib's `Fin.instMeasurableSpace = ⊤` (Instances.lean:34), and `MeasurableSingletonClass` is required in any case, which forces ⊤ on a finite type | exact (see NOTE N1) |
| Error | `P_i(ψ ≠ i)` | `testError P ψ i = (P i).real {x | ψ.1 x ≠ i}`; set measurable, finite measure, so `.real` is exact | exact |
| `p_e` | `inf_ψ max_{0≤i≤M}` | `minimaxErrorInfimum P = sInf (range (worstTestError P))`, `worstTestError = univ.sup' _ (testError P ψ)` | exact; range nonempty (constant test, `TestTransports.lean:39–54`) and bounded below by 0 (56–66), so `sInf` is the true infimum, no junk |
| `p̄_e` | `inf_ψ (1/(M+1))∑_{i=0}^M` | `averageErrorInfimum P = sInf (range (averageTestError P))`, `averageTestError = (∑ i, testError P ψ i) / Fintype.card I` with `card (Fin (M+1)) = M+1` | exact; same nonemptiness and boundedness |
| `p_e ≥ p̄_e` | both parts | `averageErrorInfimum P ≤ minimaxErrorInfimum P` in both conjuncts | exact |
| (i) KL argument order | `KL(P_1‖P_0)` | `InformationTheory.klDiv (P 1) (P 0)` | exact |
| (i) hypothesis | `KL(P_1‖P_0) ≤ β < ∞`, β real | `β : ℝ`, `klDiv (P 1) (P 0) ≠ ⊤`, `(klDiv (P 1) (P 0)).toReal ≤ β` | equivalent: for real β, `KL ≤ β` iff `KL ≠ ⊤ ∧ KL.toReal ≤ β`; negative β is vacuous in both (toReal ≥ 0); β ≥ 0 is implied, not assumed |
| (i) bound | `max{(1/4)e^{−β}, (1−√(β/2))/2}` | `max (1 / 4 * Real.exp (-β)) ((1 - Real.sqrt (β / 2)) / 2)` | exact (`1/4*x` parses as `(1/4)*x`; `√` of a nonnegative argument) |
| (ii) `M` | `M ≥ 2` | `(M : ℕ)`, `2 ≤ M` | exact |
| (ii) β | `0 < β < 1` | `0 < β`, `β < 1` | exact (both kept, although not needed for truth) |
| (ii) KL sum | `(1/(M+1))∑_{j=1}^M KL(P_j‖P_0) ≤ β log M` | `ENNReal.ofReal (1/((M:ℝ)+1)) * ∑ j : Fin M, klDiv (P j.succ) (P 0) ≤ ENNReal.ofReal (β * Real.log M)` | equivalent: `j.succ` ranges exactly over `1,…,M` of `Fin (M+1)`. The factor `ofReal(1/(M+1))` is finite and positive, so an infinite KL term makes the left side `⊤` and the hypothesis false, as in the source. With all KLs finite, both sides are `ofReal` of nonnegative reals, and `β log M > 0`, so the `ℝ≥0∞` inequality is the real one. |
| (ii) bound | `(log(M+1) − log 2)/log M − β` | `(Real.log ((M:ℝ)+1) - Real.log 2) / Real.log (M:ℝ) - β` | exact (natural log; `log M > 0`, so no division junk) |
| KL definition | `∫ log(dP/dQ) dP` for `P ≪ Q` | Mathlib `klDiv` (`irreducible_def`, Basic.lean:57–60): `ofReal(∫ llr dμ + ν(univ) − μ(univ))` if `μ ≪ ν ∧ Integrable (llr μ ν) μ`, else `∞` | agrees wherever the book defines KL, including the value `+∞` for non-integrable `llr`; `∞` off `≪` is an unprinted convention under which the hypotheses fail, so nothing extra is claimed |
| Log base | natural | `Real.log`, `Real.exp`; Mathlib KL uses `Real.log` | exact |
| Binders, universes | n/a | single universe `u`; `{Ω}` implicit; instance binders only for σ-algebra and probability; no `Nonempty Ω`, no finiteness, no extra regularity | no hidden premises |
| Missing source premises | n/a | none: every printed premise is present | n/a |
| Label / ranges in docstring | `lem:fano`, 1140–1202 | cites `lem:fano`, `prelim.tex:1141–1168` with `\begin{lemma}` at 1140 and (iii) at 1170–1199 commented; setting 1106–1132; labels at 1117 and 1124; `intro.tex:229–235`; (i) 1145–1152; (ii) 1154–1168 | correct; all line numbers checked against the pinned file (see NOTE N3) |
| Restricted/corrected label needed? | n/a | no | plain `Lemma2_10` is appropriate |

Statement-index conventions (AGENTS.md):

- The Prop is self-contained and refers to definitions (`averageErrorInfimum`, `minimaxErrorInfimum`, Mathlib `klDiv`), not to a theorem's type.
- `Ch2.lean` reaches them through `Formalization.Probability.Fano.TestRiskDefinitions`, a definitions-only module that `Ch2.lean` already imported before this change.
- `Ch2.lean` and `Ch2Proofs.lean` are both imported from `Formalization.lean` (lines 437–438), so `Audit.lean` covers them.

## 4. Proof honesty

Wrapper (`Ch2Proofs.lean:140–145`). `refine ⟨?_, ?_⟩` is followed by `intro`. The 7 binders of (i) and the 10 binders of (ii) are introduced in the declared order, then `exact` applies `fano_binary_infimum_lower P β hfin hβ` and `fano_multi_infimum_lower M P β hM hβ0 hβ1 hKL`. The wrapper does not restate the result or reprove anything.

Export signatures (`FanoLemma.lean:429–435` and `230–238`) are character-for-character the conjuncts of the Prop, with `{Ω : Type*}` in place of `{Ω : Type u}`, and their conclusions are exactly the Prop's. `_hβ1` is unused (the docstring at 228–229 says so); keeping it is harmless.

Proof chain, each step checked by hand.

Part (ii):

- `fano_multi_infimum_lower` (230–283):
  - `p_e ≥ p̄_e` comes from `averageErrorInfimum_le_minimaxErrorInfimum` (`TestTransports.lean:85–93`, `le_csInf`/`csInf_le` with nonempty/bdd proofs).
  - From `hKL` in `ℝ≥0∞`: the sum is `≠ ⊤` (because `ofReal(1/(M+1)) ≠ 0`, `ENNReal.mul_top`), so every `KL(P_{j+1}‖P_0) ≠ ⊤`. Then `KL(P_0‖P_0) = 0` (`klDiv_self`) gives finiteness for all `j : Fin (M+1)`.
  - The real form is `(1/(M+1))∑_{Fin M} toReal ≤ β log M` (`ENNReal.toReal_le_of_le_ofReal`, `toReal_mul`, `toReal_sum`).
  - Re-indexing `∑_{Fin (M+1)} = ∑_{Fin M} succ` uses `Fin.sum_univ_succ` and `klDiv_self`.
  - The per-test bound is passed through `lower_bound_averageErrorInfimum_of_forall_tests` (`le_csInf`, nonempty range).
  - The final algebra multiplies through by `log M > 0`. Correct.
- `fano_test_average_error_lower` (171–224): `a_j = P_j(ψ⁻¹{j})`, `b_j = P_0(ψ⁻¹{j})`, `∑ b = 1` (`sum_measureReal_preimage_singleton`). Absolute continuity transfers positivity for both `A_j` and `A_jᶜ`. `avg = T/(M+1)` with `T = ∑(1 − a_j)`. Combining `fano_binaryKL_sum_lower` with per-cell data processing gives `(M+1)(log(M+1) − log 2) − KLsum ≤ T log M`. Correct.
- `fano_binaryKL_sum_lower` (79–118): three applications of the zero-tolerant log-sum inequality (on `a/b`, on `(1−a)/(1−b)` with `∑(1−b) = M`, and on `(S,T)/(1,1)` with `S+T = M+1`), plus `T log(T/M) = T log T − T log M`, including the `T = 0` case. This is exactly the argument in section 2. Correct under Lean's `log 0 = 0` and `x/0 = 0` conventions, because the support hypotheses `0 < a_j → 0 < b_j` and `0 < 1−a_j → 0 < 1−b_j` are supplied.
- `finite_logSum_of_support` (37–74): restricts to the support of `a`, applies `finite_cell_logSum` (strictly positive cells; `GenerativeLowerBoundFiniteDataProcessing.lean:9–23`), then uses monotonicity of `log` in the denominator (`∑_{a>0} b ≤ ∑ b`). The case `∑a = 0` is trivial. Statement true as stated with zeros.
- `event_binaryKL_le_toReal_klDiv` (133–168): push-forward through the Boolean indicator, then:
  - `finiteValued_klDiv_map_le` (`FinitePartitionKL.lean:68–149`), which sums Mathlib's `mul_log_le_toReal_klDiv` over the restricted fibres and uses `sum_restricted_toReal_klDiv_eq`;
  - `finite_klDiv_eq_expression_of_ac` (atomic formula, zero reference atoms handled by `hac`).

  Binary data processing is correct, with the KL order `μ = P_j`, `ν = P_0`.

Part (i):

- `fano_binary_test_lower` (367–424): `A = ψ⁻¹{1}`. `{ψ ≠ 0} = A` on `Fin 2` (`Fin.eq_one_of_ne_zero`), so `avg = (b + 1 − a)/2`.
  - BH branch: `exp(−K) ≤ exp(−kl(a‖b)) ≤ 2(min(a,b) + min(1−a,1−b)) ≤ 2(b + 1 − a)`.
  - Pinsker branch: `event_sq_gap_le_klDiv` (`ReverseTest.lean:66–75`; `2(P(A) − Q(A))² ≤ KL(P‖Q)` via the Bernoulli push-forward and `bernoulli_klDiv_quadratic_lower`) gives `a − b ≤ √(K/2)`.

  Correct.
- `binary_exp_neg_kl_le_two_overlap` and `exp_neg_finiteKL_le_two_overlap_of_support` (287–364): Bretagnolle–Huber with zero atoms. They restrict to the support of `u` (where KL and affinity are unchanged, since zero-`u` terms vanish), apply Jensen (`finite_log_affinity_lower`: `−KL/2 ≤ log affinity`, positive cells), then `affinity² ≤ 2∑min` (`finite_affinity_sq_le_two_overlap`, Cauchy–Schwarz with `∑max ≤ 2`, zeros allowed). The affinity is positive because some `u_{i0} > 0` and `v_{i0} > 0`. Correct.
- `fano_binary_infimum_lower` (429–448): the per-test bounds plus monotonicity in β (`exp(−β) ≤ exp(−K)`, `√(K/2) ≤ √(β/2)`), then `max_le` and `le_csInf`. Correct.

No fallback definitions:

- `averageErrorInfimum` and `minimaxErrorInfimum` are genuine `sInf`s over the full measurable-test class.
- `finiteKLExpression` and `finiteAffinity` appear only in helper statements, never in `Lemma2_10`.
- No new global non-Prop instances (section 6).

## 5. Findings

No BLOCKING, MAJOR or MINOR findings.

- **N1 (NOTE): test class.** Lean's `p_e` and `p̄_e` range over deterministic measurable tests. That is the printed definition (and Tsybakov's). A reader who reads "all possible tests" (`prelim.tex:1121`) as including randomized tests would get a different `p_e`. Example: `Ω` a single point and `P_0 = P_1`; the deterministic `p_e = 1`, the randomized `p_e = 1/2`. Even so, the printed conclusions hold in that reading too: the randomized `p̄_e` equals the deterministic one by linearity, and max ≥ average still holds. The Lean statement simply does not formalize the randomized variant. Not a discrepancy with the printed text. The docstring discloses the measurability reading ("taken measurable so that `P_i(ψ ≠ i)` is defined").
- **N2 (NOTE): redundant premises kept.** `β < 1` is unused (`_hβ1`). `0 < β` is used only to discharge `0 ≤ β log M` and `ofReal` side conditions. The printed result is true without either (section 2). Keeping them matches the printed lemma, and the export is not weakened.
- **N3 (NOTE): citation granularity.** The docstring cites `prelim.tex:1141–1168` for the lemma. The environment spans 1140–1202 (commented (iii) through 1199, `\end{itemize}` 1201, `\end{lemma}` 1202). The docstring explicitly mentions 1140 and the commented 1170–1199, so a reader is not misled. The `FanoLemma.lean` module docstring uses 1140–1202. Cosmetic.
- **N4 (NOTE): KL off absolute continuity.** Mathlib returns `klDiv = ⊤` when `P` is not ≪ `Q`, a convention the book does not print. In both parts this makes the Lean hypothesis false exactly where the book's hypothesis is meaningless, so the Lean statement claims nothing beyond the book. The docstring states the convention.
- **N5 (NOTE, pre-existing, outside this change).** The import closure of `FanoLemma.lean` contains `ReverseFanoInfimum.lean`, whose module docstring still says "Private Claude builder draft", and `TestTransports.lean:120`, which has an "ADDED BY CLAUDE (not in Data's frozen input)" docstring. Neither touches Lemma 2.10's statement. Both are public-release hygiene items only. The new files (`FanoLemma.lean`, the `Ch2*.lean` diffs) contain no private paths or draft markers.

Concrete failure scenarios tried, none succeeded:

- (a) Negative or huge β in (i): vacuous, or the bound is trivially true.
- (b) An infinite KL term in (ii): the `ℝ≥0∞` hypothesis fails.
- (c) Zero atoms in `P_0` on decision cells: handled by the support hypotheses derived from `≪`.
- (d) `M = 1` in (ii): excluded by `2 ≤ M`, as in the source.
- (e) Junk `sInf`: excluded by nonempty and bounded-below ranges.
- (f) A non-discrete σ-algebra on the label space: excluded by `Fin.instMeasurableSpace = ⊤` and `MeasurableSingletonClass`.
- (g) Off-by-one in `∑_{j=1}^M`: `j.succ` over `Fin M` is exactly `1..M`.

## 6. Provider chain and grep results

- Provider chain:
  - `Lemma2_10_holds` → `fano_binary_infimum_lower`, built on:
    - `fano_binary_test_lower`;
    - `event_binaryKL_le_toReal_klDiv` (← `finiteValued_klDiv_map_le`, `finite_klDiv_eq_expression_of_ac`, `measurable_eventIndicatorBool`);
    - `binary_exp_neg_kl_le_two_overlap` (← `exp_neg_finiteKL_le_two_overlap_of_support` ← `finite_log_affinity_lower`, `finite_affinity_sq_le_two_overlap`);
    - `event_sq_gap_le_klDiv` (← `bernoulli_klDiv_quadratic_lower`, `map_eventIndicatorBool`);
    - `averageErrorInfimum_le_minimaxErrorInfimum`;
    - `lower_bound_averageErrorInfimum_of_forall_tests`.
  - `Lemma2_10_holds` → `fano_multi_infimum_lower`, built on:
    - `fano_test_average_error_lower`;
    - `fano_binaryKL_sum_lower` (← `finite_logSum_of_support` ← `finite_cell_logSum`);
    - `event_binaryKL_le_toReal_klDiv`;
    - `averageTestError_fin_eq`;
    - `measureReal_pos_of_ac`;
    - the two `TestTransports` lemmas.
- Mathlib names spot-checked at rev `32d24245`: `klDiv_ne_top_iff` (Basic.lean:100), `klDiv_self` (78), `toReal_klDiv` (150), `toReal_klDiv_of_measure_eq` (157), `mul_log_le_toReal_klDiv` (205), `sum_measureReal_preimage_singleton` (Measure/Real.lean:285), `probReal_compl_eq_one_sub` (Real.lean:442), `ENNReal.toReal_le_of_le_ofReal` (Data/ENNReal/Real.lean:280), `ENNReal.mul_top` (Data/ENNReal/Operations.lean:195).
- Import closure computed by a scratch script that follows `import Formalization.*` lines:
  - `FanoLemma.lean`: 63 project files.
  - `Ch2Proofs.lean`: 150 project files.
  - `Ch2.lean`: 32 project files.
- `grep -nE '\bsorry\b|\badmit\b|^\s*axiom\b|\baxiom\s|\bopaque\b|implemented_by|\bunsafe\b|native_decide|@\[extern|ofReduceBool|debug\.skipKernelTC'` over the 63-file `FanoLemma` closure: no matches (exit 1).
- `grep -lE` with the same token set over the 150-file `Ch2Proofs` closure: no matches (exit 1).
- `grep -nwE 'axiom|sorry|admit|sorryAx'` over the 150 files: no matches.
- `Ch2.lean`, `Ch2Proofs.lean`: no matches.
- `set_option` in the `FanoLemma` closure: none.
- `macro|elab|syntax|macro_rules|elab_rules|run_cmd|run_tac|#eval` in the `FanoLemma` closure: none. The only `attribute [` hits are two `attribute [local instance]` lines on unrelated state types (`EmpiricalRow.lean:23`, `Ch3Definitions.lean:208`).
- Global (non-`local`) instances in the `Ch2.lean` closure: only Prop-valued `IsProbabilityMeasure`/`IsMarkovKernel` instances and one `Fintype` instance. No project `MeasurableSpace (Fin _)` instance exists anywhere in `Formalization/`. All `MeasurableSpace … := ⊤` instances in the closure are `local`, on `State`/`Action` variables.
- `TestTransports.lean:125` adds a global `IsProbabilityMeasure (μ.map ψ.1)` instance (Prop-valued; cannot change meaning).
- Private paths or draft markers in `FanoLemma.lean`, `Ch2.lean`, `Ch2Proofs.lean`: none.

## 7. Items needing Lean-side confirmation (the critic compiled nothing)

1. `Formalization/Statements/Ch2.lean`, `Formalization/Probability/Fano/FanoLemma.lean` and `Formalization/Statements/Ch2Proofs.lean` compile at the pinned toolchain `leanprover/lean4:v4.27.0-rc1` and Mathlib `32d24245`, with no `sorry` warning.
2. `#print axioms StatisticalRL.Statements.Lemma2_10_holds` (and the two exports) reports only `propext`, `Classical.choice`, `Quot.sound`, and `lake env lean Audit.lean` passes with `FanoLemma` and `Ch2Proofs` in `Formalization.lean`.
3. The elaborated `MeasurableSpace (Fin (M+1))` instance in `Lemma2_10` is `Fin.instMeasurableSpace` (expected; any instance with `MeasurableSingletonClass` on a finite type is extensionally ⊤ anyway).
4. The wrapper's `exact` closes both goals by unification, without coercion or universe adjustment. The `intro _` instance hypotheses are still found by instance resolution (expected in Lean 4).

## 8. Verdict

VERDICT: PASS-WITH-FINDINGS. `Lemma2_10` matches both printed parts of `lem:fano` (`prelim.tex:1140–1202`, (iii) commented out) exactly, with no hidden or missing premises and no junk values, and the wrapper only applies two honestly proved exports; the findings are NOTE-level only (test-class reading, redundant printed premises kept, citation granularity, unprinted KL convention, pre-existing draft wording in imported helper docstrings), subject to the Lean-side confirmations in section 7.

## 9. Builder BUILD-LOG consistency

Read only after sections 1 to 8 were written: `<builder working folder>/BUILD-LOG.md` (56 lines, mtime 2026-11-06T19:59:08Z). Not opened: `FanoCoreWip.lean`, `AxiomProbe.lean`, and the other excluded files.

The log is consistent with what I read:

- **Hashes.** The final sha256 values it records for `FanoLemma.lean` (`cd842c00…`, 450 lines), `Ch2.lean` (`e30a8476…`, 329 lines), `Ch2Proofs.lean` (`c409f73c…`, 147 lines) and `Formalization.lean` (`1ecb6f13…`, 706 lines) equal my recomputed hashes and `wc -l` counts.
- **Olean.** The recorded `FanoLemma.olean` sha256 `941c7372…` equals the file now in `.lake/build/lib/lean/Formalization/Probability/Fano/`.
- **Timestamps.** Each source file's mtime precedes its olean's mtime:

  | File | Source mtime | Olean mtime |
  |---|---|---|
  | `FanoLemma` | 19:52:05Z | 19:52:38Z |
  | `Ch2` | 19:53:16Z | 19:53:46Z |
  | `Ch2Proofs` | 19:53:55Z | 19:54:12Z |

  These match runs 7–9 at 19:52–19:54Z, and the reviewed sources were not modified after their compiles.
- **Formalization.olean.** Its current mtime is 2026-11-06T20:05:20Z, later than the log's run 10 (19:54Z). Some later process (presumably the lead's validation) rewrote it after the log was written. This does not contradict the log, but run 10/11 evidence is not what produced the olean now on disk.
- **Importers.** The claim that only `Ch2Proofs.lean` and `Formalization.lean` import `Statements.Ch2` and `FanoLemma` matches my grep.
- **Grep coverage.** The builder's `sorry|admit|axiom` grep covered the 3 changed files. My grep (section 6) covers the full 63- and 150-file import closures with a wider token set. Both are clean.
- **Axioms.** The reported results (`Lemma2_10_holds` and both exports depend on `[propext, Classical.choice, Quot.sound]`; `Audit.lean` reports "Axiom audit passed for 9415 project declarations") are consistent with my finding that no forbidden token appears anywhere in the closure. I did not reproduce them.
- **Process.** The log says the builder used `scripts/lean-local.sh` with `-o` into the project `.lake/build` only, with no `lake`, `check.py` or LSP, and did not touch `docs/COVERAGE.md` or `docs/PROGRESS.md`. Nothing I read contradicts this.

Remaining gap: these are builder-reported results, not reproduced by the critic. The section 7 items should be confirmed by the lead's own compile and audit, ideally against the current `Formalization.olean`.
