# CRITIC — Claim 5.1 (`claim:PV-l-UB`) proposed `Claim5_1_corrected`

Public copy of the independent critic report; local paths removed.

- Date (UTC): 2026-11-07 08:55
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `9d04276f65872ed3a4b6ad3e3773fe6fc35f78f4` (branch `recovery-batch-vilcb-thm63-20261107`; working tree has an uncommitted `docs/SOURCE-ISSUES.md` diff adding C32–C35, unrelated to this claim)
- Mode: source-only reading. No Lean, lake, compiler or lean-lsp was run. Compile and axiom evidence is not independently established here.
- Not read before sections 1–4 were written: `the private preflight note (Thm5_1)`, `<builder working folder>/BUILD-LOG.md`, `docs/PROGRESS.md`, other CRITIC files.

## SHA-256

| File | SHA-256 |
|---|---|
| `source/upstream/tex/chapters/onlineRL.tex` | `393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53` (matches `source/provenance.json`) |
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` |
| `<builder working folder>/Claim51Wip/Statement.lean` | `473f4620fa615f72a2e72188fa3bcaf688164d5fb3ddfe7f6d4ee2fa463bdcb1` |
| `<builder working folder>/Claim51Wip/StatementProofs.lean` | `8681e3533a29d99bbc03473c67e5b6c1e501ed235f364290b9b57b7692278c27` |
| `<builder working folder>/Claim51Wip/Source.lean` | `7cffa6d634ea5f59a8336022f6f4886cb277f96096255a33c46cc9a89b4a6bbb` |
| `<builder working folder>/Claim51Wip/SlotIdentity.lean` | `7313d44eb56690158f38971812df8b410fb7a875f6ad499a52ec20c014faf28b` |
| `Formalization/Statements/Ch5.lean` | `61ba14796e870e43e86a80861ab0948605e13c126d3b182d2cb468fd9d21b36e` |
| `docs/SOURCE-ISSUES.md` (working tree) | `eaefe7cd653c2063f293fb5bf211622cc76879f32e0c85302466c5b2069a5638` |
| `Formalization/Online/Regret/MVP/Decoupling/OnlineMVPActualRankRadius.lean` | `73eff56bda2afb3170d08b627efee6eb13a094c348381417106e17176e827e91` |
| `Formalization/Online/Regret/MVP/Decoupling/MVPSourceProfileQuarterEvents.lean` | `03cbce51d9c121735fa277896927804a0e254d109245308f6cc10dd92037461d` |
| `Formalization/Online/Regret/MVP/Decoupling/DecouplingImageTransport.lean` | `95afa0a78af1db57d05b64ccffdb481e598f8ff9c156472cc64f6bbfaa59f1b7` |
| `Formalization/Online/SourceOptimism/SourceOptimismAllocation.lean` | `34be0110a9cdf6e48450ff4bc381d891267ca06e11d252cb1e3bc84db8b3daf3` |

## 1. Source reconstruction (independent)

Claim 5.1 (`onlineRL.tex:4340–4353`), inside the proof of Lemma 5.14 (`lemma:decouple`, statement `:1722–1744`, proof section `:4335–4476`):

With probability exceeding 1−δ′, simultaneously for all l = 1,…,log₂K and all j = 1,…,2^{l−1},

  Σ_{s,a,h} ⟨P̂^{(l)}_{s,a,h} − P_{s,a,h}, V^{k_{l,j,s,a,h}}_{h+1}⟩ ≤ √( SAHι/(2^l log₂K) · Σ_{s,a,h} Var_{P_{s,a,h}}(V^{k_{l,j,s,a,h}}_{h+1}) ) + SAH²ι/(2^l log₂K).

Objects, reconstructed from the chapter:

- ι = 40000 (log₂K)³ log(3SAH) log(1/δ′), δ′ = 100δ/(S²A²H²K²) (`:1388–1391`). Standing regime of Lemmas 5.13/5.14: K ≥ SAH log₂K.
- `k_{l,j,s,a,h}` = episode of the (2^{l−1}+j)-th visit to (s,a,h) (`:1603–1605`); convention V^k_{h+1} = 0 for k > K (`:1622`), so an absent visit contributes ⟨P̂−P,0⟩ = 0.
- P̂^{(j)}: for j ≥ 2 the empirical row of samples 2^{j−2}+1,…,2^{j−1} (1-based) of (s,a,h); for j = 1 the first sample (`:1458–1460`). Under the D^expand coupling (`:1419–1428`) the i-th visit of (s,a,h) consumes the i-th expand sample, so these batches are the same objects in either view.
- Profile I^k = max{j : 2^{j−1} ≤ N^{k,all}} (`:1510–1515`), so episodes with I = l are exactly those whose pre-episode count is in [2^{l−1}, 2^l−1], i.e. the (2^{l−1}+j)-th visits, j = 1..2^{l−1}: pre-count 2^{l−1}+j−1. At such a visit all samples of batch l (indices ≤ 2^{l−1}) are already observed.
- V^k_h = latest V^ucb before episode k (`:1449`); since MVP recomputes Q/V only when a trigger fires and every input (stored rows, stored counts) changes only at triggers, recomputing from the pre-episode history gives the same function.
- Proof (`:4406–4476`): build fixed-profile auxiliary families X_{h,I} = {V^{k,I}_h} ∪ {0}, apply Lemma 5.13 (`lemma:uniform`, `:1696–1717`), then identify V^k = V^{k,I^true} (eq. `eq:Vk-Itrue`).

Source defects found independently in this proof:

1. **Level-range mismatch (l = 1).** Lemma 5.13 is stated (and proved, `:4176–4182`, `:4248`, `:4272`) only for 2 ≤ l ≤ log₂K+1; at l = 1 its proof would use 2^{l−2} = 1/2 samples. The claim's proof (`:4464`) applies it to l = 1,…,log₂K. So the printed proof does not cover l = 1. (C16 mentions an "endpoint-index ambiguity" but not this use.)
2. **Terminal value of the auxiliary algorithm** (`:4423`, V_{H+1} = H) differs from the learner (V_{H+1} = 0, `:1267`), so `eq:Vk-Itrue` fails as printed (C17, already recorded).
3. **Generic Lemma 5.13 under the printed allocation** is refuted (C16); the claim's proof inherits that dependency.
4. Trigger set `{1,…,2^{log₂K}}` (`:1280`) conflicts with the doubling prose (C13); the batch/profile identity `eq:relation-profile-k` needs dyadic triggers.
5. Zero-count bonus undefined (C8); profile cover rounding (C15).

## 2. Proposed Lean statement (summary of what it says)

`Claim5_1_corrected` (`Statement.lean`): for all finite State/Action, H>0, K>0, environments E, initial law ρ, fallback, δ, c₁, c₂ with 0<δ≤1, 4≤c₁, c₁²≤c₂, SAH·(log K/log 2) ≤ K; with δp = δ/(100S²A²H²K²), I = 40000 x³ log(3SAH) log(1/δp), x = log K/log 2, planner = committed greedy MVP planner (fixed tie) with L = log(1/δp):

1 − δp < P_actual-sequential-law{ ∀ l∈ℕ, 1≤l, (l:ℝ)≤x, ∀ j, 1≤j≤2^{l−1}:
 Σ_{h,k} [cnt h k = 2^{l−1}+j−1]·(E_{P̂l(h,k)} U h k − E_{P(h,sa)} U h k) ≤ √(d·I/(2^l x)·Σ_{h,k}[cnt = …]·Var_{P}(U h k)) + d·H·I/(2^l x) }

with d = SAH, U h k = capped backward value at stage h+1 from the pre-episode history `history.take (k*H)`, cnt h k = number of earlier episodes whose stage-h pair equals the current one, and P̂l = `empiricalRow (2^(l−2))` of the row's successor list at zero-based indices (if l=1 then 0 else 2^(l−2)) + q.

## 3. Comparison table

| Item | Source | Lean | Verdict |
|---|---|---|---|
| Probability | "exceeding 1−δ′" | `1 − δp < …real {…}` (strict) | match |
| Allocation | δ′ = 100δ/(S²A²H²K²) | δp = δ/(100S²A²H²K²), δ ≤ 1 | correction C16, disclosed; necessity for *this* claim not shown (see MINOR-1) |
| ι | 40000(log₂K)³log(3SAH)log(1/δ′) | same with x = log K/log 2 and δp | match (modulo δp) |
| Constants | SAHι/(2^l log₂K), SAH²ι/(2^l log₂K) | d·I/(2^l x), d·H·I/(2^l x), d = S·A·H | match |
| Level range | l = 1,…,log₂K | l ∈ ℕ, 1 ≤ l, (l:ℝ) ≤ log K/log 2 | match (natural reading of possibly non-integer log₂K) |
| j range | 1,…,2^{l−1} | 1 ≤ j ≤ 2^(l−1) | match |
| Visit indexing | episode of the (2^{l−1}+j)-th visit; V=0 beyond K | episode-indexed sum over (h,k) with pre-count = 2^{l−1}+j−1; else 0 | equivalent: each (h,pair) has at most one such episode, absent visits contribute 0 exactly as ⟨P̂−P,0⟩ = 0 |
| P̂^{(l)} | batch l: samples 2^{l−2}+1..2^{l−1} (1-based); l=1 first sample | successors at zero-based visits 2^{l−2}..2^{l−1}−1; l=1 index 0, size 2^{(1−2)}=2^0=1 | match (natural-number subtraction gives size 1 at l=1, as intended); read from the full completed history, but only at episodes where all indices are < pre-count, so the fallback default is never read on a contributing term |
| V^k_{h+1} | latest V^ucb before episode k | `onlineCappedBackwardValueAt … (history.take (k*H)) (h+1)` | same object as `Lemma5_14_corrected`; trigger-only recomputation makes these equal |
| Variance | Var_{P_{s,a,h}}(V) | `(E h).transition … .variance (U h k)` | match |
| Simultaneity | all l, j | ∀ l, j inside the event | match |
| Algorithm | Alg. 5.x with undefined zero-count, literal trigger set, unspecified tie | committed greedy planner: C8 zero-count H branch, C13 dyadic triggers, one fixed maximizing tie | disclosed corrections; tie is a restriction (MINOR-2) |
| c₁,c₂ | "suitably chosen" (Thm 5.10); c₁≥4, c₂≥c₁² from the optimism analysis `:766`, `:3352`, `:3374` | 4 ≤ c₁, c₁² ≤ c₂ | inherited source-context premise, disclosed; not needed by the claim's mathematics (NOTE-2) |
| K regime | K ≥ SAH log₂K (Lemma 5.13/5.14) | SAH·x ≤ K | match; Lean does not assume the stronger K ≥ SAHι |
| δ range | 0<δ<1 | 0<δ≤1 | Lean assumes less |
| K = 1 | no level (log₂1 = 0) | event = univ, 1−δp < 1 | consistent |
| Proof at l = 1 | Lemma 5.13 (out of its range) | deterministic: each term ≤ H, ≤ one cnt=1 episode per (h,pair), total ≤ dH ≤ dHI/(2x) using I ≥ 2x (needs L ≥ 1 from the reciprocal allocation) | valid route; source proof gap must be disclosed (MINOR-3) |
| Proof at l ≥ 2 | Lemma 5.13 + `eq:Vk-Itrue` | library slot radius `mvp_actualRankSlotRadiusCondition_of_valueEvent` (radius 1/(16·2^{l−2}x), 4× stronger than 1/(2^l x)) + pathwise slot/batch/count/value identities + image transport | sound monotonicity; batch identity checked: stack batch jL = l−2 has 2^{jL} samples from index 2^{jL} |

## 4. Findings

### BLOCKING
None found on source fidelity or proof honesty from reading. (Compilation and the axiom audit of the WIP were not run by me; see section 6.)

### MAJOR
None.

### MINOR
- **MINOR-1 (allocation necessity not established for this claim).** C16 refutes the generic Lemma 5.13 under the printed allocation, not Claim 5.1 with the actual value family. When the printed δ′ is close to 1 the printed claim requires only probability > 1−δ′ ≈ 0, so it may well hold; I found no counterexample to printed Claim 5.1. The reciprocal allocation is a disclosed change of statement (hence `_corrected` is the right suffix), but the disclosure should say that printed-allocation Claim 5.1 is neither proved nor refuted, and that the change follows `Lemma5_14_corrected`/C16 rather than a counterexample to the claim itself.
- **MINOR-2 (tie rule is a restriction).** The statement covers one fixed committed greedy tie rule, not every argmax tie-breaking. Tie choice changes actions, hence counts, data and values, so this is a genuine restriction. The docstring says "one fixed maximizing tie"; keep it and state it as a restriction (precedent: `Lemma5_14_corrected`, C8 text).
- **MINOR-3 (l = 1 proof gap undisclosed).** The source proof applies Lemma 5.13 at l = 1, outside its stated range 2 ≤ l ≤ log₂K+1. The Lean proof covers l = 1 by a deterministic bound needing ι ≥ 2 log₂K, which holds because log(1/δp) ≥ 1 under the reciprocal allocation (the printed allocation does not guarantee it). This is a route difference, not a statement change, but it is a source proof gap and no `SOURCE-ISSUES.md` entry mentions Claim 5.1 or this use. Add a note (e.g. under C16) recording it.

### NOTE
- **NOTE-1.** Episode-indexed reading of Σ_{s,a,h} with `k_{l,j,s,a,h}` is exact: `mvp_slotSum_eq_rowLookupSum` proves the regrouping, and absent visits contribute 0 in both readings.
- **NOTE-2.** `4 ≤ c₁`, `c₁² ≤ c₂` are copied from `Lemma5_14_corrected` and correspond to the source's optimism analysis conditions; the claim's concentration argument does not use them. Disclosed in the docstring; acceptable as the source's analysis context. They could be described as inherited context premises rather than claim premises.
- **NOTE-3.** P̂^{(l)} is read from the full completed history, not from D^expand directly. The pathwise lemma `claimPV_batch_eq` identifies it with the expand-stack batch under the transcript equality, which is the source's coupling made explicit. Non-contributing terms never read past the observed visits.
- **NOTE-4.** The library slot radius uses coefficient 1/(16·2^{jL}x); the claim needs 1/(4·2^{jL}x). The export is stronger by a factor 4; `claimPV_scalar_high` weakens it correctly.
- **NOTE-5.** Docstring should cite the specific SOURCE-ISSUES anchors (C8, C13, C15, C16, C17) — it does list them by ID.

## 5. Proof honesty

- `StatementProofs.lean`: `Claim5_1_corrected_holds` is `intro …; exact claimPV_eventConfidence …`. It applies the export and does not reprove anything. The export's δp is `onlineSourceOptimismDeltaPrime δ S A H K`, defined as `δ / (100 * S^2 * A^2 * H^2 * K^2)` (`SourceOptimismAllocation.lean:13–14`), and `claimPVEvent` has the same body as the statement's set, so the `exact` relies only on δ-unfolding (defeq). Not compiled by me.
- The export uses the existing proved library results `mvp_actualProfileFamilies_quarterStrong_intersection` (same premises as Lemma 5.14: δ ≤ 1, 4 ≤ c₁, c₁² ≤ c₂, budget), `mvp_actualRankSlotRadiusCondition_of_valueEvent`, and `onlineStack_rank_event_to_sequential_image_conditional`. No probability or bridge statement enters as a hypothesis of the export. The only premises are the statement's.
- Grep of the four WIP files for `sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide|@[extern|ofReduceBool`: no matches. Grep over all of `Formalization/**/*.lean` (a superset of the import closure) finds only two docstring uses of the English word "admit" (`ModelFree/QLearningRobustDefinitions.lean:19`, `Obstructions/SingletonAction.lean:58`), and no tactic or declaration hits.
- `Statement.lean` imports only `Formalization.Statements.Ch5` (definition modules), matching the index rule; final placement must go into `Ch5.lean`/`Ch5Proofs.lean` and be imported from `Formalization.lean` for the axiom audit.

## 6. Disclosure requirements (before landing)

1. In `SOURCE-ISSUES.md` (C16 or a new note): Claim 5.1's printed proof applies Lemma 5.13 at l = 1, outside 2 ≤ l ≤ log₂K+1; the formal proof covers l = 1 deterministically using ι ≥ 2 log₂K under the reciprocal allocation.
2. State that printed-allocation Claim 5.1 is not refuted, only not proved; the reciprocal allocation follows C16 and `Lemma5_14_corrected`.
3. Keep the docstring's tie-rule sentence and phrase it as a restriction to one fixed deterministic tie.
4. Record compile plus axiom-audit evidence (`propext`, `Classical.choice`, `Quot.sound` only) for `Claim5_1_corrected_holds` after integration; this critic did not run Lean.

## VERDICT

**ACCEPT WITH DISCLOSURES** for source fidelity and proof honesty of `Claim5_1_corrected`, conditional on (a) compile and axiom-audit evidence that I did not produce, and (b) disclosures 1–3 above. No BLOCKING or MAJOR findings.

## Addendum (written after the verdict, after reading `<builder working folder>/BUILD-LOG.md` and `axiom-probe.out`)

The builder's log records exit-0 compiles for all four WIP modules and an axiom probe in which `Claim5_1_corrected_holds`, `claimPV_eventConfidence` and the helper lemmas depend only on `[propext, Classical.choice, Quot.sound]`. The SHA-256 values in the log match the four files I reviewed. This is builder-reported evidence; I did not reproduce it. It satisfies condition (a) provisionally, pending re-run after integration into `Ch5.lean`/`Ch5Proofs.lean` and `python3 scripts/check.py`. Verdict unchanged.
