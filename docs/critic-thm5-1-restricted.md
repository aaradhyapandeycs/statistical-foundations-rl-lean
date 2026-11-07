# CRITIC: Theorem 5.1 (`thm:bandit-pure-ucb`), Lean WIP in `<builder working folder>/`

Public copy of the independent critic report; local paths removed.

Independent critic, 2026-11-07. I did not build this. I reconstructed the model, algorithm and statement
from `bandits.tex` before reading any Lean.

## Verdict

**ACCEPT WITH DISCLOSURES.** The entry must be renamed `Thm5_1_restricted` (finding F1). No refutation
was found. Both printed bounds, the hypotheses, the constants, the algorithm and the noise model are
faithful. The axiom closure is clean. The only scope departure is the tie-rule class.

## Pins

- Source: `bandits.tex`, sha256 `d31856ba…d647d3`. This matches provenance.
- WIP files: all ten `.lean` sha256 values match the "Final files" list in `BUILD-LOG.md`, recomputed.
- Critic probe: `<reviewer probe folder>/Probe.lean`, sha256 `adb5848b…570502`.
  - Command: `bash scripts/lean-local.sh <reviewer probe folder>/Probe.lean`
    (foreground, no `-o`, one compile). Exit 0, no errors.
  - Output:
    `'Thm51Wip.Thm5_1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]`.
    `ucb_regret_bounds` gives the same result.
- Scan: no `sorry`, `admit`, `axiom` or `opaque` in the WIP `.lean` files.

## Independent reconstruction (source)

- **Model** (`:9–83`).
  - Arms are 𝒜 = {1..A} with r(a) ∈ [0,1] (`:15`). r⋆ = max_a r(a).
  - R_{a,t} = r(a) + z_{a,t}, with z_{a,t} iid N(0,1) over (a,t) (`:37–42`).
  - Bandit feedback: only R_{a_t,t} is observed (`:48`).
  - Regret(T) = T r⋆ − Σ_{t=1}^T r(a_t), a pseudo-regret and a random variable (`:67–72`).
- **Algorithm** (`:207–251`).
  - Initialize N = 0 and r^sum = 0.
  - For t = 1..T, pick a_t ∈ argmax_a r̄(a) + √(2 log(T²/δ)/N(a)). The index is +∞ when N = 0
    (stated only at `:387`).
  - Pull a_t and observe R_{a_t,t}. Update N(a_t) += 1, r^sum(a_t) += R and r̄ = r^sum/N.
  - No tie rule is given (`:232`).
- **Statement** (`:258–277`).
  - Hypotheses: 0 < δ < 1 and T ≥ A ≥ 2.
  - (5.1a) E[Regret(T)] ≤ 8√(A T log(T²/δ)).
  - (5.1b) E[Regret(T)] ≤ 10 log(T²/δ) Σ_{a: Δ(a)>0} 1/Δ(a).
  - The expectation is over the noise, and over tie randomness if there is any.

## Findings

1. **F1 (Medium, scope/naming): tie-rule class.** Locations: `Ch5StatementDraft.lean:23–25`,
   `UCBDefs.lean:47–58`.
   - The selection is `tie t (argmax)` for an arbitrary `tie : ℕ → Finset (Fin A) → Fin A` with
     `tie t s ∈ s`. This is universally quantified over every deterministic rule that depends only on
     the round and the argmax set (lowest index, highest index, round-robin by t, and so on).
   - The printed theorem concerns Algorithm 5.1 with an unspecified `a_t ∈ argmax`. Two kinds of
     instantiation are equally legitimate:
     - deterministic rules that depend on the observed history (for example, prefer the arm with
       fewer pulls, or the arm whose first reward was larger);
     - randomized tie-breaking, the common implementation.
   - The Lean says nothing about either kind, and neither reduces pathwise to a round/set rule.
     - During initialization, a history-dependent rule changes which noise entries are read.
     - Equivalence holds only in law, and that would need a separate argument.
   - The export therefore does not imply the printed result read as "for any argmax selection". By
     AGENTS.md this is a `_restricted` entry.
   - The draft docstring already discloses it (line 19: "history- or randomness-dependent tie rules
     are not covered"). That is good, but the bare name `Thm5_1` claims the printed result.
   - Precedent in the repo is mixed:
     - `Lemma6_9` keeps a bare name with a Q-row-only tie scope.
     - `Thm3_9_causal_positiveN`, `Thm6_8_corrected` and the Ch5 `_corrected` entries treat tie
       limits as disclosed restrictions.
   - I rule `_restricted`. The lead may want to harmonize `Lemma6_9` separately; that is outside this
     review.
   - The mathematics is not in doubt. The private independent check note (Thm5_1) §2 shows the repair covers every non-anticipating
     rule. The gap is formal coverage only.
   - Removing the suffix later would need a formal model with history-dependent selection and tie
     randomness U independent of the noise table, including measurability of the rule.

2. **F2 (Low, documentation): the proof route differs from C36.** Locations:
   `UCBCountBound.lean` (union `∑ s ∈ range T, ∑ k ∈ Icc 1 s`, bound `≤ δ`, around lines 160–200) and
   `UCBPath.lean:161` (`step1_pathwise`, which gives 1 ≤ count ≤ t).
   - The Lean takes the union over counts k ∈ [1, t] at 0-indexed round t. This is the count before
     round t, i.e. at the end of source round t. It does not use the initialization phase.
   - The resulting β = Σ_{t<T} 2tδ/T² = δ(T−1)/T ≤ δ. C36 states the union over n ≤ t−A+1 with
     β₁ = δ(T−A)(T−A+1)/T².
   - Both give β ≤ 1, so E N_T(a) ≤ 1 + ⌊m⌋ + β ≤ m + 2 is unchanged. (The Lean counts N from 0, so
     there are at most ⌊m⌋+1 low-count pulls instead of 1 + ⌊m⌋.) Its closure is `m + 1 + δ ≤ m + 2`,
     using δ ≤ 1.
   - Valid. This is a disclosure, not an error.

3. **F3 (none): hypotheses are exact.** Location: `Ch5StatementDraft.lean:24–26`.
   - The hypotheses are `2 ≤ A`, `A ≤ T`, `∀ a, r a ∈ Icc 0 1`, `0 < δ` and `δ < 1`, as printed. The
     proof uses only δ ≤ 1.
   - The added `tie` hypothesis is the argmax-membership semantics, not a hidden premise (scope: F1).
   - No hypothesis on the realized path, the event or the counts appears.

4. **F4 (none): conclusions and constants are exact.** Location: `Ch5StatementDraft.lean:27–34`.
   - L = `Real.log ((T:ℝ)^2/δ)`, with a positive argument, so there is no junk log.
   - (5.1a) is `8 * Real.sqrt (A*T*L)`, with ℕ→ℝ coercions at the leaves.
   - (5.1b) is `10 * L * ∑ a ∈ univ.filter (0 < Δ a), 1/Δ a`, with Δ a = r⋆ − r a and
     r⋆ = `⨆ a, r a`. That supremum is the max on a nonempty finite type because A ≥ 2.
   - `Integrable regret` is an extra conclusion, which is acceptable.
   - Regret is `T r⋆ − Σ_{t:Fin T} r(ucbAction … z t)`, a pseudo-regret integrated against the noise
     law. This is the source's E[Regret(T)] for a deterministic tie rule.

5. **F5 (none): algorithm semantics.** Location: `UCBDefs.lean:37–67`.
   - `ucbIndex` is ⊤ at N = 0 and `S/N + √(2L/N)` otherwise, with r̄ = r^sum/N as printed.
   - The argmax is `{a | ∀ b, idx b ≤ idx a}` in the linear order `WithTop ℝ`, so it is nonempty
     (`ucbArgmax_nonempty`).
   - The state update increments N(a) and adds `r a + ζ t a` to S(a) for a = `tie t (argmax)`.
   - `ucbArm t` is by definition the same arm used in the update at round t, and `ucbAction` is
     `ucbArm` on `extendNoise z`. The zero extension past T is never read by rounds < T.
   - Probe results, all compiled:
     - `ucbIndex = ⊤` when `N a = 0`, and the printed real value when `N a ≠ 0`.
     - With all N = 0 the argmax is `univ` (every index is ⊤, the correct tie).
     - `ucbArgmax L ![1,0] S = {1}`: the unpulled arm strictly beats any finite index.
     - `ucbArgmax L ![1,1] ![1,0] = {0}`: finite indices are compared as reals, with no ⊤/coercion
       junk ties.
     - With the min' tie rule, rounds 0 and 1 pull arms 0 and 1 for every noise sequence. This is the
       initialization phase of `:387`.
   - Rounds are 0-indexed (round t is source round t+1). This is disclosed and harmless.

6. **F6 (none): noise model.** Location: `UCBDefs.lean:29–30`.
   - The model is `Measure.pi (Fin T) (Measure.pi (Fin A) (gaussianReal 0 1))`: independent N(0,1)
     entries z t a over all (t, a), the round-indexed table of `:37–42`. Variance `1 : ℝ≥0` is
     standard.
   - The reward at round t reads `ζ t a` for the pulled arm a, the correct entry. Bandit feedback holds
     because the state only accumulates pulled-arm rewards.

7. **F7 (none): non-vacuity.** The probe instantiates `Thm5_1_holds` at A = T = 2, r = (1/2, 0),
   δ = 1/2 and the tie rule `fun _ s => if h : s.Nonempty then s.min' h else 0` (`minTie_ok` proved).
   - All hypotheses are discharged, so they are satisfiable.
   - In this instance both arms are forced, so Regret ≡ 1/2 > 0. The regret object is genuine and not
     identically 0, and the bounds are nontrivial true statements about it.

8. **F8 (Low, integration): landing requirements.**
   - The draft lives in namespace `Thm51Wip` under the private working folder. Landing must move the definitions into a
     library definition module. `Formalization/Statements/Ch5.lean` must import that module only, and
     `Ch5Proofs.lean` must import the proof modules and apply `ucb_regret_bounds` as the wrapper does
     now.
   - Re-run the axiom audit after the move. The current wrapper is a one-line application with no
     restatement and no re-proof, which is acceptable.

## Required edits (not made by me)

1. **Rename** `Thm5_1` to `Thm5_1_restricted` in the statement entry and wrapper (`Thm5_1_restricted_holds`).
   Add to its docstring:
   - "Restricted variant: the printed algorithm leaves the choice inside the argmax unspecified
     (`:232`). This entry covers every deterministic rule `tie t s ∈ s` that depends only on the round
     and the argmax set. It does not cover history-dependent or randomized tie-breaking."
   - "Both printed bounds and constants are unchanged."
   - A link to `docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`.
2. **SOURCE-ISSUES, scope disclosures:** add the bullet "Theorem 5.1 (`thm:bandit-pure-ucb`,
   `bandits.tex:258–277`) is indexed as `Thm5_1_restricted`", followed by:
   - the tie-rule scope above;
   - index ⊤ at N = 0 (`:387` convention);
   - 0-indexed rounds;
   - pseudo-regret with r⋆ = ⨆ r;
   - integrability is proved;
   - see C36 for the proof repair.
3. **C36 addendum:**
   - "The formal proof (UCBCountBound) takes the union over 1 ≤ n ≤ t at each 0-indexed round t
     (count before round t ≤ t). It does not use the initialization bound N_t ≤ t−A+1. This gives
     β = δ(T−1)/T ≤ δ ≤ 1, so E N_T(a) ≤ ⌊m⌋+1+δ ≤ 8L/Δ² + 2, again the printed intermediate bound."
   - "The n ≤ t−A+1 route above is an equally valid tighter alternative."
4. **Optional:** in the `ucb_expected_count_le` docstring, state the union range and β ≤ δ.
