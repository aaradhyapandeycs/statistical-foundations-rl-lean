# Critic report: federated per-agent read-off `eq:sample-size-per-agent-fedQ` (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/Ch7Rest/FedSync79ReadOff.lean` and the drafted entry `Eq_sample_size_per_agent_fedQ_restricted`. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT-WITH-FIXES; findings 5, 6, 7 and 11 applied (docstring wording for large K, γ = 0 disclosure, SOURCE-ISSUES C41 addendum and COVERAGE row, direct import in `Formalization.lean`). The entry landed with no change to the Lean statement.


Verdict: **ACCEPT-WITH-FIXES** (fixes are wording/doc only; no Lean statement change required).
Entry verdict (five-bin): `Eq_sample_size_per_agent_fedQ_restricted` = **PASS-DISCLOSED** (conditional on finding 6 C41 addendum landing).

## Evidence (commands actually run; no lake, no git)
- `bash scripts/lean-local.sh Formalization/Ch7Rest/FedSync79ReadOff.lean` rc=0, no warnings (17 s).
- `bash scripts/lean-local.sh Formalization/Statements/Ch7.lean` rc=0.
- `bash scripts/lean-local.sh Formalization/Statements/Ch7Proofs.lean` rc=0.
- `<local probe>` (#print axioms): exists_horizon_of_log_cube,
  fedSynQ_readOff_restricted, horizon_ge_exp_of_eta_le_one, Statements.Ch7.Eq_sample_size_per_agent_fedQ_restricted_holds,
  Statements.Ch7.Thm7_9_corrected_holds — all `[propext, Classical.choice, Quot.sound]`. 
- No sorry/admit/axiom in FedSync79ReadOff.lean.

## Source read
`source/upstream/tex/chapters/federated_RL.tex:15–29` (setup), `:99–117` (thm:dist-syncq-local), `:118–129`
(Implications, eq:sample-size-per-agent-fedQ: "each agent requires at most Õ(SA/(K(1−γ)⁵ε²)) samples, where each
agent draws SA samples at each iteration").

Independent reconstruction: ∃ universal C (Õ hides universal constant and polylog in S,A,K,1/δ,1/ε,1/(1−γ)) such that
for every MDP, K, δ∈(0,1), ε∈(0,1/(1−γ)], Q₀∈[0,1/(1−γ)]: there is T with SA·T ≤ C·SA/(K(1−γ)⁵ε²)·polylog for which
Theorem 7.9 (η = c_η K(1−γ)⁴ε²/log(SAKT/δ), τ obeying (106)) gives ‖Q_T−Q*‖∞ ≤ ε w.p. ≥ 1−δ.

## Findings
1. **Inversion arithmetic correct.** With L = log x, T = ⌈2.7·10⁸ B(1+L)³⌉: T ≤ 2.7·10⁸B(1+L)³+1 ≤ 270000001·x³(1+L)³
   (uses B ≤ x³ and x³(1+L)³ ≥ 1); log T ≤ log 270000001 + 3L + 3log(1+L) ≤ 30 + 6L (2³⁰ > 270000001, log 2 < 1,
   log(1+L) ≤ L); log(xT) ≤ 30 + 7L ≤ 30(1+L); 10⁴·B·30³(1+L)³ = 2.7·10⁸B(1+L)³ ≤ T. Constants consistent.
2. **Log argument correct.** x = SAK/(δε(1−γ)²) (T-free), so x·T is exactly the export's (112–113) argument
   SAKT/(δε(1−γ)²); coefficient 10⁴/(K(1−γ)⁵ε²) = 10⁴B. B ≤ y³ ≤ x³ with y = 1/(ε(1−γ)²) ≥ 1 is checked from
   ε(1−γ) ≤ 1, K ≥ 1. Correct.
3. **Sample count.** SA·T ≤ SA(2.7·10⁸B(1+L)³ + 1); the "+1" is absorbed as 216·B(1+L)³ ≥ 1, which uses the
   restriction (K(1−γ)⁴ε² ≤ 216 log(SAK/δ) ≤ 216(1+L)³) and 1/(1−γ) ≥ 1. Hence C = 270000216. Correct; T is chosen
   before τ and η (uniform in τ), SA per iteration per agent matches :127.
4. **Probability.** Conclusion is the export `fedSynQ_error_le_of_eta_le_one` verbatim: true law
   `fedSamplingLaw M T K 1`, true Q* = `M.optimalityFixedPoint`, output `fedOutput` at T. η ≤ 1 derived from the
   restriction by monotonicity of log in T (log(SAK/δ) > 0). Correct.
5. **Restriction / obstruction.** `hKr` (η at T = 1 ≤ 1) is a T-free sufficient condition for the C41 correction
   (η ≤ 1 at the chosen T); it is stronger than strictly needed (slightly larger K could still work), and the
   docstring states it as a restriction, not as necessary — fine. `horizon_ge_exp_of_eta_le_one` is correct for
   every c_η > 0 (η ≤ 1 ⇔ c_ηKg⁴ε² ≤ log(SAKT/δ) ⇒ T ≥ δe^{c_ηKg⁴ε²}/(SAK)). Nothing claims the unrestricted
   read-off is false; both docstrings say it is open. OK.
   **Fix (wording):** the entry docstring says "outside this range it only certifies horizons T ≥ δ·exp(...)/(SAK)";
   that bound holds in every range and is ≤ ~1 just past the threshold, so it only obstructs for
   K ≫ log(SAK/δ)/((1−γ)⁴ε²). Rephrase as the library docstring does: "for K ≫ log(SAK/δ)/((1−γ)⁴ε²) the corrected
   theorem only certifies horizons T ≥ δ·exp(c_η K(1−γ)⁴ε²)/(SAK), exponential in K".
6. **C41 not yet updated (required).** docs/SOURCE-ISSUES.md C41 does not mention the read-off restriction; the
   DISCLOSED bin requires a matching entry. Add the addendum below. COVERAGE row ~230 still says "Open"; update.
7. **γ = 0 (minor, disclose).** Unlike `Thm7_9_corrected`, the entry has no `0 < M.discount`. At γ = 0 Lean's
   1/(8·0) = 0 makes (106) force τ = 1, a narrower τ-range than the printed (1/0 = ∞) reading. Not EXCESS (the γ = 0
   case is extra coverage; for γ > 0 the condition is printed (106)), but add one docstring sentence: "At γ = 0
   (outside the theorem's γ ∈ (0,1)) Lean's 1/0 = 0 reduces (106) to τ = 1." Alternatively add `0 < M.discount →`
   for consistency with Thm7_9_corrected (also a DISCLOSED convention there).
8. **Õ reading faithful.** Universal C quantified before everything; polylog made explicit as (1 + log(SAK/(δε(1−γ)²)))³,
   a polylog in S,A,K,1/δ,1/ε,1/(1−γ); exponent 5, K in denominator, ε² as printed. `_restricted` suffix is right
   (domain narrowed in K; no conclusion change). Existential c_η = 1/216 matches Thm7_9_corrected.
9. **Wrapper** only applies `fedSynQ_readOff_restricted` with C = 270000216, c_η = 1/216 (`by norm_num` positivity);
   no second proof. Ch7.lean imports unchanged; Ch7Proofs imports FedSync79ReadOff.
10. **Non-vacuity.** Hypotheses satisfiable (builder Probe: unitMDP, K=1, δ=1/2, ε=1); τ = 1 always meets (106).
11. **Minor:** `Formalization.lean` does not import `Formalization.Ch7Rest.FedSync79ReadOff` directly (covered
    transitively via Ch7Proofs); add the direct import for library hygiene.

## Binder table — Eq_sample_size_per_agent_fedQ_restricted (Formalization/Statements/Ch7.lean:444)
| binder | Lean type | bin | citation |
|---|---|---|---|
| C, 0 < C | ∃ ℝ, first | SOURCE | Õ constant, :122 |
| c_η, 0 < c_η | ∃ ℝ, first | SOURCE | (114) via Thm 7.9, :115 |
| State, Action, Fintype | Type + inst | TYPING | finite S, A, :20 |
| M (nonempty S/A, rewards ∈[0,1], 0≤γ<1) | DiscountedMDP | STANDING/TYPING | :20, book conventions; γ=0 see F7 |
| K, 1 ≤ K | ℕ | STANDING | :21 |
| δ, 0<δ<1 | ℝ | SOURCE | :102 |
| ε, 0<ε≤1/(1−γ) | ℝ | SOURCE | :102 |
| Q₀, 0≤Q₀≤1/(1−γ) | function | SOURCE | :103 |
| c_ηK(1−γ)⁴ε² ≤ log(SAK/δ) | Prop | DISCLOSED | `_restricted`, docstring, C41 (after F6 addendum) |
| ∃T, 1 ≤ T | conclusion | — | :127 |
| SA·T ≤ C·SA/(K(1−γ)⁵ε²)(1+log(SAK/(δε(1−γ)²)))³ | conclusion | SOURCE | :122, :127 |
| τ, 1 ≤ τ | ℕ | STANDING | :56, :74 |
| η = c_ηK(1−γ)⁴ε²/log(SAKT/δ) | Prop | SOURCE | (114) |
| τ ≤ 1 + η⁻¹min{(1−γ)/(8γ),1/K} | Prop | SOURCE | (106) |
| 1−δ ≤ P_true(∀s a, |Q_T−Q*| ≤ ε) | conclusion | SOURCE | :112, :23–26 |
Counts: SOURCE 9, STANDING 2(+M), TYPING 1, DISCLOSED 1, EXCESS 0.

## Proposed COVERAGE row (~230)
| Federated per-agent sample size, `eq:sample-size-per-agent-fedQ`, federated chapter lines 118–129 | `Eq_sample_size_per_agent_fedQ_restricted` (`Formalization/Ch7Rest/FedSync79ReadOff.lean`) | **Restricted variant proved.** From `Thm7_9_corrected` (c_η = 1/216, c_T = 10⁴): for K with c_η K(1−γ)⁴ε² ≤ log(SAK/δ), an explicit T has per-agent samples SA·T ≤ 270000216·SA/(K(1−γ)⁵ε²)·(1 + log(SAK/(δε(1−γ)²)))³ and FedSynQ is ε-accurate w.p. ≥ 1−δ for every τ obeying (106). The unrestricted read-off (all K) is not implied by the corrected theorem (`horizon_ge_exp_of_eta_le_one`: certified horizons grow like exp(c_ηK(1−γ)⁴ε²)) and is not refuted; open ([C41](SOURCE-ISSUES.md#C41)). Independently critic-checked. Not author-approved. |

## Proposed C41 addendum (append to SOURCE-ISSUES.md C41)
Read-off (2026-11-10). The per-agent sample size eq:sample-size-per-agent-fedQ (`federated_RL.tex:118–129`) is
proved only in the K-range c_η K(1−γ)⁴ε² ≤ log(SAK/δ), i.e. where the prescribed η is at most 1 already at T = 1
(`Eq_sample_size_per_agent_fedQ_restricted`, `Formalization/Ch7Rest/FedSync79ReadOff.lean`, with explicit
Õ = 270000216·(1 + log(SAK/(δε(1−γ)²)))³). Because the corrected theorem needs η ≤ 1 and η grows linearly in K,
any horizon it certifies satisfies T ≥ δ·exp(c_η K(1−γ)⁴ε²)/(SAK) for every c_η > 0
(`horizon_ge_exp_of_eta_le_one`), so for K ≫ log(SAK/δ)/((1−γ)⁴ε²) the linear-speedup read-off does not follow
from the theorem. It is not refuted: whether FedSynQ (with some other step size) attains it for such K is open.
Not author-approved.
