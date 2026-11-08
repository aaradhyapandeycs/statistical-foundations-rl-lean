# CRITIC: corrected Theorem 7.12 (online VPO regret, `thm_online`), Lean WIP review

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): edits R1–R3 of this review were applied at integration; the integrated index entries are definitionally equal (rfl) to the reviewed Props. The review text below is unchanged.

Critic: an independent agent, not the builder. Date: 2026-11-08. Not author-approved. This file is evidence only.
Source: `source/upstream/tex/chapters/RLHF.tex`, sha256 `e60115c355d44cba835b2323cc76fef50bfbfb646644686d989115af54f4df90`
(matches docs/critic-thm7-12-plan-check.md).
Reviewed: `<builder working folder>/Thm712Wip/*.lean`. It is byte-identical to `Thm712Wip.reviewed-snapshot`
(`diff -r` is empty). Every sha256 matches the "Final file hashes" in BUILD-LOG.md, with Statement.lean at
`c61557a2…2990` (the version after the docstring edit).

## Verdicts

| Entry | Verdict |
|---|---|
| `Thm7_12_corrected` (+ `Thm7_12_corrected_holds`) | **PASS.** Approved for integration once docstring edit R1 is made. It does not block the mathematics. |
| `Thm7_12_corrected_local` (+ `Thm7_12_corrected_local_holds`) | **PASS.** Same condition (R1). |

The `_corrected` naming is correct, and the printed rate is honestly reported as neither proved nor refuted. I found no
hidden hypothesis, weakened conclusion, junk-value exploit or vacuity.

## Source reconstruction (done before reading the Lean)

- BT oracle at :24–28. NLL at :31–39. KL-regularized `J` at :41–47. The Gibbs closed form and Z at :52–59 are a sum over 𝒴.
- Calibrated `J(r,π;π_cal)` at :92–96. `J⋆ = max_π` at :99–102. α > 0 at :113.
- Linear reward at :146–153: ‖φ‖₂ ≤ 1 and r⋆ = ⟨φ,θ⋆⟩.
- Algorithm at :182–203. The loop runs over t = 0,1,…. Each round samples x∼ρ and y₁,y₂∼π^{(t)}(·|x), and gets an oracle label.
  π^{(t+1)} is the argmin of −∑_{s=1}^{t} log σ(·) + αβ E_{ρ,π_cal}[log π − log π_ref].
- Theorem (:208–215): assume ‖θ⋆‖ ≤ r_max and ‖θ^{(t)}‖ ≤ r_max for all t. Then, w.p. 1−δ,
  ∑_{t=1}^{T}[J⋆(r⋆;π_cal) − J(r⋆,π^{(t)};π_cal)] ≤ Õ(e^{2r+r/β}√(κdT)), with the printed α and κ = sup π_cal/π_ref.
- My reconstruction agrees with CHECK §0. The round-0 sample is discarded, π^{(1)} comes from the empty dataset, and
  π^{(t)} uses the comparisons of rounds 1..t−1.

## Findings

1. **Algorithm and data model: faithful.**
   - `roundKernel k h ω = ρ(x) π_k(y₁|x) π_k(y₂|x) σ(r⋆(y₊) − r⋆(y₋))` with `π_k = gibbsPolicy(sel(vpoData h k))`.
     `vpoData h k` lists `compRecord (h j)` for j < k.
   - Lean round k (0-indexed) is the source's π^{(k+1)} = argmin over D^{(k)}. This matches :190/:196.
   - The outcome encoding is correct. `o = true` gives σ(r(y₁) − r(y₂)). `o = false` gives σ(r(y₂) − r(y₁)) = 1 − σ(r(y₁) − r(y₂)).
     For y₁ = y₂ each branch has weight ½.
   - The kernel depends only on h j for j < k (`roundKernel_congr`), so the model is causal.
   - `vpoTrajWeight` is a genuine probability: `vpoTrajWeight_nonneg` and `vpoTrajWeight_sum` (∑ = 1, Traj.lean:97).
     I checked both.

2. **The selection rule subsumes printed runs: confirmed, with one caveat on tie-breaking.**
   - I machine-checked the dataset-level part in `<reviewer probe folder>/CriticProbe.lean`, theorem `critic_subsumption`. Take any partial
     rule `printed : List → Option θ` that returns a ball θ whose Gibbs policy is an `IsVPOMinimizer` of the printed objective
     over all full-support policies (the `RlhfPrinted712` definition). It extends, through `exists_ballSelection`, to an
     `IsBallSelection` rule that agrees with it wherever it is defined.
   - The trajectory-level transfer is not formalized. Trajectory weights depend on `sel` only at the datasets that are reached.
     So on every trajectory where the printed iterates exist in the ball, the printed run and the Lean run coincide. This is the
     docstring's informal argument, and it is correct.
   - Caveat: the argument needs the printed argmin's tie-breaking to be a deterministic function of the dataset. A function of
     earlier iterates is fine, because those are functions of prefixes of D. The objective is NLL (convex in θ) minus
     αβ E log Z (concave in θ), so it is not convex and ties are possible. Randomized or external tie-breaking is not covered.
     See R1.

3. **Regret notion: faithful.**
   - `vpoRegret = ∑_{k<T}[optCalValue − calValue(roundPolicy k)]`, which is the source's ∑_{t=1}^{T}.
   - `optCalValue` is sSup over all `IsCondPolicy` (closed simplex, 0 log 0 = 0). `optCalValue_eq` (Gibbs.lean:155) proves
     it is attained by the Gibbs policy (IsGreatest). It therefore equals the source's max at :99–102, with no junk sSup value.
   - Regret per round is ≥ 0.

4. **κ: faithful.**
   - `vpoKappa = ⨆_{(x,y)} π_cal/π_ref` is over a finite type.
   - X is nonempty because ∑ρ = 1, and Y is nonempty because π_ref rows sum to 1. So the ⨆ is a genuine max, not the
     empty-sup 0.
   - It matches :214, which also takes the sup over x with ρ(x) = 0. `vpoKappa_bound` gives π_cal ≤ κ π_ref.

5. **Hypotheses, five-bin table** (expanded binders of both Props, which are identical):

| Binder | Bin | Source |
|---|---|---|
| X Y Fintype | RULED-as-disclosed restriction (ii) | ρ general at :21; Z a sum over 𝒴 at :59. C44 / CHECK §2 |
| d, `0 < d` | TYPING | ℝ^d at :148 |
| T, `1 ≤ T` | TYPING | regret ∑_{t=1}^{T} at :211 |
| ρ ≥ 0, ∑ρ = 1 | SOURCE | x∼ρ at :190 |
| `IsPositivePolicy π_ref` | TYPING | log π_ref at :196, κ at :214 |
| `IsCondPolicy π_cal` | SOURCE | calibration policy at :92 |
| ‖φ‖ ≤ 1 | SOURCE | :151 |
| 0 < β | SOURCE | :47 |
| 0 < r_max | SOURCE | :210 |
| ‖θ⋆‖ ≤ r_max | SOURCE | :210 |
| 0 < α | SOURCE | :113. Generalizes the printed α, disclosure (iii) |
| 0 < δ | TYPING | "probability 1−δ" at :211 |
| `IsBallSelection … sel` | RULED-as-disclosed correction (i) | iterate norm hypothesis at :210 + C44 |

   Counts: SOURCE 8, TYPING 5, disclosed restriction/correction 2, **EXCESS 0**.
   - No `δ < 1` is assumed. For δ ≥ 1 the claim is trivially true, which is harmless.
   - The ‖θ^{(t)}‖ bound for t = 0 is unused, as in the source.

6. **Bounds: transcribed exactly.**
   - The Statement.lean bounds are B′ = 2log(2T/δ) + 2d log⌈2rT√d⌉₊ + 4, Γ = (e/(e−1))(2d log(1+T/d) + log(2/δ)) and
     K = 2κe^{4r+2r/β}.
   - They agree with the docstrings and with `vpo_regret_both` (Main.lean) term by term.
   - The local-route bound is (e^{4r/β}/(4β))(16r² + 16e^{4r}(B′+4rα))Γ.
   - Coercions: I checked them with `#print` under `pp.coercions`/`pp.numericTypes` (CriticProbe.out). `↑T / ↑d` is real
     division, `↑⌈2 r ↑T √↑d⌉₊` is a cast of a real ceiling, and `↑T * B′ / α` is (T·B′)/α.

7. **Junk values: none exploitable.**
   - ⌈2rT√d⌉₊ ≥ 1 by `one_le_gridM`, so its log is ≥ 0.
   - log(2T/δ), log(2/δ) and log(1+T/d) are real logs. Negative values only occur when δ > 2, where the claim is trivial.
   - α, β and e−1 are all > 0.
   - KL uses π_ref > 0, and 0·log 0 = 0 is the correct convention.
   - log π in `vpoObjective` is evaluated only at Gibbs policies, which are positive.
   - sSup is attained (finding 3), and ⨆ is over a finite nonempty type (finding 4).

8. **Proof spot checks: all correct.** I re-derived each step by hand. Lean has also checked all of them.
   - Gibbs variational lemma (L1): `row_value_le` and `calValue_gibbs`.
   - L3 `vpoObjective_gibbs`: the Z terms cancel in the likelihood, and the cal term equals −αJ⋆ using ∑π_cal = 1.
   - Hellinger (`sq_sub_le_two_hellinger`): (p−q)² ≤ 1−BC² ≤ 2(1−BC).
   - σ' lower bound: (1+w)²/w = w + 2 + 1/w ≤ E + 2 + 1/E ≤ 4E for w ∈ [1/E, E], which gives 1/(4e^a).
   - Inverse Lipschitz 16e^{2c}: by the MVT.
   - Adaptive product lemma L8: `Fin.snoc` induction, with the kernel depending on j < k and the factor on j ≤ k.
     Markov and the finite union bound follow.
   - E₁: `lrFac_mean` (mean 1 under the true BT law), union over grid × rounds, giving δ/2.
   - E₂: e^{(1−e⁻¹)u − X} supermartingale, giving δ/2.
   - Grid: side 2r/M with M = ⌈2rT√d⌉₊, so the cell diameter is ≤ √d·2r/M ≤ 1/T. The representative is chosen inside the ball
     (`gridRep_norm_le`).
   - Elliptical potential: det update `det_gramMat_succ`, det(V₀) = 4^d, `log_det_le_of_posSemidef` (eigenvalue AM–GM),
     tr = 4d + ∑‖v‖², X ≤ 1 from λ = 4 and ‖d‖ ≤ 2, then x ≤ 2log(1+x).
   - Final probability: weight·(1 − 1_{bad₁} − 1_{bad₂}) ≤ weight·1_{good}, summed with ∑ weight = 1.

9. **Local-curvature route: re-derived, with the same constant.**
   - Let π = π_r, g = r − s, m = E_π g, and suppose |g| ≤ G. Then exactly
     β log Z_s − (E_π s − βKL(π‖π_ref)) = β log E_π e^{−(g−m)/β}.
   - Use e^x ≤ 1 + x + (x²/2)e^{|x|} (`exp_le_quadratic`) with |g−m| ≤ 2G and E(g−m) = 0, then log(1+y) ≤ y.
     This gives ≤ e^{2G/β}/(2β)·Var_π g, and Var_π g = ½ pairDisp (`var_eq_half_pair`).
   - With G = 2r (because |⟨φ,θ−θ⋆⟩| ≤ 2r), the bound becomes e^{4r/β}/(4β)·pairDisp. This is the CHECK §4(b) constant.
   - The rest of `round_bound_local` matches CHECK §4(b) steps 2–4. It uses `pairDisp_le_gram_mul`; the reversed optimism
     J⋆(θ_t) − J⋆(θ⋆) ≤ 4r via `calValue_sub_le`; and E₁ gives c_H S ≤ B + 4rα. The `+1` in B′ is absorbed via
     G ≤ 16r² + 16e^{4r}(B+1+4rα).

10. **Non-vacuity: confirmed.**
    - Part (a), `∃ sel, IsBallSelection …`, is inside both Props and is proved, so (b) is not vacuous over an empty class.
    - CriticProbe (C) builds an instance with X = Unit, Y = Bool, d = 1, T = 5 that satisfies every hypothesis.
    - The κ bound is nontrivial: at the tuned α it is sublinear in T. The local bound is O(d² log² T) at fixed α
      (logarithmic regret), so it cannot follow from the trivial bound Regret ≤ T·max-gap.

11. **Statement-index conventions: met.**
    - Statement.lean imports only `Thm712Wip.Defs`. That imports `Formalization.Ch7Rest.RlhfPrinted712`, which contains
      definitions only (I grepped it: no theorem), plus Mathlib.
    - The Props are self-contained and do not refer to any theorem type.
    - StatementProofs applies the export `vpo_regret_both` + `exists_ballSelection` and keeps one conjunct of the export's
      conjunction. The export concludes more, which is allowed.
    - No library signature is weakened.

12. **Compile and axioms: re-elaborated by the critic.**
    - Command: `bash scripts/lean-local.sh <file>`, foreground, one at a time, no `-o`.
    - Each of the 14 modules exited 0 with no errors, warnings or `sorry`, in this order: Defs, Elementary, Gibbs,
      GibbsBounds, Adaptive, Elliptical, Grid, Traj, Confidence, Concentration, Regret, Main, Statement, StatementProofs.
      Logs are in `<reviewer probe folder>/elab-*.out`. Main and StatementProofs were checked from source, and each upstream module
      was also re-elaborated from source, so stale oleans are ruled out.
    - `AxiomProbe.lean` exited 0. `Thm7_12_corrected_holds`, `Thm7_12_corrected_local_holds`, `vpo_regret_both` and
      `exists_ballSelection` all depend on [propext, Classical.choice, Quot.sound] only.
      Output: `<reviewer probe folder>/elab-AxiomProbe.out`, sha256 `eee34bf0…678e`.
    - grep finds no sorry, admit, axiom, native_decide, implemented_by or opaque.
    - CriticProbe.lean (`c2a996cc…735df`) exited 0. Its output CriticProbe.out is `6b9be44d…4a5e`.

13. **Docstring honesty: acceptable.**
    - Disclosures (i)–(v) are present.
    - "Neither proved nor refuted" is stated in both entries.
    - "π_ref with full support" matches `IsPositivePolicy`, which also requires normalized rows.
    - The local entry marks its rate claims as informal.
    - Two wording gaps remain (R1, R2).

14. **Integration notes for the lead (not defects).**
    - Generic names now live in `StatisticalRL.Ch7Rest.Rlhf`: `ev`, `dvec`, `dz`, `nll`, `cH`, `union_bound_sum`,
      `exp_le_quadratic`, `sq_wsum_le`, `adaptive_prod_le`. The namespace currently also holds only `RlhfPrinted712` and
      `VPOIllPosed712`, so nothing clashes today. Re-check after renaming the modules into `Formalization/Ch7Rest/`.
    - AGENTS.md requires the COVERAGE row and the C44 addendum in the same change as the statement entry.

## Required edits

- **R1 (required, docstring only, `Thm7_12_corrected` difference (i); inherited by `_local`).** After "This covers every printed run
  whose iterates exist with ‖θ^{(t)}‖ ≤ r_max", add: "(when the printed argmin's tie-breaking is a deterministic function of the
  dataset; this subsumption is an informal remark, not part of the formal statement)".
- **R2 (recommended).** In difference (v), mark "which at the tuned α is O(e^{2r+r/β} d√(κT)·log)" as "(informal arithmetic,
  not formalized)", as the local entry already does.
- **R3 (optional).** In the setting paragraph, cite `vpoTrajWeight_sum`/`vpoTrajWeight_nonneg` as the proof that the trajectory
  weights form a probability distribution.

No change to any Prop body, hypothesis or bound is required.
