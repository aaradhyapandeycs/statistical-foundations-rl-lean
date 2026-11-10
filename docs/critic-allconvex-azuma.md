# CRITIC — M8a′ step 1 (Azuma route, check fix F6)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review for the all-convex Theorem 7.11 route, not a source result: no COVERAGE row, statement-index entry or named-result change follows from it. Reviewed: Azuma bridge (M8a′ step 1), `Formalization/Probability/PathAzumaBridge.lean`, `Formalization/Ch7Rest/TDInferenceAzuma711.lean`. Planning notes cited below (route plan, M5a design and design check, M6a interface note) are local and not published; the route plan check is public as [critic-allconvex-p0.md](critic-allconvex-p0.md). Probes are local scratch files (`<local probe>`).

Critic: independent (not the builder), 2026-11-09.
Under review: `Formalization/Probability/PathAzumaBridge.lean` (338 lines),
`Formalization/Ch7Rest/TDInferenceAzuma711.lean` (504 lines).

## Verdict: ACCEPT WITH FIXES

The mathematics is correct and the exports are what F6 step 1 needs. All fixes are integration or
documentation items. None changes a statement.

## Evidence (commands actually run)

- `bash scripts/lean-local.sh Formalization/Probability/PathAzumaBridge.lean`: no output (clean, no
  warnings).
- `bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferenceAzuma711.lean`: no output (clean).
- `bash scripts/lean-local.sh <local probe>`: clean.
  - The probe imports `Formalization` together with both modules, so no name collision arises on
    import.
  - It contains the builder's probe plus the critic additions below.
- Every Lean process started only when `pgrep -x lean | wc -l` was below 2. I ran one at a time and
  never invoked lake.
- `#print axioms`: all 15 exports depend only on `[propext, Classical.choice, Quot.sound]`.
- A grep for `sorry`, `admit`, `axiom`, `set_option`, `native_decide` and `implemented_by` in both
  files: no hits.
- Fully qualified names are unique.
  - `prodWeight`, `prodProb`, `DependsBelow` and `IsBoundedMartDiff` sit in
    `StatisticalRL.Probability.PathAzuma`.
  - The TD names sit in `StatisticalRL.Ch7Rest.TDInference`.
  - The only near-namesake is `prodProb_mono`, versus the existing `pathProb_mono` in
    `TDInferencePlugin711`. They are different names.
- Critic probe additions (all compile):
  - `linStepSeq η₀ k = stepSize η₀ (k+1)` and `pathWeight = ∏ tupleProb` both hold by `rfl`.
  - **F6 instantiation on instance G.** With δ = T⁻³ (T ≥ 2), `pathProb_exists_le_abs_tdError_le`
    gives P(∃ k ≤ T, s : |Δ_k(s)| ≥ transient_k + C√(2K_A η_{k+1} log(2T³))) ≤ (T+1)·|S|·T⁻³.
  - The Rademacher ±1 instance of `sum_mul_exp_le_of_centred` (the exponent constant ½ is sharp).
  - The builder's `gMartInc_ne_zero`: the increment is genuinely nonzero on instance G, which has
    Γ_true ≻ 0. So the martingale is not the zero sequence.

## Reconstruction

### (1) Hoeffding/Azuma on the finite product law: correct

**Resampling identity.** The map (ω, x) ↦ (ω[k↦x], ω k) is an involution. Together with
`prodWeight(ω[k↦x])·p(ω k) = prodWeight(ω)·p(x)`, it gives E g = E Σ_x p(x) g(ω[k↦x]).
- This identity uses only `Σp = 1`.
- It does not need p > 0, so zero-probability tuples are harmless.

**Filtration.** `DependsBelow n f` means f is a function of the coordinates `< n`.
- Adapted: d_k ∈ DependsBelow(k+1).
- Centred: for every ω, `Σ_x p(x) d_k(ω[k↦x]) = 0`. This is E[d_k | F_{k−1}] = 0, because
  coordinate k is independent of the coordinates `< k`. The quantifier over *all* ω, including those
  of probability zero, is stronger than needed but is satisfied here.

**Inductive step.** S_n ∈ DependsBelow(n), so S_n is invariant under updating coordinate n. That gives
E e^{tS_{n+1}} = E[e^{tS_n} · Σ_x p(x) e^{t d_n(ω[n↦x])}] ≤ e^{t²c_n²/2} · E e^{tS_n}.
- Hoeffding's lemma is applied to the centred finite law q = p, f = d_n(ω[n↦·]), with |f| ≤ c_n.
- It goes through the convex chord e^{tf} ≤ cosh(tc) + (sinh(tc)/c)f and then cosh ≤ e^{t²c²/2}.
- The case c ≤ 0 is handled, since then f ≡ 0.
- Exponent t²Σc²/2: ✓.

**Chernoff.** Take λ = r/v. Then −r²/v + r²/(2v) = −r²/(2v) ✓. The two-sided bound comes from `neg` ✓.

**Radius.** r² = 2v·log(2/δ) gives 2e^{−log(2/δ)} = δ ✓.
- `δ ≤ 1` is used only for log(2/δ) ≥ 0, and δ ≤ 2 would suffice. This is harmless.

**Union bound.** Proved by induction over `Finset` ✓.

### (2) TD decomposition: correct

Re-derived from `tdIter`/`tdStep` through `tdStep_sub_value_eq` and `tdError_succ`:
Δ_{t+1} = (I − e_tA)Δ_t − e_t(ξ_{ω t} + (A_{ω t} − A)Δ_t), with e_t = stepSize(t+1).

Variation of constants with G_{m,t} = L_{t−1}⋯L_m (`linKernel`, `linKernel_succ`) gives
Δ_k = G_{0,k}Δ_0 − Σ_{j<k} e_j G_{j+1,k} v_j for k ≤ T.
- In the inductive step, the new summand j = k has G_{k+1,k+1} = I ✓.
- The old summands pick up L_k on the left ✓.
- The transient G_{0,k}(V₀ − V^π) is deterministic, with no ω ✓.

**Adaptedness.** `tdError … j` depends on the coordinates `< j` (`tdError_congr`, by induction on
`tdIter`). The vector v_j = ξ(ω j) + (A_{ω j} − A)Δ_j therefore depends on the coordinates `≤ j` ✓.
The weights e_j·G_{j+1,k} are deterministic ✓.

**Centring.** Under resampling of coordinate j, Δ_j is unchanged.
- Σ_x p(x)ξ_x = 0 (Bellman, `sum_tupleProb_mul_noiseVec`).
- Σ_x p(x)A_xΔ = AΔ (`sum_tupleProb_mul_sampleA`), so the linMartVec part has mean AΔ − AΔ·Σp = 0.
- Both pieces vanish ✓.
- The proof commutes the finite sums over x and s′ correctly through the deterministic G(s, s′).

**Boundedness.** The pathwise bound is ‖Δ_j‖_∞ ≤ D = tdPathBound, which needs 0 ≤ η₀ ≤ 1.
- |ξ| ≤ B.
- |(A_xΔ)(s′)| = |Δ(s′) − γΔ(s″)| ≤ (1+γ)D.
- |(AΔ)(s′)| = μ(s′)|Δ(s′) − γ·E[Δ]| ≤ (1+γ)D.
- So ‖v_j‖_∞ ≤ C = B + 2(1+γ)D ✓.
- B2 gives ‖G_{j+1,k}v‖_∞ ≤ p_{j+1,k}‖v‖_∞.
- Hence c_j = e_j·p_{j+1,k}·C ✓. It is deterministic, as Azuma requires.

### (3) Variance proxy `sum_sq_mul_contrProd_le`: correct

The recursion is ν_{k+1} = (1 − ae_k)²ν_k + e_k² ✓, using `contrProd_succ_top`.

**Late phase (k ≥ t₁).**
- (1 − ae_k)²ν_k ≤ (1 − ae_k)·B·e_k. This needs B·e_{k+1} ≥ B·e_k − aB·e_k² + e_k².
- By slow variation, e_k − e_{k+1} ≤ (a/2)e_{k+1}e_k ≤ (a/2)e_k².
- So it suffices that 1 ≤ aB/2, which is `haB : 2 ≤ aB`, true because B ≥ 2/a ✓.

**Early phase (k ≤ t₁).**
- Σ ≤ k·E² ≤ t₁E² = (t₁E²/e_{t₁})·e_{t₁} ≤ (t₁E²/e_{t₁})·e_k, by antitonicity ✓.

**Constant.** K_A = 2/a + t₁η₀²/e_{t₁}, where t₁ = ⌈(2/(aη₀))³⌉ + 1 and e_{t₁} = η₀(t₁+1)^{−2/3}.
- So K_A = O(a⁻¹ + η₀·t₁^{5/3}). That is large in (aη₀)⁻¹ but free of T and k ✓.
- The schedule facts all come from the existing `linStepSeq_facts`, so no new hypotheses are added.

### (4) Fit to F6: yes

F6 step 1 asks for P(|Δ_k(s)| > C√(η_k log T)) ≤ T⁻³ with a variance proxy ≲ η_k. The delivered
radius is C·√(2K_A·stepSize(k+1)·log(2/δ)), plus the transient p_{0,k}‖Δ₀‖_∞.

**Indexing.** stepSize(k+1) = e_k is the step of the update Δ_k → Δ_{k+1}.
- This is disclosed in the docstring ("η_{k+1} = e_k").
- For k ≥ 1, η_{k+1} ∈ [2^{−2/3}η_k, η_k]. So the bound is the F6 bound, up to constants, and it is
  in fact slightly stronger.
- In step 2 the truncation of the summand (A_{ω k} − A)Δ_k (0-based) uses exactly the radius at index
  k. No re-indexing is needed.

**Failure probability.** With δ = T⁻³, log(2/δ) = log 2 + 3 log T. The union bound gives
failure probability ≤ (T+1)|S|T⁻³ ≤ 2|S|T⁻² for T ≥ 1. I checked this on instance G.

### (5) Hidden hypotheses and non-vacuity: none found; non-vacuous

- The hypotheses are 0 < η₀ ≤ 1, 0 < μmin ≤ μ(s), k ≤ T and 0 < δ ≤ 1. These are the standing
  hypotheses of the 7.11 library, and all are discharged on instance G.
- The set events use `≤ |…|` (≥ radius), which is the stronger form.
- The increment is nonzero on G (`gMartInc_ne_zero`).

## Fixes (R = required before integration, F = advisory)

- **R1.** The modules are not yet imported from `Formalization.lean`, so the repo axiom audit does not
  cover them. The lead must add both imports, run `python3 scripts/check.py`, and record ownership
  in `docs/PROGRESS.md`.
- **R2.** No source result is claimed. So no `Statements/Ch7.lean` entry and no change to
  `COVERAGE.md` / `named-result-status.json` should accompany the landing. Keep them listed as
  infrastructure.
- **F1.** The module doc of `TDInferenceAzuma711` says "`P(|Δ_k(s) − (G_{0,k}Δ_0)(s)| ≥ …)`". It
  would be clearer to state the indexing convention explicitly there: radius at stepSize(k+1) =
  η_{k+1}, versus F6's η_k.
- **F2 (cosmetic).** `prodProb_sqrt_le_abs_sum_le` could take `δ ≤ 2`. Not needed.

## Notes for M8a′ step 2 (E_T tail)

1. **Truncated summand.** Use m_k = T^{−1/2}·W_k·(A_{ω k} − A)Δ_k·1{‖Δ_k‖_∞ ≤ r_k}, per coordinate
   s, with W_k = −`linWeight T k` (deterministic).
   - The indicator depends on the coordinates `< k` (`tdError_congr`), so m_k(s) ∈ DependsBelow(k+1).
   - Centring follows from `sum_tupleProb_mul_sampleA` exactly as in `sum_tupleProb_mul_tdIncVec_update`,
     since the indicator is constant under resampling coordinate k.
   - `IsBoundedMartDiff` needs a *pathwise* bound for all ω. The truncation supplies it:
     |m_k(s)| ≤ T^{−1/2}·‖W_k‖_∞·2(1+γ)·r_k. Use the ∞→∞ operator norm, with K_β = `linWeightConst`.
2. **The good event.** The event {∀ k ≤ T, s : |Δ_k(s)| < r_k} is exactly the complement of the
   step-1 union event, with r_k = transient_k + C√(2K_A e_k log(2/δ)). On it, truncated = untruncated.
   The final bound is P(E_T large) ≤ P(truncated sum large) + P(bad Δ event), via `prodProb_mono` and
   `prodProb_biUnion_le`.
3. **Transient in the variance proxy.** Σ_k c_k² also contains T⁻¹K_β²·Σ_k p_{0,k}²·‖Δ₀‖². This is
   not proved here. Two options:
   - The simplest: prove `contrProd a e 0 k ≤ K′·e_k` (exp(−c k^{1/3}) ≤ K′k^{−2/3}) and fold the
     transient into the √e_k radius.
   - Alternatively, prove Σ_k p_{0,k}² ≤ K″ uniformly in T.
   Either option keeps Σc_k² ≲ T⁻¹·Σ_k e_k·log T ≲ T^{−2/3}·log T.
4. **Vector form.** The bridge is scalar. Get ‖E_T‖_∞ by a per-coordinate Azuma plus a union over s
   (`prodProb_biUnion_le`), which costs a factor |S|, or 2|S| two-sided.
5. **Choice of δ.** Choose δ = T⁻² (or T⁻³) in step 1 so that the bad-Δ probability is O(1/T) after
   the union over (T+1)|S|. Choose step 2's δ′ = 1/T.
