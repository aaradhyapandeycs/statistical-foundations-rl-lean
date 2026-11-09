# Critic report: Theorem 7.11 (corrected), milestone M7 (Stein Berry–Esseen)

Public copy of the independent critic report; local paths removed. Probe and scratch files named below (`reviewer-probes/`, `builder-probes/`) were kept in private folders and are not published.

Critic: independent reviewer, not the builder. Date: 2026-11-09.

## Verdict: **ACCEPT**

There are no blocking findings. Recommendations R1–R3 are integration and ledger items. N1–N6 are interface notes for M8.

## Files reviewed (hashes match the builder's STATUS.md)

| File | Lines | sha256 |
| --- | --- | --- |
| `Formalization/Probability/SteinGaussian.lean` | 523 | `e2dbbb4e0b55d5403d5caf113175e47d492355123ca0919554658094995fdc16` |
| `Formalization/Probability/BerryEsseenStein.lean` | 775 | `1ca1cc1559dd16c5575104efd648ddb7991fb75bfe9e0efb749271f346e3c410` |

Both files are in namespace `StatisticalRL.Probability.Stein`. Their only imports are Mathlib and `SteinGaussian`; there are no TD imports, which satisfies the F5 genericity requirement.

## Compilation evidence (my own runs, one Lean process at a time)

1. `bash scripts/lean-local.sh Formalization/Probability/SteinGaussian.lean`: no output, so no errors and no warnings. 14.6 s wall.
2. `bash scripts/lean-local.sh Formalization/Probability/BerryEsseenStein.lean`: no output. 6.7 s wall.
   - The `.olean` files are newer than both sources (02:19:12 and 02:19:30, against 02:19:07 and 02:19:24).
3. `bash scripts/lean-local.sh reviewer-probes/Probe.lean`. Output is in `reviewer-probes/probe.out`; 49 s wall.
   - `#print axioms` on **all 112** `theorem`/`def` declarations of both files returns exactly `[propext, Classical.choice, Quot.sound]` every time. There is no `sorryAx`, and there are no errors.
   - The probe's `rfl` example checks the TD fit: `pexp (fun _ : Fin T ↦ tupleProb M π μ) F = ∑ ω, pathWeight M π μ ω * F ω`, using `TDInference711Defs`.
   - Its second example checks the Gaussian link: `(gaussianReal 0 1).real (Iic z) = stdCDF z`.
4. Source scan with grep for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque` and `set_option`: nothing found in either file.
5. Name collisions: none. `pexp`, `sumStat`, `looStat`, `ramp`, `stdCDF`, `steinSol`, `intervalInd`, `gaussianReal_real_Iic`, `lyapunov_pos` and `pexp_split` occur nowhere else in `Formalization/` or in the pinned Mathlib (`~/lean1/.lake/packages/mathlib`). Nothing else imports these modules yet.

## (1) Is the statement a genuine Berry–Esseen bound?

`berryEsseen_stein` (signature printed in the probe) states the following.
- **Setting.** `ι` is a Fintype, each `X i` is a Fintype, and `p i x ≥ 0` with `∑ₓ p i x = 1`. Each summand is mean zero: `∑ₓ p i x ξ i x = 0`. The variances sum to one: `∑ᵢ∑ₓ p i x ξ i x² = 1`.
- **Conclusion.** For every `z`, `|pexp p 1{sumStat ξ ≤ z} − (gaussianReal 0 1).real (Iic z)| ≤ 26 ∑ᵢ∑ₓ p i x |ξ i x|³`.
- `pexp p F = ∑_ω ∏ᵢ p i (ω i) · F ω` is exactly the expectation under the product law.
- `Φ` is Mathlib's `gaussianReal 0 1` measure of `Iic z`. It is tied to `stdCDF` by `gaussianReal_real_Iic`, which goes through `gaussianReal_apply_eq_integral` and `ENNReal.toReal_ofReal`, with no detour.
- The summands are genuinely independent and non-identically distributed: `ξ i` reads only the coordinate `ω i`.
- **Scope.** The result is for a finite product of finite laws. This is disclosed in the module docstring and in the theorem docstring.
- **TD use.** It suffices: with `ι = Fin T`, `X _ = Tuple State Action` and `p _ = tupleProb M π μ`, `pexp` is definitionally the `pathWeight`-weighted sum used by `lawProb` (machine-checked by the `rfl` in the probe). The TD linear summands `w_k(ω_k)` are exactly of the form `ξ k (ω k)`.

`berryEsseen_stein_of_var` assumes `σ > 0` and `∑ Var = σ²`. It concludes `|P(W ≤ z) − Φ(z/σ)| ≤ 26 β / σ³`, which is the correct scaling. `berryEsseen_rademacher` instantiates this with fair signs and gets `26/√n`. It is non-vacuous: the hypotheses are discharged by `norm_num`, so the main theorem's hypotheses are satisfiable.

## (2) Hidden hypotheses and junk values

- **Division by σ.** It occurs only in `_of_var`, which has the explicit hypothesis `0 < σ`. The rewrite `W ≤ z ↔ W/σ ≤ z/σ` uses `div_le_div_iff_of_pos_right`.
- **Division by δ = β in the concentration step.** `lyapunov_pos` proves `β > 0` from `∑ Var = 1`, so there is no junk at `δ = 0`.
- **Empty index or zero total variance.** `hvar : ∑ Var = 1` excludes both, so the theorem is vacuous only where it should be.
- **Large β.** In the case `β > 1/8`, the proof uses the trivial bound `|P − Φ| ≤ 1 < 26/8`, which is correct.
- **No extra regularity hypotheses.** The Stein identity `pexp_mul_eq_sum_loo` / `_resample` holds for *every* `g : ℝ → ℝ`. This is legitimate in the finite setting.
- **Indicator convention.** `1{W ≤ z}` is the closed half-line, which matches `Iic`.

## (3) Paper re-derivation

**Stein solution.** The solution is `f = N/φ`, with
- `N = Q(z)Φ(w)` for `w ≤ z`;
- `N = Φ(z)Q(w)` for `w > z`.

Its derivative:
- For `w < z`: `f′ = Q(z)(φ² + wΦφ)/φ² = Q(z) + wf = wf + 1 − Φ(z)`.
- For `w > z`: `f′ = Φ(z)(−φ² + wQφ)/φ² = wf − Φ(z)`.

So `steinDeriv = wf + 1{w≤z} − Φ(z)` is correct off `z`, matching `hasDerivAt_steinSol`.

The bounds:
- **`|wf| ≤ 1`.** Mills gives `wQ(w) ≤ φ(w)` for `w ≥ 0`, and the mirror bound for `w ≤ 0`. The cases use `Q(z) ≤ Q(w)` (w ≤ z, w ≥ 0) and `Φ(z) ≤ Φ(w)` (w ≥ z, w ≤ 0), and the remaining factor is ≤ 1. All four cases check out.
- **`0 ≤ f ≤ 5`.** For `|w| ≥ 1`, `f ≤ |wf| ≤ 1`. For `|w| < 1`, `f ≤ N/φ ≤ 1/(1/5)`, using `φ(1) = 0.2420 ≥ 0.2`. The proof's numerics (`π < 3.15`, `√(2π) ≤ 2.51`, `e^{1/2} ≤ 1.65`, `2.51·1.65 = 4.14 ≤ 5`) are fine.
- **`|f′| ≤ |wf| + |1{·} − Φ| ≤ 2`.** Correct.

**FTC across the kink (F4).** `steinSol_sub_eq_integral` uses `integral_eq_of_hasDerivAt_off_countable` with exception set `{z}`. `steinSol` is continuous because `continuous_steinNum` matches at `w = z` via `Continuous.if_le`. `steinDeriv` is interval-integrable as continuous + antitone − constant. This is sound, and it is exactly the F4 mechanism.

**Increment bound.** `|D(v+u) − D(v+t)| ≤ (2|v|+5)(|u|+|t|) + 1{z−max(u,t) ≤ v ≤ z−min(u,t)}`.
- The first term comes from `v(f(v+u) − f(v+t)) + uf(v+u) − tf(v+t)`, with 2-Lipschitz `f` and `|f| ≤ 5`.
- The indicator term is checked over all four sign cases.

**Concentration** (`pexp_intervalInd_sumStat_mul_le`). Take `g` = the ramp clipped at `c = (b−a)/2 + δ`, and `h(x) = |x| min(δ,|x|)`.
- `E[Wg(W)] ≤ c·E|W| ≤ c`, using `E W² = B² ≤ 1`.
- `E[Wg(W)] = Σ E ηᵢ(g(W) − g(W−ηᵢ)) ≥ E[1_A H]`. Each summand is ≥ 0 because `g` is monotone, and on `A` it is ≥ `h(ηᵢ)`; both cases of `abs_mul_min_le_mul_ramp_sub` check out.
- `H − m` is a sum of independent centred terms, so `Var H ≤ Σ E h² ≤ δ² B² ≤ δ²`, and therefore `E|H − m| ≤ δ`.
- `Pm ≤ E[1_A H] + E|H − m|`.
- `x² − |x|³/(4δ) ≤ h(x)`: for `|x| > δ` this is `|x|(|x| − 2δ)² ≥ 0`. Hence `m ≥ B² − β/(4δ)`.
- Result: `P(B² − β/(4δ)) ≤ (b−a)/2 + 2δ`. Correct.

**Leave-one-out concentration** (`pexp_intervalInd_looStat_le`).
- Use `η` = `ξ` with coordinate `i` zeroed, and `δ = β`.
- `sᵢ ≤ 1/4 + 2β`, since `x² ≤ 1/4 + 2|x|³` holds in both cases.
- So `B² = 1 − sᵢ`, and the bracket is `≥ 1/2 − 2β − 1/4 ≥ 1/4` when `β ≤ 1/8`.
- This gives `P ≤ 2(b−a) + 8β`. Correct, and it is the "repo's chosen constant" that F4 allows.

**Smoothing** (`abs_pexp_steinDeriv_sub_le`). `2(|u|+|t|)·E|W⁽ⁱ⁾| + 5(|u|+|t|) + [2(|u|+|t|) + 8β] = 9(|u|+|t|) + 8β`, using `E|W⁽ⁱ⁾| ≤ 1` and interval length ≤ `|u|+|t|`. Correct.

**Assembly to the constant 26.**
- **Representation.** `P − Φ = E f′(W) − E Wf(W)`.
- `E f′(W) = cᵢ` for every `i`, and `= Σᵢ sᵢcᵢ` because `Σ sᵢ = 1`.
- `E Wf(W) = Σᵢ Σ_y pᵢ(y)ξᵢ(y) E[f(V+ξᵢ(y)) − f(V)]`.
- **Integral form.** `P − Φ = Σᵢ Σ_y pξ ∫₀^{ξ} E[cᵢ − f′(V+t)] dt`.
- **Integrand bound.** `|E[cᵢ − f′(V+t)]| ≤ Σ_x p(x)(9(|ξ(x)| + |t|) + 8β) = 9mᵢ + 9|t| + 8β`, where `mᵢ = E|ξᵢ|`.
- **Per-term bound.** Each term is `≤ (9mᵢ + 8β)pξ² + 9p|ξ|³`.
- **Summing.** The total is `≤ 9Σ mᵢsᵢ + 8βΣsᵢ + 9β`.
- Chebyshev association gives `mᵢsᵢ ≤ E|ξᵢ|³`, so the total is `≤ 9β + 8β + 9β = 26β`.

All constants check out.

## (4) Adequacy for M8 (Chen–Shao, randomized concentration F5)

These blocks are available and reusable:
- the generic `pexp` algebra: `add`, `sub`, `const_mul`, `sum`, `mono`, `nonneg`, `abs`, `const`, `intervalIntegral`;
- independence via `pexp_split`, `pexp_resample`, `pexp_comp_coord` and `pexp_coord`;
- `sumStat` / `looStat` with `sumStat_dropCoord`;
- the second moments `pexp_sumStat_sq` and `pexp_looStat_sq`;
- the ramp lemmas, which are pointwise in real `a, b` and so can be used with ω-dependent endpoints;
- the concentration template;
- the increment bound for `steinDeriv`.

These blocks suffice as foundations, but F5 still needs the new lemmas N1–N5 below. None of this blocks M7.

- **N1.** Add a random-function Stein identity: if `g : (∀ i, X i) → ℝ → ℝ` and `g ω` does not depend on `ω i`, then `pexp (ξᵢ(ωᵢ) · g ω (W⁽ⁱ⁾ ω)) = 0`. This takes a few lines from `pexp_comp_coord` plus `hmean`. Chen–Shao Lemma 5.1 applies it with the ramp at endpoints `Δ₁⁽ⁱ⁾, Δ₂⁽ⁱ⁾`.
- **N2.** The ramp needs Lipschitz continuity in its endpoints, e.g. `|ramp a b δ w − ramp a′ b′ δ w| ≤ |a − a′| + |b − b′|` (or the clipped-ramp variant that Chen–Shao use). This is needed to pass from `Δ` to `Δ⁽ⁱ⁾`. It is not present.
- **N3.** Cauchy–Schwarz for products under `pexp` is not present: `pexp |FG| ≤ √(pexp F²)·√(pexp G²)`. Only `(E|F|)² ≤ EF²` exists. M8 needs it for `E|WΔ| ≤ ‖Δ‖₂` and for `Σ E|wᵢ(Δ − Δ⁽ⁱ⁾)|`.
- **N4.** For the variance step `|Φ(z/σ_T) − Φ(z/σ)|`, two Gaussian-side lemmas are missing:
  - `stdPDF ≤ (2π)^{-1/2}`, giving Lipschitz continuity of `Φ`;
  - a scale bound such as `|Φ(z/σ₁) − Φ(z/σ₂)| ≤ C|σ₁²/σ₂² − 1|`, via `sup_x |x|φ(x)`.

  `hasDerivAt_stdCDF` and `continuous_stdCDF` exist to build these from.
- **N5.** `pexp_intervalInd_looStat_le` assumes `β ≤ 1/8` and gives `2(b−a) + 8β`. Chen–Shao's randomized version gives `E|W(Δ₂ − Δ₁)| + 2Σ E|ξᵢ(Δ − Δ⁽ⁱ⁾)| + O(β)`. Clone the proof of `pexp_intervalInd_sumStat_mul_le`, with `c` now random: use `|ramp| ≤ (Δ₂ − Δ₁)/2 + δ` pointwise and keep `E|W|·…` as `E|W(Δ₂ − Δ₁)|`. Endpoints may come in either order, so guard `a ≤ b` (for example, use `Δ₂ = z + |Δ|`).
- **N6.** Statistic `T = W + Δ`. The sandwich `P(W ≤ z − |Δ|) ≤ P(T ≤ z) ≤ P(W ≤ z + |Δ|)` gives the comparison with `P(W ≤ z)` via `P(z − |Δ| ≤ W ≤ z)` and `P(z < W ≤ z + |Δ|)`. The closed interval in `intervalInd` covers the second set (it is an upper bound), which is fine.

## Recommendations (non-blocking)

- **R1 (ledger).** PLAN line 350 names the files `Probability/SteinNormal1D.lean` and `Probability/BerryEsseen1D.lean`. The builder used `SteinGaussian.lean` and `BerryEsseenStein.lean`. Record the actual names and the ownership in `docs/PROGRESS.md` when integrating.
- **R2 (integration).** Neither module is imported from `Formalization.lean` yet, so `scripts/check.py` and the repository axiom audit do not cover them. The lead should add the imports. My probe already shows a clean axiom closure.
- **R3 (docstring precision, optional).** The module docstring says that every finite family of independent finitely supported real random variables "has this form". That is true by taking product coordinates, but it is not a Lean theorem. Phrasing it as a remark is fine. There is no general Mathlib-measure version, and none is needed for Theorem 7.11.

No source-fidelity finding: M7 is generic infrastructure and makes no statement-index entry.

## Artifacts

- `reviewer-probes/Probe.lean` (axiom probe plus TD and Φ link examples)
- `reviewer-probes/probe.out`
