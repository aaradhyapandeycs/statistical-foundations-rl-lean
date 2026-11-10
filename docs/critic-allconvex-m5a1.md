# CRITIC M5a-1 (all-convex Theorem 7.11 route) — 2026-11-09

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review for the all-convex Theorem 7.11 route, not a source result: no COVERAGE row, statement-index entry or named-result change follows from it. Reviewed: M5a-1 (Gaussian block independence and inverse-square-root telescope), `Formalization/Probability/GaussianBlock.lean`, `Formalization/Analysis/InvSqrtTelescope.lean`. Planning notes cited below (route plan, M5a design and design check, M6a interface note) are local and not published; the route plan check is public as [critic-allconvex-p0.md](critic-allconvex-p0.md). Probes are local scratch files (`<local probe>`).

Verdict: **ACCEPT** (no blocking findings; advisories A1–A4 below are optional for M5a-2/lead).

Under review (sha256 matches builder STATUS):
- `Formalization/Probability/GaussianBlock.lean` a84a6afe…e6a1 (214 lines)
- `Formalization/Analysis/InvSqrtTelescope.lean` 8f9480ea…55a (199 lines)

Spec: the M5a design (not published) §§2 (D1, D2), 4A (L1–L6), 4E (L23–L26), 7.2–7.3, as amended by the M5a design check (not published) R5, R7, R9.

## Evidence (critic's own runs, one Lean process, started only with < 2 running)
- `bash scripts/lean-local.sh Formalization/Analysis/InvSqrtTelescope.lean`: exit 0, 12 s, no output.
- `bash scripts/lean-local.sh Formalization/Probability/GaussianBlock.lean`: exit 0, 6 s, no output (no warnings).
- `bash scripts/lean-local.sh <local probe>` (imports `Formalization` +
  both modules): exit 0, 0 errors; all 17 exports `#print axioms` = [propext, Classical.choice, Quot.sound].
  (The first probe run failed on two critic-side proof slips in the probe itself; fixed, not library issues.)
- grep: no `sorry`/`admit`/`axiom`/`set_option`/`native_decide`/`implemented_by` in either file.
- Collisions: none of the 21 declaration names is declared elsewhere under `Formalization/`; the probe imports
  `Formalization` together with both modules without redeclaration errors. Neither module is yet imported by
  `Formalization.lean` (lead integration).

## (1) GaussianBlock / R5 lemma
- Signature of `integral_comp_blockOf_indep` is exactly the CHECK R5 signature (instance binders
  `[Fintype κ] [Fintype ι] [DecidableEq κ]` are the design's section variables).
- Re-derivation: ∫ G(blockOf w i, w) dγ = ∫_{w'} ∫_w G(blockOf(blockPw i w' w) i, blockPw i w' w) (L3, from L2
  measure-preservation + `integral_prod`, outer w′) = ∫_{w'} ∫_w G(blockOf w' i, w) (L6 + hind) =
  ∫_{w'} H(blockOf w' i) with H z = ∫ G z w dγ, = ∫ H dν (L4/L5). The Lean proof follows exactly this chain.
- L2 (`measurePreserving_piecewise_stdGaussianPi`): box preimage = product of two boxes; ∏_{P} ν(s c)·∏_{¬P} ν(s c)
  = ∏ ν(s c) using ν(univ)=1; checked via `Measure.pi_eq`. Correct and general (any `P`).
- L3 needs only `Integrable g` (weaker than the "bounded continuous" restriction suggested in CHECK); L5 needs only
  `AEStronglyMeasurable g` (correct: `integral_map` holds without integrability).
- Hypothesis adequacy for M5a: verified by a probe example in L18 shape:
  `G z w := φ (x + M *ᵥ z + R *ᵥ w)` with `φ` `ContDiff ℝ ⊤`, values in [0,1], and `R : Matrix ι (κ×ι) ℝ` vanishing
  on block-i columns (the `twinMat L (resSet e k)` situation, i ∉ resSet). Continuity of `uncurry G` follows from
  `hφ.continuous` and `Continuous.matrix_mulVec`; `C = 1`; `hind` is the L9 computation. Compiles. So the
  continuity/boundedness hypotheses are not stronger than M5a can supply for L18/L20/L21 (φ is C^∞ with values in
  [0,1]; pexp is a finite sum, applied per ω).
- No hidden hypotheses; non-vacuity: builder's sin·cos example (Fin 2 × Fin 1) and the critic's L18-shaped example.

## (2) InvSqrtTelescope
- L23: 4(1/a − 1/b) = 4/(ab(a+b)) with a=√j, b=√(j+1) ≤ √2·a, so ab(a+b) ≤ (2+√2)a³ < 4a³ (R7 constant correct).
  Proof uses only 1 ≤ a ≤ b and b² = a² + 1. Correct.
- L24: telescopes to 4(J^{-1/2} − N^{-1/2}) ≤ 4/√J (empty case N ≤ J handled). Correct.
- L25: reservoir size kept as ℕ `n - 1 - k`, cast once (R9 ✓). Reflection `sum_range_reflect` maps k ↦ j=n−1−k
  bijectively on range n; large-j part ≤ Aa·∑_{J≤j<n} j^{-3/2} ≤ 4Aa/√J; small-j part has ≤ min(n,J) ≤ J terms,
  each ≤ Ac. `hAc : 0 ≤ Ac` and `hAa : 0 ≤ Aa` are genuinely needed (not hidden: explicit, and the consumer's
  constants are products of nonnegatives). j ≥ J ≥ 1 in the first branch, so no j = 0 junk value is used.
- L26: with q = n^{1/4}, √n = q², J = r₀ + ⌈√n⌉ ∈ [q², r₀ + q² + 1]. Term 1 = K c₃ J/q³ ≤ K c₃ (2+r₀)/q since
  r₀ + q² + 1 ≤ (2+r₀)q² for q ≥ 1. Term 2 = 4KD/√J ≤ 4KD/q since √J ≥ q. Sum = (A₃B³/6)(c₃(2+r₀) + 4C_H(c√c)⁻¹)/n^{1/4},
  matching DESIGN §7.3 total. Correct.
- c = 0: Lean gives (0·√0)⁻¹ = 0, so Aa = 0; the theorem stays true (probe instance compiles) and the consumer simply
  cannot discharge `ha` unless costs vanish. Harmless; M5a has `0 < c` anyway. `hc : 0 ≤ c` is in fact redundant
  (for c < 0, √c = 0 so the inverse is 0 again) but harmless.
- `sum_range_le_quarter` composes L25 and L26 with `hJ` from `⌈√n⌉₊ ≥ 1` for n ≥ 1. Correct.

## (3) Hidden hypotheses / non-vacuity
None found. All hypotheses are explicit nonnegativity / positivity / the step-cost bounds themselves; each is
satisfiable (a ≡ 0, G constant, the builder's and critic's examples).

## Advisories (non-blocking)
- **A1 (M5a-2 friction).** L26's `Ac` is written `c₃ * (√√n)^3 / 6 * …`, while L21 will produce
  `sandwichConst ι 3 / ε^3 / 6 * …`. With `ε := (√√n)⁻¹` the consumer needs a `div_eq_mul_inv`/`inv_pow`/`inv_inv`
  rewrite; similarly L20's `(v * √v)⁻¹ * (moments ≤ A₃ (B/√n)³)` must be rewritten to
  `(c√c)⁻¹ … B³ · (j√j)⁻¹` via v = c·j/n (uses `Real.sqrt_mul`/`sqrt_div` with c, j ≥ 0). Fine as a consumer lemma;
  no change required here.
- **A2.** `hc : 0 ≤ c` in `quarter_arith`/`sum_range_le_quarter` is redundant; keep (signature is published contract).
- **A3 (integration).** Lead must add both imports to `Formalization.lean` and record ownership in
  `docs/PROGRESS.md` (builder notes this as not owned).
- **A4.** For M5b (pass 2, shell-localised integrands) the R5 lemma requires continuity; if M5b needs indicator-type
  integrands it will need a measurable variant (L3 + L5 already provide it with `Integrable`/`AEStronglyMeasurable`).

Probe: `<local probe>` (log `CriticProbe.lean.log`).
