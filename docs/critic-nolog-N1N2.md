# CRITIC: N1 SteinPolyhedralConcentration.lean, N2 PolyhedralSeparation.lean (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of two infrastructure modules toward the all-convex corrected Theorem 7.11 at the printed rate: N1 `Formalization/Probability/SteinPolyhedralConcentration.lean` (randomized Stein concentration for polyhedral functions) and N2 `Formalization/Analysis/PolyhedralSeparation.lean` (polyhedral representation of convex sets on finite point sets). Not a source result by itself; consumed by `Thm7_11_corrected` ([end-to-end review](critic-711-sharp.md)). Probes are local scratch files (`<local probe>`).

Integration note: N1 ACCEPT-WITH-FIXES, N2 ACCEPT. Finding 1 applied (the `pexp_devSum_le` docstring now says there is no mean-zero hypothesis and that σⱼ is the uncentred root second moment; N1 sha256 is now 2cb738536cb1ced0735dcfbf3345bb5636e498c8b3a4bf6dbc37f618a081f356). Finding 2 resolved before integration (addendum). Finding 6 applied: both modules are imported from `Formalization.lean` through `TDInferenceConvexSharp711.lean`, so the axiom audit covers them.

Inputs: N1 sha256 750a0a65...d58ff (503 lines), N2 sha256 a6234171...0d31f (213 lines).
Commands: `bash scripts/lean-local.sh <file>` for each (N1 9.9 s, N2 2.3 s, exit 0, no warnings);
probe `<local probe>` (exit 0). `-o` to a scratch path is refused by
the launcher, so the probe used the builders' `.lake/build` oleans (mtime newer than sources; hashes
match the builder logs). No lake, no git, no edits outside the critic dir.

Axioms (probe, #print axioms): every main N1/N2 declaration -> [propext, Classical.choice, Quot.sound].

## Verdicts
- N1: ACCEPT-WITH-FIXES (docstring only; mathematics accepted).
- N2: ACCEPT (after namespace fix; see addendum).

## Re-derivations (refutation attempts failed)
1. A2. `fr_mul_sub_fr_mul_nonneg` has exactly the design hypotheses (a<=b, 0<=delta, t<=s, s'<=t).
   `three_quarters_sq_le_fr_mul_sub_fr_mul` drops a<=b and 0<=delta (derived from a<=r<=b, |s|<=delta):
   weaker than the design, so fine. Theorem A supplies exactly these facts (hts, hst, hsδ, htδ via
   subgradient + Lipschitz). Re-derived by hand: Q >= (r-a+delta)(s-t)+t^2 >= |s|(s-t)+t^2 >= (3/4)s^2.
2. A4. Hypotheses: product law (hp1), coordinatewise mean zero, `G (update ω i c) = G ω`. TD supplies
   these: G = fr(ai,bi)(φ(U_i))•vsel(U_i), invariance by `vsum_update_sub` + hai/hbi; for
   Di i ω = D(update ω i xs_i), invariance holds by update_idem. hp0 not needed (correct).
3. A5 pathwise: sum_sq_dotProduct_eq decomposition + |v_j v_k|<=1 is correct. Theorem B
   `pexp_devSum_le`: covDev is centred internally by the p-mean; `humean` derived from hp1; then
   E u^2 <= E f^2 <= delta^2 E xi_j^2; no hmean needed. Correct. σ_j here is the uncentred root
   second moment (= std under mean zero).
4. Theorem A matches design §5 verbatim (constants 4/3, 2, 1; no dependence on |𝓕|, T, or |ι|);
   λ any sign; m>=0 used only off-shell. vsel/qsel: only `qsel_mem` (ℓ¹=1) and `polyPhi_eq_qsel`
   (attains the max) are used; both hold for every maximiser, so the choice is irrelevant.
5. N2 `exists_polyhedral_repr`: iff on all of P, no closedness/measurability of C, ℓ¹=1, strict
   negativity on C∩P, positivity on P\C; Lipschitz (sup norm) and convexity proved. [Nonempty κ] is
   necessary (empty κ: no ℓ¹-unit vector). Interface: probe proves
   `polyPhi 𝓕 h x = 𝓕.sup' h (fun q ↦ ∑ j, q.1 j * x j - q.2)` by `rfl`, and N2's export feeds N1's
   `h𝓕1` directly.

## Findings
1. (fix, N1) `pexp_devSum_le` docstring says "For mean-zero summands" but the theorem has no
   mean-zero hypothesis; reword (centring is internal; σ_j is the root second moment).
2. (RESOLVED, see addendum) (fix-style, N2) top-level `namespace PolyhedralSeparation`; repo convention is
   `StatisticalRL.Analysis.*` (cf. SignedDistance, ConvexSmoothIndicator). Rename before integration.
3. (note) Triplicated ℓ¹/sup lemma: N1 `abs_dotProduct_le`, N2 `abs_sum_mul_le_sum_abs_mul_norm`,
   GaussianConvexShell's same-named lemma (different full names, no collision; ambiguity only if both
   namespaces are opened). N1 `norm_le_sum_abs` duplicates LooVector711 `norm_le_sum_abs_apply`.
4. (note) No name collisions found in Formalization/ or Mathlib for fr, vsum, covDev, devSum, polyPhi,
   qsel, vsel.
5. (note) Docstrings honest: both say infrastructure; no Shao–Zhang citation; no local paths.
   Optionally add "self-contained bounded-summand variant, not Shao–Zhang" to N1 header.
6. (note) Neither file is imported by Formalization.lean yet; axiom audit coverage follows on integration.

## Addendum (namespace change)
N2 re-reviewed at sha256 9034b4c7...638fa2 (213 lines): namespace now
`StatisticalRL.Analysis.PolyhedralSeparation` (lines 35/213); line count unchanged. Recompiled
(exit 0, no warnings); probe updated to full names, exit 0, all N2 axioms [propext, Classical.choice,
Quot.sound]; rfl interface and N2->N1 plug-in examples still pass. Finding 2 resolved; N2 ACCEPT.
N1 namespace `StatisticalRL.Probability.Stein.Polyhedral` follows the convention; generic names
(`fr`, `vsum`, `devSum`, `abs_dotProduct_le`, `norm_le_sum_abs`) are safe while namespaced but should
not be `open`ed alongside Mathlib/Matrix in consumers without care. No N1 namespace fix required.
