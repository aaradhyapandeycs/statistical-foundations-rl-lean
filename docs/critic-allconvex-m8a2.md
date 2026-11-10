# Critic review: M8a' step 2 (TDInferenceRemainderTail711.lean)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review for the all-convex Theorem 7.11 route (second step of the remainder bound), not a source result: no COVERAGE row, statement-index entry or named-result change follows from it. Reviewed: `Formalization/Ch7Rest/TDInferenceRemainderTail711.lean`. Planning notes are local and not published; the route plan check is public as [critic-allconvex-p0.md](critic-allconvex-p0.md). Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT; at integration only docstring wording was changed (internal milestone and review-note labels removed). N1–N3 are informational.

Date: 2026-11-09. Target: Formalization/Ch7Rest/TDInferenceRemainderTail711.lean (548 lines).
Compile: `bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferenceRemainderTail711.lean` -> clean, no errors or warnings (30 s wall), run when <2 lean procs and no check_parallel.
Axioms: builder probe-out.txt shows the 9 exports on [propext, Classical.choice, Quot.sound]; probe non-vacuity examples produce no errors. No sorry/admit/axiom in file. No name collisions (all new names unique repo-wide).

## Verdict: ACCEPT (two cosmetic notes)

## Checks
1. Decomposition. `scaledError_sub_linPart_apply_eq_rem` (:171) is a coordinate restatement of the already-proved B3 `scaledError_sub_linPart_eq` (TDInferenceLinearised711.lean:163), with remMartVec k = linMartVec (omega k) (tdError k) for k<T (dif_pos). scaledError = sqrt T (Vbar_T - V^pi), linPart = T^{-1/2} sum Delta^lin_{t+1}; so E_T is the genuine difference, no new object. Correct.
2. Indexing. tdIter (t+1) uses omega t and stepSize(t+1); hence Delta_k depends on omega_i, i<k, and zeta_k = (A_{omega k}-A)Delta_k depends on i<=k. The radius r_k uses stepSize(k+1), exactly the step-1 radius in `pathProb_exists_le_abs_tdError_le` (Azuma711:469); the Bad set (:359) is syntactically that event, so the union bound is the step-1 theorem itself, not a re-derivation.
3. Martingale structure. adapted: DependsBelow (k+1) via remMartVec_congr + tdError_congr. centred: the indicator 1{||Delta_k|| <= r_k} is invariant under update at k (hDelta, :219), and the summand is a fixed linear image of linMartVec x Delta, centred by `sum_tupleProb_mul_mulVec_linMartVec` (sum_x p(x)A_x Delta = A Delta, sum p = 1). bounded: |.| <= T^{-1/2} K_beta 2(1+gamma) r_k using sup-norm `norm_linWeight_mulVec_le` (inf->inf, matching Pi norm) and `norm_linMartVec_le` (|A_x Delta|, |A Delta| each <= (1+gamma)||Delta||; uses mu(s)<=1). Correct.
4. Good event. On complement of Bad, for all k<T and s, |Delta_k s| < r_k, so ||Delta_k|| <= r_k and truncation is inactive (:374-383). Sup-norm attained coordinatewise via pi_norm_lt_iff contradiction; transient bounded by abs_linTransient_le. Correct.
5. Variance. r_k^2 <= 2N^2 p_{0,k}^2 + 4C^2 K_A L eta_{k+1}; sum p_{0,k}^2 <= 1 + K_beta/eta0 (new, proved via p^2<=p and p_{0,k+1}<=p_{1,k+1}); sum eta_{k+1} <= 3 eta0 T^{1/3}. Gives remVar with factor 12 and natCubeRoot T. Checked by hand.
6. Rate. delta1 = T^{-3}: log(2T^3) <= 3 log(2T); delta2 = T^{-1}: log(2T). With T = u^3: 2 v l <= u^{-2} l^2 2QX iff P + 36C^2K_A eta0 l u <= u l (P/log2 + 36C^2K_A eta0) -- true since u>=1, l>=log 2. Transient T^{-1/2} <= T^{-1/3} and multiplied by l/log2 >= 1. remTailConst (:431) is T-free. Union: (T+1)|S|T^{-3} + |S|T^{-1} <= 3|S|/T via (t+1)/t^3 <= 2/t. Correct.
7. Docstrings honest: "no source result is claimed"; rate stated as T^{-1/3} log T, explicitly not sqrt(log).

## Notes (cosmetic, non-blocking)
N1 (info) :359 Bad ranges over k <= T although only k < T is needed; costs an extra |S|delta1, already absorbed in the (T+1) factor. Fine.
N2 (info) :421 `add_one_mul_inv_cube_le` is a generic real-arithmetic lemma living in the TDInference namespace; consider moving to Analysis if reused.
N3 (info) The rate is T^{-1/3} log(2T); downstream consumers (Thm 7.11 Phase 2) must budget log T, not sqrt(log T), in the remainder; module doc already says so.
