# Critic report: no-log infrastructure for Theorem 7.11 (independent critic, read-only)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review of `Formalization/Analysis/SignedDistanceConvex.lean` and `Formalization/TDInference/LeaveOneOutVector.lean`, groundwork toward the all-convex corrected Theorem 7.11 at the printed rate. Not a source result; no statement-index entry. Probes are local scratch files (`<local probe>`).

Integration note: both ACCEPT; finding 9 (the leave-one-out module header claimed a Euclidean cross term that is not exported) applied; findings 10–11 left for later stages.

Date: 2026-11-10. Files reviewed (sha256):
- Formalization/Analysis/SignedDistanceConvex.lean  841912a842ff3215114c09e51097cf4cadc9a64ba7bc247e5c03544002b5c42f
- Formalization/TDInference/LeaveOneOutVector.lean  8a6aa3f68bdb75facbb76bd803c6e5d920faaf6c0d774a30822ca41c79de2628

Evidence: scratch copies with #print axioms appended for every declaration,
<local probe> (34 decls) and ProbeLoo.lean (19 decls), compiled with
`bash scripts/lean-local.sh <file>` (exit 0, no errors/warnings; outputs ProbeSD.out, ProbeLoo.out).
All 53 declarations: [propext, Classical.choice, Quot.sound]. No sorry/admit/axiom/native_decide in either file.
Name collisions: none in Formalization/ (grep of every exported name); neither file imported by Formalization.lean yet.

## SignedDistanceConvex.lean -- ACCEPT

1. Convexity (any real normed space, C not necessarily closed) is correct. It uses the ball-witness
   representation sd(x) = inf{dist(x,c) - rho : closedBall c rho in C, rho >= 0}:
   `signedDist_le_of_closedBall_subset` (<= direction; s<0 case shows closedBall x (-s) in C hence
   infDist x C^c >= -s; s>=0, x notin C case uses the radial point c + (rho/d)(x-c) of the ball; both valid for
   any norm) and `exists_closedBall_subset_of_signedDist_lt` (>= direction; x in C, s<0: ball of radius -s <
   infDist x C^c lies in C -- this is the interior/complement part, correct). Convex combinations of balls in a
   convex set: closedBall(a c1 + b c2, a r1 + b r2) in C via the decomposition q = a(c1 + (r1/R)w) + b(c2 + (r2/R)w);
   correct, R=0 handled. Then epsilon-argument. No duality/inner product needed.
2. Lipschitz: IVT on the segment gives a point with both distances 0; correct for every set.
3. Degenerate cases: sd(empty)=sd(univ)=0; Lipschitz/convexity hold there (handled explicitly). Every lemma
   that would be false in a degenerate case carries exactly the needed nonemptiness hypothesis
   (e.g. t<0 identity needs C^c nonempty: for C=univ, sd=0 > t but every ball is in C). No lemma is vacuous.
4. t<0 identity: IsClosed is genuinely needed (C = open unit ball, x=0, t=-1: sd=-1<=-1 but closedBall 0 1 not in C).
   Consequence for the consumer: TDInferenceConvexAll711 uses the inner parallel set {y | closedBall y d in C}
   for arbitrary convex C; use the one-sided lemmas there (or pass to closure) -- an integration note, not a defect.
5. Shell identity matches the shell `cthickening d C ∩ cthickening d (interior C)ᶜ` of TDInferenceConvexAll711.lean:66,71.
6. Docstrings honest: "states no source result".

## TDInferenceLooVector711.lean -- ACCEPT (two optional docstring/API fixes)

7. Objects: xi_i = linSummand T i (omega i) depends only on omega i; D = scaledError - linPart;
   D^(i)(omega) = D(update omega i x*_i) with deterministic x*_i. pathWeight = prod_t tupleProb(omega t)
   (TDInference711Defs.lean:98), a product law, so D^(i) and W - xi_i are functions of omega_{-i}, hence
   independent of xi_i: the right leave-one-out object for a Shao-Zhang argument (deterministic replacement is
   allowed; the bounds hold for every family x*). looRemainder_eq_sub identifies D - D^(i) with looRemainder.
8. Expectations are sums against the true path law pathWeight (no surrogate law).
9. Constants: K_CS = K_beta B K_loo (3/2) sqrt(eta0), K_E, K_beta depend on M, pi, V0, mu_min, eta0, S only; T-free.
   Rate: sum_i T^{-1} sqrt(eta_{i+1}) <= (3/2) sqrt(eta0) T^{-1/3} checked.
10. Norm steps: sup <= l1 (norm_le_sum_abs_apply) and Euclidean <= l1 via sum of squares <= square of sum; correct.
    Constants S^2 for Euclidean/l1 and sup-norm cross term are loose but honest.
11. (minor, docstring) Module header line 32 says the cross term holds with "the same constant in l1 and
    Euclidean norm"; the l1 version is exported, the Euclidean one is not (it follows in one line from
    norm_toLp_two_le_sum_abs). Either add the Euclidean export or reword.
12. (optional API) The header claims D^(i) "does not depend on omega i" in prose only; a one-line lemma
    (invariance of D(update omega i x*) under update at i, via Function.update_idem) would make the
    independence input explicit for M3.
13. Downstream obligation (not a defect): the multivariate Shao-Zhang theorem is stated for standardized W;
    standardizing by Lambda_T^{-1/2} needs a T-uniform lower eigenvalue bound on linCov, not provided here.
14. Docstrings honest: "No source result is claimed here."
