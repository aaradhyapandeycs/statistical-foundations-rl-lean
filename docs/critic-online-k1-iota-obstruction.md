# Independent source check: the `K = 1` W₁ endpoint

## Result and scope

The printed W₁ clause in the W₁/W₂/W₃ lemma at
`source/upstream/tex/chapters/onlineRL.tex:928–953` fails at `K = 1` when the
source's explicitly permitted uniform empirical row is used for an unseen
state-action-stage tuple. This is a source-level finite example, not a Lean
formalization and not a refutation of the main regret theorem. The main theorem
states `K ≥ 1` at lines 472–480 and may handle `K = 1` separately; the
reciprocal-count lemma alone explicitly assumes `K ≥ 2` at lines 640–644.

## Finite example

Take `S = A = H = 2`, `K = 1`, and `δ = 1/2`. Let the initial-state law put all
mass on state 0. Both actions have identical rewards and transitions. At
stage 1, reward is zero and every transition row is the point mass at
state 0. At stage 2, rewards are zero at state 0 and one at state 1; every
transition row may again be the point mass at state 0 (it does not affect the return).
Then `V₂*(0) = 0` and `V₂*(1) = 1`. The only realized stage-1 summand in W₁ is
the unseen row's uniform empirical expectation minus its true expectation:

`(1/2)·V₂*(0) + (1/2)·V₂*(1) − V₂*(0) = 1/2`.

The stage-2 summand is zero because `V₃* = 0`. Since the actions are cloned,
this value does not depend on the deterministic tie choice. Thus `W₁ = 1/2`
on every sample path.

The source defines `δ′ = δ/(100 S²A²H²K²)` at lines 415–418, so here
`δ′ = 1/12800`. But its logarithmic term at lines 726–733 is
`iota = 40000 (log₂ K)³ log(3SAH) log(1/δ′) = 0`. The claimed W₁ right-hand
side is therefore zero, regardless of the finite T₆ terms. The simultaneous
lemma's confidence is greater than
`1 − 12 S² A H K δ′ = 197/200` (lines 928–953), while its event is empty in
this example.

## Source convention and limitation

The text at lines 248–255 permits an unseen empirical row to be uniform, and
Algorithm `alg:main-ucbvi` initializes every empirical row uniformly at lines 288–300. Its
pre-episode notation is explicit at lines 571–573. Thus the W₁ summand above
is defined from the stated source convention. The bonus formula divides by
the visit count and does not itself specify the zero-count case; that is a
separate source-definition issue already tracked for the corrected
zero-count variant. This review does not silently choose a bonus extension
or claim that the unmodified algorithm is fully defined at zero count.

## Consequence

The W₁ auxiliary claim needs a visible `K ≥ 2` restriction (as in the
reciprocal-count lemma) or a positive logarithmic floor / separate endpoint
argument. This endpoint issue does not refute the main `K ≥ 1` regret result;
the latter can treat `K = 1` directly. No paper statement or Lean declaration
was changed in this review.
