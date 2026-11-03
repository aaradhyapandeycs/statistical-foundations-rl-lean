# Independent source check: robust chi-square singleton obstruction

Source-only independent review; no compiler run and no production edits.
Reviewed `docs/critic-robust-chi-square-lower-bound-degenerate-domains.md`, SHA
`10f3fe56d37952d2d3032a795af8c23756e01e170c6e62c3241e14ceb792530a`.
Pinned robust_RL.tex SHA
`95ce19a9bcdb275c9d4c04e4b20e836c8e5f0965426e955999817e82141196d9`;
prelim.tex SHA
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`;
chapters/commands.tex SHA
`78f6f8b5f086797d195dc72df6426df96faf632b3687723cfbe405fe411f7df3`.
All source hashes match the reviewed note.

Verdict: the singleton-action counterexample and its numerical feasibility are
correct under the printed domain. No mathematical error found. One section
reference needs correction: the theorem is **Theorem7.5**, label
thm:chi2-lower-bound, source lines461–480; the chi-square guarantees occur in
**subsection7.1.4** of Section7.1. The note's opening “Section7.4” is inaccurate.
The source inventory independently records theorem7.5 and subsection7.1.4.

## Singleton action

At A=1, the action probability simplex has a single element. Every stationary
randomized policy therefore equals the sole deterministic policy pointwise.
A data-dependent or randomized estimator cannot output a distinct admissible
policy; even allowing history-dependent randomization does not change its
sole available action.

For each nominal model separately, every admissible transition kernel in its
robust uncertainty set thus gives the same policy return across all policy
choices. Taking the infimum over that model's transition set preserves this
equality, and then maximizing over policies changes nothing. Hence
Vstar,sigma(s)=Vpi,sigma(s) for every state and every output policy. Averaging
under the adversary's chosen initial distribution mu also preserves equality.

Consequently each strict positive-epsilon failure event in the displayed
minimax expression is empty. Both risks are0, their maximum is0, and the
infimum over estimators is0. The estimator class is nonempty (the constant
unique policy). This does not depend on identifying the two models, their
rewards, sampling laws, their uncertainty sets with each other, or estimator
information. A robust-value trajectory bridge remains to be formalized, but
the source mathematical argument has no such extra premise.

The source robust definition uses nonempty finite probability rows and radius
sigma>0; the nominal kernel belongs to its own chi-square ball, so no empty
uncertainty-set pathology is involved. Robust Bellman duality is unnecessary
for the counterexample; equality is already true from the source infimum-of-
ordinary-policy-return definition at lines75 onward.

## Nonvacuous parameters and quantifiers

For arbitrary positive proposed universal constants c3,c4, take S=2,A=1,
gamma=3/4,sigma=1,N=1 and choose any positive epsilon with

`epsilon ≤ min(2c3,sqrt(320c4))`.

Both entries of the minimum are positive, so this is feasible. The source
accuracy bound is epsilon≤c3/(1−gamma)=4c3; our choice is stronger. Also
(1−gamma)^3=1/64 and1+sigma/(1−gamma)=5, so the displayed sample threshold is
exactly320c4/epsilon²≥1=N. The gamma lower endpoint is closed and sigma1 is
inside its positive range. Thus a proposed small positive c3 and arbitrary
positive c4 do not exclude this instance; choosing epsilon after those constants
is exactly the quantifier order needed to refute their universal claim.

The contradiction does not use epsilon0, N0, empty states or an unbounded
reward. Adding the omitted explicit positive-epsilon condition to the source
would therefore not repair the singleton-action issue.

## Singleton state and intended scope

The separate S=1 observation is also mathematically correct under known rewards:
there is only one transition distribution, every robust uncertainty set is that
singleton, and a known reward-maximizing action is robust-optimal. This uses the
source known-reward convention, whereas the A=1 obstruction does not need it.
The same parameter choices with S=A=1 are allowed by the literal display, which
has no SA≥16 restriction like Theorem3.7.

The robust chapter supplies no explicit S≥2 or A≥2 standing restriction; a local
search found none. Prelim.tex says it focuses on large dimensions and horizons,
but gives no quantified exclusion that can silently be inserted into this
theorem's “any(S,A,gamma,sigma,epsilon)” statement. If an author intended only
large/nondegenerate domains, that intention must be made explicit. The result
here refutes the displayed extension; it is not an author ruling about intended
scope or proof that a corrected theorem holds on every S,A≥2 instance.

The proposed minimal visible repairs S,A≥2 and epsilon>0 remove these two
examples, but sufficiency needs the cited nondegenerate lower-bound construction
and a separate source audit. No external citation proof was checked here.

## Editorial update binding

The lead replaced the two inaccurate “Section7.4” references with the
descriptive “chi-squared guarantees subsection”. Current reviewed note SHA-256:
`d640c3d4842909936a941f2612e5f3b2715649d1ba7076bca8fc27c1dcfa89bc`.
Reversing those two exact text substitutions mechanically reproduces prior
SHA `10f3fe56d37952d2d3032a795af8c23756e01e170c6e62c3241e14ceb792530a`.
Thus the substantive argument, feasibility calculation, source scope and
Theorem7.5 designation are unchanged. This final hash supersedes the initial
reviewed-note hash above; the noted editorial error is now corrected.
