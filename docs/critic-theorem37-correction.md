# Theorem 3.7: proposed correction and derivation for independent review

**Status: proposed mathematical correction, with an explicit proof route and
constants below. This has not received an independent mathematical review,
an author ruling, or a Lean proof.** The original source statement and proof
remain unchanged. The derivation relies on standard finite-hypothesis Fano and
chi-square/total-variation inequalities, which are stated explicitly below.

## Source identity and original cited paper

The monograph's `theorem:azar` is in
`source/upstream/tex/chapters/generative_model_model_based.tex` lines 1438–1464,
SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
Its proof spans lines 1840–2173. The known-reward, finite global action-space
and stationary-policy conventions are in `prelim.tex` lines 31–45, 63–67,
and the Q definition is lines 114–123, SHA-256
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
The generative model supplies independent transition samples on queries and
known reward, model-based chapter lines 11–31.

The cited original is Azar, Munos and Kappen, [*Minimax PAC Bounds on the
Sample Complexity of Reinforcement Learning with a Generative Model*](https://chercheurs.lille.inria.fr/munos/papers/files/SampCompRL_MLJ2012.pdf),
Theorem 3 and Section 4.2. Its theorem concerns existence of a hard MDP class,
total sample budget `T`, sufficiently small ε, and failure parameter
`δ < δ₀/N` (where its `N` counts state-action pairs), not the monograph's
fixed `(S,A)` and constant 1/4 assertion verbatim. Its proof describes a
special layered family with `N=3KL` state-action pairs and state-dependent
single-action states. Its result does not by itself establish the precise
fixed-size correction below, the larger ε range, or the policy-loss statement.

## Two source-statement obstructions

- If `S=1`, each transition is forced. Because the reward table and γ are
  known, the single estimator `Q̂(s,a)=r(s,a)+γ max_b r(s,b)/(1−γ)` is exact
  for every admissible MDP and every data outcome; the reward-maximizing
  policy is also optimal. Thus both parts fail even when `A=16`, and choosing
  the universal constant smaller does not cure the issue; explicit feasible
  parameters for each positive constant are in `docs/critic-one-state-review.md`.
- If `A=1`, there is exactly one deterministic stationary policy and it is
  necessarily optimal, regardless of transitions or rewards. Hence part (i)
  fails for e.g. `S=16`, even though `SA≥16`. This is a separate obstruction;
  adding only `S≥2` cannot repair both parts. It does not refute part (ii),
  which may still require estimating the value of that unique policy.

## Proof defects in the monograph beyond size assumptions

1. The proof sets `M = 1+(S−1)(A−1)` as the **total** number of candidate
   models (lines 1896–1907), but applies at lines 2022–2033 the monograph's
   Lemma `lem:fano` with `M+1` hypotheses and denominator `M+1`. That lemma
   uses `M` for the number of alternatives beyond the baseline (prelim lines
   1123–1165). This is an index mismatch, not a valid direct application.
   A safe standard `K`-hypothesis form is

   ```text
   average testing error ≥ 1 − ( (1/K) Σ_j KL(P_j || P_0) + log 2 ) / log K.
   ```

   It follows from Fano's entropy bound and mutual information bounded by the
   average KL to any fixed reference. When `K≥4` and the average KL is at
   most `(1/4) log K`, it gives error at least `1/4`.
2. In the constructed active state, a good action returns to that state with
   probability `q=p+α`, a bad action with probability `p`, and the absorbing
   state has value zero. Put `V₁=1/(1−γq)` and `V₀=1/(1−γp)`. The source's
   lines 1980–1984 claim `Q*(s,a_bad)=V₀`, but Q* takes the forced first bad
   action and follows an optimal policy **afterward**. Correctly,

   ```text
   Q*(s,a_good) = V₁,
   Q*(s,a_bad)  = 1 + γ p V₁,
   Q*(s,a_good) − Q*(s,a_bad) = γ α V₁.
   ```

   This gap need not exceed `2ε` as lines 2072–2077 and 2137–2146 assert.
   For example, `γ=0.9`, `ε=0.1` satisfies the source range; with its own
   `p` and `α`, the gap is approximately `0.03054 < 0.2 = 2ε`. The value
   gap `V₁−V₀` is larger (approximately `0.22901`) but is not the same
   as the source within-state optimal Q action gap.
3. The source's implication from small `‖Q^π−Q*‖∞` to identification of the
   correct actions is not proved by its displayed Q* action-gap alone: the
   source metric conditions on the *initial action* and then follows π.
   A valid direct loss calculation is given below. Moreover, lines 2093–2113
   call a decoder `M_{π̂}` without defining it when the policy selects wrong
   actions at several states or otherwise does not correspond to any candidate.
   Defaulting to the baseline makes a total decoder; only an implication of
   success, not the claimed equality of error events, is required.
4. The source allows only `a₀` at the absorbing state in its hard construction
   (lines 1871–1877 and 1959–1965), whereas the basic model has one global
   action set. Supply every global action at the absorbing state with the same
   zero reward and self-loop. There are then ties in the absorbing state, so
   decoders must compare active-state actions only. This padding does not
   change any informative sample row.

## Proposed corrected statement

For every pair of integers `S≥2`, `A≥2` with `SA≥16`, every
`γ∈[2/3,1)`, every `0<ε<1/[32(1−γ)]`, and every integer `N≥1` satisfying

```text
N ≤ (1/8192) log(SA) / ((1−γ)^3 ε²),
```

consider the source class of discounted MDPs on these fixed global carriers,
with known rewards and discount and `N` independent generative-model
transition samples per state-action row. For every (possibly randomized
estimation procedure whose output is a deterministic stationary policy)
policy estimator, there exists a model in the class for which
`P(‖Q^{π̂}−Q*‖∞ > ε) ≥ 1/4`. For every possibly randomized Q estimator,
there exists a model in the class for which
`P(‖Q̂−Q*‖∞ > ε) ≥ 1/4`. The `≥1/4` conclusion for Q estimation can in
fact be obtained as `≥3/8` by the construction below. The shared constant
is deliberately conservative. For part (ii) alone the proof below also allows
`A=1`, provided `S≥2` and `SA≥16`.

The assumptions `S≥2`, `A≥2` are necessary to exclude the two displayed
obstructions for the combined statement, but this document does not assert
that the remaining size condition `SA≥16` or the constant is optimal. This
is a proposed successor statement, not the original theorem or an approved
erratum.

## Common parameter arithmetic

Write `d=1−γ`, set the source's

```text
p = (4γ−1)/(3γ),       α = 32 d² ε/(9γ²),       q = p+α,
D = 1−γp = 4d/3,      V₀ = 1/(1−γp),      V₁ = 1/(1−γq).
```

The source parameter lemma at model-based lines 1747–1785 gives
`1/2 ≤ p < q < 1`, `1−p ≥ 2α`,
`α²/(1−p) ≤ 128 d³ε²`, and `V₁−V₀ > 2ε`. Explicitly,
`V₁−V₀ = γα/[D(D−γα)] > γα/D² = 2ε/γ ≥ 2ε`.
Moreover `γp=(4γ−1)/3 ≥ 5/9`. The strict ε upper endpoint is used to
ensure `q<1` and separation; γ may equal `2/3`.

## Part (i): repaired policy testing reduction

Take `S−1` active self-loop/absorbing states and one absorbing state, reward
1 at active states and 0 at the absorber. Every action at the absorber loops
there. For each active state give exactly one designated good action stay
probability `q`; all others have stay probability `p`, with the remainder
going to the absorber. The baseline designates `a₀` in every active state;
model `(j,k)` changes the designated action to `a_k` only at state `j`.
There are

```text
Kπ = 1 + (S−1)(A−1) ≥ 1 + SA/4 ≥ 5
```

models. Fix any deterministic stationary output policy that is wrong at
active state j. That state's value under the policy is `V₀`, while the
optimal state value is `V₁`. At the *forced good first action*,

```text
Q*(s_j,a_good) − Q^π(s_j,a_good)
  = γ q (V₁−V₀) > (5/9)·2ε > ε.
```

Thus `‖Q^π−Q*‖∞ ≤ ε` forces the entire active-state action pattern to
match the model's unique designated pattern; absorbing actions do not matter.
Decode a matching pattern to its model, and default to the baseline for any
other pattern. This is a total test, and testing error is contained in the
strict-loss event. Randomness in the estimator is included in its induced
sample/test distribution.

Relative to baseline, each nonbaseline sample law changes exactly two active
rows. The source's Bernoulli KL bound (lines 1995–2013) gives
`KL(P_j||P₀) ≤ 8N α²/(1−p) ≤ 1024 N d³ε²`. Under the proposed sample bound,
this is at most `(1/8) log(SA)`. Since `SA≥16`,
`log(SA/4)≥(1/2)log(SA)` and `Kπ≥SA/4`; hence the average KL is at most
`(1/4) log Kπ`. Standard Fano yields worst-case testing error ≥1/4, and the
success-to-decoding implication gives the asserted policy lower bound.

## Part (ii): different one-spike family and mixture test

The source's Q-estimation proof cannot use the incorrect action gap above.
Instead, retain the same active/absorbing states and rewards. In baseline
`P₀`, *every* active state/action has stay probability `p`. For each of the
`KQ=(S−1)A` alternatives `P_j`, choose one distinct active state/action row
and raise just that row's stay probability to `q`; all other rows remain p.
Use the fixed global action set, and let all absorber actions self-loop.
Each alternative is a valid source MDP. The baseline Q value at every active
state/action is `V₀`. In alternative j, the changed state/action has optimal
Q value `V₁`, hence its baseline-versus-alternative separation is
`V₁−V₀>2ε`. No pairwise separation among the alternatives is needed.

Let `Qmix=(1/KQ)Σ_j P_j` denote the uniform mixture **of sample-data laws**.
The samples of different queried rows are independent in the generative
model. If `L_j=dP_j/dP₀`, then `E₀ L_iL_j=1` for `i≠j`, while for the
changed row

```text
χ²(Bern(q) || Bern(p)) = α²/[p(1−p)] ≤ 256 d³ε²,
E₀ L_j² = (1 + α²/[p(1−p)])^N.
```

Consequently,

```text
χ²(Qmix || P₀)
 = ((1+α²/[p(1−p)])^N − 1)/KQ
 ≤ ((SA)^(1/4) − 1)/KQ
 ≤ 2/(SA)^(3/4) ≤ 1/4.
```

Here `p≥1/2`, the source parameter bound gives the constant 256, the proposed
`N` bound gives `N·256d³ε² ≤ (1/32)log(SA) ≤ (1/4)log(SA)`, and
`KQ=(S−1)A≥SA/2`. Cauchy–Schwarz gives
`TV(Qmix,P₀) ≤ (1/2)sqrt(χ²) ≤ 1/4`; thus any binary test has the sum of
its null and mixture-alternative error probabilities at least `3/4`, and at
least one of those two errors is `≥3/8`.

For an arbitrary Q estimator define a **total binary test**: output alternative
iff `max_(active s,a) |Q̂(s,a)−V₀| > ε`. Under the baseline, its false alarm
is contained in `‖Q̂−Q*₀‖∞>ε`; under each alternative, because that model's
changed coordinate differs from `V₀` by `>2ε`, failure to signal is contained
in `‖Q̂−Q*_j‖∞>ε`. Therefore one MDP in this finite family has Q-estimation
error probability at least `3/8`. This argument uses a baseline-versus-mixture
test, so it does not wrongly require the estimator to identify which spike was
planted. It also applies to estimators with internal randomization.

## Remaining work and confidence

The two source counterexamples, false Q* formula, index mismatch, and decoder
issues follow directly from the displayed models and source definitions; high
confidence. The proposed correction's derivation is complete at the paper
calculation level, but its statistical inequalities, constants, endpoint and
quantifier bookkeeping, and mathematical interpretation of the sampling
experiment require independent review. It is not a Lean proof, an approved
source correction, or a claim that the monograph's original proof works after
only adding size assumptions. In particular, a formalization still needs an
explicit sample-space/product law for all rows, valid Fano and chi-square
bounds, the two testing reductions, source trajectory `Q*` semantics, and a
new source/author ruling before it can be treated as a corrected source claim.
