# Independent final audit: proposed Theorem 3.7 correction

**Verdict: the proposed replacement and its independent check pass this paper-level mathematical audit**, under their stated fixed-row product sampling experiment and measurable estimators, with the source-interpretation qualification below. In particular, the mixture χ² calculation, deterministic-policy Q loss, numerical constant `1/8192`, K-hypothesis Fano indexing, and estimator/model quantifier order are valid. This is not an author-approved erratum and does not establish a complete Lean theorem.

Audited files: `docs/critic-theorem37-correction.md` (SHA-256 `b5ec75348c5ecfc3e490c15408d8d6bb0c1710b6c2c66e54dfb5cdc197607067`); `docs/critic-theorem37-correction-independent.md` (`d739059ba9d7020096c68ca560492f1d904a2956d88144c7960b66c73ab12bd6`); source `source/upstream/tex/chapters/generative_model_model_based.tex` (`b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`); and `source/upstream/tex/chapters/prelim.tex` (`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`). Original Theorem `theorem:azar` is model-based chapter lines 1438–1464; its hard family and testing proof are lines 1840–2173. The source's actual Q definition is prelim lines 114–123, and its MDP and known-reward conventions are prelim lines 31–45 and model-based lines 15–31.

## Source interpretation and candidate scope

The proposed common domain is integer `S≥2`, `A≥2`, `SA≥16`, `γ∈[2/3,1)`, `0<ε<1/[32(1−γ)]`, and integer `N≥1` with `N≤log(SA)/[8192(1−γ)^3 ε²]`. Its fixed global action set, reward `1` at active states and `0` at the absorber, and all absorber actions self-looping satisfy the source's known deterministic bounded reward and MDP conventions. The random data consist of N independent transitions for each row, independent across queries. The candidate permits internal randomization of the estimator, while requiring every output policy itself to be deterministic stationary; it does not prove the corresponding lower bound for arbitrary randomized stationary output policies.

The proposal correctly notes that an `A=1` deterministic-policy obstruction exists **if** the theorem is read to allow `A=1`. However, the earlier policy-learning setup at model-based line 787 explicitly says `A≥2`. Its applicability as a standing restriction on the later minimax theorem is interpretive, since the theorem itself states only `SA≥16`. Consequently, the proposal's unrestricted statement that the A=1 example is an independent obstruction to the original part (i) should be read with that qualification. In contrast, the one-state known-reward counterexample also has `A=16` and remains valid even if the line 787 restriction carries forward. The suggested Q-estimation extension to `A=1` is a mathematically valid separate extension, not a claim that the preceding policy-learning setup permits it.

The numerical sample premise can be vacuous for some fixed ε because N must be positive; the theorem is still a valid implication. It is not universally vacuous: e.g. `S=2`, `A=8`, `γ=2/3`, `ε=10⁻³`, `N=1` satisfies the required upper bound (its right-hand side is about 9.14), as well as the strict accuracy range.

## Parameters and policy reduction

Set `d=1−γ`, `p=(4γ−1)/(3γ)`, `α=32d²ε/(9γ²)`, `q=p+α`, `D=1−γp=4d/3`, `V₀=1/D`, `V₁=1/(D−γα)`. Under the stated range, `1/2≤p<q<1`, `1−p≥2α` and

```text
α²/(1−p) = [1024/(27γ³)] d³ε² ≤ 128 d³ε²,
V₁−V₀ = γα/[D(D−γα)] > γα/D² = 2ε/γ ≥ 2ε.
```

Both denominators are positive and the inequality remains valid at `γ=2/3`. An active state has value `V₁` if its stationary policy chooses its unique q-action and `V₀` if it chooses a p-action. The Q loss of a policy that chooses the wrong stationary action is evaluated at the forced **good** initial action:

```text
Q*(s,a_good) − Q^π(s,a_good) = γq(V₁−V₀)
  > (γp)·2ε ≥ (5/9)·2ε > ε.
```

This is the correct source Q semantics: only actions after the forced first action follow π. It is distinct from the optimal Q action gap `γαV₁`, and the proposal does not rely on the source's incorrect bad-action equation. Small Q sup-norm loss therefore pins down each active action. A decoder matching the complete active-state pattern to its candidate, and defaulting to the baseline otherwise, is total. On the small-loss event it returns the correct candidate, so its error is contained in the strict-loss event; no equality of events is needed. Absorber action ties have no effect.

## Fano count and constant

The policy family consists of exactly `K=1+(S−1)(A−1)` hypotheses, including baseline, and `K≥1+SA/4≥5`. For each alternative relative to baseline exactly two rows swap p and q. The two KL terms have the correct orientation:

```text
KL(P_j || P₀) = N KL(Bern(q)||Bern(p)) + N KL(Bern(p)||Bern(q))
                ≤ 8Nα²/(1−p) ≤ 1024 N d³ε²
                ≤ (1/8) log(SA) ≤ (1/4) log K.
```

The last step uses `SA≥16`, hence `log K ≥ log(SA/4) ≥ (1/2)log(SA)`. The baseline contribution to average KL is zero. With a uniform prior on the **K total hypotheses**, standard entropy Fano and `I(J;X)≤K⁻¹∑ KL(P_j||P₀)` give average error at least `1−[I+log 2]/log K ≥1/4`, hence some model has error at least `1/4`. This is a standard K-hypothesis bound, not an application of the source lemma with K incorrectly treated as the number of alternatives. The source constructs `M=1+(S−1)(A−1)` total candidates but its displayed invocation at lines 2022–2033 uses M+1-style indexing; the candidate avoids that mismatch.

## Q estimation and mixture χ²

Use a different family: under baseline each active row has p; each of `K_Q=(S−1)A` alternatives changes exactly one distinct row to q. At its changed coordinate, optimal Q increases from `V₀` to `V₁`, a gap strictly above `2ε`. For p,q in `(0,1)`, all alternatives have likelihoods relative to the baseline product measure. Writing `L_j=dP_j/dP₀`, independence across distinct row samples gives `E₀[L_iL_j]=1` when `i≠j`, and independence within the affected row gives

```text
E₀[L_j²] = (q²/p + (1−q)²/(1−p))^N
          = (1 + α²/[p(1−p)])^N.
χ²((1/K_Q)∑P_j || P₀)
  = [(1 + α²/[p(1−p)])^N − 1]/K_Q.
```

No pairwise alternative Q separation is used. Since `α²/[p(1−p)]≤256d³ε²`, the proposed sample bound yields `Nα²/[p(1−p)]≤(1/32)log(SA)`. The displayed proof safely weakens this to `(1/4)log(SA)`. Since `K_Q≥SA/2`,

```text
χ² ≤ ((SA)^(1/4)−1)/K_Q ≤ 2/(SA)^(3/4) ≤ 1/4,
TV ≤ (1/2)√χ² ≤ 1/4.
```

The last χ² endpoint follows at `SA=16` from `2/16^(3/4)=1/4`. Therefore the null-error plus uniform-mixture alternative-error of any binary test is at least `1−TV≥3/4`. At least one is ≥3/8, and a mixture error ≥3/8 implies at least one constituent alternative error ≥3/8.

The test flags an alternative iff some active estimated Q coordinate is more than ε away from its baseline value. A baseline false alarm is included in baseline strict Q-error; under any alternative a missed signal is included in that alternative's strict Q-error by the `>2ε` gap and triangle inequality. Equality at the threshold is handled correctly. Thus, for every Q estimator, some fixed model in this finite family has strict error probability at least `3/8`, stronger than the candidate's requested `1/4`.

## Quantifiers, randomness, and Lean boundary

Both finite model families and the baseline reward/discount depend only on public parameters `(S,A,γ,ε)` and are fixed before choosing an estimator. Each statement has the required order `for every estimator, there exists a model`; it does **not** assert a single hard model works for every estimator. Procedures are measurable functions or probability kernels from data to outputs. An estimator's model-independent random seed can be appended to every sample law with the same distribution, preserving the KL/TV calculations and decoder reductions. A model-dependent seed or side information revealing the hidden transition model is outside the experiment. The generative sampling provision is the fixed N-per-row independent product experiment, not a proof for a different adaptive or total-budget experiment.

Existing Lean declarations such as `Formalization/Obstructions/HardMDP.lean`'s `optimalityFixedPoint_eq_hardQ`, `sourceHardValue_gap_gt_two`, and `sourceHardPolicy_loss_gt` support the two-state Bellman algebra. They do not establish the whole fixed-S/A experiment, Fano, mixture χ², the testing reductions, and quantifiers as one theorem. The paper-level derivation uses standard information-theoretic inequalities and the conditional-independence model explicitly; no new compiler claim or author ruling is made here.
