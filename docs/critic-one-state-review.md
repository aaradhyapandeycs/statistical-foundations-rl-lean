# Independent source review: one-state case of Theorem 3.7(ii)

**Verdict: counterexample to the stated theorem under the source's known-reward model; confidence high.** This is an open source obligation, not an approved correction or a proof of a revised theorem. The analysis below applies to the version and source hashes in `source/provenance.json`; I made no Lean declaration or proof-status claim.

## Source and scope

- The authoritative version is arXiv:2610.41903v1, *Statistical Foundations of Reinforcement Learning: A Non-Asymptotic Perspective*. The file `source/upstream/tex/chapters/generative_model_model_based.tex` has SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`; `source/upstream/tex/chapters/prelim.tex` has SHA-256 `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`. Both match the provenance file.
- Theorem `theorem:azar`, lines 1438–1464 of the model-based chapter, requires `0 < ε < 1/[32(1−γ)]`, `γ ∈ [2/3,1)`, `SA ≥ 16`, and `N ≤ c_N log(SA)/[(1−γ)^3 ε²]` for a sufficiently small universal positive constant. In (ii), for **every** Q-estimator, it asserts the existence of an MDP with those fixed sizes on which error exceeds ε with probability at least 1/4.
- `prelim.tex` lines 31–45 defines finite state and action spaces, a stochastic transition kernel, and a deterministic `r : S × A → [0,1]` fully known to the learner a priori. Model-based chapter lines 11–31 describes transition-sample access and repeats that reward is known unless otherwise noted. The theorem does not state an exception. Consequently the estimator is allowed to take the given reward function as input, even if the adversarial MDP chooses a different reward function; it is one fixed rule applicable to every such input, not an estimator chosen after secretly seeing the unknown transition kernel.
- The general prose at `prelim.tex` line 59 says the monograph focuses on regimes with large S, A, and effective horizon, without giving a numerical lower bound on S. The theorem gives the explicit size condition `SA ≥ 16`; no additional `S ≥ 2` appears in its statement. The earlier policy-learning section (`generative_model_model_based.tex` lines 780–787) discusses `A ≥ 2`, but the counterexample uses `A = 16`, so it survives even if that condition is interpreted as applying to the lower-bound section. That section begins anew at line 1438. No earlier condition found excludes this one-state case.

## Estimator and contradiction

Take `S = 1`, with sole state `s`, and `A = 16` (in fact any finite `A ≥ 16` works). For every admissible MDP on these spaces and each action `a`, the only probability distribution on the singleton state space satisfies `P(s | s,a) = 1`. Write `r_max = max_b r(s,b)`, which the learner can compute from the known reward input. Define a single deterministic rule, ignoring its transition samples, by

```text
Q̂(s,a) = r(s,a) + γ r_max / (1−γ).
```

At the first step action `a` yields `r(s,a)`; at every later time the state is again `s`. Choosing a maximizing action thereafter gives value `r_max` at every subsequent step, and no policy can improve any per-step reward. Thus

```text
V*(s) = r_max/(1−γ),
Q*(s,a) = r(s,a) + γ r_max/(1−γ) = Q̂(s,a).
```

These equalities hold for **every** admissible reward function, every admissible transition kernel (there is only one), and every data outcome. Therefore `P_M(‖Q̂−Q*‖∞ > ε) = 0` for every `ε > 0` and every MDP of these sizes, contradicting the existential conclusion of (ii). Samples are deterministic singleton observations, which remain independent in the probabilistic sense; collecting them poses no admissibility problem.

The same case also challenges (i): choose a fixed deterministic tie-breaking rule for an action maximizing the known reward. It is optimal in every one-state MDP, hence `Q^π = Q*` for all initial actions. This observation is secondary to the requested review of (ii).

## Feasibility for every positive universal constant

The issue cannot be avoided by making `c_N` smaller. Given **any** `c_N > 0`, set

```text
S = 1,  A = 16,  γ = 2/3,  N = 1,
ε = min { 1/64, sqrt(27 c_N log 16)/2 }.
```

Then `ε > 0` and `ε ≤ 1/64 < 3/32 = 1/[32(1−γ)]`. Also `SA = 16`, `γ ∈ [2/3,1)`, and, since `ε² ≤ 27 c_N log 16 / 4`,

```text
c_N log(SA)/[(1−γ)^3 ε²]
  = 27 c_N log 16 / ε² ≥ 4 ≥ N.
```

Thus an integer, positive sample count satisfies all displayed hypotheses, no matter how small the fixed positive constant. More generally the exact estimator works for every `γ ∈ [2/3,1)` and every integer `N ≥ 1`, with sufficiently small positive ε satisfying the bound.

## Proof context and limits of this finding

The proof in the model-based chapter, lines 1844–1906, partitions the S states into `S−1` active states and one absorbing state and constructs `M = 1 + (S−1)(A−1)` hypotheses. At `S = 1`, the active set is empty and `M = 1`; the Fano step at lines 2022–2032 explicitly needs `M ≥ 4` and has `log M` in a denominator. Thus this proof construction cannot establish its claimed bound in the counterexample regime. This proof observation is supporting evidence; the exact estimator independently disproves (ii) under the stated assumptions.

An explicit extra restriction such as `S ≥ 2` would exclude this particular counterexample, but is not present in the theorem and is not asserted here to be sufficient for the full theorem or its proof. Other possible changes, including altering the learner's reward information, would change the problem and are not adopted. No author ruling or erratum was located in the source materials inspected; no silent repair is authorized.
