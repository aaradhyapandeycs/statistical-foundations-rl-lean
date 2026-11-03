# Source review: UCBVI's zero-visit bonus convention

**Scope:** source-level review of Algorithm `alg:main-ucbvi`, bonus (5.20), and the optimism proof's small-count case. This is not a Lean verification, an author-approved erratum, or a claim that the proposed convention is part of the printed algorithm.

## Finding

The printed update leaves the zero-visit case undefined. The algorithm initializes every count to zero, every Q estimate to `H`, and each empirical transition row to uniform (`onlineRL.tex:296–300`). After sampling a transition, it increments that row's count (`:313–318`), then its backward sweep loops over **all** state-action pairs and computes the bonus before applying the capped update (`:322–337`). The Bernstein bonus divides by `N_h(s,a)` in both terms (`:407–417`). Therefore rows still unvisited at the sweep encounter a zero denominator; initialization does not define their later update. The paper does not specify whether to skip that update or how to interpret its bonus.

A transparent proposed convention is: when `N=0`, retain `Q=H` and the initialized uniform empirical row; when `N>0`, use the printed bonus and capped update unchanged. This makes the intended small-count optimism branch well-defined without inventing samples or changing the observed trajectory. It remains a convention proposed to complete an undefined algorithm branch, rather than a literal consequence of the printed formula.

## Positive-count and small-count check

For positive `N`, the source update is

`min { r_h(s,a) + ⟨P̂_{s,a,h}, V̂_{h+1}⟩ + c₁ √(Var_{P̂}(V̂_{h+1}) log(1/δ′)/N) + c₂ H log(1/δ′)/N, H }`

by update (5.18a) and bonus (5.20a) (`onlineRL.tex:331–332`, `:407–417`). The proposed scalar update has this same positive-count formula, provided its arguments are instantiated by the source reward, empirical mean, empirical variance, and `L=log(1/δ′)`.

The optimism proof's Case 1 explicitly claims `Q=H` for `N_h^k(s,a)≤2` when `c₂≥2` (`onlineRL.tex:3321–3329`). The bonus's linear term is at least `H` at counts one and two when `L≥1`, since `c₂HL/N≥H`; nonnegative reward, empirical mean, and square-root term then make the capped value exactly `H`. The source lemma assumes `c₁≥4` and `c₂≥c₁²` (`:765–775`), hence `c₂≥16`, stronger than needed for this deterministic step. Its allocation `δ′=δ/(100S²A²H²K²)` (`:415–417`) gives `δ′<1/100` for positive integer dimensions and `0<δ<1`, so `L>1`.

At `N=0`, the positive-count argument does not apply. The proposed `Q=H` branch is what supplies the missing zero-count step.

## Indexing and remaining work

The algorithm increments `N_h(s,a)` before rebuilding the empirical row and running the all-row Q sweep (`:313–327`). Thus the updated row uses its **post-increment** count; consumers must not substitute the pre-episode count `N_h^k` for a visited row without accounting for the increment. The zero-count convention applies to rows untouched by the episode.

Formalization still needs to connect this scalar rule to the full backward recursion and greedy policy, derive empirical mean and variance properties from the normalized empirical/default rows and bounded continuation values, bind `L` to the stated confidence allocation, and prove that the corrected planner supports the intended optimism induction. Until those steps are completed, the correction is only a source-facing proposal and the optimism lemma is not established for the literal undefined zero-count formula.

**Source:** [Statistical Foundations of Reinforcement Learning: A Non-Asymptotic Perspective, arXiv:2610.41903v1](https://arxiv.org/pdf/2610.41903), Chapter 5, Algorithm 5.2, equations (5.18), (5.20), and the proof of Lemma 5.5.
