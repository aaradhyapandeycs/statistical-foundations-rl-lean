# Offline RL lower-bound domain review

## Scope and source snapshot

This review covers the offline-RL minimax lower bound labeled `thm:infinite-lwoer-bound` in `source/upstream/tex/chapters/offlineRL.tex` (SHA-256 `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4`) and its surrounding offline-RL setup. The cited file has one main offline-RL minimax lower-bound theorem; the earlier offline-bandit result at lines 456–471 is an upper bound.

## Degenerate dimensions

The literal lower-bound statement at `offlineRL.tex:2367–2402` already excludes the usual degenerate state/action counterexamples: it requires `S > 12`, and its hard instances each have exactly two actions. Thus a one-state or one-action counterexample does not refute this theorem. The construction at `offlineRL.tex:2459–2463` explicitly sets `A=2` and indexes its binary parameter by the `S−1` nonzero states; the packing at `offlineRL.tex:2520–2524` is built for that nondegenerate state set.

The general MDP preliminaries define finite state and action sets and a valid discount (`prelim.tex:42–54`), while the theorem adds the stronger bounds `γ∈[2/3,1)`, `S>12`, and `C⋆>2`. I found no concrete degenerate-dimension counterexample within the theorem's stated domain.

## Endpoint / accuracy-domain caveat

The theorem writes only `ε ≤ 1/(672(1−γ))`, without explicitly writing `ε>0` (`offlineRL.tex:2370–2374`). In the chapter's stated offline-RL goal, however, the intended accuracy range is explicitly `ε∈(0,1/(1−γ)]` (`offlineRL.tex:83–90`). The lower-bound analysis also assumes `224(1−γ)ε/γ ≤ 1/2` (`offlineRL.tex:2439–2445`); for positive ε this follows from the theorem’s upper bound and `γ≥2/3`. The hard-instance parameters `p,q` are defined by a perturbation proportional to ε and the following claimed ordering `p>q` relies on positive ε (`offlineRL.tex:2491–2502`).

So the chapter context gives a reasonable intended reading that excludes ε=0 and negative ε, but the theorem's local hypotheses do not repeat that lower endpoint. I found no concrete counterexample to the existential theorem at ε=0: the displayed construction degenerates there (`p=q`) and no longer proves the claim, but that alone does not falsify the theorem because it may admit a different hard family. Record this as a statement-scope omission / proof-construction gap if formalizing the theorem standalone, not as a verified false theorem. The clean source-facing repair is to state `0 < ε ≤ 1/(672(1−γ))` explicitly.

The sample size `N` is described as the number of iid dataset samples in the theorem (`offlineRL.tex:2375–2380`) and is naturally an integer sample count; no separate positivity hypothesis on N is needed to rule out a dimension-degenerate case. The theorem's construction and conclusions are explicitly conditional on the displayed sample-budget inequality.

## Conclusion

For this offline-RL lower bound, the state/action degeneracies are excluded in the literal theorem. The only basic endpoint omission found is the missing explicit `ε>0`; surrounding chapter scope supplies that intended restriction, but a standalone formal statement should include it. No compiler or production Lean files were used or modified for this review.
