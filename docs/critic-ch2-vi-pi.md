# Independent review: Chapter 2 value and policy iteration

## Source and declaration

The source is the unlabeled Lemma 2.1 at `source/upstream/tex/chapters/prelim.tex:339–343`, read with the value-iteration and policy-iteration update definitions at `:319–336`. The source does not assign a LaTeX label to this lemma; none is invented here.

The indexed proposition is [`Lemma2_1`](../Formalization/Statements/Ch2.lean); its applying theorem is [`Lemma2_1_holds`](../Formalization/Statements/Ch2Proofs.lean). The focused source index uses fixed-point values. This is connected to the source's trajectory-value formulation by proved library results, not by additional assumptions in the proposition.

The VI clause quantifies over every initial `Q₀` and every `k ≥ 1`, and preserves the source contraction factor `γ^k`. The PI clause quantifies over every initial stationary randomized policy sequence and every deterministic action selector satisfying the maximizing condition at each update. It therefore permits all maximizing tie choices. It preserves the same `γ^k` factor and the initial-policy comparison. The finite nonempty state/action assumptions come from the MDP model; discount zero and all positive iteration counts are included.

## Semantic bridge and focused evidence

The fixed-point definitions are genuine constructions from proved existence and uniqueness results. The actual trajectory `Q` of each policy is identified with its policy fixed point, the greedy policy's trajectory `Q` is identified with the optimality fixed point, and the greedy policy is proved optimal. The wrapper applies the existing value-iteration and arbitrary-greedy policy-iteration convergence results. No fixed-point characterization, optimality claim, or convergence estimate is supplied as a premise of `Lemma2_1`.

The added definition-facing modules preserve the source definitions used by the index. `FixedPointDefinitions` depends transitively on its proved existence/uniqueness provider because the selected fixed points require that construction; the index does not import a VI/PI convergence theorem provider. The existing convergence providers retain their public signatures and proof bodies.

The focused dependency-closure run compiled 25 affected modules and a probe for nine actual exports, including the Ch2 convergence exports and trajectory-characterization/optimality exports. The status file SHA-256 is `95c1b57bc1d1ae34660a21238db027ae72898ffe105ecddaa3c94e45a6dcf2b4`; the probe source SHA-256 is `bc19ab840e3b23f5df4ff2727bba3cdb24c7479b28cb93859e2865fb528731fe`; the recorded probe log SHA-256 is `0a20a470536966f22237e094dd04b152fdb51992448d5610bdcfe4b4c662cb7f`. The exports report only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Scope

This review also rechecked the completed fresh project build against the frozen 913-source assembly. The guarded run rebuilt all 913 modules with zero project-artifact reuse and the final axiom audit passed for 8,162 project declarations. Run `20261105T030921935125Z` is bound by guarded-manifest SHA-256 `750510fd73526d1592be0e61dd64f468fc1b286f50012c44037a3a15ae05de81`; the full check log SHA-256 is `47235ef53612bb2f89d69f48b8edfdfba5ec83cb3dd5899b4dfdf6b372c1f2e0`. The manifest rehash matched all 913 frozen sources and their compiled OLeans, and all 447 bound source/evidence files and configuration pins rehashed correctly. The dependency cache path/size/mtime metadata was unchanged; this does not claim an OS-level byte seal for shared dependencies. This establishes the fresh project check for the frozen assembly, not whole-monograph completion.
