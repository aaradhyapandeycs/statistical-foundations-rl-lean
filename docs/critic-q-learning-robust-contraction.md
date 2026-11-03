# Independent review: robust Q comparator and contraction

Reviewed staged sources:

- `.local/QLearningRobustComparatorDraft.lean`, SHA-256 `f4523b6f7400791447a3969c87be112c90f87c7eb64ba5a0ce9bbfc14ddfaa70`.
- `.local/QLearningRobustContractionDraft.lean`, SHA-256 `91de4ee4c14cb9a9f9d90bea6381bb8aadeadbc8ea348c4e1f39568568b7a574`.

The pinned source is arXiv:2610.41903v1. In `source/upstream/tex/chapters/generative_model_model_free.tex` (SHA-256 `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`), Lemma `lemma:Q-comparison-facts`, lines 1338–1374, defines the ball `eq:Q-comparison-ball`; the operators `eq:Q-comparison-operator-plus` and `eq:Q-comparison-operator-minus` are at lines 1401–1418; Lemma `lemma:robust-Bellman-contraction` and its proof are at lines 1420–1469. The underlying χ² definition `eq:defn-chi2` is in `source/upstream/tex/chapters/intro.tex` (SHA-256 `6bfa41c0bcb9df3aa613ebe2bce9a966caaa9942e6629d52dabee5e518d0c92a`), lines 232–235.

## Source fidelity and scope

`qChiSquared p q` sums `(q.prob x - p.prob x)^2 / p.prob x` over exactly the positive-`p` coordinates. This is the finite discrete expansion of the source's `∫(dq/dp−1)^2 dp`. `qChiBall` separately enforces the source condition `q(x)=0` wherever `p(x)=0`; this avoids giving zero denominators an invented totalized value. The nominal distribution is a feasible ball member whenever `ρ≥0`. The paper states `ρ>0`; allowing `ρ=0` is a benign extension, not a claim that the source's strict domain was stated that way.

`qRobustBellmanPlus` and `qRobustBellmanMinus` use the actual statewise maximum `qLearningValue`, the transition-row expectation image of that support-aware ball, and separate `+b` / `−b` reward shifts. Their equations agree with source `eq:Q-comparison-operator`. The two residual definitions have their correct opposite orientations: plus is robust fixed point minus nominal Bellman value; minus is nominal Bellman value minus robust fixed point. Their equation lemmas derive the corresponding `b + γ(sup−nominal)` and `b + γ(nominal−inf)` identities from a supplied fixed-point equation. These are conditional algebraic identities; the first module alone does not assert a fixed point exists.

The second module proves each expectation image nonempty and bounded, bounds the change in each row expectation by `‖Q−R‖` using the finite action maximum, then transfers that bound to its supremum and infimum over the same nonempty ball. This yields the source `γ`-contraction inequalities for both shifted robust operators. The bundled Lean result `ContractingWith M.discountConstant` also includes strict contraction factor `<1`, which follows from the standing `DiscountedMDP.discount_lt_one`. Banach contraction then proves actual existence and uniqueness of each fixed point; neither is assumed. The only extra operator-domain premise is `ρ≥0`, used to establish nonemptiness. The extension to `ρ=0` remains valid.

These files do **not** prove Lemma `Q-comparison-facts` parts (i) or (ii): there is no square-root variance deviation bound, χ² support/stability inequality, perturbed transition-kernel comparison, compactness/attainment result, selected extremizing kernel, shifted range/span bound, or Q-learning probability theorem. This review and compilation therefore certify only these staged definitions and deterministic contraction/fixed-point ingredients, not the full source result or production integration.

## Fresh staged compilation and transitive axioms

Both exact-hash sources were freshly compiled in dependency order to `.local/ql-robust-contraction-independent-audit-f4523b6f/`. The comparator source was compiled with `bash scripts/lean-local.sh`; the contraction source was then compiled using the pinned `.local/lean` executable with that output directory first in `LEAN_PATH`, so its unqualified staged import resolved to the freshly rebuilt comparator module. Project dependencies were imported from existing project artifacts and were not rebuilt.

All 16 exported definitions/theorems in the two target modules were probed. Each has only the standard transitive axioms `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom or unfinished proof appeared in the target sources.

## Production integration

The reviewed operator and contraction results are now integrated as `Formalization/ModelFree/QLearningRobustComparator.lean` and `QLearningRobustContraction.lean`. The declaration and proof bodies match the reviewed sources; imports and source-status comments were qualified or updated. The complete project check compiled 245 modules and audited 3,277 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The scope and remaining obligations described above remain in force.
