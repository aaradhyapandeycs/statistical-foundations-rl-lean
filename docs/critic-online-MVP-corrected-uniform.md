# Independent review: corrected MVP uniform concentration statement

The corrected Chapter 5 entry covers onlineRL.tex 1670–1712. It states both uniform inequalities: the signed aggregate error is bounded by its positive-part sum, and that sum is bounded by the variance radius plus the additive term with coefficient 40000. The event is simultaneous over profiles, levels, and all coordinatewise vector sequences drawn from the corresponding family.

The formal family is deliberately broader than the source’s deterministic empirical-summary class. It may depend on the complete sample block at stages strictly later than the current stage. The profile index also uses a monotone ceiling cover that contains the source profile set. Each family retains the source size bound K+1, zero vector, and pointwise range [0,H]. The current-stage family represents the continuation at h+1; the generic statement does not impose a terminal-zero condition.

The level translation is j=l−2, so the batch contains the source coordinates 2^j through 2^(j+1)−1, and 2^l=4·2^j. The K=1 level event is empty. The assumption K≥SAH log₂K is retained through the equivalent finite profile dimension.

The confidence allocation is corrected to δ′=δ/(100 S²A²H²K²), as documented for source issue C16. This differs from the printed allocation 100δ/(S²A²H²K²), so the theorem is a corrected variant rather than a formal proof of the printed allocation.

The applying proof consumes the full expanded-product-law provider, then transfers its event by pointwise inclusion and measure monotonicity. The focused run compiled all 19 provider/index targets and the 31-export probe; every export reported only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` (some exports use a subset).

The affected integration check also passed: run `20261104T191201004806Z`, manifest SHA-256 `e74d4454e8b4417fb01f8facd3981ddd72673dfdf68523f362a546b4faffded3`, guarded driver SHA-256 `bbc894f2e2f8dd669eaab62fc22583d08cdebbe52b9079490425802fae2c7754`. It rebuilt 21 affected modules and verified reuse of 719 modules, for 740 total; the whole-project Audit checked 6,951 declarations with only the standard three axioms. This is an affected rebuild, not a new clean full-project check.

This result is limited to the corrected uniform concentration statement under the expanded product law. It does not yet prove the actual MVP learner’s batch-profile event law, couple the expanded event back to the online execution, or close the MVP regret theorem. The downstream actual-MVP construction uses the documented power-of-two trigger correction (C13); this generic concentration theorem does not certify the literal pseudocode.
