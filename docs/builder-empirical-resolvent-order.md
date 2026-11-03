# Order properties of the empirical policy resolvent

Source: `source/upstream/tex/chapters/generative_model_model_based.tex` lines 234–260 and 480–495, especially `eq:sum-I-minu-gammaP-expand` and `eq:upper-bound-Vl-Vhatl-00`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/EmpiricalResolventOrder.lean` proves, for the direct policy-evaluation algorithm's actual empirical stochastic matrix and every sample realization, that `(I−γP̂π)⁻¹` maps nonnegative vectors to nonnegative vectors, is monotone, maps the all-ones vector to `(1−γ)⁻¹1`, and satisfies `|(I−γP̂π)⁻¹f| ≤ (I−γP̂π)⁻¹|f|` entrywise. The proof of positivity uses the minimum of the actual inverse image and the stochastic-row Bellman equation; it assumes neither inverse positivity nor the desired statistical bound. The results include γ=0 and require only the sampling algorithm's `N>0`, the existing MDP discount assumptions, and nonnegativity/order of the input where stated.

These are deterministic ingredients for source step (i)–(ii). They do not prove the Bernstein event, apply it to the recursive auxiliary vectors, generalize the true variance-resolvent estimate, or prove the recursive error inequality or final theorem. See `docs/builder-policy-evaluation-recursion-plan.md` for the remaining derivation. No independent source or semantic review or integrated-export validation is claimed.

Validation: `bash scripts/lean-local.sh .local/EmpiricalResolventOrder.lean` passed. A separate exact-source temporary probe checked all four declarations and reported only `propext`, `Classical.choice`, and `Quot.sound`. Staged file SHA-256 `bed62174679d0a11f0778702e29f77a004d144a26d5e8f5b4661644ffafd0bf5`.
