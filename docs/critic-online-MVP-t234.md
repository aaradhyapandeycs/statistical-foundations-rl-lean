# Independent source review: MVP T₂/T₃/T₄ displayed estimate

## Review result

The reviewed T₂/T₃/T₄ displayed proposition matches the corrected source scope, and its application uses the same actual sequential episode experiment for all three bounds. The proposition’s event is a single intersection. Its displayed probability is the source’s non-strict lower bound, `1 − 4 log₂(K) δ′`.

The focused qualification passed: 14 canonical provider modules and 27 exports, followed by the three bridge/index targets and a 21-export probe. The final affected integration check also passed: 19 modules rebuilt and 807 verified modules reused, covering 826 modules in total. The whole-library axiom audit passed for 7,575 declarations with only the permitted standard axioms. This was an affected rebuild with verified reuse, not a fresh clean build.

## Statement and source correspondence

The index is `Formalization.Statements.MVP_T234_K2_corrected`, with application `MVP_T234_K2_corrected_holds` in `Formalization.Statements.Ch5Proofs`. The proposition retains the source’s displayed quantities and quantifier order: finite state/action spaces, positive horizon, `K ≥ 2`, a fixed environment and reset distribution, `δ ∈ (0,1]`, and the source large-sample condition `SAH·Iota ≤ K`. The confidence allocation is the corrected reciprocal allocation. It fixes `c₁ = 4` and `c₂ = 16`, as well as the source analysis parameterization.

The same committed greedy planner and actual sequential law govern the event and all three estimates:

- **T₂** is the sum of the selected empirical-planning-row bonuses, with the source zero-count completion and its `H` charge.
- **T₃** is the signed sum of true-transition expectations of the retained continuation value minus that value at the realized next state. The indexed next state is the actual transcript entry at `kH+h`; the deterministic bridge proves this lookup is in range, so its fallback is not used.
- **T₄** is each episode’s realized reward sum minus the true trajectory value of the same greedy policy frozen from the pre-episode history, evaluated at that episode’s sampled initial state.

The source’s three weak inequalities are preserved. The provider’s stronger probability bound is weakened to the printed non-strict form in the wrapper.

## Source corrections and scope

This corrected variant makes the source corrections visible:

- **C8:** the finite completion for an unobserved row and the associated `H` analysis charge are explicit.
- **C12:** `K ≥ 2` is retained for the logarithmic event.
- **C13:** the corrected power-of-two trigger is documented; the literal consecutive-count pseudocode is not certified by this result.
- **C16:** the confidence allocation uses the corrected reciprocal `δ′`.
- The policy uses one fixed deterministic maximizing tie rule.

The surrounding source subsection’s standing condition `K ≥ SAH·Iota` is retained on the displayed indexed statement. The three providers for optimism, T₂, and T₅ remain the stronger exports already reviewed; the wrapper does not weaken them by inserting a theorem premise into their types. It supplies the displayed standing regime and projects/rewrites their actual events to the source-facing statement.

## Modules and focused validation

The focused providers are the modules under `Formalization.Online.Regret.MVP.T34`, including `MVPJointSource` (SHA-256 `fa10b58956fd681d902d2c430177cc6ce68411dbc8b8286a2f18d068999ff902`) and `MVPT234SourceBridges` (SHA-256 `87ac3016f821a4b1b038ccc67e0fe6f1db8f6d383111cbc652420a6d45726b22`). The indexed files are `Formalization.Statements.Ch5` (SHA-256 `2f72e054bf25d8696b2ee18b3c0d9437d174648f10fedffb9cb92cf864cc7101`) and `Formalization.Statements.Ch5Proofs` (SHA-256 `2c3b804b6899dd014bb1b99a322d7115a78b0beaeb53d1396992df06e80fb849`). These are the source hashes in the reviewed candidate freeze.

The 14-provider run reported 27 exact exports, and the index run reported 21 exact exports. All reported only `propext`, `Classical.choice`, and `Quot.sound`. Earlier failed preparation/index attempts are excluded from this evidence; the reviewed index bytes are from the successful v5 run.

## Limits

This result covers the corrected T₂/T₃/T₄ displayed estimate only. The integration evidence is run `20261104T235938606339Z`, manifest SHA-256 `b3146bcb0a8810dbeaeea69aef78b2836b80f456fa51455757015fd3d9065472`, with 19 rebuilt and 807 verified reused modules. The reviewed source freeze contained 826 modules and 84,223 Lean lines. The named-result ledger remains 20 original entries with 10 corrected variants; no numbered entry was added for this displayed estimate. The full MVP regret theorem, source Lemma 5.14/decoupling, and the monograph-wide proof remain open.
