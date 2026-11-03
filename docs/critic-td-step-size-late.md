# Independent review: corrected TD late-weight and combined bounds

Reviewed `.local/TDStepSizeLate.lean`, SHA-256 `19328664e1fd1dae04b4be67317533f24e4ae77f3343d5fbdace113b21b423c6`, with its exact dependencies `.local/TDStepSizeEarly.lean` (`5a22bf277da8eba2bf94f10163ab886a7c8582bd94ffe0b807adfbc7a56d3cfa`) and `.local/TDLearningWeights.lean` (`45cebbdcb5ff62d586b28932803ae727ec2f1d31bb814346c7e5886e3c19a59f`). Source: `source/upstream/tex/chapters/generative_model_model_free.tex`, schedule and weight definition at lines 180–193, 307–312, TD step-size statement at 317–327, and its proof at 2286–2320.

## Source/semantic review

PASS for the late branch and combined corrected statement as written. The standalone late theorem assumes `T≥2`, `0≤γ<1`, positive `c₁,c₂`, the source schedule on its actual finite prefix, `t≤T`, `k≤t`, the source time threshold `T/(c₂logT)≤t`, and the late case `t<2k`. It does not require the early branch's additional large-T contraction premise or `c₁c₂≤1/8`.

The late condition and nonnegative natural indices imply `k>0`. The previously reviewed finite-product bound gives `tdRateWeight≤η_k`; the schedule upper bound has positive `x=c₂(1−γ)k/log²T` and yields `η_k≤1/(1+x)≤1/x=log²T/[c₂(1−γ)k]`. The time threshold gives `T≤tc₂logT`, while `t<2k` gives `tc₂logT<2c₂klogT`. Combining them with positive `(1−γ)log²T` gives the desired upper bound `η_k≤2log³T/[(1−γ)T]`. The strict intermediate inequality entails the displayed weak conclusion. The conditions exactly encode the source range `t/2<k≤t`; no parity assumption is needed.

The combined theorem partitions all `k≤t` into the exhaustive alternatives `2k≤t` and `t<2k`. It keeps the large-T condition and `c₁c₂≤1/8` visible because its early branch uses them, and retains `t≤T` so both branches stay inside the finite schedule. The common premise `hlarge` is stronger than needed if only the late implication is selected, but it is explicit and valid for the combined source-facing helper. The standalone late theorem avoids that unnecessary premise.

## Fresh exact-source compile and axioms

The hash-pinned script `.local/audit-td-step-size-late-independent.sh` verified all three exact staged hashes, then rebuilt the weights, early, and late modules in dependency order into `.local/td-step-size-late-independent-audit`. Both compilation and the import probe exited successfully without diagnostics. `#print axioms` covered all 15 exports across the three modules; every declaration used only `propext`, `Classical.choice`, and `Quot.sound`.

## Limits

These helpers do not prove the printed standalone source lemma with its missing premises, and they do not show that the main TD theorem's sample-size budget discharges the added large-T condition. Nor do they prove the stochastic TD concentration/rate theorem. Production integration remains separate.

Production integration: the reviewed source body compiles in the project export with qualified imports; the Q-learning causality file has been given the production module name `QLearningCausality`. The full project check audited 2,755 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
