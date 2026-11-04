# Theorem 4.1 integration verification

Status: passed. This certifies the TD theorem milestone, not an entire chapter or monograph.

## Source and semantics

`chapters/generative_model_model_free.tex:204–224`, label `thm:policy-evaluation-TD`, with the learning-rate schedule at 179–187. The index definition is `StatisticalRL.Statements.Ch4.Thm4_1`; its proof is `Thm4_1_holds`. The actual export is `StatisticalRL.TemporalDifference.tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants`.

The endpoint uses exactly T independent row draws per state and the actual infinite-trajectory policy value. The proof of the full joint pushforward law and pointwise terminal-output equality transfers an internal padded experiment to the source experiment. Constants are quantified before all model parameters; the chosen witnesses are c₁=c₂=1/4 and c₃=max(4096, exp(4)/(log 2)^4). The positive-index schedule, initialization, δ∈(0,1), γ∈[1/2,1), and full ε∈(0,1/(1−γ)] range are retained. The standalone step-size issue C5 remains recorded; its missing inequality is derived from the main theorem's budget in this proof.

## Build and axiom evidence

- Command: `python3 scripts/check.py`, in a fresh project-only snapshot based on c157821fae7b88d5002e22ca75708e7d1c800417 plus the explicit TD release paths. Shared pinned dependencies were read without rebuilding or modifying them.
- Evidence run: `verification/20261104T025758885628Z/`. All **418/418 modules exited 0**; no module was skipped. The checker verified that every Lean source remained unchanged through the run.
- `Audit.lean`: **4820 project declarations passed** the transitive axiom audit, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
- Compiler: `Lean (version 4.27.0-rc1, arm64-apple-darwin24.6.0, commit 2fcce7258eeb6e324366bc25f9058293b04b7547, Release)`.
- Full manifest SHA-256: `4efcc949d3abf69f7050863139d465f21f2428b608f34be302f9c4f2937e4382`.
- Complete Lean source-hash map digest (sorted-key compact JSON, UTF-8): `cbe0a424c003a6d4fa189474dc82a9c08bd1c01802dcca9307469c4d4a5a7721`.
- A separate focused run passed 14 affected targets. The actual-export probe passed for the joint-law map, prefix and terminal iterate equalities, intermediate and exact-T accuracy exports, and the statement proof; each reported only the three permitted axioms.
- Actual-export probe SHA-256: `91cf517fbc99915c5fb09d2065b28a806a1b1092a1060b058111b7419b931b08`; output SHA-256: `3690c093eea0235e352869ab5835a212275070b45323848c042be7bd0679e362`.

Raw compiler receipts are local reproducibility evidence; the public source, pins and build command permit a fresh rerun. Independent reviews are [source correspondence](critic-td-full-accuracy-source-20261104.md) and [proof consumption](critic-td-full-accuracy-consumption-20261104.md). Their statements that integration was pending describe the review time; this later receipt supplies the completed gate. The older [403-module backfill report](statement-index-verification.md) remains bound to its own c157821 source version.

## Exact released Lean sources

| Source | SHA-256 |
|---|---|
| `Formalization.lean` | `558c6b4c412cac99edb669fbf1ebdc8a8a8ad6d6224b9f6fb5b0685fdd1248a0` |
| `Formalization/ModelFree/TDInitialErrorContraction.lean` | `2a95be0921d9262d45f0dc0e8a24de3ed7d18c8a53c2d42f08a450f884a1eb30` |
| `Formalization/ModelFree/TDSamplingDefinitions.lean` | `2d2280acdd8b244ffc8717c7120a9e2c86414282597a699233a1b662981a9db4` |
| `Formalization/ModelFree/TDSourceAccuracyExactSamples.lean` | `7afd0996fff921fdc91f22e53aad673e6485aa8dfffd472faf8d6b687e67f375` |
| `Formalization/ModelFree/TDSourceFinalAccuracyComposition.lean` | `3b764f48fe4f27c8c6c0ec320bd029eb43ceac8ed40b51269a79f3e8bc0b7fbb` |
| `Formalization/ModelFree/TDSourceFinalScalarArithmetic.lean` | `7e58e659c1a83b4b33e149e04aa04c077de5668f3602f8e99fc7bba8000a3992` |
| `Formalization/ModelFree/TDSourceFinalScalarBudgetBridge.lean` | `b10542da0532c8c9868643731f7770ad4d972673c6a820716152cc72849e88f6` |
| `Formalization/ModelFree/TDSourceFinalScalarBudgetConsumer.lean` | `dfe035f37dcb83af43406fa3cfcb1e321b874e6cf8b12aa66b92c3d42a0ad597` |
| `Formalization/ModelFree/TDSourceFirstFreedmanAssembly.lean` | `15dd0b646592e456c8337f3f318cf8e1b721d3bdd9f55270f008f6debdb962c5` |
| `Formalization/ModelFree/TDSourceFirstFreedmanComparisons.lean` | `a29ae10bee6e96d4f98f3dec3a64a01373e6b68e7808ea7ab269d1a656b81995` |
| `Formalization/ModelFree/TDSourceFirstFreedmanUnion.lean` | `223457e58b420df3a2822125ab1097044211e39bdeb683ef60c184f4a8f54eeb` |
| `Formalization/ModelFree/TDSourceFreedmanScheduleCaps.lean` | `5ceea08b8316c1c63c4e6d4435f1e1722cab71551d85cd296440f8e92ed72b7a` |
| `Formalization/ModelFree/TDSourceFullAccuracyUniversal.lean` | `1bcc96d2b7dd6af07196a404e30ba9169df2227ae754c317b9ff4880bce4f6d5` |
| `Formalization/ModelFree/TDSourceSamplingDefinitions.lean` | `c7a55219c10f2e4f76b317a199aead2115fd24dd1d80c3ee5b4a76e9cc136a63` |
| `Formalization/ModelFree/TDSourceSamplingProjection.lean` | `75b995e0bb0afd5520d6f8e31d2ecc8f2a184d24ed38d0fb6c2c682f770d3a99` |
| `Formalization/ModelFree/TDSynchronousSampling.lean` | `5020bee22055547ac5a7b013e1a8e2e307c243428b4d570c3478a1c2764e6bd4` |
| `Formalization/ModelFree/TDVarianceLemmaComposition.lean` | `48a16fd5c5c8adf37af4550032dfa1388058c3d27dc571492b8b4c541b90bdf1` |
| `Formalization/Statements/Ch4.lean` | `9e467e08dec8d5b33a79311d79bd17d7f51657d136c2ae939824dba8fac1fd96` |
| `Formalization/Statements/Ch4Proofs.lean` | `af79e1ab3fb474241d4030cb12acc4e113bcf61e36cec206ab925465b3d345b3` |
