# Independent source review: corrected online regret telescope

**Scope:** source and statement review of the corrected pathwise UCBVI decomposition. This review does not claim the online regret rate or completion of Chapter 5.

## Source result and statement

The target is `lemma:decomdetail`, Lemma 5.6, at `chapters/onlineRL.tex:808–818`. The source’s four-term episode decomposition is at lines 849–858, and its fixed-optimal split is at lines 917–925. The pinned source file SHA-256 is `393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

`StatisticalRL.Statements.Lemma5_6_corrected` writes the complete one-episode inequality over arbitrary pre-episode observed stage tables and a realized state/action path, assuming the selected action maximizes its corresponding capped Q row at each stage. The summands are the source reward, backup analysis charge, empirical-row minus true-row continuation expectation, and true-row expectation minus realized successor value. `Lemma5_6_corrected_holds` applies the nonnegative telescope at (L=\log(1/\delta')). Its only sign conditions are (L,c_1,c_2\ge0), so the source parameter setting is included without extra large-constant or small-confidence restrictions. The deterministic statement permits every maximizing tie choice.

The frozen source hashes for the eight preview modules are:

- `Formalization/Online/Regret/Definitions.lean`: `7589b4a0f7bdcf208444f989a919ab726fc89931b5151e65e6dfbb4f540b934f`
- `Formalization/Online/Regret/Telescope.lean`: `be312d326e01c4569b279ee3b7485448c904007536e32943ffffa43452f715c2`
- `Formalization/Online/Regret/SummedEpisodes.lean`: `08908a2d730e6825396fa5b691816ec4870ffb1baeca5bb7997bff933777a147`
- `Formalization/Online/Regret/FixedOptimalSplit.lean`: `b3c11606730dec0152efb3a143a6cfa327909adaa503dd10bd9a0bf44a29ca0e`
- `Formalization/Online/Regret/ProbabilityTransfer.lean`: `c87006ba970b136ec24ff5e0fd32c24e016db93156f73a339854525da850a8f1`
- `Formalization/Online/Regret/NonnegativeTelescope.lean`: `e58c9d562480f87fe6770ccdabfa9e45c424cae79eefe52d81ab14a5c84e92e6`
- `Formalization/Statements/Ch5.lean`: `045b1ae583c38ad52c8f60df7756bdc520a38e0d874df0757d6e18d4d1be4838`
- `Formalization/Statements/Ch5Proofs.lean`: `a9f483dc493196401135da82f10416b47f99b8439489da01687ffc4013449baa`

The same-path episode sum consumes the one-episode inequality on each episode of the realized path. The (T_1=W_1+W_2) helper uses the true optimal continuation value for (W_1) and leaves the adaptive residual (W_2) data-dependent. The probability-transfer theorem uses the actual joint reset-vector/sequential-transition law and transfers the already-proved optimism event to the decomposition event. It assumes no concentration or centering result for (T_1)–(T_4). The probability/history construction uses the implementation’s fixed deterministic tie rule; the deterministic telescope itself is tie-agnostic subject to the explicit argmax premise.

## Zero-count correction

The algorithm initializes an unvisited Q entry to (H), while the printed bonus divides by the visit count. The printed expression is undefined at zero visits. This corrected variant uses the algorithm’s (Q=H) branch and an (H) analysis charge at zero count; at positive counts it uses the printed Bernstein expression. This is the C8 correction documented in [SOURCE-ISSUES.md](SOURCE-ISSUES.md), not a claim that the printed zero-count formula is defined.

## Verification boundary

The focused preview compiled the six extracted modules and the Ch5 statement/proof pair, and its actual-export probes exited successfully. Separately, the canonical affected rebuild reports 10 rebuilt plus 443 reused modules and a whole-library axiom audit of 5,097 declarations. Its manifest SHA-256 is `5be7cccc781ad43fa6b3460cbd222a46c664b5e3ea395987ddd1cab5f5fd76df`. This is an affected rebuild against the immediate verified 447-module baseline; that baseline’s verified ancestry includes the 438-module TV integration and 418-module clean TD run. It is not a fresh 453-module clean build. The reviewed sources and project-owned OLean artifacts have since been copied into the working tree, and a post-landing comparison confirms that all 453 source and OLean hashes match the canonical manifest. Shared dependency artifacts were not modified.

This result does not bound (T_1,T_2,T_3,) or (T_4), prove the final regret rate, or close the chapter. The separate (W_1) concentration and (T_3) filtration work are not dependencies of this deterministic endpoint and remain separate proof obligations.
