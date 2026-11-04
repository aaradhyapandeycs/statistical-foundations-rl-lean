# Independent source review: joint W₁/W₂/W₃ clauses

## Scope and source correspondence

This review covers the corrected, restricted joint result corresponding to `lemma:bound-W1-W2-ucbvi-proof` in `chapters/onlineRL.tex:928–955`, with the W₃ definition at lines 931–932 and the shared confidence statement at lines 935–946. The theorem combines the source’s three separate displayed inequalities on one event under the source allocation

\[
\delta' = \frac{\delta}{100S^2A^2H^2K^2}, \qquad
\iota = 40000\Bigl(\frac{\log K}{\log 2}\Bigr)^3\log(1/\delta').
\]

The Lean event uses the same finite sequential episode law for the reset vector and trajectory. It states the W₁, W₂, and W₃ inequalities over the actual sampled states, actions, empirical rows, and capped planner values. The combined wrapper consumes the three restricted source exports and proves their intersection bound by a four-event union argument: one fixed-\(V^*\) event, one fixed-\((V^*)^2\) event, one shared coordinate event, and the optimism event. It does not assume those events are independent.

The resulting failure coefficient is \((10+4S)SAHK\delta'\). For \(S\ge2\), this is at most the printed \(12S^2AHK\delta'\). For a singleton state space, the empirical and true expectations of every state function agree, including at unvisited rows; the three deviations are zero pointwise, and the event is universal. Thus the final wrapper covers singleton state spaces as well.

## Corrected and restricted scope

The statement is explicitly restricted to \(K\ge2\). At \(K=1\), the printed \(\log_2 K\) factor in \(\iota\) vanishes, so this index entry does not certify the unrestricted source claim at that endpoint; see Candidate C12 in [SOURCE-ISSUES.md](SOURCE-ISSUES.md).

The algorithm uses the finite zero-count completion \(Q=H\), recorded as Candidate C8 in [SOURCE-ISSUES.md](SOURCE-ISSUES.md), and one fixed deterministic greedy tie rule. The source’s positive-count bonus is unchanged. The theorem’s parameter domains retain \(0<\delta\le1\), \(c_1\ge4\), and \(c_2\ge c_1^2\). These are statement-scope disclosures, not silent changes to the paper’s claim.

The result is the joint W₁/W₂/W₃ component only. It does not establish the later T₂₃₄ bounds or the final regret theorem.

## Reviewed source and focused evidence

The qualified preview contains 36 new Lean modules. The hash-bound transformation manifest is `2aeec5ce04e1dbe370aacb49ae430ced9af7ecb65cd617048c35d4a1a4af3b95`. Its extracted `onlineActualW3Point` definition is theorem-free; the transformation review found the declaration bodies preserved while imports and qualified names were routed through the existing public W₁ definitions and proof modules.

The joint source modules reviewed were:

- `Formalization/Online/Regret/Joint/W123Definitions.lean` — `0974d81cc6ec2a19eadaeb4faa07cf9bf49be122de51b5c77ec05fd8183a8aca`.
- `Formalization/Online/Regret/Joint/OnlineW123Singleton.lean` — `92603e905f08b27a46d606d406369a47b9a39e1f787d4f7a336d72e41bf2424a`.
- `Formalization/Online/Regret/Joint/OnlineW123SharedEvent.lean` — `c6dc9ab165ee9ccd2245655e9c83050063b45f16b892007984262e269ea3bc22`.
- `Formalization/Online/Regret/Joint/OnlineW123Final.lean` — `9eb5fb2539fcfc720ec82af1786464d91d71184547a207f7e207005dd462e3a9`.

The source-facing Chapter 5 statement and applying proof were reviewed at:

- `Formalization/Statements/Ch5.lean` — `ed9852c3a47f7e49515b8cd929207c5c08b3d7d28538c1af807383364345b10c`.
- `Formalization/Statements/Ch5Proofs.lean` — `785cfdb270e2bf4c111382797219ce65f56de1776448179fb504484bd023d1a2`.

The focused statement build compiled both files against the hash-verified 477-module W₁ project baseline. The six-export axiom probe exited successfully with the standard three Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). The focused probe source hash is `92db132b037aa1c5feac9c80e632e529258e9bd06e34b2cd1676f86ecbe7ecf2`; its output hash is `d749599e6b19e577afed442b8acfd1c220d67b3ac2866204e96a0fd15ac17278`.

The affected-project integration check has now passed: 40 modules were rebuilt and 473 unchanged modules were reused from the verified 477-module baseline. The whole-library axiom audit covered 5,423 declarations, and the final source and OLean hashes for all 513 project modules match the successful manifest and landed workspace. This is an affected rebuild, not a fresh 513-module clean build. Its provenance chain is 477 → 453 → 447 → 438 → clean418; the historical clean418 manifest did not record OLean or dependency byte hashes, and that limitation is retained in the verification record. The final integration manifest SHA-256 is `bce1165017a1bbc0f40b621742d0cf6001fdaf97c4469ef2d9faefff56958306`.

Before the final run, six module comments were corrected to remove stale “uncompiled” and draft wording. Exact source review confirms these edits left all Lean tokens and all bytes outside the module comments unchanged. The immutable preceding successful candidate remains available; the final run rebuilt the same 40-module affected closure with those six comments included.

This result certifies the corrected, restricted joint W₁/W₂/W₃ component only. It does not certify the unrestricted \(K=1\) statement, later T₂₃₄ bounds, a final regret theorem, or completion of the chapter or monograph.
