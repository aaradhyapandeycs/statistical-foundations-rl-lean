# Independent review: MVP uniform confidence and terminal-value source issues

## Scope

I reviewed the source-facing counterexample to Lemma 5.13, the actual-law
Lean export and its probe, the qualified probability-provider graph, the
affected integration receipt, and the public C16/C17 descriptions. The source
is `chapters/onlineRL.tex`, pinned at SHA-256
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.
This review does not certify the full MVP regret proof.

## C16: generic Lemma 5.13 counterexample

The source places the allocation at lines 1388–1391, Assumption
`assumption-X-mvp` at 1670–1690, and Lemma 5.13 (`lemma:uniform`) at
1696–1712. The assumption declares the vector families for stages through
H, while both the dependence clause and conclusion use `X_{h+1}`. The
counterexample uses the natural bounded continuation-family completion at
H+1. The source gives no generic terminal-zero restriction; the endpoint
ambiguity remains explicit in C16.

Set S=2, A=H=1, K=4 and let each of the two true rows be uniform on the two
states. For each profile, take the deterministic family `{0,e₀,e₁}`. It has
three elements, is contained in `[0,1]^2`, contains zero, and has no future
data dependence. At batch index `l=2`, the batch consists of one sample
(the second sample in each row). For every sample outcome, choose `e_b` in
each row, where b is the state observed in that row. The two positive
deviations sum to 1 and the two true variances sum to 1/2.

With ε=`(320000 log 6)⁻¹`, δ′=`exp(−ε)`, and δ=`(16/25)δ′`, the printed
allocation holds exactly, iota=1, and both `K≥SAH log₂K` and the stronger
`K≥SAH·iota` condition hold. The printed right side is
`sqrt(1/8)+1/4 < 3/4 < 1`. Thus the necessary simultaneous event is empty
under the actual expanded product law, while its claimed probability lower
bound `1−δ′` is positive. This is a counterexample to the generic uniform
bound under the stated endpoint interpretation; it does not refute the main
MVP regret theorem or its particular value-function family.

The frozen raw witness is
`MVPUniformCounterDraft.lean`, SHA
`354cf7364d39e57fda1bca57c1386b0edcd95da87bed66d7ac841519808f9865`.
Its target compiled successfully to OLean
`3dbd81d1148ee8333b8fa542e507c06a3910d7415159f9ab682ead265b0b7f01`.
The active 19-export probe source is
`4b4457fb4ad4ae6897a867ad17b527ba664da6f9f0334f90734f8d996b518994`;
its log SHA is
`abdf2e564e00e1b605f260a0db8f4b900d474e207b3b33e341dea5fb8222e73d`.
All 19 exports report only `propext`, `Classical.choice`, and `Quot.sound`.

## C17: auxiliary terminal-value identification

The actual algorithm initializes `V_{H+1}=0` at source line 1267; the
fixed-profile auxiliary algorithm initializes its terminal value to H at
4423–4433. The asserted actual-value equality and family membership are at
4467–4472. For S=A=1, H=2, K=2, zero rewards and the sole-state transition,
take c₂>0 and
`q=min(1/(2c₂),1/(80000 log 6))`, δ′=`exp(−q)`, and δ=`(4/25)δ′`.
Then the source allocation holds, iota=`40000 log(6)q≤1/2`, and both the
printed K condition and the stronger large-regime condition hold. After
the first stage-2 observation, the actual terminal continuation is zero,
the variance term vanishes, and the stage-2 value is `2c₂q∈(0,1]`. The
auxiliary continuation is 2 and its clipped stage-2 value is 2 for every
profile. Its family `{0,2}` excludes the actual continuation value used by
the stage-1 coupling argument.

This is a source-level counterexample to the auxiliary family-membership
step, not a formal execution theorem and not a refutation of the final MVP
regret conclusion. A complete algorithm-to-algorithm Lean coupling remains
open.

## Qualified infrastructure and integration evidence

The qualified map, runner, and pins have SHA-256
`23990e3caee44e09679a3564bdcb278718e308f4d7fbcad468b7f0bd0ddc9c3f`,
`fff640b6bf17d8bae5e2ba1ad33ad9f6cb83d5d021b781c873dedbe50e165bdc`, and
`e01d56b15d644ce1ed82805e570318c8e98f23cd3f938bbfe4b74a0a1e804840`,
respectively. The corrected graph contains 39 providers; its isolated build
compiled all 39 providers and the probe. The probe has 73 requested exports
and reports only the standard three axioms. Run-status SHA:
`9f2425dfd7d51e6d7b50f40bcf5a08566e18ca1f128a45c7f5f6a1922f8de589`.

The final whitespace-clean affected integration is run
`20261104T175908349662Z`, manifest SHA
`e680c9d04b2f2425c67172cb3464c5dcb1510e2804ee4bf5f7a9f65097514c0b`.
It rebuilt 9 modules and verified 714 reused modules out of 723 current
sources; the whole-library axiom audit covered 6,876 declarations and found
only the standard three axioms. I independently checked every manifest
source and OLean hash against both the candidate and synchronized workspace.
The ancestry is an affected rebuild from the preceding verified 723-source
snapshot, with recorded ancestry through the public 684-source baseline to
the earlier clean 418-source check; it is not a fresh clean 723-source
rebuild. Historical clean418 did not record OLean or package byte hashes, as
the verification record discloses.

The final source differs from the immediately preceding verified 723-source
candidate only by removal of one trailing space in
`MVPActualPositiveParts.lean`; no Lean token or proof body changed. The
executed driver prose said “twelve” ancestry edges, but the 14 snapshots
contain 13 parent-child edges, all of which the driver loop checked. The
verification record corrects that metadata without changing the pinned run.

The 39 providers establish actual-product conditional moments, reverse
reveal, batch identities, finite-product concentration, uniform finite
family/mask coverage, and the explicit cardinality-dependent probability
bound. They do not complete the printed iota comparison or certify Lemma
5.13. The ledger therefore remains unchanged; C16 and C17 are source
findings, not certified named results. The chapter and monograph remain
incomplete. See [C16](SOURCE-ISSUES.md#C16), [C17](SOURCE-ISSUES.md#C17),
and the [verification record](online-MVP-probability-verification.md).
