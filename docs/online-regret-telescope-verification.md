# Corrected UCBVI telescope and decomposition: verification

The corrected variant of `lemma:decomdetail` (Lemma 5.6),
`chapters/onlineRL.tex:808–818`, is proved. It uses a finite H analysis charge
at zero visits, where the printed bonus divides by zero. The positive-count
bonus is unchanged. This is the proposed correction recorded as Candidate C8
in [SOURCE-ISSUES](SOURCE-ISSUES.md), not a proof of the literal undefined
zero-count formula. The full regret theorem and chapter remain incomplete.

## Exact mathematical endpoint

`StatisticalRL.Statements.Lemma5_6_corrected` writes out the complete one-episode
inequality over arbitrary observed stage tables and state/action paths whose
selected actions maximize the same capped backward Q table. It expands the
reward, analysis charge, empirical-minus-true continuation expectation, and
true expectation minus realized next-state value. Every term uses the same
table and path, the continuation starts at h+1, and its terminal value is zero.

The generic result covers **any greedy tie choice**, `0 < δ′ ≤ 1`, and
nonnegative bonus coefficients. This includes the source's positive
coefficients and actual confidence allocation. The proof uses only
`L=log(1/δ′) ≥ 0`, nonnegative coefficients and greedy action selection. It
adds no optimism, event-probability, stochastic-centering or fluctuation-bound
premise. The wrapper consumes
`onlineCappedEpisode_realized_telescope_nonnegative` and unfolds definitions;
the exact proof export is `StatisticalRL.Statements.Lemma5_6_corrected_holds`.

The same change supplies supporting actual-history results: the selected
row/action and successor agree with the causal sequential path; episode
inequalities sum on that same path; the existing actual optimism event implies
the four-term regret decomposition; and T₁ splits exactly into W₁ with fixed
true optimal continuation and W₂ with the adaptive value difference. The
probability transfer uses the source iid reset law and the existing fixed-tie
planner, with its strict `1−2SAHKδ′` bound and exact printed δ′ allocation.
That probability construction keeps its fixed-tie scope; the generic
deterministic telescope imposes no tie choice. T₁ is not asserted centered.

These results do not bound T₁–T₄ or prove a regret rate. The separate W₁
concentration, visit-count aggregation and T₃ global-filtration work remain
quarantined and are not included or counted in this release.

## Source and independent review

The authoritative source hash is
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.
The [independent review](critic-online-regret-telescope.md) compared the exact
source statement, all 35 preserved declaration chunks from four input drafts,
the definitions-only extraction, the broader nonnegative-parameter helpers,
the final Chapter 5 proposition and its consuming proof. The existing
Lemma5_5_corrected declaration and proof bodies are preserved.

Ownership: builders proved the actual-history telescope, four-term sum,
confidence transfer and fixed-optimal split; the coordinator extracted the
definitions, added the broader helpers and statement index, and integrated;
the independent critic reviewed source semantics, transformation and scope.

## Build and axiom evidence

The five original qualified modules compiled and their six-export axiom probe
passed. The nonnegative extension and its two exports also passed. The final
Ch5 statement/proof modules and their actual-export probe passed; both the new
Lemma5_6_corrected_holds and existing Lemma5_5_corrected_holds report only
`propext`, `Classical.choice`, and `Quot.sound`. One initial focused probe used
a file outside Lean's selected source root; rerunning that probe from the
project root passed. An initial statement overlay was incomplete; the check
was rerun with a complete project OLean mirror. Those failed logs are retained.
No mathematical source was changed to address either path issue.

Canonical run `20261104T061902221003Z` passed: **10 rebuilt modules
+ 443 unchanged reused modules = 453 current project modules**. The complete
facade and `Audit.lean` were rebuilt; the whole namespace audit passed
**5,097 project declarations** with only the three standard axioms above.
The source and OLean hashes of all 453 modules were checked after the run.
Canonical source hashes match the focused actual-export versions; the full
namespace audit covers those exact integrated exports. A duplicate post-run
Lean import was not required for this check.

After landing, 31 inherited workspace OLean files differed from the canonical
snapshot while their source files matched. Those project-owned cache files
were synchronized from the verified snapshot; all 453 workspace project OLean
hashes then matched. Shared dependency artifacts were not changed.

This is an **affected rebuild, not a fresh 453-module clean build**. Its
verified 447-module baseline has manifest SHA-256
`10a64197a318d88cb077e8fcc85d10f05f6c041d881eefacbcc50d37262078a0`.
The ancestry includes the TV438 affected check and clean418 TD check. The
driver verified source/artifact identity along both reuse edges before and
after this run, with all current447 and TV438 artifact hashes pinned to their
manifests. The historical clean418 manifest lacks OLean/package byte hashes;
its inherited artifacts are bound by TV438 reuse receipts and the retained
snapshot. The compiler and dependency paths match the verified baseline;
shared dependency metadata was unchanged. External package bytes were not
newly hashed or rebuilt.

Compiler: `Lean (version 4.27.0-rc1, arm64-apple-darwin24.6.0, commit 2fcce7258eeb6e324366bc25f9058293b04b7547, Release)`.
Canonical manifest SHA-256: `5be7cccc781ad43fa6b3460cbd222a46c664b5e3ea395987ddd1cab5f5fd76df`.

| Released Lean source | SHA-256 |
| --- | --- |
| `Formalization/Online/Regret/Definitions.lean` | `7589b4a0f7bdcf208444f989a919ab726fc89931b5151e65e6dfbb4f540b934f` |
| `Formalization/Online/Regret/Telescope.lean` | `be312d326e01c4569b279ee3b7485448c904007536e32943ffffa43452f715c2` |
| `Formalization/Online/Regret/SummedEpisodes.lean` | `08908a2d730e6825396fa5b691816ec4870ffb1baeca5bb7997bff933777a147` |
| `Formalization/Online/Regret/FixedOptimalSplit.lean` | `b3c11606730dec0152efb3a143a6cfa327909adaa503dd10bd9a0bf44a29ca0e` |
| `Formalization/Online/Regret/ProbabilityTransfer.lean` | `c87006ba970b136ec24ff5e0fd32c24e016db93156f73a339854525da850a8f1` |
| `Formalization/Online/Regret/NonnegativeTelescope.lean` | `e58c9d562480f87fe6770ccdabfa9e45c424cae79eefe52d81ab14a5c84e92e6` |
| `Formalization/Statements/Ch5.lean` | `045b1ae583c38ad52c8f60df7756bdc520a38e0d874df0757d6e18d4d1be4838` |
| `Formalization/Statements/Ch5Proofs.lean` | `a9f483dc493196401135da82f10416b47f99b8439489da01687ffc4013449baa` |
| `Formalization.lean` | `1e61c7464e552cafdb2f542a09dc7e2b2edf0f829e55ebdf58f5b1df832733c0` |

## Reproduction and counting

`python3 scripts/check.py` compiles every current project module and audits
the entire project namespace without rebuilding dependencies. This performs
a full-project check, rather than the historical affected mode above. Focused
edits use `bash scripts/lean-local.sh` in dependency order; integration also
includes the facade and `Audit.lean`.

The ledger retains 17 named-result entries, with their existing restrictions,
and now records two separate corrected variants: optimism and Lemma5.6. The
new corrected lemma does not increment the original named-result count.
These are not a whole-monograph completion percentage. Every chapter and the
whole formalization goal remain open.
