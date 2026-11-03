# Initial independent source review

Date: 2026-11-02. Target: arXiv `2610.41903v1`, *Statistical Foundations of Reinforcement Learning: A Non-Asymptotic Perspective*.

This is a raw-source scope and semantic-risk review, prepared independently of the builder inventory. It is not a statement seal, proof seal, or completed mathematical audit. Citations below use the unmodified files under `source/upstream/tex/`; line ranges refer to that pinned source. No Lean theorem was certified by this review. No build, axiom audit, or independent kernel replay was performed.

The review follows the workspace instructions and the installed `lean-workflow`, `lean-project-architecture`, and `lean-statement-audit` guidance. A separate reviewer examined the extension chapters directly; their observations are integrated below. The review samples load-bearing statements and proof interfaces across the whole included scope; it does not claim to have checked every algebraic line of every proof.

## Scope that “the entire paper” must cover

The active main-file include sequence is `StatisticalRL-nowplain.tex:198–236`: introduction, preliminaries, model-based generative RL, model-free generative RL, online RL, offline RL, extensions, and conclusion. The extension include list in `chapters/cousins.tex:8–18` adds **all five** of robust RL, multi-agent RL, federated RL, inference, and RLHF. Bandits is included separately at `chapters/onlineRL.tex:202`.

Coverage must account for more than numbered theorem environments. Definitions, unnumbered Bellman identities, optimal-policy existence assertions, algorithm specifications, probability models, displayed estimates, intermediate proof bridges, minimax constructions, corollaries stated only in prose, and cited mathematical inputs each need a disposition. Introductory history, empirical illustrations, acknowledgments, and open-problem statements can have an explicit expository disposition; they must not disappear silently from the scope accounting.

| Source component | Required mathematical coverage and source locators |
|---|---|
| `chapters/prelim.tex` | Discounted finite-state MDPs and randomized policies (`31–76`); trajectory values, Q-functions, simultaneous optimality and occupancies (`89–176`); Bellman operators/contraction (`185–286`); VI/PI (`289–364`); matrices, variance and resolvents (`366–594`); finite-horizon nonstationary models (`656–868`); concentration (`908–1075`); hypothesis testing and divergence tools (`1108` onward). |
| `chapters/generative_model_model_based.tex` | Independent simulator sampling (`12–31`), policy evaluation and sharp analysis (`39–779`), empirical policy learning and leave-one-out arguments (`780–1437`), minimax lower bounds (`1438–2177`), finite-horizon extension (`2501–2593`), auxiliary proofs (`2594` onward). The large `comment` region `2178–2495` is not active published content. |
| `chapters/generative_model_model_free.tex` | Stochastic approximation and TD (`14–783`), synchronous Q-learning upper and algorithm-specific lower bounds (`784–1886`), **Markovian asynchronous** Q-learning (`1887–2132`), finite-horizon extension (`2167–2255`), Appendices A–C (`2256`, `2506`, `2707` onward). The alternative theorem at `2133–2157` is commented out. |
| `chapters/onlineRL.tex` and `chapters/bandits.tex` | Adaptive episodic sampling, regret/PAC conversion, bandit warm-up, UCBVI (`205–1158`), MVP (`1159–1864`), model-free UCB Q-learning (`1870–2425`), minimax lower bounds (`2426–3292`), Appendices A–D (`3293`, `4070`, `4639`, `4796`). The missing files mentioned in `onlineRL.tex:1865–1867` are commented inputs; the active treatment is inline. |
| `chapters/offlineRL.tex` | IID transition data, unknown test distribution, single-policy coverage (`23–180`), bandit/offline warm-up, pessimistic model-based and model-free algorithms, upper bounds and minimax lower bounds (`2360–2930`), **independent-trajectory** finite-horizon extension (`2931–3199`), Appendices A–C (`3200`, `4411`, `5498`). |
| `chapters/robust_RL.tex` | Rectangular uncertainty sets, robust values and Bellman theory (`21–132`), strong duality (`302–324`), TV/chi-square upper and lower sample-complexity results (`342–480`). |
| `chapters/marl.tex` | Markov games, correlated/product policies and independent best responses; NE/CCE distinctions; plug-in bound (`384–399`), Q-FTRL (`441–467`), and lower bound (`487–503`). |
| `chapters/federated_RL.tex` | Independent agent/iteration samples (`21–25`), local/synchronized/final iterates (`45–70`), joint upper-bound conditions (`99–117`), restricted intermittent-communication lower bound (`227–239`). |
| `chapters/inference.tex` | IID TD data (`49–67`), averaged iterates, Gaussian approximation and covariance (`98–140`), plug-in estimation and confidence sets (`150–215`). The linear-approximation draft in the `comment` environment `218–311` is excluded from active published scope. |
| `chapters/RLHF.tex` | Preference/MLE model (`23–39`), KL objective and optimizer (`41–74`), calibration (`85–103`), linear-feature and parameter assumptions (`146–153`), adaptive data (`158–177`), regret theorem (`208–215`), and additional calibration-rate claim (`218–234`). |

The word “Appendix” is used inside chapter sections. The commented `\appendix` command in the main file (`StatisticalRL-nowplain.tex:247`) does **not** remove those sections. A chapter-only theorem list would omit substantial proof material.

The source uses `%` comments, `comment` environments, `\arxiv{...}`, and `\book{...}`. The main file defines `\arxiv` to discard its argument and `\book` to retain it (`57–58`); the inventory must follow these meanings. Raw regular-expression environment counts are not published theorem counts. Comment exclusions must retain their source locations and reasons.

## First load-bearing prerequisites

1. **Finite probability and actual MDP data.** Build genuine finite probability distributions, stochastic kernels, nonempty finite state/action carriers, bounded deterministic rewards, and discounts `0 ≤ γ < 1`. These are the source model, not arbitrary real arrays. The source allows randomized stationary policies (`prelim.tex:66–76`), while the chosen optimal policy is deterministic (`136–140`). The finite-horizon model uses step-dependent kernels/rewards and policies (`663–696`); a stationary-only API cannot certify that part.
2. **Source-faithful values and trajectories.** Values and Q-values are expectations of cumulative reward under actual generated trajectories (`prelim.tex:94–123`, `707–733`); Q fixes the first action and follows the policy thereafter. A recursively or fixed-point-defined implementation needs a proved equivalence to these semantics. Bellman contraction, unique fixed points, deterministic optimal-policy existence, value bounds, and normalization of discounted occupancies are proof obligations (`136–176`, `203–264`). Do not place them in an MDP structure as assumed fields.
3. **Finite-horizon terminal semantics and randomized policies.** Establish backward recursion with the correct terminal zero, horizon indexing, expectation over actions, and simultaneous optimality at every state/time (`prelim.tex:738–815`). A proof for one chosen initial state is weaker than the stated uniform assertions.
4. **Linear algebra with the source norm convention.** The paper calls the maximum absolute **row sum** its matrix `ℓ₁` norm (`intro.tex:203–208`). Do not substitute the usual induced column-sum `1` norm, an entrywise matrix norm, or the spectral norm. Prove variance nonnegativity, row-stochastic operator bounds, resolvent invertibility and nonnegativity, Neumann series, and the exact all-ones/norm identities (`prelim.tex:427–486`, `541–594`). Lean's totalized inverse is not an invertibility proof.
5. **Sampling spaces before probabilistic guarantees.** The simulator provides independent responses across queries (`generative_model_model_based.tex:12–29`); policy evaluation samples `Pπ` rather than merely handing an arbitrary empirical matrix to a theorem (`81–105`). Prove empirical-kernel normalization for positive sample count. Define estimators as measurable functions of permitted observations and, where appropriate, their independent random seeds. An estimator with access to the true unknown kernel violates the statistical experiment.
6. **Concentration and adaptive probability.** The finite test-vector family must be independent of the empirical row/kernel in Hoeffding/Bernstein (`prelim.tex:939–995`). Data-dependent optimal values cannot receive this premise for free: leave-one-out or decoupling is substantive mathematics. For sequential results, define filtrations, adaptation, conditional mean zero, almost-sure boundedness, and conditional variance before applying Azuma/Freedman (`1038–1075`). Restricting all later data to IID samples would discard the principal online/asynchronous obligations.
7. **Testing/information APIs.** Define measurable tests, minimax infima over the intended estimator class, KL with its correct direction and absolute-continuity/infinite-value behavior, tensorization, and reductions from policy/value errors to testing (`prelim.tex:1113–1224`, `1313` onward). A lower bound for one estimator, one fixed policy, or a data-dependent chosen MDP is not the paper's minimax theorem.

This is a readiness order, not yet an approved frozen-anchor graph. Small source-facing declarations should be independently reviewed before graph extraction. The statistical theorems should then consume proved probability/algorithm implementations rather than bundles of their desired estimates.

## Candidate source defects and ambiguities to resolve openly

These findings require checking against the rendered v1 and all applicable standing conventions. They are **not certified errata** and must not be silently repaired in a Lean signature.

### C1: Generative minimax theorem permits degenerate model sizes

**Subsequent independent review:** Section 3.3 explicitly introduces policy
learning under `A ≥ 2` (`generative_model_model_based.tex:787`). Whether that
assumption extends into the following lower-bound section is an interpretive
question. The singleton-action example below contradicts a standalone reading
without this assumption, not necessarily the authors' intended scoped claim.

`generative_model_model_based.tex:1443–1464` (`theorem:azar`) assumes only `SA ≥ 16` on sizes. Part (i) asserts a positive policy-error probability for every deterministic policy estimator. If `A = 1`, every policy takes the only action, hence `Qπ = Q*`; the event with positive ε is empty. The sample restriction is not a remedy: ε may be chosen sufficiently small that a positive integer sample count meets the bound for any fixed positive proposed universal constant.

The same statement permits `S = 1, A ≥ 16`. With one state and known deterministic rewards, transitions carry no unknown information and

`Q*(s,a) = r(s,a) + γ max_b r(s,b)/(1−γ)`.

An estimator can compute this exactly without samples, defeating part (ii) as well. The source statement and the intended lower-bound domains must be reconciled. A builder should prove these degenerate-case counterchecks as soon as the basic MDP API permits, then record the exact approved correction. Adding `S ≥ 2` or `A ≥ 2` silently would change the published statement rather than prove it.

The construction also switches from the global action space to state-dependent action sets (`1871–1877`). If a fixed-action Lean model is used, demonstrate a padding/equivalence construction preserving values, the observation experiment, sample count, and estimator reduction.

### C2: Inference covariance and confidence-set semantics

`inference.tex:108–119` defines the asymptotic covariance using Γ, and `132–140` uses `Γ⁻¹` and its condition number. Strict positivity of state sampling (`49–67`) does not by itself ensure Γ is positive definite: deterministic TD noise may vanish. Clarify the intended nondegeneracy/domain convention from the cited theorem; do not let totalized matrix inversion fabricate finite bounds. Also reconcile the Γ formula's `r(s)` (`115`) with sampled state-action rewards before treating the covariance expression as audited.

The confidence hyperrectangle radius is `R̂/√T` (`202`), while R̂ is described as a quantile for covariance `Λ̂/T` (`205`), suggesting an extra scaling by `√T`. Independently test the one-dimensional known-covariance case. The discussion at `189–196` also needs covariance-estimation and data-dependent-set control before a quantitative frequentist coverage theorem can follow from Gaussian approximation alone.

### C3: Nonnegative rewards versus zero-sum specialization

`marl.tex:41–43` imposes `[0,1]` rewards on all players, then `50–54` imposes `r₂ = −r₁`; the footnote explicitly acknowledges the conflict and proposes a constant shift. Encoding both conditions literally would collapse the zero-sum class to zero rewards. Use a separately faithful zero-sum carrier or prove the reward-shift equivalence, preserving equilibrium gaps and constants. Record the choice and its source justification.

## High-risk shortcuts the builder must reject

| Risk | Required challenge/evidence |
|---|---|
| Universal constants chosen after problem parameters or data | `intro.tex:191–192` defines order constants as universal. For model-based learning (`generative_model_model_based.tex:900–923`), exhibit constants before dimensions, MDP, ε, δ, and samples. Do not replace `N` inside the logarithm with an unrelated asymptotic slogan. |
| Replacing simultaneous events by pointwise probability bounds | Preserve the single event for all states/actions in policy learning (`900–923`) and all test vectors in concentration (`prelim.tex:939–995`). An individual bound for each vector needs an explicit union/conditioning argument. |
| Treating sample count, updates, episodes, and communication as the same variable | Policy evaluation uses `NS` samples (`generative_model_model_based.tex:111`); synchronous Q-learning uses `SAT` (`generative_model_model_free.tex:932–938`); online data uses `T=KH` (`onlineRL.tex:52–53`). Federated `N=BT` is per-agent and its converse concerns a restricted algorithm class (`federated_RL.tex:227–239`). |
| Oracle or noncausal online algorithms | Policies depend on previous episodes (`onlineRL.tex:35–43`, `2454`). Random samples and the policy-selection filtration must prevent access to future observations or the true kernel. Preserve the distinction between high-probability realized initial-state regret (`85–87`, `470–484`) and expected distributional regret (`2446–2454`). |
| Strengthening single-policy coverage to every action/policy | Offline density ratios use optimal occupancies and permit `0/0=0` (`offlineRL.tex:128–140`, `2983–2993`). A positive numerator over zero denominator must mean lack of coverage/infinite ratio, not Lean's real `x/0=0`. Use a faithful extended-valued definition or an explicitly equivalent finite-coverage formulation. The clipped ratio (`175–180`) is a different quantity. |
| Turning one trajectory into IID data | Discounted offline IID transitions (`offlineRL.tex:31–46`), finite-horizon independent trajectories (`2943–2973`), asynchronous Markovian samples (`generative_model_model_free.tex:1896–1907`), and adaptive online episodes are distinct experiments. Uniform ergodicity and mixing-time definitions (`2012–2042`) are not permission to assume independence. |
| Compiling “optimal policy” or fixed-point choices without well-definedness | Prove existence/uniqueness or finite maximizer selection on the real carrier. Preserve all empirical optimal deterministic policies where the statement says “any” (`generative_model_model_based.tex:902`), and address measurability of data-dependent tie selection. |
| Abstract robust values detached from an actual uncertainty set | Robust values are infima over kernels (`robust_RL.tex:71–82`); rectangularity (`31–48`), Bellman equivalence (`88–132`), and duality (`302–324`) need proofs. Preserve TV versus chi-square orientation and support behavior. |
| Replacing correlated policies by products, or vice versa | General joint policies permit correlation (`marl.tex:81–91`); NE requires product policies (`214–224`), CCE does not (`232–240`), and best-response deviations have their own independent interpretation (`119–143`). |
| Certifying omitted external algorithms through an assumed performance field | The full Q-FTRL algorithm is intentionally referred externally (`marl.tex:432`); its existence/complexity claim (`441–467`) requires a pinned external definition/proof input. The same discipline applies to quoted concentration, inference, and asynchronous results. |
| Totalized log/division/argmax concealing RLHF support or existence | Preference MLE, KL objective, normalized exponential policy, and log policy/reward identity (`RLHF.tex:23–74`) need their actual normalization, support, and optimizer-existence conditions. Calibration removes prompt-dependent reward shifts (`85–103`); adaptive online preferences (`158–177`) cannot be replaced by the independent background dataset. |

Polylogarithmic notation in regret theorems (`onlineRL.tex:470–484`, `1339–1352`) needs an explicit mathematically equivalent convention and bounds from the proofs/cited sources. A vacuous predicate called `TildeO`, a constant depending on K, or an unspecified “sufficiently large” sample field is not a formalized statistical rate. Preserve source endpoint ranges such as γ=0 in the base model, the restricted γ/ε ranges of individual theorems, and finite-horizon H=1 behavior rather than forcing every result into one stronger global model.

## Acceptance challenges and honest status

Before calling any chapter complete, the builder should deliver:

1. An active-source inventory with a disposition for every relevant statement, algorithm, definition, proof region, extension, appendix, and external input. Numbered environments alone are insufficient.
2. Actual source-facing Lean declarations and all meaning-carrying definitions; independent five-bin binder audits must reject every excess hypothesis, including those hidden in structures/typeclasses/Prop aliases.
3. Exact source/Lean correspondence preserving quantifiers, joint constants/witnesses, probability experiments, error metrics, and estimator classes; explicit rulings and renewed versions for corrected source defects.
4. Term-level applications showing that algorithm outputs satisfy the advertised theorem and that each conditional premise is supplied by proved dependencies. Import reachability and dependency diagrams do not establish this.
5. Focused compilation, transitive axiom closure with no unauthorized `sorryAx` or custom axioms, independent kernel evidence at the chosen release trust boundary, and independent source/semantic review of the exact public exports.
6. Small counterexample/regression probes covering singleton actions/states, zero rewards, γ=0, H=1, zero empirical counts, unsupported actions, singular covariance, multiple optimal policies, and data-dependent vector families. These must test mathematical behavior rather than merely match implementation text.
7. A public release built from the exact allowlisted tree with pinned dependencies, reproduction commands, provenance/licenses, independently verified errata/deviations, and limitations stated plainly. Publication authorization and source redistribution rights remain separate from proving results.

Keep at least these status layers distinct:

| Layer | What it establishes |
|---|---|
| Source inventory | A source item has been found and classified. |
| Source dependency review | Mathematical prerequisites and routes have been independently reconstructed. |
| Declaration fidelity | The exact Lean statement/definition matches the source and approved rulings. |
| Frozen unproved draft | The approved statement is fixed; its proof remains unavailable and quarantined. |
| Proof/axiom evidence | The exact export compiles and its transitive trust assumptions are recorded. |
| Certified source result | Both source fidelity and required proof/axiom/kernel evidence pass independent review. |

Current verdict of this document: **INITIAL SOURCE REVIEW ONLY; NO SOURCE RESULT CERTIFIED HERE**. Candidate C1 is a high-priority source-statement obstruction; C2 and C3 need explicit semantic resolution before related declarations can receive passing audits. A repository skeleton, source inventory, prose blueprint, or working toolchain cannot establish completion of the paper.
