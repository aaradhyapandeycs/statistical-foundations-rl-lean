# Critic review: `Thm7_9_corrected` (FedSynQ, Theorem 7.9, C41)

Public copy of the independent critic report; local paths removed.

Critic: independent of the builder. Date 2026-11-08.
Scope: `<builder working folder>/Thm79Wip/{Pathwise,Noise,Event,Rate,Main,StatementDraft,StatementProofDraft}.lean`
and `AxiomProbe.lean`. Before review I ran `diff -r` against `Thm79Wip.reviewed-snapshot`: the two trees are identical.
The source sha256 prefixes match `BUILD-LOG.md` (Pathwise 4694a16b, Noise 35f18664, Event a3c29ddf, Rate fd5a1a14,
Main d5f88e62, StatementDraft 27469a51, StatementProofDraft aee5c04a, AxiomProbe 88d9f604).

## Verdict: PASS (integration may proceed)

No blocking findings. The entry states the printed theorem. Its only added hypothesis that is not a
convention is `η < 1`. It is stronger than the old existential printed Prop restricted to `η < 1`;
this is machine-checked in probe (A). The hypotheses are jointly satisfiable, and the satisfying
instance exercises averaging (probe (B)). The proof route is mathematically sound. All files
re-elaborate, and the axiom closure is exactly `[propext, Classical.choice, Quot.sound]`.

## Source reconstruction (done before reading the Lean)

`chapters/federated_RL.tex`:
- Setup and sampling, :19–25: `s_t^k(s,a)` are drawn independently from `P(·|s,a)`.
- Algorithm, :35–90:
  - `Q_0^k = Q_0` and `V = max_a Q`, :35–40.
  - Local update (47–49): `Q_{t-1/2}^k = (1-η)Q_{t-1}^k + η(r + γ V_{t-1}^k(s_t^k(s,a)))`, with `0<η<1` (:51, :76).
  - Averaging of the intermediate iterates when `t ≡ 0 mod τ` (56–62).
  - Output `Q_T = (1/K)Σ_k Q_T^k` (:68). `τ | T` is assumed "without loss of generality" (:70).
- Theorem 7.9, :99–117:
  - Hypotheses: `δ∈(0,1)`, `ε∈(0,1/(1-γ)]`, `0≤Q₀≤1/(1-γ)`, and `τ ≤ 1 + η⁻¹ min{(1-γ)/(8γ), 1/K}` (106).
  - Constants: there exist a large `c_T` and a small `c_η`.
  - Conditions: `T ≥ c_T/(K(1-γ)⁵ε²)·log³(SAKT/(δε(1-γ)²))` (112–113) and `η = c_η K(1-γ)⁴ε²/log(SAKT/δ)` (114).
  - Conclusion: with probability `≥ 1-δ`, `‖Q_T − Q⋆‖_∞ ≤ ε`.

## Findings

### F1. Binder-by-binder check of the entry: faithful

| Printed item | Entry (`StatementDraft.lean`) | Status |
|---|---|---|
| `c_T` large, `c_η` small, existential | `∃ c_T c_η, 0<c_T ∧ 0<c_η ∧ ∀ …`, quantified before everything | Stronger: the constants are universal. |
| MDP, rewards in [0,1], `γ<1` | `DiscountedMDP` | As printed. |
| `γ>0` | hypothesis `0 < M.discount` | Definedness convention for the `/(8γ)` in (106), disclosed (see F6). |
| `K, τ, T ≥ 1`, `τ ∣ T` | hypotheses | Standing conventions (:54, :70). The export uses neither `γ>0` nor `τ∣T`. |
| `δ∈(0,1)` | `0<δ`, `δ<1` | Exact. |
| `ε∈(0,1/(1-γ)]` | `0<ε`, `ε ≤ 1/(1-γ)` | Exact. |
| `0≤Q₀≤1/(1-γ)` | `∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1/(1-γ)` | Exact. |
| η (114) | `η = c_η*K*(1-γ)^4*ε^2 / log(S*A*K*T/δ)` | Exact, including the log argument `SAKT/δ`. |
| added | `η < 1` | The only correction, C41. Since `log(SAKT/δ) > 0`, it is equivalent to `c_η K(1-γ)⁴ε² < log(SAKT/δ)`. |
| τ (106) | `τ ≤ 1 + 1/η * min((1-γ)/(8γ), 1/K)` | Exact, both halves. |
| T (112–113) | `c_T/(K(1-γ)^5 ε^2) * log(SAKT/(δ ε (1-γ)^2))^3 ≤ T` | Exact: the log argument is `SAKT/(δε(1-γ)²)` and the power is 3. |
| law | `FedGeneric.fedSamplingLaw M T K 1` | The true product law (:23–25). |
| `Q⋆` | `M.optimalityFixedPoint` | The true `Q⋆`. |
| conclusion | `1-δ ≤ P(∀ s a, |fedOutput M η K τ Q₀ (… fedSamplesExtend … 0) T s a − Q⋆ s a| ≤ ε)` | Exact. The `ℓ_∞` norm is written entrywise. The output is the real `fedOutput` with the prescribed `η`. |

- **Stronger than the old Prop (probe A).** `corrected_implies_printed_at_restricted` proves that
  `Thm7_9_corrected` implies the body of `Fed.Thm7_9_at` with the extra hypothesis `η<1`, for the
  same constants. The probe instantiates `Ω`, `μ` and the samples with the true law, and discharges
  `IsOptimalQ` through `FedGeneric.optimalityFixedPoint_bellman` (`vStar = greedyValue`). The
  converse fails in general. (Probe file: `<reviewer probe folder>/CriticProbe.lean`.)
- **Junk values.**
  - `log(SAKT/δ) > 0`, because `SAKT ≥ 1` and `δ < 1`.
  - `log(SAKT/(δε(1-γ)²)) ≥ log(SAKT/δ) > 0`, because `ε(1-γ)² ≤ 1`.
  - The denominators `K(1-γ)⁵ε²` are positive, so `η > 0` and `1/η` is genuine.
  - `8γ ≠ 0` under `γ > 0`.
  - `K ≥ 1`, so the agent averages are genuine.
  - `Q⋆` is `optimalityFixedPoint`, not a fallback value.
  - Every set in the sample space is measurable: the space is finite and the instance on `State` is `⊤`.

### F2. Algorithm fidelity: faithful

These definitions were reviewed earlier, in `FedPrinted79` and `FedGeneric710`.

- `fedRun (t+1) = fedStep … (t+1) (fedRun t) (samples (t+1))`.
  - `fedStep` averages `localUpdate` over the agents and gives the average to every agent when `(t+1) % τ = 0`.
  - Otherwise each agent applies its own `localUpdate`.
  - `localUpdate` is (47–49) with `V = ⨆_a Q`.
  - The run starts from `Q₀` for every agent.
- `fedOutput` is the agent average at `T`.
- Sample indexing. `fedSamplesExtend M T K 1 data t k s a 0` reads coordinate `((t-1, k), (s,a), 0)` for `1 ≤ t ≤ T`.
  - So each (iteration, agent, `(s,a)`) gets exactly one independent draw from `P(·|s,a)`.
  - Iteration `t` uses only its own coordinates, and the slot is `Fin 1`.
  - Indices outside `[1,T]` are never queried.

### F3. Proof route: sound, re-derived independently

I checked each step by hand. All of them are fully compiled.

- **Noise decomposition.**
  - Set `w_u^j = V_u^j(s_{u+1}^j) − P V_u^j`.
  - Let `G` follow the FedSynQ recursion driven by `ηw`:
    - local step: `G ← (1-η)G + ηw`;
    - synchronization: `G ← avg_j[(1-η)G^j + ηw^j]`.
  - Then `G_t^k = Σ_{u<t} a(t,u)·avg_j w_u^j + b(t,u)·w_u^k`, with deterministic coefficients:
    - at synchronization: `a ← (1-η)(a+b) + η[u=t]` and `b ← 0`;
    - otherwise: `a ← (1-η)a` and `b ← (1-η)b + η[u=t]`.
  - This needs `avg_j G^j = Σ(a+b)·avg w`. That holds because `a` does not depend on the agent.
    `noiseG_succ` proves the recursion.
- **Contraction.**
  - `E = Q − Q⋆ − γG`, and `Q⋆ = r + γP V⋆`, so `E_{t+1} = (1-η)E_t + ηγ(PV_t − PV⋆)` locally, or its agent average at synchronization (`errE_succ`).
  - `|V_t−V⋆| ≤ ‖E_t‖ + γσ`, which gives `‖E_{t+1}‖ ≤ (1-ηg)‖E_t‖ + ηγ²σ`.
  - Unrolling: `‖E_t‖ ≤ ρ^t/g + γ²σ/g` with `‖E_0‖ ≤ 1/g`, since `Q₀` and `Q⋆` both lie in `[0,1/g]`.
  - The output error is then at most `ρ^T/g + γ²σ/g + γσ = ρ^T/g + γσ/g` (`fedOutput_abs_le`).
  - This needs `0 ≤ η ≤ 1` for `|1-η| = 1-η`, and the bound on `G_u` for every `u ≤ T`. The event supplies both.
- **Variance.**
  - The coefficient of `w_u^j` is `c_{u,j} = a/K + b[j=k]`. Because `ab = 0` (`coefA_mul_coefB`), `Σ_j c² = a²/K + b²`.
  - The invariants are `Σ_u (a²+b²) ≤ η` (geometric: `(1-η)²η + η² ≤ η`) and `Σ_u b² ≤ η²(t mod τ)` (`coef_sq_sum_le`).
  - Hence `Σ c² ≤ η/K + η²(τ-1) ≤ 2η/K`. This uses only `η(τ-1) ≤ 1/K`, which follows from the second half of (106) because `min ≤ 1/K` (`Main.lean`, `hητ`).
- **The unused half of (106).** The `(1-γ)/(8γ)` half sits inside a `min`, so it only makes the
  hypothesis stronger. Dropping it from the proof is honest, and keeping it in the entry is
  correct, since it is printed. `hτc` is consumed only through `min_le_right`. No other use, hidden
  or otherwise, exists: I grepped Main, Event and Noise.
- **Causality.**
  - `V_u^j` depends only on iterations `≤ u`, that is, on coordinates with time index `< u`.
  - Under `posEquiv` (time first, then a rank on `(agent,(s,a),slot)`), those coordinates are strictly before the coordinate `(u, j, (s,a))`.
  - `smOf_extendPrefix` together with `fedRun_congr` turns this into the equality used in `increment_eq`.
  - Centering and adaptedness come from the library lemmas `mvp_paddedRevealIncrement_centered` and `_adapted`. Azuma is the library lemma `azuma_filtration_strict`.
  - The increment bound is `|c|·H`, with `|w| ≤ H = 1/g` because `V ∈ [0,1/g]` (`fedRun_mem` needs `η ≤ 1`).
  - The tail is `σ = √(2H²(2η/K)log(2/δ'))`.
- **Union bound.**
  - The targets are `(u,k,s,a)` with `u ≤ T`, so `C = (T+1)KSA` events at `δ' = δ/C`.
  - `measureReal_biUnion_finset_le` gives a total below `δ`.
- **Rates, with explicit numerals for every `T` above the minimum.**
  - `σ² = g²ε²L/(54ℓ)`, where `L = log(2C/δ) ≤ log 4 + ℓ ≤ 3ℓ` (using `2C ≤ 4P` and `ℓ ≥ log 2`). So `σ ≤ gε/2`.
  - Bias: `ηgT = TY/(216ℓ) ≥ 10⁴ℓ_T³/(216ℓ) ≥ ℓ_T`, using `ℓ_T ≥ ℓ ≥ 0.69`. Also `ℓ_T ≥ log(2/(εg))` because `P ≥ 2δg`. So `ρ^T ≤ e^{-ηgT} ≤ εg/2`.
  - The proof uses `T` only through the lower bound `hTc`; minimality of `T` is never used.
- **Degenerate case `SAKT = 1`.**
  - The state space is a single point, so `w ≡ 0` surely (`noiseG_of_subsingleton`).
  - `ℓ_T ≤ 1/20` gives `g, εg ≥ 19/20`, and then `1-εg ≤ ηg` by explicit numerals.
  - The event is the whole space, so the probability is `1 ≥ 1-δ`.

### F4. Compilation and axioms (critic re-run)

The commands were run foreground, one at a time, without `-o`, and without lake or lean-lsp.

- `bash scripts/lean-local.sh <builder working folder>/Thm79Wip/Main.lean`: exit 0, about 5 s, no errors or warnings.
- `bash scripts/lean-local.sh <builder working folder>/Thm79Wip/StatementProofDraft.lean`: exit 0, about 2 s.
- `bash scripts/lean-local.sh <builder working folder>/AxiomProbe.lean`: exit 0. `Thm7_9_corrected_holds` and `fedSynQ_error_le_of_eta_le_one` both depend on `[propext, Classical.choice, Quot.sound]`.
- `bash scripts/lean-local.sh <reviewer probe folder>/CriticProbe.lean`: exit 0, sha256 `64b16d03cd5a6c488e29e91cd2ad542865219376156718b274501ea9a8c83b86`. Both probes depend on `[propext, Classical.choice, Quot.sound]`.
- A grep for `sorry`, `admit`, `native_decide`, `axiom`, `maxHeartbeats`, `implemented_by` and `extern` in `Thm79Wip/` found nothing.
- Not done here: the full `python3 scripts/check.py` with the modules integrated under `Formalization/`. The lead must run it after the namespace and module move.

### F5. Non-vacuity (probe B)

`Thm79Critic.nonvacuous` uses the following instance:
- one state and one action, `r ≡ 1`, `γ = 1/2`;
- `K = 2`, `τ = 2` (so averaging is used), `T = 10⁹`;
- `δ = 1/2`, `ε = 2 = 1/(1-γ)`, `Q₀ = 0`.

At `c_T = 10⁴` and `c_η = 1/216` the probe proves `0 < η < 1`, the τ condition, the T condition
(via `log(8·10⁹) < 23`), `ε ≤ 1/(1-γ)` and `τ ∣ T`. So the hypotheses are jointly satisfiable, not
only in the degenerate branch.

### F6. Non-blocking remarks

1. **`γ > 0`.** At `γ = 0`, Lean's `1/0 = 0` would turn (106) into `τ ≤ 1`, a junk reading,
   whereas the mathematical reading `(1-γ)/(8γ) = +∞` gives `τ ≤ 1 + 1/(ηK)`. Excluding `γ = 0` is
   the honest choice and is disclosed. Optionally, `γ = 0` could also be covered by a second entry
   that writes the τ condition as `8γη(τ-1) ≤ 1-γ ∧ η(τ-1) ≤ 1/K`; the export already covers that
   case. This is not required.
2. **Reading of the constants.** The entry gives one pair of constants, `(10⁴, 1/216)`.
   - The `c_T` direction is monotone: any larger `c_T` also works, because the hypothesis gets stronger.
   - The `c_η` direction is not: "every sufficiently small `c_η` with `c_T` fixed" is not claimed, and it is false in general, because the bias bound needs `c_T c_η` bounded below.
   - This matches the project's existential reading in `FedPrinted79` ("sufficiently … reading implies this one"), and the docstring says "there are universal constants". If the lead wants to pre-empt the question, add one clause to the C41 entry or the docstring saying that the pair is existential.
3. **Integration hygiene.**
   - Rename the namespace `Ch7Draft79 → Ch7`.
   - Move the modules under `Formalization/Ch7Rest/`, and keep `Statements/Ch7.lean` importing only `FedGeneric710`, which is definitions-only.
   - Delete the transient `.lake/build/lib/lean/Thm79Wip/*.olean`, which `compile.sh -o` wrote into the project build directory.
   - Update `COVERAGE`, `PROGRESS` and `SOURCE-ISSUES#C41`. C41 currently says "no positive result about the true generative law is formalized"; that sentence must change.
   - Run `python3 scripts/check.py`.
4. **Main.lean docstring.** It says the export assumes `η ≤ 1`, which is correct: the export is
   weaker in its hypothesis than the entry's `η < 1`. Keep the wrapper's `hη1.le`.

## Required edits

None blocking. The integration steps in F6.3 are mandatory at landing. F6.1 and F6.2 are optional
wording or coverage improvements.
