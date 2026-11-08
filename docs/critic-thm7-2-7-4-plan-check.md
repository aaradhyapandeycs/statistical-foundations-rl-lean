# CHECK: plan for corrected Theorems 7.2 (TV) and 7.4 (χ²), DRVI upper bounds

Public copy of the independent critic report; local paths removed.

This is an independent critic check of a paper proof. It uses the source only and compiles no Lean. Cited papers
(shi2024curious, shi2026curious) were not used. No project file was edited. The only files written are this report
and `<reviewer check folder>/`.

## 0. Pins

| Item | sha256 |
| --- | --- |
| Repo HEAD | `0e71fef97ad9697cf5558808b609c052de054052` (dirty tree) |
| `source/upstream/tex/chapters/robust_RL.tex` | `95ce19a9bcdb275c9d4c04e4b20e836c8e5f0965426e955999817e82141196d9` |
| the builder's private plan (checked) | `d246d16ae8cb51db4102b90a1131b2b637a51276fa3912fad7a9f2014e6202e3` |
| `<builder plan folder>/check_thm7_2_7_4.py` / `.out` | `1708baf9…db1d` / `8023fbe4…7f36` (match the plan's pins) |
| `<reviewer check folder>/critic_check.py` (mine) | `5172be7938daedf6d2d7fc61bd1645cfdb7c1722655a99421f9413bf912ba254` |
| `<reviewer check folder>/critic_check.out` | `68b49f5c2515eac042f6dfccfb2f79266f7f2f84dfb329cc017c0d85b6e8420a` |

My script is independent of the plan's script. It runs with `python3 -I critic_check.py` (pure Python, about 9 s) and
prints `ALL PASS`. Its results are numerical evidence only.

## 1. Printed statements (reconstructed before reading the plan)

**Shared setup.** The model is (s,a)-rectangular (`:31–48`), with TV defined at `intro.tex:223` and χ² at
`intro.tex:229–234`. The χ² divergence is defined only when P ≪ Q. Then:
- `V^{π,σ} = inf_{P∈U} V^{π,P}`, a static adversary choosing one kernel (`:76–79`);
- `V^{⋆,σ} = max_π V^{π,σ}`, where the policy class is not specified; `:90` asserts that a deterministic maximizer
  exists;
- DRVI starts from `Q̂_0 = 0`, uses the exact inner infimum, and outputs a greedy π̂ with unspecified ties
  (`:243–289`).

Lemma 7.1 (`:302–324`) gives the duals with α ∈ [V_min, V_max].

**Theorem 7.2** (`:342–359`). ρ = TV. There exist universal constants C1, C2 > 0. Assume γ ∈ [1/4,1), σ ∈ (0,1),
δ ∈ (0,1) and ε ∈ (0, √(1/max{1−γ,σ})]. Run DRVI for T = C1 log(N/(1−γ)) iterations. Assume
N ≥ C2 log(SAN/((1−γ)δ)) / ((1−γ)² max{1−γ,σ} ε²). Then with probability ≥ 1−δ, V^{⋆,σ}(s) − V^{π̂,σ}(s) ≤ ε for
every s.

**Theorem 7.4** (`:437–450`). ρ = χ². Assume σ ∈ (0,∞), γ ∈ [1/4,1), δ ∈ (0,1) and ε ∈ (0, 1/(1−γ)]. Run DRVI for
T = c1 log(N/(1−γ)) iterations. Assume N ≥ c2 (1 + max{√σ,σ}/(1−γ)) log(SAN/δ) / ((1−γ)³ε²). The conclusion is the
same as in Theorem 7.2.

The remarks (`:361–372`, `:453–457`) are oracle-planner variants. Both theorems are cited and not proved in the
monograph. My reconstruction matches plan §1.

## 2. Verdicts per claim

### (1) C37 is the only correction needed, and it is the weakest natural one — CONFIRMED, with a wording caveat

- **The printed count is refuted.** HorizonTrap shows this, as recorded in SOURCE-ISSUES C37. When
  N ≤ poly(1/(1−γ)), we get γ^{C1 log(N/(1−γ))} → 1. So no strengthening of the N condition can rescue the printed
  T; changing the iteration count is the right repair.
- **The corrected count suffices.** With T ≥ C1 log(N/(1−γ))/(1−γ) and C1 = 2, the inequality log γ ≤ γ−1 gives
  γ^T ≤ ((1−γ)/N)². Then ‖ξ‖/(1−γ) ≤ 2γ^T/(1−γ)² ≤ 2/N². Quantifying "∀ T ≥ bound" implies every rounding of the
  printed formula, so this form is the strongest of them.
- **No other hypothesis, range, constant, log factor or conclusion needs to change.** I checked every place the proof
  uses the hypotheses: σ ∈ (0,1) for TV, ε·√max ≤ 1, ε(1−γ) ≤ 1, γ ≥ 1/4, and the log arguments. All are within the
  printed domain. S = A = 1 under χ² is trivial because there is a single policy.
- **Caveat on "weakest".** The correction is the *minimal edit* of the printed formula. The 1/(1−γ) factor is
  necessary up to constants, as the trap shows. That the full log(N/(1−γ)) factor is necessary is not shown, and
  equivalent forms such as C1 log(N/(1−γ))/log(1/γ) exist. The plan should say "minimal edit" rather than suggest
  the count is tight.

### (2) χ² support mismatch via the support-aware Lemma 7.1 dual — CONFIRMED

- **The export's α-range.** The Lean export `Lemma7_1` (Statements/Ch7.lean:43–77) takes α over the *global*
  [inf V, sup V], including zero-mass states. Its χ² feasibility is support-aware (q = 0 off supp p). `chiBall` is
  `qChiBall`, which is support-aware, so there is no totalized-division junk.
- **Why the global range is harmless.** For α below min_{supp p} V, the clipped vector is constant α on supp p, so
  φ(α) = α, which increases up to the support minimum. For α above max_{supp p} V, φ is constant. So the max over
  the global range equals the max over the support range.
- **The deviation bound.** The same interval I = [W_min, W_max] serves p and p̂. Hence
  |g_p̂(W) − g_p(W)| ≤ sup_{α∈I} |φ_p̂(α) − φ_p(α)|, and the support of p̂ plays no role.
- **Net points outside I.** For α < W_min, the clipped vector is constant α, so φ_p̂(α) = φ_p(α) = α. φ is
  (1+√σ)-Lipschitz on all α ≥ 0, because std_q(f) ≤ ‖f‖∞. So net points lying outside I are harmless.
- **K1 (global α range).** The dual equals the exact KKT primal (q ∝ p(t−V)_+ on supp p) in 400 random rows with
  zero-mass states, including zero-mass states that carry the global min or max of V. The primal is also ≤ ⟨q,V⟩
  for 5310 random feasible q.
- **K2 (TV).** The global dual equals the primal in 231 rows. Here mass may move onto zero atoms, and the penalty uses
  the global min.

### (3) Decomposition and planning slack — CONFIRMED (re-derived)

- **Planning slack.** ξ(s) = max_a Q̂⋆(s,a) − Q̂⋆(s,π̂(s)) ∈ [0, 2γ^T/(1−γ)], because ‖Q̂_T − Q̂⋆‖ ≤ γ^T/(1−γ) from
  Q̂_0 = 0.
- **Term A.** Z − Y ≤ γK_Y(Z−Y) + γ|d_A|, where K_Y is the true row-minimizer at Y = V̂^{π⋆}.
- **Term B.** Y − Z ≤ γ|d_B| + γK_Z(Y−Z) + ξ, where K_Z is the true minimizer at Z = V^{π̂}.
- **Signs.** Both use G(Z) ≤ K_Y Z and G(Y) ≤ K_Z Y by admissibility, so the signs are right. The gap split uses
  V̂^{π⋆} ≤ V̂⋆.
- **Residual.** The one-sided residual e ≤ γ|d| + ξ holds in both cases.
- **K3 checks.** On 28 random robust MDPs (TV and χ², real sampling, truncated DRVI with ξ > 0), these hold:
  (i), (ii), 0 ≤ ξ ≤ 2e_T, and V^{π⋆} = V⋆.
- **Minor fix.** "ξ ≤ 2(1−γ)/N² ≤ 1" needs N ≥ 2, since N = 1 and γ = 1/4 give 1.5. N ≥ 2 follows from the sample
  bound (N ≥ 0.28·C2), but the plan should say so.

### (4) One-sided residual total-variance lemma and the TV span — CONFIRMED

- **Lemma V, re-derived.** The shift r' = r − (1−γ)min Y ≤ 1 may be negative. That is fine, because only
  2Y'(r'+e) ≤ 2B(1+e⁺) is used, with Y' ∈ [0,B].
- **Span lemma.** q = (1−σ)p + σδ_{argmin} lies in the TV ball, which gives span ≤ 1/(1−γ+γσ) ≤ 4/max{1−γ,σ} for
  γ ≥ 1/4. This applies to empirical robust values because the argument uses only the ball around p̂.
- **Variance transfer.** For TV, Var_p ≤ Var_q + σ·span². For χ², Var_p ≤ Var_q + (√σ/2)·span², by Cauchy–Schwarz
  with q ≪ p.
- **K3 checks.** Lemma V holds in cases A and B. The span bound and the std transfer hold.

### (5) Self-bounding on the resolvent-weighted deviation X — CONFIRMED

- **Derivation.** Pointwise, (I−γK)^{-1}|d| ≤ a1·(I−γK)^{-1}std_K Y + (a1√clos + a0)/(1−γ). Jensen and Lemma V then
  give X ≤ c + √(c'X). AM-GM yields (★). The algebra is correct.
- **Why the sup-norm route fails.** A self-bound in ‖V̂ − V‖∞ needs N ≳ ℓ/(1−γ)². At ε = 1/(1−γ) with small σ, the
  printed χ² bound only gives N ≈ c2·L·(1 + m/(1−γ))/(1−γ), where m = max{√σ, σ}. The ratio is
  c2(1−γ)(1 + m/(1−γ)), which is less than 1 when 1−γ ≪ 1/c2. My script reports 1.0e-2 at 1−γ = 1e-8, σ = 1e-20.
- **The X route is fine.** Its second-order term is 16ℓ/(N(1−γ)²) ≤ 129.6ε/c2, using ε(1−γ) ≤ 1.
- **K3 check.** (★) holds end to end, with ℓ* chosen as the least ℓ for which every Bernstein inequality of the actual
  leave-one-out net family holds.

### (6) Leave-one-out robust absorbing models — CONFIRMED (the override is necessary for TV)

- **Coincidence.** W_{s,V̂(s)} = V̂, since at s we have (1−γ)u + γu = u and the fixed point is unique. This holds for
  both the optimal family and the π⋆ family.
- **Lipschitz in u.** ‖W_{s,u} − W_{s,u'}‖ ≤ |u−u'|.
- **Grid.** The grid u_i = i/(N(1−γ)), i = 0..N, covers [0, 1/(1−γ)] with gap ≤ step/2.
- **Decoupling.** W^{opt}_{s,u} depends only on rows (s',·) with s' ≠ s, and W^{π⋆}_{s,u} only on rows
  (s', π⋆(s')). π⋆ is data-free. Under the product sampling law these are independent of every row-(s,a) sample, so
  the decoupling is valid.
- **Data-dependent indices.** The data-dependent action π̂(s) and grid index i are handled because the good event is
  uniform over all a, i and j.
- **K3 checks.** Coincidence holds (138 cases) and Lipschitz-in-u holds (about 1000 cases).
- **K4 (override needed).** Without the singleton override, the TV absorbing model fails coincidence in 30/30
  instances, because g_{δ_s} = (1−σ)u + σ min. For χ², chiBall(δ_s) = {δ_s}, so no override is needed there.

### (7) Concentration family sizes and the χ² std lemma — CONFIRMED

- **Family sizes per row.** TV: 2(N+1)². χ²: 4(N+1)², including h = (f − E_p f)². h is off-state measurable, since
  the centering uses the true p.
- **Bernstein.** `bernsteinRadius` uses log(4k/δ). Applied per row at δ/(SA) it gives ℓ = log(4kSA/δ). Then
  ℓ ≤ 15·L_TV, since L_TV ≥ log(4/3), and ℓ ≤ 8.1·L_χ, since SA ≥ 2. These reproduce exactly the printed
  log(SAN/((1−γ)δ)) and log(SAN/δ). No log(1/(1−γ)) term appears.
- **(S), re-derived.** Var_p̂ f = E_p̂ h − m² and Var_p h ≤ B²·Var_p f. Using b ≤ B²/4 and t ≤ 1, we get
  |Δvar| ≤ √2·B√b·t + 2.556·B²t². Splitting into the cases √b ≥ Bt and √b < Bt gives the bound ≤ 3.97·Bt ≤ 4Bt.
- **K5 check.** (S) holds in 4000 cases at the least admissible ℓ, including rows with tiny atoms.
- **Lean notes.**
  - The radius uses the family's actual `card` (≤ k), so a monotonicity-in-k lemma is needed.
  - The hypothesis `hV : ∀ V ∈ family, 0 ≤ V` holds, since both f and h are nonnegative.

### (8) Constants C1 = c1 = 2 and C2 = c2 = 10⁶ — CONFIRMED, with a minor arithmetic fix

- **TV.** (★) gives 57ε_ℓ + 64(1−γ)ε_ℓ² + 6ℓ/(N(1−γ)²). I re-derived 32√2 + 8√2 ≈ 56.6 for the first coefficient.
- **χ² arithmetic slip.** The step coefficient in §3.8 should be (12 + 4√σ), not (10 + 4√σ), because
  2·(4 + 2(1+√σ)) = 12 + 4√σ. It is harmless.
- **Implicit conditions.** a1 ≤ 1 (used as a1·step ≤ step) needs ℓ ≤ N/2, and (S) needs ℓ ≤ N. Both follow from the
  sample bounds: TV gives N ≥ C2·L_TV, and χ² gives N ≥ c2·L_χ/(1−γ). The plan should state these.
- **K6 check at the least admissible N.** The plan's C8 doubles N for χ², so it does not test the least N. Over 6000
  TV and 5696 χ² draws at the least admissible N, using T = ⌈bound⌉ and the corrected coefficient 12 + 4√σ:
  - gap ≤ ε and ℓ ≤ N/2 hold in every draw;
  - the worst gap/ε ratio is 0.023 (TV) and 0.030 (χ²);
  - so 10⁶ is far from tight, but valid.

### (9) Library facts and history-dependent policies — CONFIRMED

- **Library facts.** R0b, R0c and R0d (robust consistency, a deterministic optimal policy, γ-contraction) are correct
  for any nonempty row family that attains its infimum. TV and χ² balls are compact; the singleton override is
  trivial.
- **History-dependent policies, re-derived.** Let K⋆ be the row-wise minimizer at V⋆, taken over *all* (s,a). Then
  V⋆ is the Bellman-optimal value of the MDP K⋆. So every history-dependent π satisfies
  inf_K V^{π,K} ≤ V^{π,K⋆} ≤ V⋆.
- **Does the printed theorem need this?** No, not for the Lean statement. The stationary class in `robustOptimalValue`
  agrees with the source's `:90` reading. The argument only shows that the source's unspecified policy class gives
  the same V⋆. Keeping it optional and paper-level is correct.

## 3. Required corrections to the plan (none blocks)

1. §2.1: say "minimal edit". The 1/(1−γ) factor is necessary, but the tightness of the log factor is not claimed.
2. §3.1 and §3.8: state N ≥ 2 (for ξ ≤ 1), ℓ ≤ N/2 (for a1 ≤ 1) and ℓ ≤ N (for (S)), each derived from the sample
   bound.
3. §3.8 χ²: change (10 + 4√σ) to (12 + 4√σ), or recount the steps (my count is 5 + 2√σ before doubling).
4. Script C8: the χ² check should bisect to the least admissible N. My K6 does this.
5. If oracle-remark variants are added: the decomposition must use the residual slack ξ' of π̂ at V̂⋆, not
   V̂^{π̂}. V̂^{π̂} depends on row (s,π̂(s)) and has no data-free absorbing family. The conversion is
   0 ≤ ξ' ≤ ‖V̂⋆ − V̂^{π̂}‖, because ξ' = V̂⋆ − V̂^{π̂} + γ(Ĝ(V̂^{π̂}) − Ĝ(V̂⋆)).
6. Lean risks to add:
   - a monotonicity lemma in the `card` argument of `bernsteinRadius`;
   - generic R0 over arbitrary attaining row families, since the override is not of the form ball(p, σ).

## 4. Go / no-go

**GO.** The proof architecture is sound, as are corrections C37 (T ≥ 2 log(N/(1−γ))/(1−γ)) and the constants
2 and 10⁶. I found no counterexample and no hidden hypothesis. Items 1–4 of §3 are textual or arithmetic fixes to make
before the builder briefs. This check certifies nothing in Lean, and no author approval is implied.
