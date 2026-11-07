import Formalization.MDP.OptimalTrajectoryValue
import Formalization.MDP.DiscountedOccupancy
import Formalization.Online.QLearning.RateWeightDefinitions
import Mathlib.Data.Nat.Nth

/-!
# Pessimistic Q-learning (LCB-Q): algorithm model and analysis quantities

Definitions only (no theorems). Source: arXiv:2610.41903v1, `chapters/offlineRL.tex`.

* Parameters `eq:stepsize-penalty-offlineQ` (`:1666–1687`): `H = ⌈4 log(SAT/δ)/(1-γ)⌉`,
  `η_n = (H+1)/(H+n)` (the shared `onlineQRate`), `b_n = c_b √(H log(SAT/δ)/(n(1-γ)²))`.
* Algorithm `alg:q-infinite-lcb` (`:1701–1745`): `Q ≡ 0`, `V ≡ 0`, `n ≡ 0`, an arbitrary
  deterministic initial policy `π₀`; iteration `t = 1..T` reads the `t`-th triple
  `((s_t,a_t),s_t')` and applies `eq:Q-lcb-update-rule-Q`, `eq:Q-lcb-update-rule-V` and the
  strict-increase policy update. Ties in the arg max are broken by an arbitrary deterministic
  rule, modelled by a selector `sel : (A → ℝ) → A`; consumers assume `∀ f a, f a ≤ f (sel f)`.
* Analysis notation (`:1806–1854`): `Q_t, V_t, n_t, π_t` are the fields of `run … t`;
  the source's `k_i(s,a)` is `visitTime data (s,a) (i-1) + 1` (zero-based sample index plus one),
  so `V_{k_i(s,a)-1}` is `(run … (visitTime data (s,a) (i-1))).V`.
* Concentrability `assumption:concentrate-infinite-simple` (`:127–137`) in `ℝ≥0∞`, and the
  auxiliary sequences of Step 3 (`eq:dj-offlineQ`, `eq:five-sequence-def-offlineQ`,
  `:1970–2018`).
-/

open scoped BigOperators ENNReal

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL

variable {S A : Type*} [Fintype S] [Fintype A]

/-- `ι = log(SAT/δ)` (`eq:iota-defn-lcbq-proof`, `offlineRL.tex:1849–1852`). -/
noncomputable def iota (S A : Type*) [Fintype S] [Fintype A] (T : ℕ) (δ : ℝ) : ℝ :=
  Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / δ)

/-- The effective horizon `H = ⌈4 ι/(1-γ)⌉` (`eq:defn-H-lcbq-stepsize-proof`, `:1669–1672`);
the same expression as in `lcbq_useful` and `Lemma6_11_restricted`. -/
noncomputable def horizon (γ ι : ℝ) : ℕ := ⌈4 / (1 - γ) * ι⌉₊

/-- The Hoeffding penalty `b_n = c_b √(H ι/(n(1-γ)²))` (`eq:penalty-offlineQ`, `:1682–1684`). -/
noncomputable def penalty (cb γ ι : ℝ) (H n : ℕ) : ℝ :=
  cb * Real.sqrt (H * ι / (n * (1 - γ) ^ 2))

/-- The algorithm's state: Q-table, value table, visit counts and the policy iterate `π̂`. -/
structure Iterate (S A : Type*) where
  Q : S → A → ℝ
  V : S → ℝ
  count : S → A → ℕ
  policy : S → A

open Classical in
/-- One iteration of `alg:q-infinite-lcb` (`offlineRL.tex:1712–1736`) on the sample
`x = ((s,a),s')`: increment `n(s,a)`, set `n := n(s,a)`, update
`Q(s,a) ← (1-η_n)Q(s,a) + η_n{r(s,a) + γV(s') − b_n}`, then
`V(s) ← max{V_old(s), max_a Q(s,a)}`, and if `V(s) > V_old(s)` set `π̂(s) ← sel(Q(s,·))`.
Only the visited entries change. -/
noncomputable def step (M : DiscountedMDP S A) (cb ι : ℝ) (H : ℕ) (sel : (A → ℝ) → A)
    (σ : Iterate S A) (x : (S × A) × S) : Iterate S A :=
  letI : Nonempty A := M.action_nonempty
  let s := x.1.1
  let a := x.1.2
  let k := σ.count s a + 1
  let q := (1 - onlineQRate H k) * σ.Q s a +
    onlineQRate H k * (M.reward s a + M.discount * σ.V x.2 - penalty cb M.discount ι H k)
  let Q' : S → A → ℝ := fun s' a' => if s' = s ∧ a' = a then q else σ.Q s' a'
  let v := max (σ.V s) (actionMaximum (Q' s))
  { Q := Q'
    V := fun s' => if s' = s then v else σ.V s'
    count := fun s' a' => if s' = s ∧ a' = a then k else σ.count s' a'
    policy := fun s' => if s' = s ∧ σ.V s < v then sel (Q' s) else σ.policy s' }

/-- The initial iterate: `Q ≡ 0`, `V ≡ 0`, `n ≡ 0`, policy `π₀` (`offlineRL.tex:1706–1707`). -/
def init (π₀ : S → A) : Iterate S A :=
  ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, π₀⟩

/-- `(Q_t, V_t, n_t, π_t)` for `t = 0, …, T` of `alg:q-infinite-lcb`, run with
`eq:stepsize-penalty-offlineQ` (`ι = log(SAT/δ)`, `H = ⌈4ι/(1-γ)⌉`) on the data
`data : Fin T → (S × A) × S`. Iteration `t` (one-based) reads `data ⟨t-1, _⟩`. After `T` the
iterate is frozen (never used by the source). -/
noncomputable def run (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) : ℕ → Iterate S A
  | 0 => init π₀
  | t + 1 =>
    if h : t < T then
      step M cb (iota S A T δ) (horizon M.discount (iota S A T δ)) sel
        (run M cb δ sel π₀ data t) (data ⟨t, h⟩)
    else run M cb δ sel π₀ data t

/-- The zero-based sample index of the `(i+1)`-st visit to `sa`, i.e. the source's
`k_{i+1}(s,a) − 1` (`offlineRL.tex:1817`). Only meaningful for `i < n_T(s,a)`; then
`V_{k_{i+1}(s,a)-1}` is `(run … (visitTime data sa i)).V`. -/
noncomputable def visitTime {T : ℕ} (data : Fin T → (S × A) × S) (sa : S × A) (i : ℕ) : ℕ :=
  Nat.nth (fun u => ∃ h : u < T, (data ⟨u, h⟩).1 = sa) i

/-- A deterministic policy as a stationary randomized policy. -/
noncomputable def detPolicy (π : S → A) : StationaryPolicy S A :=
  fun s => EnvironmentStage.pointMass (π s)

/-- The single-policy concentrability coefficient `C⋆_ρ = max_{(s,a)} d⋆(s,a;ρ)/d^b(s,a)`
(`assumption:concentrate-infinite-simple`, `offlineRL.tex:127–137`), computed in `ℝ≥0∞` so that
`0/0 = 0` and `x/0 = ∞` for `x > 0`. `d⋆` is the discounted joint occupancy of the deterministic
policy `πstar` from `ρ` (`prelim.tex:145–172`). -/
noncomputable def concentrability (M : DiscountedMDP S A) (ρ : FiniteDistribution S)
    (πstar : S → A) (db : FiniteDistribution (S × A)) : ℝ≥0∞ :=
  ⨆ p : S × A, ENNReal.ofReal (M.discountedJointOccupancy (detPolicy πstar) ρ p.1 p.2) /
    ENNReal.ofReal (db.prob p)

/-- `d_j(s,a) = [ρᵀ(P_{π⋆})^j](s) 1{a = π⋆(s)}` (`eq:dj-offlineQ`, `offlineRL.tex:1970–1973`). -/
noncomputable def dWeight (M : DiscountedMDP S A) (ρ : FiniteDistribution S) (πstar : S → A)
    (j : ℕ) (s : S) (a : A) : ℝ :=
  open Classical in
  M.occupancyStateAt (detPolicy πstar) ρ j s * if a = πstar s then 1 else 0

/-- `V⋆`, the actual infinite-trajectory value of the optimal greedy policy. -/
noncomputable def optValue (M : DiscountedMDP S A) : S → ℝ :=
  M.trajectoryExpectedValue M.optimalGreedyPolicy

/-- `Δ_t = V⋆ − V_t` (`eq:Delta-chi-offlineQ`, `offlineRL.tex:1922–1925`). -/
noncomputable def delta (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) (t : ℕ) (s : S) : ℝ :=
  optValue M s - (run M cb δ sel π₀ data t).V s

/-- `min{β_n, 1/(1-γ)}` with `β_n = 3c_b√(Hι/(n(1-γ)²))` for `n ≥ 1` and `β_0 = +∞`
(`eq:beta-bar-beta-lcbq`, `offlineRL.tex:1886–1891`); at `n = 0` the minimum is `1/(1-γ)`. -/
noncomputable def betaTrunc (cb γ ι : ℝ) (H n : ℕ) : ℝ :=
  if n = 0 then 1 / (1 - γ) else min (3 * cb * Real.sqrt (H * ι / (n * (1 - γ) ^ 2))) (1 / (1 - γ))

/-- `γ(1+1/H)³` (`eq:defn-kappa-proof-lcbq`, `offlineRL.tex:2284–2289`). -/
noncomputable def kappa (γ : ℝ) (H : ℕ) : ℝ := γ * (1 + 1 / (H : ℝ)) ^ 3

/-- `Σ_{i=1}^{n_t(s,a)} η_i^{n_t(s,a)} P_{s,a} Δ_{k_i(s,a)−1}` (the inner sums in
`eq:psi-j-offlineQ`). -/
noncomputable def visitDeltaSum (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A)
    (π₀ : S → A) {T : ℕ} (data : Fin T → (S × A) × S) (t : ℕ) (s : S) (a : A) : ℝ :=
  let H := horizon M.discount (iota S A T δ)
  let n := (run M cb δ sel π₀ data t).count s a
  ∑ i ∈ Finset.range n, onlineQRateWeight H n (i + 1) *
    (M.transition s a).expectation (delta M cb δ sel π₀ data (visitTime data (s, a) i))

/-- `α_j = κ^j Σ_{t=1}^T ρᵀ(P_{π⋆})^j Δ_t` (`eq:alpha-j-offlineQ`, `offlineRL.tex:1981–1983`). -/
noncomputable def alphaSeq (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
    (j : ℕ) : ℝ :=
  kappa M.discount (horizon M.discount (iota S A T δ)) ^ j *
    ∑ t ∈ Finset.Icc 1 T, ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s *
      delta M cb δ sel π₀ data t s

/-- `θ_j = κ^j Σ_{t=1}^T Σ_s [ρᵀ(P_{π⋆})^j](s) min{β_{n_t(s,π⋆(s))}, 1/(1-γ)}`
(`eq:theta-j-offlineQ`, `offlineRL.tex:1984–1987`). -/
noncomputable def thetaSeq (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
    (j : ℕ) : ℝ :=
  let ι := iota S A T δ
  let H := horizon M.discount ι
  kappa M.discount H ^ j *
    ∑ t ∈ Finset.Icc 1 T, ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s *
      betaTrunc cb M.discount ι H ((run M cb δ sel π₀ data t).count s (πstar s))

/-- `ξ_j = κ^{j+1} ρᵀ(P_{π⋆})^{j+1} Δ_0` (`eq:xi-j-offlineQ`, `offlineRL.tex:1988–1990`). -/
noncomputable def xiSeq (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
    (j : ℕ) : ℝ :=
  kappa M.discount (horizon M.discount (iota S A T δ)) ^ (j + 1) *
    ∑ s, M.occupancyStateAt (detPolicy πstar) ρ (j + 1) s * delta M cb δ sel π₀ data 0 s

/-- `ψ_j` (`eq:psi-j-offlineQ`, `offlineRL.tex:1991–2001`). The sample at iteration `t` is
`data ⟨t-1, _⟩`. The ratio `d_j(s_t,a_t)/d^b(s_t,a_t)` uses real division; a sampled pair has
`d^b(s_t,a_t) > 0` almost surely, so the value `x/0 = 0` is never used on a full-measure set. -/
noncomputable def psiSeq (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
    (db : FiniteDistribution (S × A)) (j : ℕ) : ℝ :=
  let H := horizon M.discount (iota S A T δ)
  M.discount * kappa M.discount H ^ j *
    ∑ t : Fin T,
      ((∑ s, ∑ a, dWeight M ρ πstar j s a * visitDeltaSum M cb δ sel π₀ data (t.val + 1) s a) -
        (1 + 1 / (H : ℝ)) * (dWeight M ρ πstar j (data t).1.1 (data t).1.2 / db.prob (data t).1) *
          visitDeltaSum M cb δ sel π₀ data (t.val + 1) (data t).1.1 (data t).1.2)

/-- `φ_j` (`eq:phi-j-offlineQ`, `offlineRL.tex:2002–2015`), with the same data indexing and ratio
convention as `psiSeq`. -/
noncomputable def phiSeq (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
    (db : FiniteDistribution (S × A)) (j : ℕ) : ℝ :=
  let H := horizon M.discount (iota S A T δ)
  M.discount * kappa M.discount H ^ j * (1 + 1 / (H : ℝ)) ^ 2 *
    ∑ t : Fin T,
      ((dWeight M ρ πstar j (data t).1.1 (data t).1.2 / db.prob (data t).1) *
          (M.transition (data t).1.1 (data t).1.2).expectation
            (delta M cb δ sel π₀ data t.val) -
        (1 + 1 / (H : ℝ)) * ∑ s, ∑ a, dWeight M ρ πstar j s a *
          (M.transition s a).expectation (delta M cb δ sel π₀ data t.val))

end StatisticalRL.OfflineRL.LCBQ
