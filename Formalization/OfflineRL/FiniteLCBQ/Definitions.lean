import Formalization.OfflineRL.FiniteVILCB.Definitions
import Formalization.Online.QLearning.RateWeightDefinitions

/-!
# Finite-horizon LCB-Q (Theorem 6.17): the explicit algorithm

Source: arXiv:2610.41903v1, `chapters/offlineRL.tex`, Section `sec:finite-horizon-offline`:
data model `eq:finite-batch-size-def` (`:2943–2963`), algorithm prose (`:3126–3148`), penalty
`eq:lcb-q-penalty` (`:3141–3143`), Theorem 6.17 (`thm:lcbq`, `:3176–3192`). The algorithm box
`:3150–3173` is commented out in the source. See `docs/SOURCE-ISSUES.md#C33`.

The prose leaves the algorithm under-specified. This file fixes one explicit completion; every
choice below is ours and is disclosed in the statement entry:

* **Initialisation** (from `alg:q-infinite-lcb`, `:1706–1707`): `Q ≡ 0`, `V ≡ 0`, `N ≡ 0`,
  terminal `V_{H} ≡ 0` (the paper's `V_{H+1}`), and an arbitrary deterministic initial policy `π₀`.
* **Order**: one pass over the episodes `k = 0, …, K-1`; inside episode `k` the stages are
  processed in **forward** order `h = 0, …, H-1`, each updating one entry with the transition
  `(s_h^k, a_h^k, s_{h+1}^k)` (`:3132`).
* **Row update** (`:3132–3139`): `n ← N_h(s,a) + 1`,
  `Q_h(s,a) ← (1-η_n) Q_h(s,a) + η_n (r_h(s,a) + V_{h+1}(s') - b_n)` with `η_n = (H+1)/(H+n)`
  (`onlineQRate`) and the penalty `b_n = c_b √(H³ L / n)`.
* **V update** (never written in the source; monotone, as `eq:Q-lcb-update-rule-V`):
  `V_h(s) ← max{V_h(s), max_a Q_h(s,a)}`.
* **Output rule** (from `alg:q-infinite-lcb`, `:1726–1731`): the policy entry `π̂_h(s)` is set to
  `sel(Q_h(s,·))` only when `V_h(s)` strictly increases; `sel` is a deterministic selector of a
  maximizer of the Q-row. The output is `π̂` after the last episode. This **departs** from the
  literal reading of `:3145` ("acting greedily with respect to" the final `Q`).

Stage indices are `0, …, H-1` (the paper's `h = i + 1`).
-/

namespace StatisticalRL.LCBQFinite

open StatisticalRL.FiniteVILCB (Traj)

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The penalty `b_n = c_b √(H³ L / n)` (`eq:lcb-q-penalty`, with the log factor `L` explicit). -/
noncomputable def penalty (cb L : ℝ) (H n : ℕ) : ℝ := cb * Real.sqrt ((H : ℝ) ^ 3 * L / n)

/-- The algorithm's state: Q-estimates, values, visit counts and the current policy. -/
structure Iterate (S A : Type*) (H : ℕ) where
  /-- `Q_h(s,a)`. -/
  Q : Fin H → S → A → ℝ
  /-- `V_h(s)`. -/
  V : Fin H → S → ℝ
  /-- `N_h(s,a)`. -/
  N : Fin H → S → A → ℕ
  /-- `π̂_h(s)`. -/
  pol : Fin H → S → A

variable {H : ℕ}

/-- Initial state: `Q ≡ 0`, `V ≡ 0`, `N ≡ 0`, policy `π₀`. -/
def init (π₀ : Fin H → S → A) : Iterate S A H := ⟨fun _ _ _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0, π₀⟩

/-- The next-stage value `V_{h+1}` as currently stored (`0` after the last stage). -/
def nextV (it : Iterate S A H) (h : Fin H) : S → ℝ :=
  if hh : h.val + 1 < H then it.V ⟨h.val + 1, hh⟩ else fun _ ↦ 0

section

variable [DecidableEq S] [DecidableEq A]

/-- One row update at stage `h` with the transition `(s, a, s')`. -/
noncomputable def rowStep [Nonempty A] (cb L : ℝ) (sel : (A → ℝ) → A) (r : Fin H → S → A → ℝ)
    (h : Fin H) (s : S) (a : A) (s' : S) (it : Iterate S A H) : Iterate S A H :=
  let n := it.N h s a + 1
  let q := (1 - OnlineRL.onlineQRate H n) * it.Q h s a +
    OnlineRL.onlineQRate H n * (r h s a + nextV it h s' - penalty cb L H n)
  let row : A → ℝ := Function.update (it.Q h s) a q
  let v := max (it.V h s) (actionMaximum row)
  { Q := Function.update it.Q h (Function.update (it.Q h) s row)
    V := Function.update it.V h (Function.update (it.V h) s v)
    N := Function.update it.N h (Function.update (it.N h) s (Function.update (it.N h s) a n))
    pol := if it.V h s < v then Function.update it.pol h (Function.update (it.pol h) s (sel row))
      else it.pol }

/-- The first `m` stages of one episode, in forward order `h = 0, …, m-1`. -/
noncomputable def stagesUpTo [Nonempty A] (cb L : ℝ) (sel : (A → ℝ) → A) (r : Fin H → S → A → ℝ)
    (τ : Traj S A H) (it : Iterate S A H) : ℕ → Iterate S A H
  | 0 => it
  | m + 1 =>
    if hm : m < H then
      rowStep cb L sel r ⟨m, hm⟩ (τ.1 (Fin.castSucc ⟨m, hm⟩)) (τ.2 ⟨m, hm⟩)
        (τ.1 (Fin.succ ⟨m, hm⟩)) (stagesUpTo cb L sel r τ it m)
    else stagesUpTo cb L sel r τ it m

/-- One episode: all stages `h = 0, …, H-1` in forward order. -/
noncomputable def episodeStep [Nonempty A] (cb L : ℝ) (sel : (A → ℝ) → A)
    (r : Fin H → S → A → ℝ) (τ : Traj S A H) (it : Iterate S A H) : Iterate S A H :=
  stagesUpTo cb L sel r τ it H

/-- The state after the first `k` episodes (single pass over the data, in index order). -/
noncomputable def iterAfter [Nonempty A] {K : ℕ} (cb L : ℝ) (sel : (A → ℝ) → A)
    (π₀ : Fin H → S → A) (r : Fin H → S → A → ℝ) (x : Fin K → Traj S A H) :
    ℕ → Iterate S A H
  | 0 => init π₀
  | k + 1 =>
    if hk : k < K then episodeStep cb L sel r (x ⟨k, hk⟩) (iterAfter cb L sel π₀ r x k)
    else iterAfter cb L sel π₀ r x k

end

/-- **The algorithm** `LCB-Q(c_b, L, sel, π₀)`: the returned policy after all `K` episodes. It
reads only the rewards and the data (never the transitions, the behavior policy, `ρ^b` or `ρ`). -/
noncomputable def output [Nonempty A] {K : ℕ} (cb L : ℝ) (sel : (A → ℝ) → A)
    (π₀ : Fin H → S → A) (r : Fin H → S → A → ℝ) (x : Fin K → Traj S A H) : Fin H → S → A :=
  haveI := Classical.decEq S
  haveI := Classical.decEq A
  (iterAfter cb L sel π₀ r x K).pol

end StatisticalRL.LCBQFinite
