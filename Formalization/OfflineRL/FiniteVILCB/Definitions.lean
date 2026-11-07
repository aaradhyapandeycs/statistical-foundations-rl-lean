import Formalization.Probability.VarianceDefinitions
import Formalization.MDP.OptimalityOperatorDefinitions
import Formalization.MDP.PointMassDefinitions
import Formalization.MDP.PolicyEnvironmentDefinitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite-horizon VI-LCB with two-fold sample splitting: definitions

Source: arXiv:2610.41903v1, `chapters/offlineRL.tex`, Section `sec:finite-horizon-offline`
(`:2931–3112`): data model `eq:finite-batch-size-def` (`:2943–2963`), occupancies `eq:dhb-finite`
(`:2967–2971`), concentrability `assumption:concentrate-finite` (`:2983–2993`), VI-LCB recursion
`eq:VI-LCB-finite` (`:3020–3046`), Bernstein penalty (`:3051–3056`), two-fold sample splitting
(`:3061–3062`), Theorem 6.16 (`thm:finite-VI-LCB`, `:3093–3112`).

The book does not define the "variant" of VI-LCB to which Theorem 6.16 refers. This file fixes one
explicit variant (`docs/SOURCE-ISSUES.md#C32`): the first half of the trajectories (auxiliary)
determines per-`(h,s)` trimmed counts `m_h(s)`; from the second half (main) only the first `m_h(s)`
visits to `(h,s)` are used (aux-determined subsampling is our reading of `:3061`). Stage indices
are `0, …, H-1` (the paper's `h = i + 1`).

The tape construction used only in the analysis is in `FiniteVILCB.TapeDefinitions`.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A]

noncomputable local instance finiteVILCBDecS : DecidableEq S := Classical.decEq S
noncomputable local instance finiteVILCBDecA : DecidableEq A := Classical.decEq A

/-! ## Trajectories and their law -/

/-- A trajectory: states `s_0, …, s_H` and actions `a_0, …, a_{H-1}`. -/
abbrev Traj (S A : Type*) (H : ℕ) := (Fin (H + 1) → S) × (Fin H → A)

/-- Probability of one trajectory under `s_0 ~ ρ`, `a_h ~ π_h(·|s_h)`,
`s_{h+1} ~ P_h(·|s_h,a_h)` (`eq:finite-batch-size-def`). -/
def trajProb {H : ℕ} (E : Fin H → EnvironmentStage S A) (π : Fin H → StationaryPolicy S A)
    (ρ : FiniteDistribution S) (τ : Traj S A H) : ℝ :=
  ρ.prob (τ.1 0) * ∏ h : Fin H, ((π h (τ.1 h.castSucc)).prob (τ.2 h) *
    ((E h).transition (τ.1 h.castSucc) (τ.2 h)).prob (τ.1 h.succ))

/-- The trajectory law as a measure on the discrete trajectory space. -/
noncomputable def trajMeasure {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) :
    @Measure (Traj S A H) ⊤ :=
  letI : MeasurableSpace (Traj S A H) := ⊤
  ∑ τ : Traj S A H, ENNReal.ofReal (trajProb E π ρ τ) • Measure.dirac τ

/-- Occupancy `d_h^π(s,a;ρ) = P(s_h = s, a_h = a)` (`eq:dh-pi-defn`, `prelim.tex:751–757`). -/
noncomputable def occupancy {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (h : Fin H) (s : S) (a : A) :
    ℝ :=
  ∑ τ : Traj S A H, trajProb E π ρ τ * (if τ.1 h.castSucc = s ∧ τ.2 h = a then 1 else 0)

/-- Point-mass policy of a deterministic nonstationary policy. -/
noncomputable def detPolicy {H : ℕ} (π : Fin H → S → A) : Fin H → StationaryPolicy S A :=
  fun h s ↦ EnvironmentStage.pointMass (π h s)

/-- Concentrability `C⋆ = max_{h,s,a} d⋆_h(s,a;ρ) / d^b_h(s,a)` (`eq:concentrate-finite`,
`:2987–2990`) in `ℝ≥0∞`, so that `0/0 = 0` and `x/0 = ∞` for `x > 0`. -/
noncomputable def concentrability {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (πb : Fin H → StationaryPolicy S A) (ρb ρ : FiniteDistribution S) (πstar : Fin H → S → A) :
    ℝ≥0∞ :=
  ⨆ (h : Fin H) (s : S) (a : A),
    ENNReal.ofReal (occupancy E (detPolicy πstar) ρ h s a) / ENNReal.ofReal (occupancy E πb ρb h s a)

/-! ## Values -/

/-- Optimal value at stage `h` (backward induction, zero at `h ≥ H`). -/
noncomputable def optV [Nonempty A] {H : ℕ} (E : Fin H → EnvironmentStage S A) (h : ℕ) (s : S) : ℝ :=
  if hh : h < H then
    actionMaximum (fun a ↦ (E ⟨h, hh⟩).reward s a +
      ((E ⟨h, hh⟩).transition s a).expectation (optV E (h + 1)))
  else 0
termination_by H - h

/-- Value of a deterministic nonstationary policy at stage `h` (zero at `h ≥ H`). -/
noncomputable def polV {H : ℕ} (E : Fin H → EnvironmentStage S A) (π : Fin H → S → A)
    (h : ℕ) (s : S) : ℝ :=
  if hh : h < H then
    (E ⟨h, hh⟩).reward s (π ⟨h, hh⟩ s) +
      ((E ⟨h, hh⟩).transition s (π ⟨h, hh⟩ s)).expectation (polV E π (h + 1))
  else 0
termination_by H - h

/-! ## The generic backward VI-LCB recursion on per-`(h,s,a)` statistics -/

/-- Normalized count row; the uniform row when all counts vanish. -/
noncomputable def normRow [Nonempty S] (f : S → ℕ) : FiniteDistribution S where
  prob s := if (∑ t, f t) = 0 then 1 / Fintype.card S else (f s : ℝ) / (∑ t, f t : ℕ)
  prob_nonneg s := by
    split_ifs
    · positivity
    · positivity
  sum_prob := by
    split_ifs with h
    · simp [Finset.card_univ, Fintype.card_ne_zero]
    · rw [← Finset.sum_div]
      push_cast
      exact div_self (by exact_mod_cast h)

/-- `‖V‖ = max_s V(s)`. -/
noncomputable def vmax [Nonempty S] (V : S → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty V

/-- The penalty: `‖V‖` for an unvisited pair; otherwise the Bernstein-style
`max{sqrt(c_b ι Var_{P̂}(V)/N), c_b H ι/N}` clipped at `‖V‖` (`:3051–3056`). -/
noncomputable def bonus [Nonempty S] (cb ι : ℝ) (H n : ℕ) (q : FiniteDistribution S)
    (V : S → ℝ) : ℝ :=
  if n = 0 then vmax V
  else min (max (Real.sqrt (cb * ι * q.variance V / n)) (cb * H * ι / n)) (vmax V)

/-- Backward VI-LCB values from statistics `cnt` (counts) and `row` (empirical rows):
`V̂_h(s) = max_a max{r_h(s,a) + P̂_h(s,a)·V̂_{h+1} - b_h(s,a;V̂_{h+1}), 0}`, `V̂_H = 0`
(`eq:VI-LCB-finite`). -/
noncomputable def vhatGen [Nonempty S] [Nonempty A] {H : ℕ} (cb ι : ℝ) (r : Fin H → S → A → ℝ)
    (cnt : Fin H → S → A → ℕ) (row : Fin H → S → A → FiniteDistribution S) (h : ℕ) (s : S) :
    ℝ :=
  if hh : h < H then
    actionMaximum (fun a ↦ max (r ⟨h, hh⟩ s a + (row ⟨h, hh⟩ s a).expectation
      (vhatGen cb ι r cnt row (h + 1)) -
        bonus cb ι H (cnt ⟨h, hh⟩ s a) (row ⟨h, hh⟩ s a) (vhatGen cb ι r cnt row (h + 1))) 0)
  else 0
termination_by H - h

/-- The pessimistic Q-estimate at stage `h`. -/
noncomputable def qhatGen [Nonempty S] [Nonempty A] {H : ℕ} (cb ι : ℝ) (r : Fin H → S → A → ℝ)
    (cnt : Fin H → S → A → ℕ) (row : Fin H → S → A → FiniteDistribution S)
    (h : Fin H) (s : S) (a : A) : ℝ :=
  max (r h s a + (row h s a).expectation (vhatGen cb ι r cnt row (h.val + 1)) -
    bonus cb ι H (cnt h s a) (row h s a) (vhatGen cb ι r cnt row (h.val + 1))) 0

/-! ## The algorithm on data: split, trimming, kept data -/

/-- Confidence logarithm `ι = log(16 H K / δ)`. -/
noncomputable def iota (H K : ℕ) (δ : ℝ) : ℝ := Real.log (16 * H * K / δ)

/-- Trimmed count from an auxiliary count `X`: `⌊X/4⌋` if `X > 16 ι`, else `0`. -/
noncomputable def trim (ι : ℝ) (X : ℕ) : ℕ := if 16 * ι < X then X / 4 else 0

section Data

variable {H K : ℕ}

/-- State of trajectory `k` at stage `h`. -/
def stAt (x : Fin K → Traj S A H) (h : Fin H) (k : Fin K) : S := (x k).1 h.castSucc
/-- Action of trajectory `k` at stage `h`. -/
def acAt (x : Fin K → Traj S A H) (h : Fin H) (k : Fin K) : A := (x k).2 h
/-- Next state of trajectory `k` after stage `h`. -/
def nxAt (x : Fin K → Traj S A H) (h : Fin H) (k : Fin K) : S := (x k).1 h.succ

/-- Auxiliary visit count `X_a(h,s)`: trajectories `k < ⌊K/2⌋` with `s_h = s`. -/
noncomputable def auxCount (x : Fin K → Traj S A H) (h : Fin H) (s : S) : ℕ :=
  (Finset.univ.filter (fun k : Fin K ↦ k.val < K / 2 ∧ stAt x h k = s)).card

/-- Trimmed counts `m_h(s)`, computed from the auxiliary half only. -/
noncomputable def trimCount (ι : ℝ) (x : Fin K → Traj S A H) (h : Fin H) (s : S) : ℕ :=
  trim ι (auxCount x h s)

/-- Rank of main trajectory `k` among main visits to `(h, s_h^k)`: the number of main
trajectories `k' < k` at the same state at stage `h`. -/
noncomputable def mainRank (x : Fin K → Traj S A H) (h : Fin H) (k : Fin K) : ℕ :=
  (Finset.univ.filter (fun k' : Fin K ↦ K / 2 ≤ k'.val ∧ k' < k ∧ stAt x h k' = stAt x h k)).card

/-- Main trajectory `k` is kept at `(h,s)`: it visits `(h,s)` and is among the first
`m_h(s)` main visits to `(h,s)` (in index order). -/
abbrev kept (m : Fin H → S → ℕ) (x : Fin K → Traj S A H) (h : Fin H) (s : S) (k : Fin K) : Prop :=
  K / 2 ≤ k.val ∧ stAt x h k = s ∧ mainRank x h k < m h s

/-- `N_h(s,a)`: number of kept transitions from `(h,s)` with action `a`. -/
noncomputable def keptCount (m : Fin H → S → ℕ) (x : Fin K → Traj S A H) (h : Fin H) (s : S)
    (a : A) : ℕ :=
  (Finset.univ.filter (fun k ↦ kept m x h s k ∧ acAt x h k = a)).card

/-- Next-state counts of kept transitions from `(h,s,a)`. -/
noncomputable def keptNext (m : Fin H → S → ℕ) (x : Fin K → Traj S A H) (h : Fin H) (s : S)
    (a : A) (s' : S) : ℕ :=
  (Finset.univ.filter (fun k ↦ kept m x h s k ∧ acAt x h k = a ∧ nxAt x h k = s')).card

/-- **The algorithm** (`FVILCB(c_b, δ)`): Q-estimates computed from the rewards and the data
only (never the transitions, the behavior policy or the test distribution). -/
noncomputable def qhat [Nonempty S] [Nonempty A] (cb δ : ℝ) (r : Fin H → S → A → ℝ)
    (x : Fin K → Traj S A H) (h : Fin H) (s : S) (a : A) : ℝ :=
  let m := trimCount (iota H K δ) x
  qhatGen cb (iota H K δ) r (keptCount m x) (fun h s a ↦ normRow (keptNext m x h s a)) h s a

end Data

/-! ## Library-facing objects used by the statement entry -/

/-- `ℕ`-indexed extension of a `Fin H`-indexed Markov policy, as required by
`EnvironmentStage.controlled` (an arbitrary point mass at `n ≥ H`, never used there). -/
noncomputable def extPolicy [Nonempty A] {H : ℕ} (π : Fin H → StationaryPolicy S A) :
    ℕ → StationaryPolicy S A :=
  fun n ↦ if hn : n < H then π ⟨n, hn⟩ else fun _ ↦ EnvironmentStage.pointMass (Classical.arbitrary A)

theorem controlled_length (es : List (EnvironmentStage S A)) (π : ℕ → StationaryPolicy S A) :
    (EnvironmentStage.controlled es π).length = es.length := by
  induction es generalizing π with
  | nil => rfl
  | cons e es ih => simp [EnvironmentStage.controlled, ih]

/-- Stage `h` as an index of the controlled stage list `controlled (List.ofFn E) π`. -/
def stageIndex {H : ℕ} (E : Fin H → EnvironmentStage S A) (π : ℕ → StationaryPolicy S A)
    (h : Fin H) : Fin (EnvironmentStage.controlled (List.ofFn E) π).length :=
  ⟨h.val, by rw [controlled_length, List.length_ofFn]; exact h.isLt⟩

end StatisticalRL.FiniteVILCB
