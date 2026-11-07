import Formalization.MDP.PolicyEnvironmentDefinitions
import Formalization.MDP.TrajectoryDefinitions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Hard MDP families for the online minimax lower bound

Definitions for `thm:minimax-lower-online` (`chapters/onlineRL.tex:2443–2456`) and
`lem:Vh-star-Vhpi-gap-lower-bound-online-final` (`:2654–2668`).

* `onlineLBq H ε a⋆ a` is the exit probability `q_{a⋆}(a)` of `eqn:prob-astar-a-1` (`:2582–2604`).
  The source's arms are `1, …, A`; here they are `Fin A`, with the source's distinguished arm `1`
  represented by the index `0`. The definition follows the printed case split literally.
* `onlineLBSubStages` is the two-state MDP `M_i` of `:2512–2650` (`C^sub_mdp`): states `Fin 2`, with
  the source's state `1` (reward `1`, exits to `0` with probability `q_{i_h}(a)`) and the absorbing
  zero-reward state `0`. The source's state `0` has the single action `0`; here every state has the
  action set `Fin A`, and at state `0` all actions coincide (absorbing, reward `0`).
* `onlineLBStages` is the general-`S` family of `:3020–3075`: with `m = ⌊S/2⌋`, the copy `j < m`
  occupies the states `j` (the source's state `1` of that copy) and `j + m` (its absorbing state `0`).
  The source assumes `S` even (`:3015`); when `S` is odd the remaining state `2m` is absorbing with
  reward `0` and receives no initial mass, so it is never visited.
* `onlineLBRho S` is the initial law `eq:defn-rho-general-S-lower-bound-pf-online` (`:3067–3072`),
  uniform on the `m` copies' states `j < m`.

The construction requires `2 ≤ H`, `0 < ε` and `ε ≤ H/2` (the source's range `0 < ε₀ ≤ H/2`,
`:2602`); these hypotheses are arguments of the stage definitions because they make every exit
probability lie in `[1/(2H), 1/H] ⊆ [0, 1]`.
-/

open scoped BigOperators

namespace StatisticalRL.OnlineLowerBound

open StatisticalRL

/-- The exit probability `q_{a⋆}(a)` of `eqn:prob-astar-a-1` (`chapters/onlineRL.tex:2582–2604`).
The source's arm `1` is the index `0`. When `a⋆ ≠ 1`: `q(a⋆) = 1/H − ε/H²`, `q(1) = 1/H − ε/(2H²)`,
and `q(a) = 1/H` otherwise; when `a⋆ = 1`: `q(1) = 1/H − ε/(2H²)` and `q(a) = 1/H` otherwise. -/
noncomputable def onlineLBq (H : ℕ) (ε : ℝ) {A : ℕ} (astar a : Fin A) : ℝ :=
  if (astar : ℕ) ≠ 0 then
    (if a = astar then 1 / (H : ℝ) - ε / (H : ℝ) ^ 2
      else if (a : ℕ) = 0 then 1 / (H : ℝ) - ε / (2 * (H : ℝ) ^ 2) else 1 / (H : ℝ))
  else
    (if a = astar then 1 / (H : ℝ) - ε / (2 * (H : ℝ) ^ 2) else 1 / (H : ℝ))

/-- Under `2 ≤ H` and `0 < ε ≤ H/2`, every exit probability lies in `[1/(2H), 1/H]`. -/
theorem onlineLBq_bounds {H : ℕ} {ε : ℝ} (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    {A : ℕ} (astar a : Fin A) :
    1 / (2 * (H : ℝ)) ≤ onlineLBq H ε astar a ∧ onlineLBq H ε astar a ≤ 1 / (H : ℝ) := by
  have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  have h1 : ε / (H : ℝ) ^ 2 ≤ 1 / (2 * H) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : 0 ≤ ε / (H : ℝ) ^ 2 := by positivity
  have h3 : ε / (2 * (H : ℝ) ^ 2) ≤ ε / (H : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_left hε.le (by positivity); nlinarith
  have h4 : 0 ≤ ε / (2 * (H : ℝ) ^ 2) := by positivity
  have h5 : 1 / (H : ℝ) = 1 / (2 * H) + 1 / (2 * H) := by field_simp; ring
  unfold onlineLBq
  split_ifs <;> constructor <;> linarith

theorem onlineLBq_nonneg {H : ℕ} {ε : ℝ} (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    {A : ℕ} (astar a : Fin A) : 0 ≤ onlineLBq H ε astar a := by
  have := (onlineLBq_bounds hH hε hεH astar a).1
  have : (0 : ℝ) ≤ 1 / (2 * (H : ℝ)) := by positivity
  linarith

theorem onlineLBq_le_one {H : ℕ} {ε : ℝ} (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    {A : ℕ} (astar a : Fin A) : onlineLBq H ε astar a ≤ 1 := by
  have h := (onlineLBq_bounds hH hε hεH astar a).2
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast (by omega : 1 ≤ H)
  have : 1 / (H : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hH'
  linarith

section Rows

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- The point mass at `s` (an absorbing transition row). -/
def stayRow (s : State) : FiniteDistribution State where
  prob x := if x = s then 1 else 0
  prob_nonneg x := by split_ifs <;> norm_num
  sum_prob := by simp

/-- The transition row of a copy's rewarding state `g`: move to the absorbing state `b` with
probability `q`, stay at `g` with probability `1 - q`. -/
def exitRow (g b : State) (hgb : g ≠ b) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    FiniteDistribution State where
  prob x := if x = b then q else if x = g then 1 - q else 0
  prob_nonneg x := by split_ifs <;> linarith
  sum_prob := by
    have h : ∀ x, (if x = b then q else if x = g then 1 - q else 0) =
        (if x = b then q else 0) + (if x = g then 1 - q else 0) := by
      intro x
      by_cases hb : x = b
      · subst hb; simp [Ne.symm hgb]
      · simp [hb]
    simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

end Rows

/-- One stage of the two-state MDP `M_i` (`chapters/onlineRL.tex:2512–2580`) with optimal action
`a⋆` at state `1`: `r(1, a) = 1`, `r(0, ·) = 0`, `P(0 | 1, a) = q_{a⋆}(a)`, `P(1 | 1, a) = 1 − q_{a⋆}(a)`,
and state `0` absorbing. -/
noncomputable def onlineLBSubStage (H : ℕ) (ε : ℝ) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (astar : Fin A) : EnvironmentStage (Fin 2) (Fin A) where
  state_nonempty := ⟨0⟩
  action_nonempty := ⟨astar⟩
  transition s a :=
    if s = 1 then
      exitRow 1 0 (by decide) (onlineLBq H ε astar a) (onlineLBq_nonneg hH hε hεH astar a)
        (onlineLBq_le_one hH hε hεH astar a)
    else stayRow s
  reward s _ := if s = 1 then 1 else 0
  reward_nonneg s _ := by split_ifs <;> norm_num
  reward_le_one s _ := by split_ifs <;> norm_num

/-- The two-state MDP `M_i`, `i ∈ [A]^H` (`chapters/onlineRL.tex:2620–2650`), with optimal action
`i h` at state `1` and (0-based) step `h`. -/
noncomputable def onlineLBSubStages (H : ℕ) (ε : ℝ) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (i : Fin H → Fin A) : Fin H → EnvironmentStage (Fin 2) (Fin A) :=
  fun h => onlineLBSubStage H ε hH hε hεH (i h)

/-- One stage of the general-`S` MDP (`chapters/onlineRL.tex:3020–3060`) with optimal actions
`a⋆ j` in the copies `j < m = ⌊S/2⌋`: a state `s` with `s < m` is copy `s`'s rewarding state
(reward `1`, exit to `s + m` with probability `q_{a⋆ s}(a)`); every other state is absorbing with
reward `0` (copy states `j + m`, and the unused state `2m` when `S` is odd). -/
noncomputable def onlineLBStage (S H : ℕ) (ε : ℝ) (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (astar : Fin (S / 2) → Fin A) :
    EnvironmentStage (Fin S) (Fin A) where
  state_nonempty := ⟨⟨0, by omega⟩⟩
  action_nonempty := ⟨astar ⟨0, by omega⟩⟩
  transition s a :=
    if hs : (s : ℕ) < S / 2 then
      exitRow s ⟨s + S / 2, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (onlineLBq H ε (astar ⟨s, hs⟩) a) (onlineLBq_nonneg hH hε hεH _ a)
        (onlineLBq_le_one hH hε hεH _ a)
    else stayRow s
  reward s _ := if (s : ℕ) < S / 2 then 1 else 0
  reward_nonneg s _ := by split_ifs <;> norm_num
  reward_le_one s _ := by split_ifs <;> norm_num

/-- The general-`S` family `C_mdp = (C^sub_mdp)^{S/2}` (`chapters/onlineRL.tex:3030–3060`),
indexed by `i : Fin (S/2) × Fin H → Fin A`: copy `j` has optimal action `i (j, h)` at step `h`. -/
noncomputable def onlineLBStages (S H : ℕ) (ε : ℝ) (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (i : Fin (S / 2) × Fin H → Fin A) :
    Fin H → EnvironmentStage (Fin S) (Fin A) :=
  fun h => onlineLBStage S H ε hS hH hε hεH (fun j => i (j, h))

/-- `∑_{s < n} c` over `Fin S` restricted to the first `n ≤ S` states. -/
theorem sum_fin_ite_lt (S n : ℕ) (hn : n ≤ S) (c : ℝ) :
    ∑ s : Fin S, (if (s : ℕ) < n then c else 0) = n * c := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x < n then c else 0) S]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range n, (if x < n then c else 0) = n * c := by
    rw [Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))]
    simp
  have h2 : ∑ x ∈ Finset.range r, (if n + x < n then c else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => if_neg (by omega)
  rw [h1, h2, add_zero]

/-- The initial law `ρ(s) = 2/S` for `1 ≤ s ≤ S/2` (`chapters/onlineRL.tex:3067–3072`): uniform on
the copies' rewarding states `s < ⌊S/2⌋`, and `0` elsewhere. -/
noncomputable def onlineLBRho (S : ℕ) (hS : 2 ≤ S) : FiniteDistribution (Fin S) where
  prob s := if (s : ℕ) < S / 2 then 1 / ((S / 2 : ℕ) : ℝ) else 0
  prob_nonneg s := by split_ifs <;> positivity
  sum_prob := by
    rw [sum_fin_ite_lt S (S / 2) (Nat.div_le_self S 2)]
    have : ((S / 2 : ℕ) : ℝ) ≠ 0 := by
      have : 1 ≤ S / 2 := by omega
      exact_mod_cast (by omega : S / 2 ≠ 0)
    field_simp

end StatisticalRL.OnlineLowerBound
