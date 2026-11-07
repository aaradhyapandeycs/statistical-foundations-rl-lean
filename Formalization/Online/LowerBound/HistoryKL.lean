import Formalization.Online.LowerBound.RegretDefinitions
import Formalization.Online.LowerBound.ValueGap
import Formalization.Online.LowerBound.TestingTools

/-!
# Coordinatewise testing in the general-`S` hard family

The step `eq:coordinatewise-testing-lower-bound-online` (`chapters/onlineRL.tex:2852–2885`) lifted to
the general-`S` family (`:3075–3141`), proved directly from the adaptive KL chain rule on the
`k`-episode history law instead of through the source's prose reduction to an induced bandit
algorithm (`:2759–2765`, `:3093–3110`).

Fix a copy `j`, a step `h`, and the optimal actions of all other coordinates. Changing the optimal
action of `(j, h)` from the arm `1` (index `0`) to `a` changes only the step-`h` transition at
state `j`, a Bernoulli row whose KL divergence is at most `4ε²/H³`, and only for the action `a`. An
episode reaches state `j` only if it starts there, which has probability `ρ(j) = 1/⌊S/2⌋`. Hence the
alternatives' history KL divergences sum to at most `4ε² k / (⌊S/2⌋ H³)` after `k` episodes, and reverse
Fano bounds the average probability that the counterfactual action `ã^k_h ∼ π^k_h(· | j)` misses the
optimal action from below by `1/3`.
-/

open scoped BigOperators

namespace StatisticalRL.OnlineLowerBound

open StatisticalRL AdaptiveKL GenerativeLowerBound EnvironmentStage

section Generic

/-- Bounding a family of sequential chain-rule sums by a uniform per-step bound. -/
theorem seqLaw_sum_finiteKLExpression_le {Z : Type*} [Fintype Z] {J : Type*} [Fintype J]
    (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z)
    (κ' : J → (t : ℕ) → (Fin t → Z) → FiniteDistribution Z)
    (hac : ∀ j t h z, (κ' j t h).prob z = 0 → (κ t h).prob z = 0) (T : ℕ) (δ : ℝ)
    (hδ : ∀ t h, ∑ j, finiteKLExpression (κ t h).prob (κ' j t h).prob ≤ δ) :
    ∑ j, finiteKLExpression (seqLaw κ T).prob (seqLaw (κ' j) T).prob ≤ T * δ := by
  have hrw := fun j => seqLaw_finiteKLExpression κ (κ' j) (fun t h _ z hz => hac j t h z hz) T
  simp_rw [hrw]
  rw [Finset.sum_comm]
  calc ∑ t ∈ Finset.range T, ∑ j, ∑ h : Fin t → Z,
          (seqLaw κ t).prob h * finiteKLExpression (κ t h).prob (κ' j t h).prob
      = ∑ t ∈ Finset.range T, ∑ h : Fin t → Z,
          (seqLaw κ t).prob h * ∑ j, finiteKLExpression (κ t h).prob (κ' j t h).prob := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ Finset.range T, ∑ h : Fin t → Z, (seqLaw κ t).prob h * δ :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun h _ =>
          mul_le_mul_of_nonneg_left (hδ t h) ((seqLaw κ t).prob_nonneg h)
    _ = T * δ := by
        have h2 : ∀ t, ∑ h : Fin t → Z, (seqLaw κ t).prob h * δ = δ := fun t => by
          rw [← Finset.sum_mul, (seqLaw κ t).sum_prob, one_mul]
        simp_rw [h2]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Bounding a family of adaptive chain-rule sums by a step-dependent bound `g`. -/
theorem interactionLaw_sum_finiteKLExpression_le_fun {A O J : Type*} [Fintype A] [Fintype O]
    [Fintype J] (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (e' : J → (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ j t h a o, (e' j t h a).prob o = 0 → (e t h a).prob o = 0) (T : ℕ)
    (g : (t : ℕ) → (Fin t → A × O) → A → ℝ)
    (hδ : ∀ t h a, ∑ j, finiteKLExpression (e t h a).prob (e' j t h a).prob ≤ g t h a) :
    ∑ j, finiteKLExpression (interactionLaw π e T).prob (interactionLaw π (e' j) T).prob ≤
      ∑ t ∈ Finset.range T, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h *
        ∑ a, (π t h).prob a * g t h a := by
  have hrw := fun j => interactionLaw_finiteKLExpression π e (e' j) (hac j) T
  simp_rw [hrw]
  rw [Finset.sum_comm]
  calc ∑ t ∈ Finset.range T, ∑ j, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h *
          ∑ a, (π t h).prob a * finiteKLExpression (e t h a).prob (e' j t h a).prob
      = ∑ t ∈ Finset.range T, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h *
          ∑ a, (π t h).prob a * ∑ j, finiteKLExpression (e t h a).prob (e' j t h a).prob := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun h _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ ((interactionLaw π e t).prob_nonneg h)
        exact Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hδ t h a) ((π t h).prob_nonneg a)

theorem compLaw_ac_right {W Z : Type*} [Fintype W] [Fintype Z] (P : FiniteDistribution W)
    (κ κ' : W → FiniteDistribution Z) (hac : ∀ w z, (κ' w).prob z = 0 → (κ w).prob z = 0)
    (x : W × Z) : (compLaw P κ').prob x = 0 → (compLaw P κ).prob x = 0 := by
  intro hx
  change P.prob x.1 * (κ' x.1).prob x.2 = 0 at hx
  change P.prob x.1 * (κ x.1).prob x.2 = 0
  rcases mul_eq_zero.mp hx with h | h
  · rw [h, zero_mul]
  · rw [hac _ _ h, mul_zero]

/-- With a common first law, the KL expression of `compLaw` is the averaged KL of the kernels. -/
theorem compLaw_finiteKLExpression_right {W Z : Type*} [Fintype W] [Fintype Z]
    (P : FiniteDistribution W) (κ κ' : W → FiniteDistribution Z)
    (hac : ∀ w z, (κ' w).prob z = 0 → (κ w).prob z = 0) :
    finiteKLExpression (compLaw P κ).prob (compLaw P κ').prob =
      ∑ w, P.prob w * finiteKLExpression (κ w).prob (κ' w).prob := by
  have h := finiteKLExpression_comp P.prob P.prob (fun w z => (κ w).prob z)
    (fun w z => (κ' w).prob z) (fun w _ => (κ w).sum_prob) (fun _ h => h)
    (fun w _ z hz => hac w z hz)
  rw [finiteKLExpression_self, zero_add] at h
  rw [← h]
  exact Fintype.sum_prod_type _

end Generic

section HardFamily

variable {S H : ℕ} {ε : ℝ}

/-- Support of a general-`S` stage row: an atom has zero mass iff it is neither the current state nor,
for a copy's rewarding state, that copy's absorbing state. -/
theorem onlineLBStage_prob_eq_zero_iff (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (astar : Fin (S / 2) → Fin A) (x o : Fin S) (a : Fin A) :
    ((onlineLBStage S H ε hS hH hε hεH astar).transition x a).prob o = 0 ↔
      (o ≠ x ∧ ¬ ((x : ℕ) < S / 2 ∧ (o : ℕ) = x + S / 2)) := by
  unfold onlineLBStage
  dsimp only
  split_ifs with hx
  · have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
    have hHpos : (0 : ℝ) < H := by linarith
    obtain ⟨hq1, hq2⟩ := onlineLBq_bounds hH hε hεH (astar ⟨x, hx⟩) a
    have hhalf : 1 / (H : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hHpos (by norm_num)]; linarith
    have h2H : 0 < 1 / (2 * (H : ℝ)) := by positivity
    have hq0 : onlineLBq H ε (astar ⟨x, hx⟩) a ≠ 0 := by linarith
    have hq1' : 1 - onlineLBq H ε (astar ⟨x, hx⟩) a ≠ 0 := by linarith
    have hxb : x ≠ ⟨x + S / 2, by omega⟩ := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    simp only [exitRow]
    constructor
    · intro h
      refine ⟨fun hox => ?_, fun ⟨_, hov⟩ => ?_⟩
      · subst hox; rw [if_neg hxb, if_pos rfl] at h; exact hq1' h
      · have : o = ⟨x + S / 2, by omega⟩ := Fin.ext hov
        rw [if_pos this] at h; exact hq0 h
    · rintro ⟨h1, h2⟩
      have : o ≠ ⟨x + S / 2, by omega⟩ := fun h => h2 ⟨hx, by rw [h]⟩
      rw [if_neg this, if_neg h1]
  · simp [stayRow, hx]

theorem onlineLBStage_prob_ne_zero (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (astar : Fin (S / 2) → Fin A) (x o : Fin S) (a : Fin A)
    (h : ((onlineLBStage S H ε hS hH hε hεH astar).transition x a).prob o ≠ 0) :
    o = x ∨ ((x : ℕ) < S / 2 ∧ (o : ℕ) = x + S / 2) := by
  by_contra hc
  push_neg at hc
  exact h ((onlineLBStage_prob_eq_zero_iff hS hH hε hεH astar x o a).mpr
    ⟨hc.1, fun h' => hc.2 h'.1 h'.2⟩)

/-- All instances of the general-`S` family have the same row supports. -/
theorem stepRow_onlineLBStages_ac (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (i i' : Fin (S / 2) × Fin H → Fin A) (t : ℕ) (x o : Fin S)
    (a : Fin A) :
    (stepRow (onlineLBStages S H ε hS hH hε hεH i') t x a).prob o = 0 →
      (stepRow (onlineLBStages S H ε hS hH hε hεH i) t x a).prob o = 0 := by
  unfold stepRow
  split_ifs with ht
  · intro h
    exact (onlineLBStage_prob_eq_zero_iff hS hH hε hεH _ x o a).mpr
      ((onlineLBStage_prob_eq_zero_iff hS hH hε hεH _ x o a).mp h)
  · exact id

/-- An episode of the general-`S` family started at `s` only visits `s` and states `≥ ⌊S/2⌋`; in
particular it never visits another copy's rewarding state. -/
theorem hard_path_reach (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ}
    (i : Fin (S / 2) × Fin H → Fin A) (π : ℕ → StationaryPolicy (Fin S) (Fin A)) (s : Fin S) :
    ∀ (T : ℕ) (x : Fin T → Fin A × Fin S),
      (interactionLaw (episodePolicy π s)
        (episodeEnv (onlineLBStages S H ε hS hH hε hεH i) s) T).prob x ≠ 0 →
      pathCurrentState s T x = s ∨ S / 2 ≤ ((pathCurrentState s T x : Fin S) : ℕ)
  | 0, _, _ => Or.inl rfl
  | T + 1, x, hx => by
    have hx' : (interactionLaw (episodePolicy π s)
        (episodeEnv (onlineLBStages S H ε hS hH hε hεH i) s) T).prob (Fin.init x) *
        ((episodePolicy π s T (Fin.init x)).prob (x (Fin.last T)).1 *
          (episodeEnv (onlineLBStages S H ε hS hH hε hεH i) s T (Fin.init x)
            (x (Fin.last T)).1).prob (x (Fin.last T)).2) ≠ 0 := hx
    have h1 := left_ne_zero_of_mul hx'
    have h3 := right_ne_zero_of_mul (right_ne_zero_of_mul hx')
    have ih := hard_path_reach hS hH hε hεH i π s T (Fin.init x) h1
    show (x (Fin.last T)).2 = s ∨ S / 2 ≤ ((x (Fin.last T)).2 : ℕ)
    unfold episodeEnv stepRow at h3
    split_ifs at h3 with hT
    · rcases onlineLBStage_prob_ne_zero hS hH hε hεH _ _ _ _ h3 with h | ⟨_, ho⟩
      · rw [h]; exact ih
      · right; omega
    · have heq : (x (Fin.last T)).2 = pathCurrentState s T (Fin.init x) := by
        by_contra hne
        apply h3
        simp [EnvironmentStage.pointMass, hne]
      rw [heq]; exact ih

variable {M : ℕ}

/-- Away from the flipped coordinate `(j, h)`, the stage rows of two instances that agree off
`(j, h)` coincide. -/
theorem stepRow_eq_of_agree (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    {A : ℕ} (i i' : Fin (S / 2) × Fin H → Fin A) (j : Fin (S / 2)) (h : Fin H)
    (hagree : ∀ c, c ≠ (j, h) → i' c = i c) (t : ℕ) (x : Fin S) (b : Fin A)
    (hne : ¬ (t = (h : ℕ) ∧ (x : ℕ) = j)) :
    stepRow (onlineLBStages S H ε hS hH hε hεH i') t x b =
      stepRow (onlineLBStages S H ε hS hH hε hεH i) t x b := by
  unfold stepRow
  split_ifs with ht
  · unfold onlineLBStages onlineLBStage
    dsimp only
    split_ifs with hx
    · have hc : ((⟨x, hx⟩ : Fin (S / 2)), (⟨t, ht⟩ : Fin H)) ≠ (j, h) := fun hc =>
        hne ⟨congrArg (fun p => (p.2 : ℕ)) hc, congrArg (fun p => (p.1 : ℕ)) hc⟩
      simp only [hagree _ hc]
    · rfl
  · rfl

/-- At the flipped coordinate, the alternatives' row KL divergences sum to at most `4ε²/H³`. -/
theorem stepRow_flip_sum_le (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    (i : Fin (S / 2) × Fin H → Fin (M + 1)) (i' : Fin M → Fin (S / 2) × Fin H → Fin (M + 1))
    (j : Fin (S / 2)) (h : Fin H) (hi : i (j, h) = 0) (hi' : ∀ a', i' a' (j, h) = a'.succ)
    (x : Fin S) (hx : (x : ℕ) = j) (b : Fin (M + 1)) :
    ∑ a' : Fin M, finiteKLExpression (stepRow (onlineLBStages S H ε hS hH hε hεH i) h x b).prob
        (stepRow (onlineLBStages S H ε hS hH hε hεH (i' a')) h x b).prob ≤
      4 * ε ^ 2 / (H : ℝ) ^ 3 := by
  have hxm : (x : ℕ) < S / 2 := hx ▸ j.isLt
  have hxj : (⟨x, hxm⟩ : Fin (S / 2)) = j := Fin.ext hx
  have hrow : ∀ i'' : Fin (S / 2) × Fin H → Fin (M + 1),
      stepRow (onlineLBStages S H ε hS hH hε hεH i'') h x b =
        exitRow x ⟨x + S / 2, by omega⟩
          (fun hc => by have := congrArg Fin.val hc; simp at this; omega)
          (onlineLBq H ε (i'' (j, h)) b) (onlineLBq_nonneg hH hε hεH _ b)
          (onlineLBq_le_one hH hε hεH _ b) := by
    intro i''
    unfold stepRow onlineLBStages onlineLBStage
    rw [dif_pos h.isLt]
    dsimp only
    rw [dif_pos hxm]
    simp only [Fin.eta, hxj]
  simp_rw [hrow, exitRow_finiteKLExpression, hi, hi']
  refine sum_succ_le_of_single b _ _ (by positivity) (fun a' ha' => ?_) (fun a' _ =>
    onlineLBq_bernoulliKL_le hH hε hεH _ _ _)
  rw [← onlineLBq_zero_eq_succ H ε a' b ha']
  unfold bernoulliKLExpression
  have hm : ∀ y : ℝ, y * Real.log (y / y) = 0 := fun y => by
    by_cases hy : y = 0 <;> simp [hy]
  rw [hm, hm, add_zero]

/-- Path-level bound: the alternatives' episode-path KL divergences from a start state `s` sum to at
most `4ε²/H³` if `s` is copy `j`'s rewarding state, and to `0` otherwise. -/
theorem path_sum_KL_le (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    (i : Fin (S / 2) × Fin H → Fin (M + 1)) (i' : Fin M → Fin (S / 2) × Fin H → Fin (M + 1))
    (j : Fin (S / 2)) (h : Fin H) (hi : i (j, h) = 0) (hi' : ∀ a', i' a' (j, h) = a'.succ)
    (hagree : ∀ a' c, c ≠ (j, h) → i' a' c = i c)
    (π : ℕ → StationaryPolicy (Fin S) (Fin (M + 1))) (s : Fin S) :
    ∑ a' : Fin M, finiteKLExpression
        (episodePathLaw (onlineLBStages S H ε hS hH hε hεH i) π s).prob
        (episodePathLaw (onlineLBStages S H ε hS hH hε hεH (i' a')) π s).prob ≤
      if (s : ℕ) = j then 4 * ε ^ 2 / (H : ℝ) ^ 3 else 0 := by
  set δ : ℝ := 4 * ε ^ 2 / (H : ℝ) ^ 3 with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  let g : (t : ℕ) → (Fin t → Fin (M + 1) × Fin S) → Fin (M + 1) → ℝ := fun t y _ =>
    if t = (h : ℕ) ∧ ((pathCurrentState s t y : Fin S) : ℕ) = j then δ else 0
  have hg : ∀ t y b, ∑ a' : Fin M, finiteKLExpression
      (episodeEnv (onlineLBStages S H ε hS hH hε hεH i) s t y b).prob
      (episodeEnv (onlineLBStages S H ε hS hH hε hεH (i' a')) s t y b).prob ≤ g t y b := by
    intro t y b
    by_cases hc : t = (h : ℕ) ∧ ((pathCurrentState s t y : Fin S) : ℕ) = j
    · simp only [g, if_pos hc]
      obtain ⟨rfl, hcx⟩ := hc
      exact stepRow_flip_sum_le hS hH hε hεH i i' j h hi hi' _ hcx b
    · simp only [g, if_neg hc]
      refine le_of_eq (Finset.sum_eq_zero fun a' _ => ?_)
      unfold episodeEnv
      rw [stepRow_eq_of_agree hS hH hε hεH i (i' a') j h (hagree a') t _ b hc,
        AdaptiveKL.finiteKLExpression_self]
  have hac : ∀ (a' : Fin M) t y b o,
      (episodeEnv (onlineLBStages S H ε hS hH hε hεH (i' a')) s t y b).prob o = 0 →
        (episodeEnv (onlineLBStages S H ε hS hH hε hεH i) s t y b).prob o = 0 :=
    fun a' t y b o => stepRow_onlineLBStages_ac hS hH hε hεH i (i' a') t _ o b
  have hle := interactionLaw_sum_finiteKLExpression_le_fun (episodePolicy π s)
    (episodeEnv (onlineLBStages S H ε hS hH hε hεH i) s)
    (fun a' => episodeEnv (onlineLBStages S H ε hS hH hε hεH (i' a')) s) hac H g hg
  refine hle.trans ?_
  -- only the step `t = h` contributes
  have hπ : ∀ t (y : Fin t → Fin (M + 1) × Fin S),
      ∑ b, (episodePolicy π s t y).prob b * g t y b =
        if t = (h : ℕ) ∧ ((pathCurrentState s t y : Fin S) : ℕ) = j then δ else 0 := by
    intro t y
    simp only [g]
    rw [← Finset.sum_mul, (episodePolicy π s t y).sum_prob, one_mul]
  simp_rw [hπ]
  rw [Finset.sum_eq_single_of_mem (h : ℕ) (Finset.mem_range.mpr h.isLt) (fun t _ ht => by
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg (fun hc => ht hc.1), mul_zero])]
  simp only [true_and]
  by_cases hs : (s : ℕ) = j
  · rw [if_pos hs]
    calc ∑ y : Fin h → Fin (M + 1) × Fin S,
          (interactionLaw (episodePolicy π s)
            (episodeEnv (onlineLBStages S H ε hS hH hε hεH i) s) h).prob y *
          (if ((pathCurrentState s h y : Fin S) : ℕ) = j then δ else 0)
        ≤ ∑ y : Fin h → Fin (M + 1) × Fin S,
          (interactionLaw (episodePolicy π s)
            (episodeEnv (onlineLBStages S H ε hS hH hε hεH i) s) h).prob y * δ :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
            (by split_ifs <;> linarith) ((interactionLaw _ _ _).prob_nonneg y)
      _ = δ := by rw [← Finset.sum_mul, (interactionLaw _ _ _).sum_prob, one_mul]
  · rw [if_neg hs]
    refine le_of_eq (Finset.sum_eq_zero fun y _ => ?_)
    by_cases hy : (interactionLaw (episodePolicy π s)
        (episodeEnv (onlineLBStages S H ε hS hH hε hεH i) s) h).prob y = 0
    · rw [hy, zero_mul]
    · have hr := hard_path_reach hS hH hε hεH i π s h y hy
      have hcur : ((pathCurrentState s h y : Fin S) : ℕ) ≠ j := by
        rcases hr with hr | hr
        · rw [hr]; exact hs
        · have := j.isLt; omega
      rw [if_neg hcur, mul_zero]

/-- The history law of the general-`S` family for a seed-free learner `pol`. -/
noncomputable def hardHistoryLaw (S H : ℕ) (ε : ℝ) (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (i : Fin (S / 2) × Fin H → Fin A)
    (pol : (τ : ℕ) → (Fin τ → OnlineEpisode (Fin S) (Fin A) H) → ℕ → StationaryPolicy (Fin S) (Fin A))
    (k : ℕ) : FiniteDistribution (Fin k → OnlineEpisode (Fin S) (Fin A) H) :=
  seqLaw (fun τ p => episodeLaw (onlineLBStages S H ε hS hH hε hεH i) (onlineLBRho S hS) (pol τ p)) k

/-- History-level bound: after `k` episodes the alternatives' history KL divergences sum to at most
`k · 4ε² / (⌊S/2⌋ H³)`. -/
theorem history_sum_KL_le (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    (i : Fin (S / 2) × Fin H → Fin (M + 1)) (i' : Fin M → Fin (S / 2) × Fin H → Fin (M + 1))
    (j : Fin (S / 2)) (h : Fin H) (hi : i (j, h) = 0) (hi' : ∀ a', i' a' (j, h) = a'.succ)
    (hagree : ∀ a' c, c ≠ (j, h) → i' a' c = i c)
    (pol : (τ : ℕ) → (Fin τ → OnlineEpisode (Fin S) (Fin (M + 1)) H) →
      ℕ → StationaryPolicy (Fin S) (Fin (M + 1))) (k : ℕ) :
    ∑ a' : Fin M, finiteKLExpression (hardHistoryLaw S H ε hS hH hε hεH i pol k).prob
        (hardHistoryLaw S H ε hS hH hε hεH (i' a') pol k).prob ≤
      k * (4 * ε ^ 2 / (H : ℝ) ^ 3 / ((S / 2 : ℕ) : ℝ)) := by
  have hpathac : ∀ (a' : Fin M) (π : ℕ → StationaryPolicy (Fin S) (Fin (M + 1))) s z,
      (episodePathLaw (onlineLBStages S H ε hS hH hε hεH (i' a')) π s).prob z = 0 →
        (episodePathLaw (onlineLBStages S H ε hS hH hε hεH i) π s).prob z = 0 :=
    fun a' π s z => interactionLaw_ac' _ _ _
      (fun t y b o => stepRow_onlineLBStages_ac hS hH hε hεH i (i' a') t _ o b) H z
  refine seqLaw_sum_finiteKLExpression_le _ _
    (fun a' τ p z => compLaw_ac_right _ _ _ (fun s z => hpathac a' (pol τ p) s z) z) k _
    (fun τ p => ?_)
  -- one episode
  simp_rw [compLaw_finiteKLExpression_right _ _ _ (fun s z => hpathac _ (pol τ p) s z)]
  rw [Finset.sum_comm]
  calc ∑ s, ∑ a' : Fin M, (onlineLBRho S hS).prob s * finiteKLExpression
          (episodePathLaw (onlineLBStages S H ε hS hH hε hεH i) (pol τ p) s).prob
          (episodePathLaw (onlineLBStages S H ε hS hH hε hεH (i' a')) (pol τ p) s).prob
      = ∑ s, (onlineLBRho S hS).prob s * ∑ a' : Fin M, finiteKLExpression
          (episodePathLaw (onlineLBStages S H ε hS hH hε hεH i) (pol τ p) s).prob
          (episodePathLaw (onlineLBStages S H ε hS hH hε hεH (i' a')) (pol τ p) s).prob :=
        Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ s, (onlineLBRho S hS).prob s *
          (if (s : ℕ) = j then 4 * ε ^ 2 / (H : ℝ) ^ 3 else 0) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
          (path_sum_KL_le hS hH hε hεH i i' j h hi hi' hagree (pol τ p) s)
          ((onlineLBRho S hS).prob_nonneg s)
    _ = 4 * ε ^ 2 / (H : ℝ) ^ 3 / ((S / 2 : ℕ) : ℝ) := by
        have hjS : (j : ℕ) < S := by have := j.isLt; omega
        rw [Finset.sum_eq_single ⟨j, hjS⟩ (fun s _ hs => by
          rw [if_neg (fun h' => hs (Fin.ext h')), mul_zero]) (by simp)]
        simp only [if_true]
        unfold onlineLBRho
        dsimp only
        rw [if_pos j.isLt]
        ring

end HardFamily

end StatisticalRL.OnlineLowerBound
