import Formalization.ModelFree.FiniteQ.Unfolding
import Formalization.MDP.Basic

/-! # Pathwise range of the finite-horizon Q-learning iterates

Finite-horizon analogue of `lemma:non-negativity-Qt-Vt`: if `0 ≤ Q_{0,h} ≤ H + 1 - h` and the
learning rates used lie in `[0,1]`, then `0 ≤ Q_{t,h} ≤ H + 1 - h` for every iteration, on every
sample path. In the list representation the source bound `H + 1 - h` is the number of stages
remaining, i.e. the length of the stage list. -/

namespace StatisticalRL.FiniteQLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem actionMaximum_le_of_forall {Action : Type*} [Fintype Action] [Nonempty Action]
    {f : Action → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) : actionMaximum f ≤ c :=
  (Finset.sup'_le_iff Finset.univ_nonempty f).2 fun a _ ↦ h a

theorem le_actionMaximum_of_forall {Action : Type*} [Fintype Action] [Nonempty Action]
    {f : Action → ℝ} {c : ℝ} (h : ∀ a, c ≤ f a) : c ≤ actionMaximum f :=
  (h (Classical.arbitrary Action)).trans (le_actionMaximum f _)

/-- The source initialization range, stage by stage: the first stage of a list of length `k + 1`
(source stage `h` with `H + 1 - h = k + 1`) has `0 ≤ Q_{0,h} ≤ k + 1`. -/
def InitBounded : List (LearningStage State Action) → Prop
  | [] => True
  | x :: xs => (∀ s a, 0 ≤ x.init s a ∧ x.init s a ≤ xs.length + 1) ∧ InitBounded xs

theorem initBounded_iff (L : List (LearningStage State Action)) :
    InitBounded L ↔ ∀ k (hk : k < L.length) (s : State) (a : Action),
      0 ≤ (L[k]).init s a ∧ (L[k]).init s a ≤ (L.length - k : ℕ) := by
  induction L with
  | nil => simp [InitBounded]
  | cons x xs ih =>
    simp only [InitBounded, ih, List.length_cons]
    constructor
    · rintro ⟨h0, hrest⟩ k hk s a
      cases k with
      | zero => simpa using h0 s a
      | succ k =>
        have := hrest k (by omega) s a
        simpa [show xs.length + 1 - (k + 1) = xs.length - k by omega] using this
    · intro h
      refine ⟨fun s a ↦ by simpa using h 0 (by omega) s a, fun k hk s a ↦ ?_⟩
      have := h (k + 1) (by omega) s a
      simpa [show xs.length + 1 - (k + 1) = xs.length - k by omega] using this

theorem InitBounded.drop {L : List (LearningStage State Action)} (hL : InitBounded L) (n : ℕ) :
    InitBounded (L.drop n) := by
  induction n generalizing L with
  | zero => simpa using hL
  | succ n ih =>
    cases L with
    | nil => simp [InitBounded]
    | cons x xs => simpa using ih hL.2

/-- The source initialization hypothesis `0 ≤ Q_{0,h} ≤ H + 1 - h` (0-based: `H - h`) gives the
stagewise range of the sampled stage list. -/
theorem initBounded_sampledStages {H : ℕ} (E : Fin H → EnvironmentStage State Action) (T : ℕ)
    (Q₀ : Fin H → State → Action → ℝ)
    (hQ₀ : ∀ h s a, 0 ≤ Q₀ h s a ∧ Q₀ h s a ≤ (H : ℝ) - h)
    (data : FiniteHorizonGenerative.Samples State Action H T) :
    InitBounded (sampledStages E T Q₀ data) := by
  rw [initBounded_iff]
  intro k hk s a
  have hkH : k < H := by simpa [sampledStages] using hk
  have h := hQ₀ ⟨k, hkH⟩ s a
  simp only [sampledStages, List.getElem_ofFn, List.length_ofFn]
  refine ⟨h.1, ?_⟩
  rw [Nat.cast_sub hkH.le]
  exact h.2

/-- Pathwise range of the iterates: `0 ≤ Q_{t,h} ≤ H + 1 - h` for `t ≤ N`, provided the
rates `η_1, …, η_N` lie in `[0,1]`. -/
theorem iterate_mem_range (η : ℕ → ℝ) (N : ℕ)
    (hη : ∀ t, 1 ≤ t → t ≤ N → 0 ≤ η t ∧ η t ≤ 1) :
    ∀ (L : List (LearningStage State Action)), InitBounded L →
      ∀ t, t ≤ N → ∀ s a, 0 ≤ iterate η L t s a ∧ iterate η L t s a ≤ L.length := by
  intro L
  induction L with
  | nil => intro _ t _ s a; simp [iterate]
  | cons x xs ih =>
    intro hL t
    induction t with
    | zero =>
      intro _ s a
      have := hL.1 s a
      simpa [iterate, headIterate] using this
    | succ t iht =>
      intro htN s a
      letI : Nonempty Action := x.env.action_nonempty
      have hprev := iht (by omega) s a
      have hnext := ih hL.2 (t + 1) htN
      have hmax0 : 0 ≤ actionMaximum (iterate η xs (t + 1) (x.sample t s a)) :=
        le_actionMaximum_of_forall fun a' ↦ (hnext _ a').1
      have hmax1 : actionMaximum (iterate η xs (t + 1) (x.sample t s a)) ≤ xs.length :=
        actionMaximum_le_of_forall fun a' ↦ (hnext _ a').2
      have hr0 := x.env.reward_nonneg s a
      have hr1 := x.env.reward_le_one s a
      obtain ⟨he0, he1⟩ := hη (t + 1) (by omega) htN
      change 0 ≤ (1 - η (t + 1)) * iterate η (x :: xs) t s a + η (t + 1) * (x.env.reward s a +
          actionMaximum (iterate η xs (t + 1) (x.sample t s a))) ∧
        (1 - η (t + 1)) * iterate η (x :: xs) t s a + η (t + 1) * (x.env.reward s a +
          actionMaximum (iterate η xs (t + 1) (x.sample t s a))) ≤ ((x :: xs).length : ℝ)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hprev ⊢
      constructor
      · have h1 : 0 ≤ 1 - η (t + 1) := by linarith
        exact add_nonneg (mul_nonneg h1 hprev.1) (mul_nonneg he0 (by linarith))
      · have h1 : 0 ≤ 1 - η (t + 1) := by linarith
        have ha := mul_le_mul_of_nonneg_left hprev.2 h1
        have hb : η (t + 1) * (x.env.reward s a +
            actionMaximum (iterate η xs (t + 1) (x.sample t s a))) ≤
            η (t + 1) * ((xs.length : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) he0
        nlinarith

end StatisticalRL.FiniteQLearning
