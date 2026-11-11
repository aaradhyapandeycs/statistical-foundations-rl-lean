import Formalization.MultiAgent.Hedge.Events

/-!
# Theorem 7.7: the good event, per stage, state and player

`good_E1`, `good_E2a`, `good_E2b`, `good_E3` rewrite the event sums of `Good` as sums over rounds
`t` (and actions `b`) of the stage quantities `q̂ = gain`, `q̃ = qtil`, `m = mbar`, `csec`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76
open StatisticalRL.Online.Hedge StatisticalRL.AdaptiveKL

variable {m S H : ℕ} {A : Fin m → ℕ}

theorem Alg.sum_index (al : Alg m S H A) (F : Fin al.N → ℝ) :
    ∑ k, F k = ∑ d : ((Fin H × Fin S) × Fin al.T) × Fin (numPairs A),
      F (slotEquiv H S al.T (numPairs A) d) :=
  (Equiv.sum_comp (slotEquiv H S al.T (numPairs A)) F).symm

theorem Alg.dec_slotEquiv (al : Alg m S H A) (d : ((Fin H × Fin S) × Fin al.T) × Fin (numPairs A)) :
    al.dec (slotEquiv H S al.T (numPairs A) d) = d := Equiv.symm_apply_apply _ _

/-- Collapse a sum over slots supported on a fixed `(c₀, s₀, j₀)`. -/
theorem sum_slots_single {T M : ℕ} (F : ((Fin H × Fin S) × Fin T) × Fin M → ℝ) (c₀ : Fin H)
    (s₀ : Fin S) (j₀ : Fin M) (hF : ∀ d, ¬ (d.1.1.1 = c₀ ∧ d.1.1.2 = s₀ ∧ d.2 = j₀) → F d = 0) :
    ∑ d, F d = ∑ t, F (((c₀, s₀), t), j₀) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [sum_eq_single (c₀, s₀)]
  · refine sum_congr rfl fun t _ => ?_
    rw [sum_eq_single j₀]
    · intro j _ hj; exact hF _ (by simp [hj])
    · simp
  · intro p _ hp
    refine sum_eq_zero fun t _ => sum_eq_zero fun j _ => hF _ ?_
    rintro ⟨h1, h2, _⟩
    exact hp (Prod.ext h1 h2)
  · simp

/-- Collapse a sum over slots supported on `(c₀, s₀)` and pairs of player `i₀`. -/
theorem sum_slots_player {T : ℕ} (F : ((Fin H × Fin S) × Fin T) × Fin (numPairs A) → ℝ)
    (c₀ : Fin H) (s₀ : Fin S) (i₀ : Fin m)
    (hF : ∀ d, ¬ (d.1.1.1 = c₀ ∧ d.1.1.2 = s₀ ∧ ((pairEquiv A).symm d.2).1 = i₀) → F d = 0) :
    ∑ d, F d = ∑ t, ∑ b : Fin (A i₀), F (((c₀, s₀), t), pairEquiv A ⟨i₀, b⟩) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [sum_eq_single (c₀, s₀)]
  · refine sum_congr rfl fun t _ => ?_
    rw [← Equiv.sum_comp (pairEquiv A), Fintype.sum_sigma, sum_eq_single i₀]
    · intro i _ hi
      refine sum_eq_zero fun b _ => hF _ ?_
      simp [hi]
    · simp
  · intro p _ hp
    refine sum_eq_zero fun t _ => sum_eq_zero fun j _ => hF _ ?_
    rintro ⟨h1, h2, _⟩
    exact hp (Prod.ext h1 h2)
  · simp

theorem Alg.gain_fin (al : Alg m S H A) (V : Fin m → Fin S → ℝ) (x : Fin al.N → Entry m S H A)
    (c : Fin H) (s : Fin S) (i : Fin m) (t : Fin al.T) (b : Fin (A i)) :
    al.gain V x c s i t b = al.gz V c s i (x (al.slot c s t (pairEquiv A ⟨i, b⟩))) := by
  simp [Alg.gain, t.isLt]

/-- The conditional second moment as a kernel sum. -/
theorem Alg.kernel_sq (al : Alg m S H A) (G : MarkovGame m S H A) (x : Fin al.N → Entry m S H A)
    (c : Fin H) (s : Fin S) (t : Fin al.T) (i : Fin m) (b : Fin (A i)) (α μ : ℝ) :
    ∑ z, (interactionKernel al.rule (genEnv G) (al.slot c s t (pairEquiv A ⟨i, b⟩))
        (seqPrefix (al.slot c s t (pairEquiv A ⟨i, b⟩)) x)).prob z *
        (α * (al.gz (al.vb x c) c s i z - μ)) ^ 2 = α ^ 2 * al.csec G x c s t i b μ := by
  rw [al.kernel_sum_slot]
  unfold Alg.csec
  simp only [mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun s' _ => by ring

theorem Alg.kernel_lin (al : Alg m S H A) (G : MarkovGame m S H A) (x : Fin al.N → Entry m S H A)
    (c : Fin H) (s : Fin S) (t : Fin al.T) (i : Fin m) (b : Fin (A i)) (α μ : ℝ) :
    ∑ z, (interactionKernel al.rule (genEnv G) (al.slot c s t (pairEquiv A ⟨i, b⟩))
        (seqPrefix (al.slot c s t (pairEquiv A ⟨i, b⟩)) x)).prob z *
        (α * (al.gz (al.vb x c) c s i z - μ) ^ 2) = α * al.csec G x c s t i b μ := by
  rw [al.kernel_sum_slot]
  unfold Alg.csec
  simp only [mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun s' _ => by ring

theorem Alg.good_E1 (al : Alg m S H A) (G : MarkovGame m S H A) {lam L : ℝ}
    {x : Fin al.N → Entry m S H A} (hg : al.Good G lam L x) (c : Fin H) (s : Fin S) (i : Fin m)
    (b : Fin (A i)) :
    ∑ t : Fin al.T, (lam * (al.qtil G x c s t i b - al.gain (al.vb x c) x c s i t b) -
      lam ^ 2 * al.csec G x c s t i b (al.qtil G x c s t i b)) < L := by
  have h := hg (Sum.inl (c, s, pairEquiv A ⟨i, b⟩))
  rw [al.sum_index] at h
  rw [sum_slots_single _ c s (pairEquiv A ⟨i, b⟩)] at h
  · refine lt_of_le_of_lt (le_of_eq ?_) h
    refine sum_congr rfl fun t _ => ?_
    have hnm : ¬ al.IsMult (Sum.inl (c, s, pairEquiv A ⟨i, b⟩)) := by
      rintro ⟨_, _, _, h⟩; cases h
    simp only [Alg.fv, if_neg hnm, al.dec_slotEquiv]
    have hk : slotEquiv H S al.T (numPairs A) (((c, s), t), pairEquiv A ⟨i, b⟩) =
        al.slot c s t (pairEquiv A ⟨i, b⟩) := rfl
    have hinc : ∀ z, al.incr G lam (Sum.inl (c, s, pairEquiv A ⟨i, b⟩))
        (((c, s), t), pairEquiv A ⟨i, b⟩) x z =
        (-lam) * (al.gz (al.vb x c) c s i z - al.qtil G x c s t i b) := by
      intro z
      simp only [Alg.incr]
      rw [Equiv.symm_apply_apply]
      simp only [and_self, ↓reduceIte]
      ring
    simp only [hinc]
    rw [hk, al.kernel_sq, al.gain_fin]
    ring
  · intro d hd
    have hnm : ¬ al.IsMult (Sum.inl (c, s, pairEquiv A ⟨i, b⟩)) := by
      rintro ⟨_, _, _, h⟩; cases h
    have hz : ∀ z, al.incr G lam (Sum.inl (c, s, pairEquiv A ⟨i, b⟩)) (al.dec
        (slotEquiv H S al.T (numPairs A) d)) x z = 0 := by
      intro z
      rw [al.dec_slotEquiv]
      simp only [Alg.incr]
      rw [if_neg hd]
    simp only [Alg.fv, if_neg hnm, hz]
    simp

/-- Shared shape of the player events. -/
theorem Alg.good_player (al : Alg m S H A) (G : MarkovGame m S H A) {lam L : ℝ}
    {x : Fin al.N → Entry m S H A} (hg : al.Good G lam L x) (c : Fin H) (s : Fin S) (i : Fin m)
    (κ : Fin 3) :
    ∑ t : Fin al.T, ∑ b : Fin (A i), al.fv G lam (Sum.inr (c, s, i, κ))
      (al.slot c s t (pairEquiv A ⟨i, b⟩)) x < L := by
  have h := hg (Sum.inr (c, s, i, κ))
  rw [al.sum_index] at h
  rw [sum_slots_player _ c s i] at h
  · exact h
  · intro d hd
    have hz : ∀ z, al.incr G lam (Sum.inr (c, s, i, κ)) (al.dec
        (slotEquiv H S al.T (numPairs A) d)) x z = 0 := by
      intro z
      rw [al.dec_slotEquiv]
      simp only [Alg.incr]
      rw [if_neg hd]
    simp only [Alg.fv, hz]
    split_ifs <;> simp

theorem Alg.incr_player (al : Alg m S H A) (G : MarkovGame m S H A) (lam : ℝ)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : Fin al.T) (i : Fin m)
    (b : Fin (A i)) (κ : Fin 3) (z : Entry m S H A) :
    al.incr G lam (Sum.inr (c, s, i, κ)) (al.dec (al.slot c s t (pairEquiv A ⟨i, b⟩))) x z =
      if κ = 0 then lam * (al.hedgeAt x c s i t).prob b *
          (al.gz (al.vb x c) c s i z - al.qtil G x c s t i b)
      else if κ = 1 then lam * (al.hedgeAt x c s i t).prob b *
          (al.qtil G x c s t i b - al.gz (al.vb x c) c s i z)
      else (al.hedgeAt x c s i t).prob b * (al.gz (al.vb x c) c s i z - al.mbar G x c s t i) ^ 2 /
        (H : ℝ) ^ 2 := by
  rw [show al.slot c s t (pairEquiv A ⟨i, b⟩) =
    slotEquiv H S al.T (numPairs A) (((c, s), t), pairEquiv A ⟨i, b⟩) from rfl, al.dec_slotEquiv]
  simp only [Alg.incr]
  rw [Equiv.symm_apply_apply]
  simp only [and_self, ↓reduceIte]

theorem Alg.good_E2a (al : Alg m S H A) (G : MarkovGame m S H A) {lam L : ℝ}
    {x : Fin al.N → Entry m S H A} (hg : al.Good G lam L x) (c : Fin H) (s : Fin S) (i : Fin m) :
    ∑ t : Fin al.T, ∑ b : Fin (A i),
      (lam * (al.hedgeAt x c s i t).prob b * (al.gain (al.vb x c) x c s i t b - al.qtil G x c s t i b) -
        lam ^ 2 * (al.hedgeAt x c s i t).prob b ^ 2 * al.csec G x c s t i b (al.qtil G x c s t i b))
      < L := by
  refine lt_of_le_of_lt (le_of_eq ?_) (al.good_player G hg c s i 0)
  refine sum_congr rfl fun t _ => sum_congr rfl fun b _ => ?_
  have hnm : ¬ al.IsMult (Sum.inr (c, s, i, (0 : Fin 3))) := by
    rintro ⟨_, _, _, h⟩; simp at h
  simp only [Alg.fv, if_neg hnm, al.incr_player, ↓reduceIte]
  rw [al.kernel_sq, al.gain_fin]
  ring

theorem Alg.good_E2b (al : Alg m S H A) (G : MarkovGame m S H A) {lam L : ℝ}
    {x : Fin al.N → Entry m S H A} (hg : al.Good G lam L x) (c : Fin H) (s : Fin S) (i : Fin m) :
    ∑ t : Fin al.T, ∑ b : Fin (A i),
      (lam * (al.hedgeAt x c s i t).prob b * (al.qtil G x c s t i b - al.gain (al.vb x c) x c s i t b) -
        lam ^ 2 * (al.hedgeAt x c s i t).prob b ^ 2 * al.csec G x c s t i b (al.qtil G x c s t i b))
      < L := by
  refine lt_of_le_of_lt (le_of_eq ?_) (al.good_player G hg c s i 1)
  refine sum_congr rfl fun t _ => sum_congr rfl fun b _ => ?_
  have hnm : ¬ al.IsMult (Sum.inr (c, s, i, (1 : Fin 3))) := by
    rintro ⟨_, _, _, h⟩; simp at h
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  simp only [Alg.fv, if_neg hnm, al.incr_player, h10, ↓reduceIte]
  have : ∀ z, lam * (al.hedgeAt x c s i t).prob b *
      (al.qtil G x c s t i b - al.gz (al.vb x c) c s i z) =
      (-(lam * (al.hedgeAt x c s i t).prob b)) * (al.gz (al.vb x c) c s i z - al.qtil G x c s t i b) :=
    fun z => by ring
  simp only [this]
  rw [al.kernel_sq, al.gain_fin]
  ring

theorem Alg.good_E3 (al : Alg m S H A) (G : MarkovGame m S H A) {lam L : ℝ}
    {x : Fin al.N → Entry m S H A} (hg : al.Good G lam L x) (c : Fin H) (s : Fin S) (i : Fin m) :
    ∑ t : Fin al.T, ∑ b : Fin (A i),
      ((al.hedgeAt x c s i t).prob b * (al.gain (al.vb x c) x c s i t b - al.mbar G x c s t i) ^ 2 /
          (H : ℝ) ^ 2 -
        2 * ((al.hedgeAt x c s i t).prob b / (H : ℝ) ^ 2 * al.csec G x c s t i b (al.mbar G x c s t i)))
      < L := by
  refine lt_of_le_of_lt (le_of_eq ?_) (al.good_player G hg c s i 2)
  refine sum_congr rfl fun t _ => sum_congr rfl fun b _ => ?_
  have hm : al.IsMult (Sum.inr (c, s, i, (2 : Fin 3))) := ⟨c, s, i, rfl⟩
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [Alg.fv, if_pos hm, al.incr_player, h20, h21, ↓reduceIte]
  have : ∀ z, (al.hedgeAt x c s i t).prob b * (al.gz (al.vb x c) c s i z - al.mbar G x c s t i) ^ 2 /
      (H : ℝ) ^ 2 = ((al.hedgeAt x c s i t).prob b / (H : ℝ) ^ 2) *
        (al.gz (al.vb x c) c s i z - al.mbar G x c s t i) ^ 2 := fun z => by ring
  simp only [this]
  rw [al.kernel_lin, al.gain_fin]
  ring

end StatisticalRL.Ch7Rest.Marl77
