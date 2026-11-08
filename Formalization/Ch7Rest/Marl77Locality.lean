import Formalization.Ch7Rest.Marl77Algorithm
import Formalization.Probability.SeqLawExpTail

/-!
# Theorem 7.7: locality of the algorithm and the step law

* Slot arithmetic: stage `c` occupies `[stageStart c, stageStart (c+1))`, round `t` of
  `(c, s)` starts at `slotStart c s t`.
* Every algorithm quantity used at index `k` depends only on history entries before `k`
  (`vb_congr`, `hedgeAt_congr`, `queryAt_congr`).
* `rule_pre`: the rule applied to the true prefix is `queryAt x k`.
* `kernel_sum_slot`: the conditional law of the entry at slot `(c, s, t, (i, b))` given the prefix:
  `a ∼ devDist (⊗_j π^t_j) i b`, `s′ ∼ P_{H−c}(·|s, a)`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76
open StatisticalRL.Online.Hedge StatisticalRL.AdaptiveKL

variable {m S H : ℕ} {A : Fin m → ℕ}

/-! ### Slot arithmetic -/

/-- First index of stage `c`. -/
def Alg.stageStart (al : Alg m S H A) (c : ℕ) : ℕ := numPairs A * (al.T * (S * c))

/-- First index of round `t` of `(c, s)`. -/
def Alg.slotStart (al : Alg m S H A) (c : ℕ) (s : ℕ) (t : ℕ) : ℕ :=
  numPairs A * (t + al.T * (s + S * c))

theorem Alg.slotStart_le_slot (al : Alg m S H A) (c : Fin H) (s : Fin S) (t : Fin al.T)
    (j : Fin (numPairs A)) : al.slotStart c s t ≤ (al.slot c s t j).val := by
  rw [al.slot_val, slotStart]; omega

theorem Alg.slot_lt_slotStart (al : Alg m S H A) (c : Fin H) (s : Fin S) (t' : Fin al.T)
    (j : Fin (numPairs A)) (t : ℕ) (ht : (t' : ℕ) < t) :
    (al.slot c s t' j).val < al.slotStart c s t := by
  rw [al.slot_val, slotStart]
  have hj := j.isLt
  have : (t' : ℕ) + al.T * (s + S * c) + 1 ≤ t + al.T * (s + S * c) := by omega
  calc (j : ℕ) + numPairs A * (t' + al.T * (s + S * c))
      < numPairs A * (t' + al.T * (s + S * c)) + numPairs A := by omega
    _ = numPairs A * (t' + al.T * (s + S * c) + 1) := by ring
    _ ≤ numPairs A * (t + al.T * (s + S * c)) := Nat.mul_le_mul_left _ this

theorem Alg.stageStart_le_slotStart (al : Alg m S H A) (c s t : ℕ) :
    al.stageStart c ≤ al.slotStart c s t := by
  unfold stageStart slotStart
  apply Nat.mul_le_mul_left
  have : al.T * (S * c) ≤ al.T * (s + S * c) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem Alg.slot_lt_stageStart_succ (al : Alg m S H A) (c : Fin H) (s : Fin S) (t : Fin al.T)
    (j : Fin (numPairs A)) : (al.slot c s t j).val < al.stageStart (c + 1) := by
  rw [al.slot_val, stageStart]
  have hj := j.isLt
  have ht := t.isLt
  have hs := s.isLt
  have h1 : (t : ℕ) + al.T * (s + S * c) + 1 ≤ al.T * (S * (c + 1)) := by
    have : al.T * ((s : ℕ) + 1 + S * c) ≤ al.T * (S * (c + 1)) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have h2 : (t : ℕ) + 1 + al.T * (s + S * c) ≤ al.T * ((s : ℕ) + 1 + S * c) := by
      have : al.T * ((s : ℕ) + 1 + S * c) = al.T + al.T * (s + S * c) := by ring
      omega
    omega
  calc (j : ℕ) + numPairs A * (t + al.T * (s + S * c))
      < numPairs A * (t + al.T * (s + S * c)) + numPairs A := by omega
    _ = numPairs A * (t + al.T * (s + S * c) + 1) := by ring
    _ ≤ numPairs A * (al.T * (S * (c + 1))) := Nat.mul_le_mul_left _ h1

theorem Alg.stageStart_mono (al : Alg m S H A) {c c' : ℕ} (h : c ≤ c') :
    al.stageStart c ≤ al.stageStart c' := by
  unfold stageStart
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h))

/-! ### Agreement of histories -/

/-- `x` and `y` agree at all indices `< n`. -/
def Alg.Agree (al : Alg m S H A) (n : ℕ) (x y : Fin al.N → Entry m S H A) : Prop :=
  ∀ k : Fin al.N, k.val < n → x k = y k

theorem Alg.Agree.mono {al : Alg m S H A} {n n' : ℕ} {x y : Fin al.N → Entry m S H A}
    (h : al.Agree n x y) (hn : n' ≤ n) : al.Agree n' x y :=
  fun k hk => h k (lt_of_lt_of_le hk hn)

theorem hedgeIter_congr {n : ℕ} (hn : 0 < n) (η : ℝ) (q q' : ℕ → Fin n → ℝ) (t : ℕ)
    (h : ∀ t' < t, q t' = q' t') : hedgeIter hn η q t = hedgeIter hn η q' t := by
  have : cumGain q t = cumGain q' t := by
    funext b
    exact sum_congr rfl fun t' ht' => by rw [h t' (mem_range.1 ht')]
  simp only [hedgeIter, this]

theorem Alg.gain_congr (al : Alg m S H A) (V : Fin m → Fin S → ℝ) (x y : Fin al.N → Entry m S H A)
    (c : Fin H) (s : Fin S) (i : Fin m) (t' : ℕ)
    (h : ∀ (ht : t' < al.T) (j : Fin (numPairs A)), x (al.slot c s ⟨t', ht⟩ j) =
      y (al.slot c s ⟨t', ht⟩ j)) :
    al.gain V x c s i t' = al.gain V y c s i t' := by
  funext b
  unfold gain
  split_ifs with ht
  · rw [h ht]
  · rfl

theorem Alg.hedge_congr (al : Alg m S H A) (V : Fin m → Fin S → ℝ) (x y : Fin al.N → Entry m S H A)
    (c : Fin H) (s : Fin S) (i : Fin m) (t : ℕ) (hxy : al.Agree (al.slotStart c s t) x y) :
    al.hedge V x c s i t = al.hedge V y c s i t := by
  unfold hedge
  refine hedgeIter_congr _ _ _ _ _ fun t' ht' => al.gain_congr V x y c s i t' fun ht j => ?_
  exact hxy _ (al.slot_lt_slotStart c s ⟨t', ht⟩ j t ht')

theorem Alg.stageV_congr (al : Alg m S H A) (V : Fin m → Fin S → ℝ)
    (x y : Fin al.N → Entry m S H A) (c : Fin H) (hxy : al.Agree (al.stageStart (c + 1)) x y) :
    al.stageV V x c = al.stageV V y c := by
  have hg : ∀ s i, al.gain V x c s i = al.gain V y c s i := by
    intro s i
    funext t'
    exact al.gain_congr V x y c s i t' fun ht j => hxy _ (al.slot_lt_stageStart_succ c s _ j)
  funext i s
  simp only [stageV, optU, bonus, hedge, hg s i]

theorem Alg.vb_congr (al : Alg m S H A) (x y : Fin al.N → Entry m S H A) :
    ∀ c, al.Agree (al.stageStart c) x y → al.vb x c = al.vb y c := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
    intro hxy
    have hprev := ih (hxy.mono (al.stageStart_mono (Nat.le_succ c)))
    simp only [vb]
    split_ifs with hc
    · rw [hprev]
      exact al.stageV_congr _ x y ⟨c, hc⟩ hxy
    · rfl

theorem Alg.hedgeAt_congr (al : Alg m S H A) (x y : Fin al.N → Entry m S H A) (c : Fin H)
    (s : Fin S) (i : Fin m) (t : ℕ) (hxy : al.Agree (al.slotStart c s t) x y) :
    al.hedgeAt x c s i t = al.hedgeAt y c s i t := by
  unfold hedgeAt
  rw [al.vb_congr x y c (hxy.mono (al.stageStart_le_slotStart c s t))]
  exact al.hedge_congr _ x y c s i t hxy

theorem Alg.stageProd_congr (al : Alg m S H A) (x y : Fin al.N → Entry m S H A) (c : Fin H)
    (s : Fin S) (t : ℕ) (hxy : al.Agree (al.slotStart c s t) x y) :
    al.stageProd x c s t = al.stageProd y c s t := by
  unfold stageProd
  congr 1
  funext i
  exact al.hedgeAt_congr x y c s i t hxy

theorem Alg.slot_symm (al : Alg m S H A) (k : Fin al.N) :
    let d := (slotEquiv H S al.T (numPairs A)).symm k
    al.slot d.1.1.1 d.1.1.2 d.1.2 d.2 = k := by
  simp [Alg.slot]

theorem Alg.queryAt_congr (al : Alg m S H A) (x y : Fin al.N → Entry m S H A) (k : Fin al.N)
    (hxy : al.Agree k x y) : al.queryAt x k = al.queryAt y k := by
  have hk : al.slotStart ((slotEquiv H S al.T (numPairs A)).symm k).1.1.1
      ((slotEquiv H S al.T (numPairs A)).symm k).1.1.2
      ((slotEquiv H S al.T (numPairs A)).symm k).1.2 ≤ k.val := by
    have := al.slotStart_le_slot ((slotEquiv H S al.T (numPairs A)).symm k).1.1.1
      ((slotEquiv H S al.T (numPairs A)).symm k).1.1.2
      ((slotEquiv H S al.T (numPairs A)).symm k).1.2 ((slotEquiv H S al.T (numPairs A)).symm k).2
    rwa [al.slot_symm k] at this
  unfold queryAt
  dsimp only
  rw [al.stageProd_congr x y _ _ _ (hxy.mono hk)]

theorem Alg.queryAt_slot (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (c : Fin H)
    (s : Fin S) (t : Fin al.T) (i : Fin m) (b : Fin (A i)) :
    al.queryAt x (al.slot c s t (pairEquiv A ⟨i, b⟩)) =
      queryDist c s (devDist (al.stageProd x c s t) i b) := by
  unfold queryAt Alg.slot
  dsimp only
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-! ### The rule on the true prefix and the step law -/

theorem Alg.ext_pre_agree (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (k : Fin al.N) :
    al.Agree k (al.ext k (seqPrefix k x)) x := by
  intro n hn
  simp only [Alg.ext, dif_pos hn, seqPrefix]
  rfl

theorem Alg.rule_pre (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (k : Fin al.N) :
    al.rule k (seqPrefix k x) = al.queryAt x k := by
  unfold rule
  rw [dif_pos k.isLt]
  exact al.queryAt_congr _ _ k (al.ext_pre_agree x k)

/-- The conditional law of the entry at slot `(c, s, t, (i, b))` given the prefix. -/
theorem Alg.kernel_sum_slot (al : Alg m S H A) (G : MarkovGame m S H A)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : Fin al.T) (i : Fin m)
    (b : Fin (A i)) (F : Entry m S H A → ℝ) :
    ∑ z, (interactionKernel al.rule (genEnv G) (al.slot c s t (pairEquiv A ⟨i, b⟩))
        (seqPrefix (al.slot c s t (pairEquiv A ⟨i, b⟩)) x)).prob z * F z =
      ∑ a, (devDist (al.stageProd x c s t) i b).prob a *
        ∑ s', (G.transition (H - c) s a).prob s' * F ((c.rev, s, a), s') := by
  simp only [interactionKernel]
  rw [al.rule_pre, al.queryAt_slot, Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← mul_sum]
  rw [queryDist_sum]
  have hstep : ((c.rev : ℕ) + 1) = H - c := by
    rw [Fin.val_rev]; have := c.isLt; omega
  simp only [genEnv, hstep]

end StatisticalRL.Ch7Rest.Marl77
