import Formalization.OfflineRL.FiniteLCBQ.Tails
import Formalization.OfflineRL.FiniteLCBQ.Arith
import Formalization.OfflineRL.FiniteVILCB.LibraryBridge

/-!
# Finite-horizon LCB-Q: the export (Theorem 6.17, restricted variant)

`lcbqFinite_restricted` (in `FiniteLCBQ.Export`): for `c_b ≥ 5`, `c_a = 10⁶ c_b²`, every `L ≥ ι = log(SAK/δ)` and
`K ≥ c_a H⁵ S C⋆ L / ε²`, with probability at least `1 - δ` the output of `LCBQFinite.output`
is `ε`-optimal. The rate is the one the source prints with `log³` replaced by the penalty's
`L`; the printed form (`L ≤ ι³`) follows in the statement wrapper.

Assembly: the good event `GoodEv` (E1 both sides, M1, M2, Cnt) at the confidence level
`ι' = log(6HSAK/δ)` fails with probability at most `(2HSAK + 2H + HS) e^{-ι'} ≤ δ`; on it the
deterministic analysis (`gap_le`) and the constant arithmetic (`final_arith`) give the gap
`≤ ε`. The corner `|A| = 1` holds surely (every policy is optimal).
-/

namespace StatisticalRL.LCBQFinite

open Finset MeasureTheory ProbabilityTheory OnlineRL StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance thDecS' : DecidableEq S := Classical.decEq S
noncomputable local instance thDecA' : DecidableEq A := Classical.decEq A
local instance thMT' (H : ℕ) : MeasurableSpace (Traj S A H) := ⊤

/-! ## The corner `|A| = 1` -/

theorem polV_eq_optV_of_subsingleton [Subsingleton A] {H : ℕ} (E : Fin H → EnvironmentStage S A)
    (π : Fin H → S → A) : ∀ m h, H - h = m → ∀ s, polV E π h s = optV E h s := by
  intro m
  induction m with
  | zero => intro h hh s; rw [polV_of_ge E π (by omega), optV_of_ge E (by omega)]
  | succ m ih =>
    intro h hh s
    have hlt : h < H := by omega
    have h1 := polV_of_lt E π ⟨h, hlt⟩ s
    have h2 := optV_of_lt E ⟨h, hlt⟩ s
    simp only at h1 h2
    have hfun : polV E π (h + 1) = optV E (h + 1) := funext (ih (h + 1) (by omega))
    rw [h1, h2, hfun]
    have hf : ∀ a, (E ⟨h, hlt⟩).reward s a + ((E ⟨h, hlt⟩).transition s a).expectation
        (optV E (h + 1)) = (E ⟨h, hlt⟩).reward s (π ⟨h, hlt⟩ s) +
        ((E ⟨h, hlt⟩).transition s (π ⟨h, hlt⟩ s)).expectation (optV E (h + 1)) := by
      intro a; rw [Subsingleton.elim a (π ⟨h, hlt⟩ s)]
    refine le_antisymm (le_actionMaximum (fun a ↦ (E ⟨h, hlt⟩).reward s a +
      ((E ⟨h, hlt⟩).transition s a).expectation (optV E (h + 1))) (π ⟨h, hlt⟩ s)) ?_
    exact actionMaximum_le fun a ↦ (hf a).le

/-! ## Penalty versus the E1 radius -/

theorem radius_le_penalty {H : ℕ} {cb L ι : ℝ} (hcb : 0 ≤ cb) (hL : 0 ≤ L) (hι0 : 0 ≤ ι)
    (hι : 4 * ι ≤ cb ^ 2 * L) (n : ℕ) :
    2 * Real.sqrt ((H : ℝ) ^ 3 * ι / n) ≤ penalty cb L H n := by
  unfold penalty
  have hH : (0 : ℝ) ≤ (H : ℝ) ^ 3 := by positivity
  refine sqrt_bound (by positivity) (by positivity) ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  calc (2 : ℝ) ^ 2 * ((H : ℝ) ^ 3 * ι / n) = ((H : ℝ) ^ 3 * (4 * ι)) / n := by ring
    _ ≤ ((H : ℝ) ^ 3 * (cb ^ 2 * L)) / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hι hH) (Nat.cast_nonneg n)
    _ = cb ^ 2 * ((H : ℝ) ^ 3 * L / n) := by ring

theorem le_sum_univ {α : Type*} [Fintype α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (a : α) :
    f a ≤ ∑ b, f b := single_le_sum (fun b _ ↦ hf b) (mem_univ a)

/-- Indicator. -/
def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

theorem ind_nonneg (P : Prop) [Decidable P] : 0 ≤ ind P := by unfold ind; split_ifs <;> norm_num

theorem ind_of (P : Prop) [Decidable P] (h : P) : ind P = 1 := by unfold ind; rw [if_pos h]

theorem swap_le {X ι : Type*} [Fintype X] [Fintype ι] (w : X → ℝ) (g : ι → X → ℝ) (c : ℝ)
    (h : ∀ i, ∑ x, w x * g i x ≤ c) : ∑ x, w x * ∑ i, g i x ≤ Fintype.card ι * c := by
  rw [show ∑ x, w x * ∑ i, g i x = ∑ i, ∑ x, w x * g i x by simp only [mul_sum]; exact sum_comm]
  calc _ ≤ ∑ _i : ι, c := sum_le_sum fun i _ ↦ h i
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-! ## The export -/

section Export

variable {H K : ℕ} (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
  (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (cb L : ℝ) (sel : (A → ℝ) → A)
  (π₀ : Fin H → S → A)

/-- E1 upper-side failure at `(h,s,a,n = k+1)`. -/
def e1Up (ι : ℝ) (x : Fin K → Traj S A H) (i : Fin H × S × A × Fin K) : Prop :=
  2 * Real.sqrt ((H : ℝ) ^ 3 * ι / ((i.2.2.2.val + 1 : ℕ) : ℝ)) ≤
    1 * mart E cb L sel π₀ x i.1 i.2.1 i.2.2.1 (i.2.2.2.val + 1)

/-- E1 lower-side failure. -/
def e1Lo (ι : ℝ) (x : Fin K → Traj S A H) (i : Fin H × S × A × Fin K) : Prop :=
  2 * Real.sqrt ((H : ℝ) ^ 3 * ι / ((i.2.2.2.val + 1 : ℕ) : ℝ)) ≤
    (-1) * mart E cb L sel π₀ x i.1 i.2.1 i.2.2.1 (i.2.2.2.val + 1)

/-- M1 failure at stage `h`. -/
def m1Bad (C ι : ℝ) (x : Fin K → Traj S A H) (h : Fin H) : Prop :=
  ∑ k ∈ range K, Z1 E πb ρb ρ πs cb L sel π₀ x k h + 2 * C * (H : ℝ) ^ 2 * ι <
    (1 - 1 / (2 * (H : ℝ))) * ∑ k ∈ range K, a1 E ρ πs cb L sel π₀ x k h

/-- M2 failure at stage `h`. -/
def m2Bad (C ι : ℝ) (x : Fin K → Traj S A H) (h : Fin H) : Prop :=
  (1 + 1 / (H : ℝ)) * ∑ k ∈ range K, a2 E ρ πs cb L sel π₀ x k h + C * (H : ℝ) ^ 2 * ι <
    ∑ k ∈ range K, Z2 E πb ρb ρ πs cb L sel π₀ x k h

/-- Cnt failure at `(h,s)`. -/
def cntBad (ι : ℝ) (x : Fin K → Traj S A H) (hs : Fin H × S) : Prop :=
  2 * K * db E πb ρb πs hs.1 hs.2 + ι < (cnt (visA πs x hs.1 hs.2) K : ℝ)

noncomputable instance (ι : ℝ) (x : Fin K → Traj S A H) (i) :
    Decidable (e1Up E cb L sel π₀ ι x i) := by unfold e1Up; infer_instance
noncomputable instance (ι : ℝ) (x : Fin K → Traj S A H) (i) :
    Decidable (e1Lo E cb L sel π₀ ι x i) := by unfold e1Lo; infer_instance
noncomputable instance (C ι : ℝ) (x : Fin K → Traj S A H) (h) :
    Decidable (m1Bad E πb ρb ρ πs cb L sel π₀ C ι x h) := by unfold m1Bad; infer_instance
noncomputable instance (C ι : ℝ) (x : Fin K → Traj S A H) (h) :
    Decidable (m2Bad E πb ρb ρ πs cb L sel π₀ C ι x h) := by unfold m2Bad; infer_instance
noncomputable instance (ι : ℝ) (x : Fin K → Traj S A H) (hs) :
    Decidable (cntBad E πb ρb πs ι x hs) := by unfold cntBad; infer_instance

/-- Sum of the bad-event indicators. -/
noncomputable def badSum (C ι : ℝ) (x : Fin K → Traj S A H) : ℝ :=
  (∑ i : Fin H × S × A × Fin K,
    (ind (e1Up E cb L sel π₀ ι x i) + ind (e1Lo E cb L sel π₀ ι x i))) +
  (∑ h : Fin H, (ind (m1Bad E πb ρb ρ πs cb L sel π₀ C ι x h) +
    ind (m2Bad E πb ρb ρ πs cb L sel π₀ C ι x h))) +
  ∑ hs : Fin H × S, ind (cntBad E πb ρb πs ι x hs)

theorem badSum_nonneg (C ι : ℝ) (x : Fin K → Traj S A H) :
    0 ≤ badSum E πb ρb ρ πs cb L sel π₀ C ι x := by
  unfold badSum
  exact add_nonneg (add_nonneg (sum_nonneg fun _ _ ↦ add_nonneg (ind_nonneg _) (ind_nonneg _))
    (sum_nonneg fun _ _ ↦ add_nonneg (ind_nonneg _) (ind_nonneg _)))
    (sum_nonneg fun _ _ ↦ ind_nonneg _)

/-- If the good event fails, some bad event occurs. -/
theorem one_le_badSum (hcb : 0 ≤ cb) (hL : 0 ≤ L) {C ι : ℝ} (hι0 : 0 ≤ ι)
    (hι : 4 * ι ≤ cb ^ 2 * L) (x : Fin K → Traj S A H)
    (hG : ¬ GoodEv E πb ρb ρ πs cb L sel π₀ x C ι) :
    1 ≤ badSum E πb ρb ρ πs cb L sel π₀ C ι x := by
  set U := ∑ i : Fin H × S × A × Fin K,
    (ind (e1Up E cb L sel π₀ ι x i) + ind (e1Lo E cb L sel π₀ ι x i))
  set M := ∑ h : Fin H, (ind (m1Bad E πb ρb ρ πs cb L sel π₀ C ι x h) +
    ind (m2Bad E πb ρb ρ πs cb L sel π₀ C ι x h))
  set N := ∑ hs : Fin H × S, ind (cntBad E πb ρb πs ι x hs)
  have hU0 : 0 ≤ U := sum_nonneg fun _ _ ↦ add_nonneg (ind_nonneg _) (ind_nonneg _)
  have hM0 : 0 ≤ M := sum_nonneg fun _ _ ↦ add_nonneg (ind_nonneg _) (ind_nonneg _)
  have hN0 : 0 ≤ N := sum_nonneg fun _ _ ↦ ind_nonneg _
  have hUi : ∀ i, ind (e1Up E cb L sel π₀ ι x i) + ind (e1Lo E cb L sel π₀ ι x i) ≤ U :=
    le_sum_univ _ fun _ ↦ add_nonneg (ind_nonneg _) (ind_nonneg _)
  have hMi : ∀ h, ind (m1Bad E πb ρb ρ πs cb L sel π₀ C ι x h) +
      ind (m2Bad E πb ρb ρ πs cb L sel π₀ C ι x h) ≤ M :=
    le_sum_univ _ fun _ ↦ add_nonneg (ind_nonneg _) (ind_nonneg _)
  have hNi : ∀ hs, ind (cntBad E πb ρb πs ι x hs) ≤ N := le_sum_univ _ fun _ ↦ ind_nonneg _
  show 1 ≤ U + M + N
  by_contra hlt
  push_neg at hlt
  apply hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h s a n hn hnK
    by_contra hbad
    push_neg at hbad
    have hr := radius_le_penalty (H := H) hcb hL hι0 hι n
    have hb : e1Up E cb L sel π₀ ι x (h, s, a, ⟨n - 1, by omega⟩) := by
      unfold e1Up
      simp only [show n - 1 + 1 = n by omega]
      linarith
    have := hUi (h, s, a, ⟨n - 1, by omega⟩)
    rw [ind_of _ hb] at this
    linarith [ind_nonneg (e1Lo E cb L sel π₀ ι x (h, s, a, ⟨n - 1, by omega⟩))]
  · intro h s a n hn hnK
    by_contra hbad
    push_neg at hbad
    have hr := radius_le_penalty (H := H) hcb hL hι0 hι n
    have hb : e1Lo E cb L sel π₀ ι x (h, s, a, ⟨n - 1, by omega⟩) := by
      unfold e1Lo
      simp only [show n - 1 + 1 = n by omega]
      linarith
    have := hUi (h, s, a, ⟨n - 1, by omega⟩)
    rw [ind_of _ hb] at this
    linarith [ind_nonneg (e1Up E cb L sel π₀ ι x (h, s, a, ⟨n - 1, by omega⟩))]
  · intro h
    by_contra hbad
    push_neg at hbad
    have hb : m1Bad E πb ρb ρ πs cb L sel π₀ C ι x h := hbad
    have := hMi h
    rw [ind_of _ hb] at this
    linarith [ind_nonneg (m2Bad E πb ρb ρ πs cb L sel π₀ C ι x h)]
  · intro h
    by_contra hbad
    push_neg at hbad
    have hb : m2Bad E πb ρb ρ πs cb L sel π₀ C ι x h := hbad
    have := hMi h
    rw [ind_of _ hb] at this
    linarith [ind_nonneg (m1Bad E πb ρb ρ πs cb L sel π₀ C ι x h)]
  · intro h s
    by_contra hbad
    push_neg at hbad
    have hb : cntBad E πb ρb πs ι x (h, s) := hbad
    have := hNi (h, s)
    rw [ind_of _ hb] at this
    linarith

/-- The expected bad-event count is at most `(2HSAK + 2H + HS) e^{-ι}`. -/
theorem sum_badSum_le (hH : 0 < H) (hcb : 0 ≤ cb) (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (hC1 : 1 ≤ (concentrability E πb ρb ρ πs).toReal) {ι : ℝ} (hι : 0 < ι) :
    ∑ x : Fin K → Traj S A H, prodP E πb ρb x *
      badSum E πb ρb ρ πs cb L sel π₀ (concentrability E πb ρb ρ πs).toReal ι x ≤
      (2 * (H * Fintype.card S * Fintype.card A * K) + 2 * H + H * Fintype.card S : ℝ) *
        Real.exp (-ι) := by
  set C := (concentrability E πb ρb ρ πs).toReal
  set w := prodP E πb ρb (K := K)
  have hU := swap_le w (fun i x ↦ ind (e1Up E cb L sel π₀ ι x i) +
      ind (e1Lo E cb L sel π₀ ι x i)) (2 * Real.exp (-ι)) fun i ↦ by
    simp only [mul_add, sum_add_distrib]
    have t1 := e1_tail (K := K) E πb ρb cb L sel π₀ hH hcb i.1 i.2.1 i.2.2.1 (Nat.succ_pos i.2.2.2.val)
      (σ := 1) (by norm_num) hι
    have t2 := e1_tail (K := K) E πb ρb cb L sel π₀ hH hcb i.1 i.2.1 i.2.2.1 (Nat.succ_pos i.2.2.2.val)
      (σ := -1) (by norm_num) hι
    simp only [ind, e1Up, e1Lo, w, prodP] at t1 t2 ⊢
    linarith
  have hM := swap_le w (fun h x ↦ ind (m1Bad E πb ρb ρ πs cb L sel π₀ C ι x h) +
      ind (m2Bad E πb ρb ρ πs cb L sel π₀ C ι x h)) (2 * Real.exp (-ι)) fun h ↦ by
    simp only [mul_add, sum_add_distrib]
    have t1 := m1_tail (K := K) E πb ρb ρ πs cb L sel π₀ hH hC hC1 h (ι := ι)
    have t2 := m2_tail (K := K) E πb ρb ρ πs cb L sel π₀ hH hC hC1 h (ι := ι)
    simp only [ind, m1Bad, m2Bad, w, prodP] at t1 t2 ⊢
    linarith
  have hN := swap_le w (fun hs x ↦ ind (cntBad E πb ρb πs ι x hs)) (Real.exp (-ι)) fun hs ↦ by
    have t1 := cnt_tail (K := K) E πb ρb πs hs.1 hs.2 (ι := ι)
    simp only [ind, cntBad, w, prodP] at t1 ⊢
    exact t1
  have e : ∑ x : Fin K → Traj S A H, w x * badSum E πb ρb ρ πs cb L sel π₀ C ι x =
      ∑ x, w x * ∑ i : Fin H × S × A × Fin K, (ind (e1Up E cb L sel π₀ ι x i) +
        ind (e1Lo E cb L sel π₀ ι x i)) +
      ∑ x, w x * ∑ h : Fin H, (ind (m1Bad E πb ρb ρ πs cb L sel π₀ C ι x h) +
        ind (m2Bad E πb ρb ρ πs cb L sel π₀ C ι x h)) +
      ∑ x, w x * ∑ hs : Fin H × S, ind (cntBad E πb ρb πs ι x hs) := by
    unfold badSum; simp only [mul_add, sum_add_distrib]
  rw [e]
  have c1 : (Fintype.card (Fin H × S × A × Fin K) : ℝ) = H * Fintype.card S * Fintype.card A * K := by
    simp only [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  have c2 : (Fintype.card (Fin H × S) : ℝ) = H * Fintype.card S := by
    simp only [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  rw [c1] at hU; rw [c2] at hN; rw [Fintype.card_fin] at hM
  have := Real.exp_pos (-ι)
  nlinarith

end Export

end StatisticalRL.LCBQFinite
