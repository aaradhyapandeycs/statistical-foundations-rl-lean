import Formalization.MultiAgent.Hedge.Stage

/-!
# Theorem 7.7: the concentration events

For each stage `c`, state `s`:
* (E1) for each pair `j = (i, b)`: Freedman with `X = λ(q̃^t_i(b) − q̂^t_i(b))`;
* (E2±) for each player `i`: Freedman with `X = ±λ π^t_i(b)(q̂^t_i(b) − q̃^t_i(b))` over all `(t, b)`;
* (E3) for each player `i`: multiplicative with `Y = π^t_i(b)(q̂^t_i(b) − m^t_i)² / H²`.

Here `q̃` (`qtil`) is the conditional mean of the gain given the history before the query,
`m^t_i = ∑_b π^t_i(b) q̃^t_i(b)` (`mbar`). `Good` is the intersection of the
`H·S·(Σ_iA_i + 3m)` events `∑_k f_k < L`; `good_prob`: `P(Good) ≥ 1 − #events·e^{−L}`.
The consequences `good_E1`, `good_E2a`, `good_E2b`, `good_E3` are stated per `(c, s, i)`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76
open StatisticalRL.Online.Hedge StatisticalRL.AdaptiveKL

variable {m S H : ℕ} {A : Fin m → ℕ}

/-! ### The step law at a general index -/

/-- Decoded slot coordinates of an index. -/
abbrev Alg.dec (al : Alg m S H A) (k : Fin al.N) : ((Fin H × Fin S) × Fin al.T) × Fin (numPairs A) :=
  (slotEquiv H S al.T (numPairs A)).symm k

theorem Alg.kernel_sum (al : Alg m S H A) (G : MarkovGame m S H A)
    (x : Fin al.N → Entry m S H A) (k : Fin al.N) (F : Entry m S H A → ℝ) :
    ∑ z, (interactionKernel al.rule (genEnv G) k (seqPrefix k x)).prob z * F z =
      ∑ a, (devDist (al.stageProd x (al.dec k).1.1.1 (al.dec k).1.1.2 (al.dec k).1.2)
          ((pairEquiv A).symm (al.dec k).2).1 ((pairEquiv A).symm (al.dec k).2).2).prob a *
        ∑ s', (G.transition (H - (al.dec k).1.1.1) (al.dec k).1.1.2 a).prob s' *
          F (((al.dec k).1.1.1.rev, (al.dec k).1.1.2, a), s') := by
  simp only [interactionKernel]
  rw [al.rule_pre, Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← mul_sum]
  unfold Alg.queryAt
  dsimp only
  rw [queryDist_sum]
  have hstep : (((al.dec k).1.1.1.rev : ℕ) + 1) = H - (al.dec k).1.1.1 := by
    rw [Fin.val_rev]; have := (al.dec k).1.1.1.isLt; omega
  simp only [genEnv, hstep]

/-! ### Conditional means and second moments -/

/-- Conditional mean `q̃^t_i(b)` of the gain at slot `(c, s, t, (i, b))`. -/
noncomputable def Alg.qtil (al : Alg m S H A) (G : MarkovGame m S H A)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) (b : Fin (A i)) : ℝ :=
  ∑ a, (devDist (al.stageProd x c s t) i b).prob a *
    ∑ s', (G.transition (H - c) s a).prob s' * al.gz (al.vb x c) c s i ((c.rev, s, a), s')

/-- Conditional second moment of the gain about `μ`. -/
noncomputable def Alg.csec (al : Alg m S H A) (G : MarkovGame m S H A)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) (b : Fin (A i))
    (μ : ℝ) : ℝ :=
  ∑ a, (devDist (al.stageProd x c s t) i b).prob a *
    ∑ s', (G.transition (H - c) s a).prob s' * (al.gz (al.vb x c) c s i ((c.rev, s, a), s') - μ) ^ 2

/-- `m^t_i = ∑_b π^t_i(b) q̃^t_i(b)`. -/
noncomputable def Alg.mbar (al : Alg m S H A) (G : MarkovGame m S H A)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) : ℝ :=
  ∑ b, (al.hedgeAt x c s i t).prob b * al.qtil G x c s t i b

theorem two_stage_sum_one (μ : FiniteDistribution (JointAction m A))
    (P : JointAction m A → FiniteDistribution (Fin S)) :
    ∑ a, μ.prob a * ∑ s', (P a).prob s' = 1 := by
  simp_rw [FiniteDistribution.sum_prob, mul_one]; exact μ.sum_prob

theorem two_stage_const (μ : FiniteDistribution (JointAction m A))
    (P : JointAction m A → FiniteDistribution (Fin S)) (k : ℝ) :
    ∑ a, μ.prob a * ∑ s', (P a).prob s' * k = k := by
  simp_rw [← sum_mul, FiniteDistribution.sum_prob, one_mul]
  rw [← sum_mul, μ.sum_prob, one_mul]

theorem two_stage_mem (μ : FiniteDistribution (JointAction m A))
    (P : JointAction m A → FiniteDistribution (Fin S)) (g : JointAction m A → Fin S → ℝ) (lo hi : ℝ)
    (hg : ∀ a s', lo ≤ g a s' ∧ g a s' ≤ hi) :
    lo ≤ ∑ a, μ.prob a * ∑ s', (P a).prob s' * g a s' ∧
      ∑ a, μ.prob a * ∑ s', (P a).prob s' * g a s' ≤ hi := by
  constructor
  · calc lo = ∑ a, μ.prob a * ∑ s', (P a).prob s' * lo := (two_stage_const μ P lo).symm
      _ ≤ _ := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (hg a s').1 ((P a).prob_nonneg s')) (μ.prob_nonneg a)
  · calc _ ≤ ∑ a, μ.prob a * ∑ s', (P a).prob s' * hi :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (sum_le_sum fun s' _ =>
            mul_le_mul_of_nonneg_left (hg a s').2 ((P a).prob_nonneg s')) (μ.prob_nonneg a)
      _ = hi := two_stage_const μ P hi

theorem Alg.qtil_mem (al : Alg m S H A) (hr : al.RewOK) (hη : 0 < al.η) (G : MarkovGame m S H A)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) (b : Fin (A i)) :
    0 ≤ al.qtil G x c s t i b ∧ al.qtil G x c s t i b ≤ (c : ℝ) + 1 :=
  two_stage_mem _ _ _ 0 ((c : ℝ) + 1) fun a s' => al.gz_mem hr hη x c s i _

theorem Alg.mbar_mem (al : Alg m S H A) (hr : al.RewOK) (hη : 0 < al.η) (G : MarkovGame m S H A)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (t : ℕ) (i : Fin m) :
    0 ≤ al.mbar G x c s t i ∧ al.mbar G x c s t i ≤ (c : ℝ) + 1 := by
  set p := al.hedgeAt x c s i t
  constructor
  · exact sum_nonneg fun b _ => mul_nonneg (p.prob_nonneg b) (al.qtil_mem hr hη G x c s t i b).1
  · calc al.mbar G x c s t i ≤ ∑ b, p.prob b * ((c : ℝ) + 1) :=
          sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (al.qtil_mem hr hη G x c s t i b).2
            (p.prob_nonneg b)
      _ = (c : ℝ) + 1 := by rw [← sum_mul, p.sum_prob, one_mul]

/-! ### Events -/

/-- Event indices: `inl (c, s, j)` is E1 for pair `j`; `inr (c, s, i, κ)` is E2+ (`κ = 0`),
E2− (`κ = 1`) or E3 (`κ = 2`). -/
abbrev Alg.Ev (_al : Alg m S H A) :=
  (Fin H × Fin S × Fin (numPairs A)) ⊕ (Fin H × Fin S × Fin m × Fin 3)

/-- The increment of event `e` at the slot `d`, as a function of the history and the new entry. -/
noncomputable def Alg.incr (al : Alg m S H A) (G : MarkovGame m S H A) (lam : ℝ) (e : al.Ev)
    (d : ((Fin H × Fin S) × Fin al.T) × Fin (numPairs A)) (x : Fin al.N → Entry m S H A)
    (z : Entry m S H A) : ℝ :=
  let c := d.1.1.1
  let s := d.1.1.2
  let t := d.1.2
  let σ := (pairEquiv A).symm d.2
  let g := al.gz (al.vb x c) c s σ.1 z
  let q := al.qtil G x c s t σ.1 σ.2
  let w := (al.hedgeAt x c s σ.1 t).prob σ.2
  match e with
  | Sum.inl (c0, s0, j0) => if c = c0 ∧ s = s0 ∧ d.2 = j0 then lam * (q - g) else 0
  | Sum.inr (c0, s0, i0, κ) =>
    if c = c0 ∧ s = s0 ∧ σ.1 = i0 then
      (if κ = 0 then lam * w * (g - q) else if κ = 1 then lam * w * (q - g)
        else w * (g - al.mbar G x c s t σ.1) ^ 2 / (H : ℝ) ^ 2)
    else 0

/-- Whether event `e` is of multiplicative type (E3). -/
def Alg.IsMult (al : Alg m S H A) (e : al.Ev) : Prop :=
  ∃ c0 s0 i0, e = Sum.inr (c0, s0, i0, 2)

noncomputable instance (al : Alg m S H A) (e : al.Ev) : Decidable (al.IsMult e) := Classical.dec _

/-- The summand of event `e` at index `k`. -/
noncomputable def Alg.fv (al : Alg m S H A) (G : MarkovGame m S H A) (lam : ℝ) (e : al.Ev)
    (k : Fin al.N) (x : Fin al.N → Entry m S H A) : ℝ :=
  if al.IsMult e then
    al.incr G lam e (al.dec k) x (x k) -
      2 * ∑ z, (interactionKernel al.rule (genEnv G) k (seqPrefix k x)).prob z *
        al.incr G lam e (al.dec k) x z
  else
    al.incr G lam e (al.dec k) x (x k) -
      ∑ z, (interactionKernel al.rule (genEnv G) k (seqPrefix k x)).prob z *
        al.incr G lam e (al.dec k) x z ^ 2

/-- The good event: every event sum is below `L`. -/
def Alg.Good (al : Alg m S H A) (G : MarkovGame m S H A) (lam L : ℝ)
    (x : Fin al.N → Entry m S H A) : Prop :=
  ∀ e : al.Ev, ∑ k, al.fv G lam e k x < L

/-! ### Locality of the increments -/

theorem Alg.agree_slot (al : Alg m S H A) (x y : Fin al.N → Entry m S H A) (k : Fin al.N)
    (hxy : ∀ j : Fin al.N, j < k → x j = y j) :
    al.Agree (al.slotStart (al.dec k).1.1.1 (al.dec k).1.1.2 (al.dec k).1.2) x y := by
  intro n hn
  refine hxy n (Fin.lt_def.2 (lt_of_lt_of_le hn ?_))
  have := al.slotStart_le_slot (al.dec k).1.1.1 (al.dec k).1.1.2 (al.dec k).1.2 (al.dec k).2
  rwa [al.slot_symm k] at this

theorem Alg.incr_congr (al : Alg m S H A) (G : MarkovGame m S H A) (lam : ℝ) (e : al.Ev)
    (k : Fin al.N) (x y : Fin al.N → Entry m S H A) (hxy : ∀ j : Fin al.N, j < k → x j = y j) :
    al.incr G lam e (al.dec k) x = al.incr G lam e (al.dec k) y := by
  have hA := al.agree_slot x y k hxy
  have hv : al.vb x (al.dec k).1.1.1 = al.vb y (al.dec k).1.1.1 :=
    al.vb_congr x y _ (hA.mono (al.stageStart_le_slotStart _ _ _))
  have hp : al.stageProd x (al.dec k).1.1.1 (al.dec k).1.1.2 (al.dec k).1.2 =
      al.stageProd y (al.dec k).1.1.1 (al.dec k).1.1.2 (al.dec k).1.2 :=
    al.stageProd_congr x y _ _ _ hA
  have hh : ∀ i, al.hedgeAt x (al.dec k).1.1.1 (al.dec k).1.1.2 i (al.dec k).1.2 =
      al.hedgeAt y (al.dec k).1.1.1 (al.dec k).1.1.2 i (al.dec k).1.2 :=
    fun i => al.hedgeAt_congr x y _ _ i _ hA
  funext z
  simp only [Alg.incr, Alg.qtil, Alg.mbar, hv, hp, hh]

/-! ### The probability of the good event -/

theorem Alg.incr_bound (al : Alg m S H A) (hr : al.RewOK) (hη : 0 < al.η)
    (G : MarkovGame m S H A) {lam : ℝ} (hlam : 0 ≤ lam) (hlamH : lam * H ≤ 1) (e : al.Ev)
    (he : ¬ al.IsMult e) (d : ((Fin H × Fin S) × Fin al.T) × Fin (numPairs A))
    (x : Fin al.N → Entry m S H A) (z : Entry m S H A) : |al.incr G lam e d x z| ≤ 1 := by
  set c := d.1.1.1
  set σ := (pairEquiv A).symm d.2
  have hg := al.gz_mem hr hη x c d.1.1.2 σ.1 z
  have hq := al.qtil_mem hr hη G x c d.1.1.2 d.1.2 σ.1 σ.2
  have hw0 := (al.hedgeAt x c d.1.1.2 σ.1 d.1.2).prob_nonneg σ.2
  have hw1 : (al.hedgeAt x c d.1.1.2 σ.1 d.1.2).prob σ.2 ≤ 1 := by
    rw [← (al.hedgeAt x c d.1.1.2 σ.1 d.1.2).sum_prob]
    exact single_le_sum (fun b _ => (al.hedgeAt x c d.1.1.2 σ.1 d.1.2).prob_nonneg b) (mem_univ _)
  have hcH : (c : ℝ) + 1 ≤ H := by have := c.isLt; exact_mod_cast this
  have hdiff : |al.qtil G x c d.1.1.2 d.1.2 σ.1 σ.2 - al.gz (al.vb x c) c d.1.1.2 σ.1 z| ≤ H :=
    abs_le.2 ⟨by linarith [hg.2, hq.1], by linarith [hg.1, hq.2]⟩
  have key : ∀ w : ℝ, 0 ≤ w → w ≤ 1 → ∀ u : ℝ, |u| ≤ H → |lam * w * u| ≤ 1 := by
    intro w hw0 hw1 u hu
    rw [abs_mul, abs_mul, abs_of_nonneg hlam, abs_of_nonneg hw0]
    calc lam * w * |u| ≤ lam * 1 * H := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hw1 hlam) hu (abs_nonneg _) (by positivity)
      _ ≤ 1 := by linarith
  rcases e with ⟨c0, s0, j0⟩ | ⟨c0, s0, i0, κ⟩
  · simp only [Alg.incr]
    split_ifs
    · have := key 1 zero_le_one le_rfl _ hdiff
      simpa using this
    · simp
  · have hκ : κ ≠ 2 := fun h => he ⟨c0, s0, i0, by rw [h]⟩
    simp only [Alg.incr]
    split_ifs with h1 h2 h3
    · exact key _ hw0 hw1 _ (by rw [abs_sub_comm]; exact hdiff)
    · exact key _ hw0 hw1 _ hdiff
    · exact absurd (by omega : κ = 2) hκ
    · simp

theorem Alg.incr_mult_mem (al : Alg m S H A) (hr : al.RewOK) (hη : 0 < al.η)
    (G : MarkovGame m S H A) (lam : ℝ) (e : al.Ev) (he : al.IsMult e)
    (d : ((Fin H × Fin S) × Fin al.T) × Fin (numPairs A))
    (x : Fin al.N → Entry m S H A) (z : Entry m S H A) :
    0 ≤ al.incr G lam e d x z ∧ al.incr G lam e d x z ≤ 1 := by
  obtain ⟨c0, s0, i0, rfl⟩ := he
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [Alg.incr, h20, h21, ↓reduceIte]
  have hg := al.gz_mem hr hη x d.1.1.1 d.1.1.2 ((pairEquiv A).symm d.2).1 z
  have hq := al.mbar_mem hr hη G x d.1.1.1 d.1.1.2 d.1.2 ((pairEquiv A).symm d.2).1
  have hw0 := (al.hedgeAt x d.1.1.1 d.1.1.2 ((pairEquiv A).symm d.2).1 d.1.2).prob_nonneg
    ((pairEquiv A).symm d.2).2
  have hw1 : (al.hedgeAt x d.1.1.1 d.1.1.2 ((pairEquiv A).symm d.2).1 d.1.2).prob
      ((pairEquiv A).symm d.2).2 ≤ 1 := by
    rw [← (al.hedgeAt x d.1.1.1 d.1.1.2 ((pairEquiv A).symm d.2).1 d.1.2).sum_prob]
    exact single_le_sum (fun b _ =>
      (al.hedgeAt x d.1.1.1 d.1.1.2 ((pairEquiv A).symm d.2).1 d.1.2).prob_nonneg b) (mem_univ _)
  have hcH : ((d.1.1.1 : ℕ) : ℝ) + 1 ≤ H := by have := d.1.1.1.isLt; exact_mod_cast this
  have hH : (0 : ℝ) < H := by linarith [(Nat.cast_nonneg d.1.1.1 : (0 : ℝ) ≤ (d.1.1.1 : ℕ))]
  split_ifs with h1
  · have hsq : (al.gz (al.vb x d.1.1.1) d.1.1.1 d.1.1.2 ((pairEquiv A).symm d.2).1 z -
        al.mbar G x d.1.1.1 d.1.1.2 d.1.2 ((pairEquiv A).symm d.2).1) ^ 2 ≤ (H : ℝ) ^ 2 :=
      sq_le_sq' (by linarith [hg.2, hq.1]) (by linarith [hg.1, hq.2])
    constructor
    · exact div_nonneg (mul_nonneg hw0 (sq_nonneg _)) (sq_nonneg _)
    · rw [div_le_one (by positivity)]
      calc _ ≤ 1 * (H : ℝ) ^ 2 := mul_le_mul hw1 hsq (sq_nonneg _) zero_le_one
        _ = _ := one_mul _
  · exact ⟨le_rfl, zero_le_one⟩

theorem Alg.incr_mean (al : Alg m S H A) (G : MarkovGame m S H A) (lam : ℝ) (e : al.Ev)
    (he : ¬ al.IsMult e) (k : Fin al.N) (x : Fin al.N → Entry m S H A) :
    ∑ z, (interactionKernel al.rule (genEnv G) k (seqPrefix k x)).prob z *
      al.incr G lam e (al.dec k) x z = 0 := by
  rw [al.kernel_sum]
  set d := al.dec k
  set c := d.1.1.1
  set σ := (pairEquiv A).symm d.2
  set μ := devDist (al.stageProd x c d.1.1.2 d.1.2) σ.1 σ.2
  set P := fun a => G.transition (H - c) d.1.1.2 a
  have hone := two_stage_sum_one μ P
  -- the mean of the gain is `qtil`
  have hmean : ∀ (α β : ℝ), ∑ a, μ.prob a * ∑ s', (P a).prob s' *
      (α * (al.qtil G x c d.1.1.2 d.1.2 σ.1 σ.2 -
        al.gz (al.vb x c) c d.1.1.2 σ.1 ((c.rev, d.1.1.2, a), s')) + β) = β := by
    intro α β
    have e1 : ∀ a, μ.prob a * ∑ s', (P a).prob s' * (α * (al.qtil G x c d.1.1.2 d.1.2 σ.1 σ.2 -
        al.gz (al.vb x c) c d.1.1.2 σ.1 ((c.rev, d.1.1.2, a), s')) + β) =
        (α * al.qtil G x c d.1.1.2 d.1.2 σ.1 σ.2 + β) * (μ.prob a * ∑ s', (P a).prob s') -
        α * (μ.prob a * ∑ s', (P a).prob s' *
          al.gz (al.vb x c) c d.1.1.2 σ.1 ((c.rev, d.1.1.2, a), s')) := by
      intro a
      simp only [mul_sum]
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun s' _ => by ring
    simp_rw [e1]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hone]
    have : ∑ a, μ.prob a * ∑ s', (P a).prob s' *
        al.gz (al.vb x c) c d.1.1.2 σ.1 ((c.rev, d.1.1.2, a), s') =
        al.qtil G x c d.1.1.2 d.1.2 σ.1 σ.2 := rfl
    rw [this]; ring
  rcases e with ⟨c0, s0, j0⟩ | ⟨c0, s0, i0, κ⟩
  · simp only [Alg.incr]
    split_ifs
    · have := hmean lam 0
      simp only [add_zero] at this
      exact this
    · simp
  · have hκ : κ ≠ 2 := fun h => he ⟨c0, s0, i0, by rw [h]⟩
    simp only [Alg.incr]
    split_ifs with h1 h2 h3
    · have := hmean (-(lam * (al.hedgeAt x c d.1.1.2 σ.1 d.1.2).prob σ.2)) 0
      simp only [add_zero] at this
      rw [← this]
      refine sum_congr rfl fun a _ => congrArg _ (sum_congr rfl fun s' _ => by ring)
    · have := hmean (lam * (al.hedgeAt x c d.1.1.2 σ.1 d.1.2).prob σ.2) 0
      simp only [add_zero] at this
      rw [← this]
    · exact absurd (by omega : κ = 2) hκ
    · simp

/-- Each event fails with probability at most `e^{-L}`. -/
theorem Alg.event_tail (al : Alg m S H A) (hr : al.RewOK) (hη : 0 < al.η)
    (G : MarkovGame m S H A) {lam : ℝ} (hlam : 0 ≤ lam) (hlamH : lam * H ≤ 1) (L : ℝ) (e : al.Ev) :
    ∑ x, (interactionLaw al.rule (genEnv G) al.N).prob x *
      (if L ≤ ∑ k, al.fv G lam e k x then 1 else 0) ≤ Real.exp (-L) := by
  by_cases he : al.IsMult e
  · have := seqLaw_multiplicative_tail (interactionKernel al.rule (genEnv G)) al.N
      (fun k x z => al.incr G lam e (al.dec k) x z) (fun k x y hxy => al.incr_congr G lam e k x y hxy)
      (fun k x z => (al.incr_mult_mem hr hη G lam e he _ x z).1)
      (fun k x z => (al.incr_mult_mem hr hη G lam e he _ x z).2) L
    simp only [Alg.fv, if_pos he]
    exact this
  · have := seqLaw_freedman_tail (interactionKernel al.rule (genEnv G)) al.N
      (fun k x z => al.incr G lam e (al.dec k) x z) (fun k x y hxy => al.incr_congr G lam e k x y hxy)
      (fun k x => al.incr_mean G lam e he k x)
      (fun k x z => al.incr_bound hr hη G hlam hlamH e he _ x z) L
    simp only [Alg.fv, if_neg he]
    exact this

open Classical in
/-- `P(Good) ≥ 1 − #events · e^{-L}`. -/
theorem Alg.good_prob (al : Alg m S H A) (hr : al.RewOK) (hη : 0 < al.η)
    (G : MarkovGame m S H A) {lam : ℝ} (hlam : 0 ≤ lam) (hlamH : lam * H ≤ 1) (L : ℝ) :
    1 - (Fintype.card al.Ev : ℝ) * Real.exp (-L) ≤
      ∑ x, (interactionLaw al.rule (genEnv G) al.N).prob x *
        (if al.Good G lam L x then 1 else 0) := by
  classical
  set P := interactionLaw al.rule (genEnv G) al.N
  have hU := StatisticalRL.AdaptiveKL.union_bound_sum P.prob P.prob_nonneg (univ : Finset al.Ev)
    (fun e x => L ≤ ∑ k, al.fv G lam e k x)
  have htail : ∑ e ∈ (univ : Finset al.Ev), ∑ x, P.prob x *
      (if L ≤ ∑ k, al.fv G lam e k x then 1 else 0) ≤ (Fintype.card al.Ev : ℝ) * Real.exp (-L) := by
    calc _ ≤ ∑ e ∈ (univ : Finset al.Ev), Real.exp (-L) :=
          sum_le_sum fun e _ => al.event_tail hr hη G hlam hlamH L e
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hsplit : ∀ x, P.prob x * (if al.Good G lam L x then 1 else 0) =
      P.prob x - P.prob x * (if ∃ e ∈ (univ : Finset al.Ev), L ≤ ∑ k, al.fv G lam e k x then 1 else 0) := by
    intro x
    by_cases hg : al.Good G lam L x
    · have : ¬ ∃ e ∈ (univ : Finset al.Ev), L ≤ ∑ k, al.fv G lam e k x := by
        rintro ⟨e, _, he⟩; exact absurd (hg e) (not_lt.2 he)
      rw [if_pos hg, if_neg this]; ring
    · have : ∃ e ∈ (univ : Finset al.Ev), L ≤ ∑ k, al.fv G lam e k x := by
        simp only [Alg.Good, not_forall, not_lt] at hg
        obtain ⟨e, he⟩ := hg
        exact ⟨e, mem_univ _, he⟩
      rw [if_neg hg, if_pos this]; ring
  simp_rw [hsplit]
  rw [sum_sub_distrib, P.sum_prob]
  linarith

end StatisticalRL.Ch7Rest.Marl77
