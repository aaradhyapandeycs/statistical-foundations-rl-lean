import Formalization.OfflineRL.LCBQLemma612Events
import Formalization.Online.Regret.MVP.Probability.MVPFiniteProductFreedman

/-!
# LCB-Q, Lemma 6.12: the Freedman events for `ψ` and `φ`

`lem:lcbq-alpha-xi-psi-phi-bound`, `chapters/offlineRL.tex:5126–5259` (well-covered part of
`κ₁`, Freedman `lem:Freedman-prelim` and AM–GM) and the omitted `φ` argument (`:5483–5485`).

The martingales are taken on the product of the `T` iid data triples, with the natural reveal
order. Since `Δ_t ≥ 0` holds only on the pessimism event, the tests are gated by the predictable
predicate "`V_v ≤ V⋆` for all `v ≤ t`" (on the pessimism event the gate is open). The tests are
`1_I(X_t)(d̃/d^b)(X_t)·G_t(X_t)`, valued in `[0, 504 C⋆/(1-γ)²]`, with `G_t = F_t` (for `ψ`) or
`G_t = P Δ_t` (for `φ`); Freedman with `K = T` peels and confidence `δ/5`, then AM–GM, gives the
absorbed bound required by `psiTotal_le` and `phiTotal_le`.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A]

section Causality

theorem count_congr_below {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {k : ℕ}
    (h : ∀ v, v < k → (p v ↔ q v)) : Nat.count p k = Nat.count q k := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  exact Finset.filter_congr fun v hv => h v (Finset.mem_range.1 hv)

theorem nth_congr_below {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {k : ℕ}
    (h : ∀ v, v < k → (p v ↔ q v)) {i : ℕ} (hi : i < Nat.count p k) :
    Nat.nth q i = Nat.nth p i := by
  have hlt : Nat.nth p i < k := Nat.nth_lt_of_lt_count hi
  have hp : p (Nat.nth p i) := Nat.nth_mem i (lt_card_of_lt_count hi)
  have hq : q (Nat.nth p i) := (h _ hlt).1 hp
  have hcnt : Nat.count q (Nat.nth p i) = i := by
    rw [← count_congr_below (fun v hv => h v (lt_trans hv hlt))]
    exact Nat.count_nth (lt_card_of_lt_count hi)
  calc Nat.nth q i = Nat.nth q (Nat.count q (Nat.nth p i)) := by rw [hcnt]
    _ = Nat.nth p i := Nat.nth_count hq

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A) {T : ℕ}

theorem visitPred_congr_below {data data' : Fin T → (S × A) × S} {u : ℕ}
    (h : ∀ i : Fin T, i.val < u → data i = data' i) (sa : S × A) :
    ∀ v, v < u → (visitPred data sa v ↔ visitPred data' sa v) := by
  intro v hv
  constructor
  · rintro ⟨hT, he⟩; exact ⟨hT, by rw [← h ⟨v, hT⟩ hv]; exact he⟩
  · rintro ⟨hT, he⟩; exact ⟨hT, by rw [h ⟨v, hT⟩ hv]; exact he⟩

theorem delta_congr {data data' : Fin T → (S × A) × S} {u : ℕ}
    (h : ∀ i : Fin T, i.val < u → data i = data' i) :
    delta M cb δ sel π₀ data u = delta M cb δ sel π₀ data' u := by
  funext s
  simp only [delta, run_congr_prefix M cb δ sel π₀ data h le_rfl]

/-- `F_u(s,a) = Σ_i η_i^n P_{s,a}Δ_{k_i−1}` depends only on the samples before `u`. -/
theorem visitDeltaSum_congr {data data' : Fin T → (S × A) × S} {u : ℕ} (hu : u ≤ T)
    (h : ∀ i : Fin T, i.val < u → data i = data' i) (s : S) (a : A) :
    visitDeltaSum M cb δ sel π₀ data u s a = visitDeltaSum M cb δ sel π₀ data' u s a := by
  have hrun : ∀ v, v ≤ u → run M cb δ sel π₀ data v = run M cb δ sel π₀ data' v :=
    fun v hv => run_congr_prefix M cb δ sel π₀ data h hv
  simp only [visitDeltaSum, hrun u le_rfl]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < Nat.count (visitPred data (s, a)) u := by
    rw [← run_count M cb δ sel π₀ data hu, hrun u le_rfl]; exact Finset.mem_range.1 hi
  have hvt : visitTime data' (s, a) i = visitTime data (s, a) i :=
    nth_congr_below (visitPred_congr_below h (s, a)) hi'
  have hlt : visitTime data (s, a) i < u := visitTime_lt data hi'
  rw [hvt, delta_congr M cb δ sel π₀ (u := visitTime data (s, a) i)
    (fun j hj => h j (lt_trans hj hlt))]

end Causality

section Helpers

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  (ρ : FiniteDistribution S) (πstar : S → A) (db : FiniteDistribution (S × A))

/-- Extend a revealed prefix of data triples to a full data sequence (by `x₀`). -/
noncomputable def extendTriple (x₀ : (S × A) × S) {T : ℕ} (k : ℕ)
    (code : (i : mvpRevealedPrefix (id : Fin T → Fin T) k) → (S × A) × S) :
    Fin T → (S × A) × S :=
  fun i => if h : i ∈ mvpRevealedPrefix (id : Fin T → Fin T) k then code ⟨i, h⟩ else x₀

theorem extendTriple_revealed (x₀ : (S × A) × S) {T : ℕ} (k : ℕ) (data : Fin T → (S × A) × S)
    (i : Fin T) (hi : i.val < k) :
    extendTriple x₀ k (onlineRevealedCode (mvpRevealedPrefix (id : Fin T → Fin T) k) data) i =
      data i := by
  unfold extendTriple
  rw [dif_pos ((mem_revealedPrefix_id i k).2 hi)]
  rfl

/-- Pessimism up to time `u` (the predictable gate of the Freedman tests). -/
def gateProp {T : ℕ} (data : Fin T → (S × A) × S) (u : ℕ) : Prop :=
  ∀ v, v ≤ u → ∀ s, (run M cb δ sel π₀ data v).V s ≤ optValue M s

theorem gateProp_congr {T : ℕ} {data data' : Fin T → (S × A) × S} {u : ℕ}
    (h : ∀ i : Fin T, i.val < u → data i = data' i) :
    gateProp M cb δ sel π₀ data u ↔ gateProp M cb δ sel π₀ data' u := by
  unfold gateProp
  constructor
  · intro hg v hv s; rw [← run_congr_prefix M cb δ sel π₀ data h hv]; exact hg v hv s
  · intro hg v hv s; rw [run_congr_prefix M cb δ sel π₀ data h hv]; exact hg v hv s

theorem jointRow_expectation_fst (h : S × A → ℝ) :
    (JointRow.jointRow db M.transition).expectation (fun x => h x.1) = db.expectation h := by
  unfold FiniteDistribution.expectation
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [JointRow.jointRow]
  rw [show (∑ y : S, db.prob p * (M.transition p.1 p.2).prob y * h p) =
    db.prob p * h p * ∑ y : S, (M.transition p.1 p.2).prob y by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring,
    (M.transition p.1 p.2).sum_prob, mul_one]

theorem expectation_ratioI {κ thr : ℝ} (hthr : 0 < thr) (G : S → A → ℝ) :
    db.expectation (fun p => ratioI M ρ πstar db κ thr p * G p.1 p.2) =
      edI M ρ πstar db κ thr G := by
  unfold FiniteDistribution.expectation edI
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
  unfold ratioI
  by_cases h : thr ≤ db.prob (s, a)
  · have : db.prob (s, a) ≠ 0 := (lt_of_lt_of_le hthr h).ne'
    simp only [h, if_true]
    field_simp
  · simp only [h, if_false, mul_zero, zero_mul]

/-- On well-covered pairs, `d̃/d^b ≤ 504 C⋆/(1-γ)` (`eq:fg-envelope-offlineQ-B-defn`). -/
theorem ratioI_bounds {T : ℕ} (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1) (hι : 1 ≤ iota S A T δ)
    (hC : concentrability M ρ πstar db ≠ ⊤) (p : S × A) :
    0 ≤ ratioI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
        (δ / (5 * Fintype.card S * T)) p ∧
      ratioI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
        (δ / (5 * Fintype.card S * T)) p ≤
        504 * (concentrability M ρ πstar db).toReal / (1 - M.discount) := by
  set κ := kappa M.discount (horizon M.discount (iota S A T δ))
  set thr := δ / (5 * Fintype.card S * T) with hthr
  set Cs := (concentrability M ρ πstar db).toReal
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hCs := one_le_concentrability M ρ πstar db hC
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  haveI := M.state_nonempty
  have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hR0 : 0 ≤ 504 * Cs / (1 - M.discount) := by positivity
  unfold ratioI
  split_ifs with hp
  · have hdb : 0 < db.prob p := lt_of_lt_of_le (by positivity) hp
    refine ⟨div_nonneg (dTilde_nonneg M ρ πstar hκ0 _ _) hdb.le, ?_⟩
    rw [div_le_iff₀ hdb]
    by_cases ha : p.2 = πstar p.1
    · have hd := dTilde_le M ρ πstar hT hδ hδ1 hι p.1 p.2
      have hstar := dstarState_le M ρ πstar db hC p.1
      rw [show (p.1, πstar p.1) = p by rw [← ha]] at hstar
      have h4 : δ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - M.discount)) ≤
          5 * db.prob p / (1 - M.discount) := by
        rw [div_le_div_iff₀ (by positivity) hx0]
        have hT4 : (T : ℝ) ≤ (T : ℝ) ^ 4 := by
          calc (T : ℝ) = (T : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (T : ℝ) ^ 4 := pow_le_pow_right₀ hT' (by norm_num)
        have h5 : δ ≤ 5 * db.prob p * (Fintype.card S * T) := by
          have := (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * Fintype.card S * T)).1 hp
          linarith
        have : δ * (1 - M.discount) ≤ 5 * db.prob p * (Fintype.card S * T ^ 4 * (1 - M.discount)) := by
          have h6 : 5 * db.prob p * (Fintype.card S * T) ≤ 5 * db.prob p * (Fintype.card S * T ^ 4) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hT4 (by positivity)
          nlinarith
        linarith
      have h1 : M.discountedStateOccupancy (detPolicy πstar) ρ p.1 / (1 - M.discount) ≤
          Cs * db.prob p / (1 - M.discount) := div_le_div_of_nonneg_right hstar hx0.le
      calc dTilde M ρ πstar κ p.1 p.2
          ≤ 84 * (Cs * db.prob p / (1 - M.discount) + 5 * db.prob p / (1 - M.discount)) :=
            hd.trans (by gcongr)
        _ = 84 * (Cs + 5) / (1 - M.discount) * db.prob p := by ring
        _ ≤ 504 * Cs / (1 - M.discount) * db.prob p := by
            apply mul_le_mul_of_nonneg_right _ hdb.le
            apply div_le_div_of_nonneg_right _ hx0.le
            linarith
    · rw [dTilde_of_ne M ρ πstar κ p.1 p.2 ha]
      positivity
  · exact ⟨le_rfl, hR0⟩

end Helpers

section Freedman

local instance lcbqTripleMeasurable : MeasurableSpace ((S × A) × S) := ⊤

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  (ρ : FiniteDistribution S) (πstar : S → A) (db : FiniteDistribution (S × A))

set_option maxHeartbeats 1000000 in
/-- **Gated Freedman event** for the well-covered martingale with tests
`1_I(X_u)(d̃/d^b)(X_u)G_u(X_u)` (`offlineRL.tex:5164–5259`), after AM–GM:
with probability `≥ 1 − δ/5`, if pessimism holds before `T` then
`|Σ_u (1_I(d̃/d^b)G_u)(X_u) − E_{d^b}[1_I(d̃/d^b)G_u]| ≤ A/(2H) + K₀` with
`A = Σ_u E_{d^b}[1_I(d̃/d^b)G_u]` and `K₀ = C_f(4HL + 1 + 10L)`, `C_f = 504C⋆/(1-γ)²`,
`L = log(2T/(δ/5))`. -/
theorem freedman_gated_prob {T : ℕ} (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : 1 ≤ iota S A T δ) (hC : concentrability M ρ πstar db ≠ ⊤) (x₀ : (S × A) × S)
    (G : (Fin T → (S × A) × S) → ℕ → S → A → ℝ)
    (hcausal : ∀ (data data' : Fin T → (S × A) × S) (u : ℕ), u < T →
      (∀ i : Fin T, i.val < u → data i = data' i) → G data u = G data' u)
    (hbound : ∀ (data : Fin T → (S × A) × S) (u : ℕ), u < T → gateProp M cb δ sel π₀ data u →
      ∀ s a, 0 ≤ G data u s a ∧ G data u s a ≤ 1 / (1 - M.discount))
    (Cf L K₀ : ℝ)
    (hCf : Cf = 504 * (concentrability M ρ πstar db).toReal / (1 - M.discount) ^ 2)
    (hL : L = Real.log (2 * T / (δ / 5)))
    (hK₀ : K₀ = Cf * (4 * horizon M.discount (iota S A T δ) * L + 1 + 10 * L)) :
    1 - δ / 5 ≤ (onlineStackProductLaw (fun _ : Fin T => JointRow.jointRow db M.transition)).real
      {data | (∀ u, u < T → gateProp M cb δ sel π₀ data u) →
        |∑ u : Fin T,
            (ratioI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
                (δ / (5 * Fintype.card S * T)) (data u).1 * G data u.val (data u).1.1 (data u).1.2 -
              edI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
                (δ / (5 * Fintype.card S * T)) (G data u.val))| ≤
          (∑ u : Fin T, edI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
              (δ / (5 * Fintype.card S * T)) (G data u.val)) /
            (2 * horizon M.discount (iota S A T δ)) + K₀} := by
  set κ := kappa M.discount (horizon M.discount (iota S A T δ)) with hκ
  set thr := δ / (5 * Fintype.card S * T) with hthr
  set H := horizon M.discount (iota S A T δ) with hH
  set jr := JointRow.jointRow db M.transition with hjr
  set ν := onlineStackProductLaw (fun _ : Fin T => jr) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  haveI := M.state_nonempty
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hthr0 : 0 < thr := by positivity
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hCs := one_le_concentrability M ρ πstar db hC
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  have hHpos : 0 < H := horizon_pos M hT hδ hδ1
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hL0 : 0 ≤ L := by
    rw [hL]
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  -- the tests
  let F : (j : Fin T) → ((i : mvpRevealedPrefix (id : Fin T → Fin T) j.val) → (S × A) × S) →
      (S × A) × S → ℝ := fun j code x =>
    if gateProp M cb δ sel π₀ (extendTriple x₀ j.val code) j.val then
      ratioI M ρ πstar db κ thr x.1 * G (extendTriple x₀ j.val code) j.val x.1.1 x.1.2
    else 0
  have hF : ∀ j code x, 0 ≤ F j code x ∧ F j code x ≤ Cf := by
    intro j code x
    simp only [F]
    split_ifs with hg
    · have hr := ratioI_bounds M δ ρ πstar db hT hδ hδ1 hι hC x.1
      have hg' := hbound _ j.val j.isLt hg x.1.1 x.1.2
      refine ⟨mul_nonneg hr.1 hg'.1, ?_⟩
      calc ratioI M ρ πstar db κ thr x.1 * G (extendTriple x₀ j.val code) j.val x.1.1 x.1.2
          ≤ 504 * (concentrability M ρ πstar db).toReal / (1 - M.discount) *
              (1 / (1 - M.discount)) := mul_le_mul hr.2 hg'.2 hg'.1 (by positivity)
        _ = Cf := by rw [hCf]; field_simp
    · exact ⟨le_rfl, hCf0⟩
  have hfr := mvp_finiteProduct_freedman (id : Fin T → Fin T) Function.injective_id
    (fun _ => jr) F Cf hCf0 hF T hT (δ / 5) (by positivity) (by linarith)
  have hpsm := mvp_reveal_predictableSecondMomentSum (id : Fin T → Fin T) Function.injective_id
    (fun _ => jr) F
  set Bset := {data : Fin T → (S × A) × S |
    |StatisticalRL.incrementSum (mvpPaddedRevealIncrement (id : Fin T → Fin T) (fun _ => jr) F) T
        data| ≤
      Real.sqrt (8 * max (∑ j : Fin T, jr.variance
          (F j (onlineRevealedCode (mvpRevealedPrefix (id : Fin T → Fin T) j.val) data)))
        ((T : ℝ) * Cf ^ 2 / (2 : ℝ) ^ T) * Real.log (2 * T / (δ / 5))) +
        (4 / 3) * Cf * Real.log (2 * T / (δ / 5))} with hBset
  have hcongr : ν.real {data | |StatisticalRL.incrementSum (mvpPaddedRevealIncrement
        (id : Fin T → Fin T) (fun _ => jr) F) T data| ≤
      Real.sqrt (8 * max (StatisticalRL.predictableSecondMomentSum ν
          (mvpRevealFiltration (Outcome := (S × A) × S) (id : Fin T → Fin T))
          (mvpPaddedRevealIncrement (id : Fin T → Fin T) (fun _ => jr) F) T data)
        ((T : ℝ) * Cf ^ 2 / (2 : ℝ) ^ T) * Real.log (2 * T / (δ / 5))) +
        (4 / 3) * Cf * Real.log (2 * T / (δ / 5))} = ν.real Bset := by
    apply measureReal_congr
    rw [Filter.eventuallyEq_set]
    filter_upwards [hpsm] with data hd
    simp only [hBset, Set.mem_setOf_eq]
    rw [hν, hd]
  refine (hfr.trans (le_of_eq hcongr)).trans (measureReal_mono ?_)
  intro data hdata hgate
  simp only [hBset, Set.mem_setOf_eq] at hdata
  -- identify the tests on the gated data
  have hkey : ∀ u : Fin T,
      F u (onlineRevealedCode (mvpRevealedPrefix (id : Fin T → Fin T) u.val) data) =
        fun x => ratioI M ρ πstar db κ thr x.1 * G data u.val x.1.1 x.1.2 := by
    intro u
    have hag : ∀ i : Fin T, i.val < u.val →
        extendTriple x₀ u.val (onlineRevealedCode (mvpRevealedPrefix (id : Fin T → Fin T) u.val)
          data) i = data i := fun i hi => extendTriple_revealed x₀ u.val data i hi
    funext x
    simp only [F]
    rw [if_pos ((gateProp_congr M cb δ sel π₀ hag).2 (hgate u.val u.isLt)),
      hcausal _ data u.val u.isLt hag]
  have hsum : StatisticalRL.incrementSum (mvpPaddedRevealIncrement (id : Fin T → Fin T)
      (fun _ => jr) F) T data = ∑ u : Fin T,
        (ratioI M ρ πstar db κ thr (data u).1 * G data u.val (data u).1.1 (data u).1.2 -
          edI M ρ πstar db κ thr (G data u.val)) := by
    unfold StatisticalRL.incrementSum
    rw [← Fin.sum_univ_eq_sum_range (fun k => mvpPaddedRevealIncrement (id : Fin T → Fin T)
      (fun _ => jr) F k data)]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [mvpPaddedRevealIncrement, dif_pos u.isLt, Fin.eta, id]
    have he : jr.expectation (fun x => ratioI M ρ πstar db κ thr x.1 * G data u.val x.1.1 x.1.2) =
        edI M ρ πstar db κ thr (G data u.val) := by
      rw [show jr.expectation (fun x => ratioI M ρ πstar db κ thr x.1 * G data u.val x.1.1 x.1.2) =
        db.expectation (fun p => ratioI M ρ πstar db κ thr p * G data u.val p.1 p.2) from
        jointRow_expectation_fst M db (fun p => ratioI M ρ πstar db κ thr p * G data u.val p.1 p.2)]
      exact expectation_ratioI M ρ πstar db hthr0 (G data u.val)
    rw [hkey u, he]
  have hvar : ∑ j : Fin T, jr.variance
      (F j (onlineRevealedCode (mvpRevealedPrefix (id : Fin T → Fin T) j.val) data)) ≤
      Cf * ∑ u : Fin T, edI M ρ πstar db κ thr (G data u.val) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [hkey u]
    have hb : ∀ x : (S × A) × S, 0 ≤ ratioI M ρ πstar db κ thr x.1 * G data u.val x.1.1 x.1.2 ∧
        ratioI M ρ πstar db κ thr x.1 * G data u.val x.1.1 x.1.2 ≤ Cf := by
      intro x
      have := hF u (onlineRevealedCode (mvpRevealedPrefix (id : Fin T → Fin T) u.val) data) x
      rw [hkey u] at this
      exact this
    refine (variance_le_mul_expectation jr _ hb).trans (le_of_eq ?_)
    rw [show jr.expectation (fun x => ratioI M ρ πstar db κ thr x.1 * G data u.val x.1.1 x.1.2) =
      db.expectation (fun p => ratioI M ρ πstar db κ thr p * G data u.val p.1 p.2) from
      jointRow_expectation_fst M db (fun p => ratioI M ρ πstar db κ thr p * G data u.val p.1 p.2),
      expectation_ratioI M ρ πstar db hthr0 (G data u.val)]
  rw [hsum] at hdata
  have hA0 : 0 ≤ ∑ u : Fin T, edI M ρ πstar db κ thr (G data u.val) :=
    Finset.sum_nonneg fun u _ => edI_nonneg M ρ πstar db hκ0 _ fun s a =>
      (hbound data u.val u.isLt (hgate u.val u.isLt) s a).1
  have hTr1 : (T : ℝ) / 2 ^ T ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (Nat.lt_two_pow_self).le
  have hmax : (T : ℝ) * Cf ^ 2 / (2 : ℝ) ^ T = (T : ℝ) / 2 ^ T * Cf ^ 2 := by ring
  rw [hmax, ← hL] at hdata
  have h := freedman_absorb hA0 hCf0 hHr hL0 hvar hTr1 hdata
  rw [hK₀]
  linarith

end Freedman

end StatisticalRL.OfflineRL.LCBQ
