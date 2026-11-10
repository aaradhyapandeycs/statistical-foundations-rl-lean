import Formalization.Federated.Sync.Pathwise
import Formalization.Probability.AzumaFiltrationSource
import Formalization.Online.Regret.MVP.Probability.MVPRevealIncrement

/-!
# Corrected Theorem 7.9 (FedSynQ): concentration of the noise process

Under the true independent generative law `FedGeneric.fedSamplingLaw M T K 1`
(`federated_RL.tex:23–26`), for each `t ≤ T`, agent `k` and `(s,a)`, the noise process
`noiseG t k s a` is a sum of centred increments revealed in the time-first lexicographic order
of the sample coordinates `(iteration, agent, (s,a), slot)`. Agent `j`'s increment at iteration
`u+1` is `c_{u,j} · (V_u^j(s_{u+1}^j(s,a)) - P V_u^j(s,a))`, where `V_u^j` depends only on
coordinates of iterations `≤ u` (causality) and `c_{u,j} = a(t,u)/K + b(t,u)[j = k]` is
deterministic. Azuma–Hoeffding (`azuma_filtration_strict`) with
`Σ c² ≤ 2η/K` (`agent_coef_sq_sum_le`) gives the tail bound; a union bound over the
`(T+1) K S A` targets gives the good event.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Classical

namespace StatisticalRL.Ch7Rest.FedSync

open StatisticalRL StatisticalRL.OnlineRL StatisticalRL.Ch7Rest.Fed StatisticalRL.Ch7Rest.FedGeneric

set_option linter.unusedSectionVars false

local instance fedSyncStateMeasurable {State : Type} : MeasurableSpace State := ⊤

/-! ## Causality of `fedRun` -/

theorem fedRun_congr {State Action : Type} [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (η : ℝ) (K τ : ℕ)
    (Q₀ : State → Action → ℝ) (sm sm' : ℕ → Fin K → State → Action → State) :
    ∀ n : ℕ, (∀ t, 1 ≤ t → t ≤ n → sm t = sm' t) →
      fedRun M η K τ Q₀ sm n = fedRun M η K τ Q₀ sm' n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := fedRun_congr M η K τ Q₀ sm sm' n (fun t h1 h2 => h t h1 (by omega))
    show fedStep M η K τ (n + 1) (fedRun M η K τ Q₀ sm n) (sm (n + 1)) =
      fedStep M η K τ (n + 1) (fedRun M η K τ Q₀ sm' n) (sm' (n + 1))
    rw [ih, h (n + 1) (by omega) le_rfl]

/-! ## The time-first reveal order -/

/-- Coordinates other than the iteration index. -/
abbrev FedRest (State Action : Type) (K : ℕ) := Fin K × (State × Action) × Fin 1

/-- Position of a coordinate in the time-first order: `rank(agent, (s,a), slot) + R · (t-1)`. -/
noncomputable def posEquiv (State Action : Type) [Fintype State] [Fintype Action] (T K : ℕ) :
    FedIndex State Action T K 1 ≃ Fin (T * Fintype.card (FedRest State Action K)) :=
  (Equiv.prodAssoc (Fin T) (Fin K) ((State × Action) × Fin 1)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin T)) (Fintype.equivFin (FedRest State Action K))).trans
      finProdFinEquiv)

/-- The reveal order. -/
noncomputable def revealOrder (State Action : Type) [Fintype State] [Fintype Action] (T K : ℕ) :
    Fin (T * Fintype.card (FedRest State Action K)) → FedIndex State Action T K 1 :=
  (posEquiv State Action T K).symm

variable {State Action : Type} [Fintype State] [Fintype Action]

theorem posEquiv_val (T K : ℕ) (i : FedIndex State Action T K 1) :
    ((posEquiv State Action T K i : Fin _) : ℕ) =
      (Fintype.equivFin (FedRest State Action K) (i.1.2, i.2) : ℕ) +
        Fintype.card (FedRest State Action K) * i.1.1.val := rfl

theorem revealOrder_injective (T K : ℕ) : Function.Injective (revealOrder State Action T K) :=
  (posEquiv State Action T K).symm.injective

/-- Every coordinate of an earlier iteration is revealed before the coordinate `revealOrder j`. -/
theorem mem_prefix_of_time_lt (T K : ℕ) (j : Fin (T * Fintype.card (FedRest State Action K)))
    (i : FedIndex State Action T K 1) (h : i.1.1.val < (revealOrder State Action T K j).1.1.val) :
    i ∈ mvpRevealedPrefix (revealOrder State Action T K) j.val := by
  simp only [mvpRevealedPrefix, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  have hinv : revealOrder State Action T K (posEquiv State Action T K i) = i := by
    simp [revealOrder]
  refine ⟨⟨posEquiv State Action T K i, hinv⟩, posEquiv State Action T K i, ?_, hinv⟩
  have hjv : j.val = ((posEquiv State Action T K (revealOrder State Action T K j) : Fin _) : ℕ) := by
    simp [revealOrder]
  rw [hjv, posEquiv_val, posEquiv_val]
  have h1 := (Fintype.equivFin (FedRest State Action K) (i.1.2, i.2)).isLt
  have h2 := Nat.mul_le_mul_left (Fintype.card (FedRest State Action K)) h
  rw [Nat.mul_succ] at h2
  linarith

/-! ## Sample paths from data -/

section Data

variable (M : DiscountedMDP State Action) (T K : ℕ)

/-- The sample path `s_t^k(s,a)` read from the data (slot `0`). -/
noncomputable def smOf (data : FedSamples State Action T K 1) :
    ℕ → Fin K → State → Action → State :=
  fun t k s a => fedSamplesExtend M T K 1 data t k s a 0

/-- Extend a revealed prefix of the data by a fixed state. -/
noncomputable def extendPrefix (s₀ : State) (j : ℕ)
    (code : (i : mvpRevealedPrefix (revealOrder State Action T K) j) → State) :
    FedSamples State Action T K 1 :=
  fun i => if h : i ∈ mvpRevealedPrefix (revealOrder State Action T K) j then code ⟨i, h⟩ else s₀

theorem smOf_extendPrefix (s₀ : State) (j : Fin (T * Fintype.card (FedRest State Action K)))
    (data : FedSamples State Action T K 1) (t' : ℕ) (h1 : 1 ≤ t')
    (h2 : t' ≤ (revealOrder State Action T K j).1.1.val) :
    smOf M T K (extendPrefix T K s₀ j.val
      (onlineRevealedCode (mvpRevealedPrefix (revealOrder State Action T K) j.val) data)) t' =
      smOf M T K data t' := by
  have hT : t' ≤ T := le_trans h2 (le_of_lt (revealOrder State Action T K j).1.1.isLt)
  funext k s a
  have hc : 0 < t' ∧ t' ≤ T := ⟨by omega, hT⟩
  simp only [smOf, fedSamplesExtend, dif_pos hc]
  unfold extendPrefix
  rw [dif_pos (mem_prefix_of_time_lt T K j _ (by show t' - 1 < _; omega))]
  rfl

/-- The row laws of the sample coordinates. -/
noncomputable def rowLaw (i : FedIndex State Action T K 1) : FiniteDistribution State :=
  M.transition i.2.1.1 i.2.1.2

theorem data_eq_smOf (data : FedSamples State Action T K 1) (i : FedIndex State Action T K 1)
    (s : State) (a : Action) (h : i.2.1 = (s, a)) :
    data i = smOf M T K data (i.1.1.val + 1) i.1.2 s a := by
  obtain ⟨⟨tt, kk⟩, sa', b⟩ := i
  simp only at h
  subst h
  have hb : b = 0 := Subsingleton.elim _ _
  subst hb
  have hc : 0 < tt.val + 1 ∧ tt.val + 1 ≤ T := ⟨by omega, tt.isLt⟩
  simp only [smOf, fedSamplesExtend, dif_pos hc, Nat.add_sub_cancel, Fin.eta]

end Data

/-! ## Reindexing sums over the reveal order -/

theorem sum_reindex (T K : ℕ) (f : FedIndex State Action T K 1 → ℝ) :
    ∑ n ∈ Finset.range (T * Fintype.card (FedRest State Action K)),
        (if h : n < T * Fintype.card (FedRest State Action K) then
          f (revealOrder State Action T K ⟨n, h⟩) else 0) = ∑ i, f i := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => if h : n < T * Fintype.card (FedRest State Action K)
    then f (revealOrder State Action T K ⟨n, h⟩) else 0)]
  rw [Finset.sum_congr rfl (fun j _ => by rw [dif_pos j.isLt])]
  exact Equiv.sum_comp (posEquiv State Action T K).symm f

theorem sum_target (T K t : ℕ) (ht : t ≤ T) (s : State) (a : Action) (ψ : ℕ → Fin K → ℝ) :
    ∑ i : FedIndex State Action T K 1,
        (if i.2.1 = (s, a) then (if i.1.1.val < t then ψ i.1.1.val i.1.2 else 0) else 0) =
      ∑ u ∈ Finset.range t, ∑ jj, ψ u jj := by
  rw [Fintype.sum_prod_type]
  have hq : ∀ p : Fin T × Fin K,
      ∑ q : (State × Action) × Fin 1,
        (if q.1 = (s, a) then (if p.1.val < t then ψ p.1.val p.2 else 0) else 0) =
      if p.1.val < t then ψ p.1.val p.2 else 0 := by
    intro p
    rw [Fintype.sum_prod_type]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [Finset.sum_ite_eq' Finset.univ (s, a), if_pos (Finset.mem_univ _)]
  simp only [hq]
  rw [Fintype.sum_prod_type]
  have hp : ∀ tt : Fin T, (∑ kk : Fin K, if tt.val < t then ψ tt.val kk else 0) =
      if tt.val < t then ∑ kk, ψ tt.val kk else 0 := by
    intro tt
    split_ifs <;> simp
  simp only [hp]
  rw [Fin.sum_univ_eq_sum_range (fun u => if u < t then ∑ kk, ψ u kk else 0) T,
    ← Finset.sum_filter]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-! ## The martingale for one target `(t, k, s, a)` -/

section Target

variable (M : DiscountedMDP State Action) (η : ℝ) (K τ : ℕ) (Q₀ : State → Action → ℝ) (T : ℕ)

/-- Per-agent coefficient `c_{u,j} = a(t,u)/K + b(t,u)[j = k]`. -/
noncomputable def cfun (t : ℕ) (k : Fin K) (u : ℕ) (jj : Fin K) : ℝ :=
  coefA η τ t u / K + (if jj = k then coefB η τ t u else 0)

/-- The revealed-prefix test for target `(t,k,s,a)`: the coordinate `revealOrder j` contributes
`c · V_u^jj(x)` when it samples `(s,a)` at an iteration `u + 1 ≤ t`, with `V_u^jj` computed from
the revealed prefix. -/
noncomputable def testF (s₀ : State) (t : ℕ) (k : Fin K) (s : State) (a : Action)
    (j : Fin (T * Fintype.card (FedRest State Action K)))
    (code : (i : mvpRevealedPrefix (revealOrder State Action T K) j.val) → State) (x : State) :
    ℝ :=
  if (revealOrder State Action T K j).2.1 = (s, a) then
    (if (revealOrder State Action T K j).1.1.val < t then
      cfun η K τ t k (revealOrder State Action T K j).1.1.val (revealOrder State Action T K j).1.2 *
        greedyValue (fedRun M η K τ Q₀ (smOf M T K (extendPrefix T K s₀ j.val code))
          (revealOrder State Action T K j).1.1.val (revealOrder State Action T K j).1.2) x
    else 0)
  else 0

/-- Its value on the actual data. -/
noncomputable def targetTerm (t : ℕ) (k : Fin K) (s : State) (a : Action)
    (data : FedSamples State Action T K 1) (i : FedIndex State Action T K 1) : ℝ :=
  if i.2.1 = (s, a) then
    (if i.1.1.val < t then
      cfun η K τ t k i.1.1.val i.1.2 * noiseW M η K τ Q₀ (smOf M T K data) i.1.1.val i.1.2 s a
    else 0)
  else 0

theorem increment_eq (s₀ : State) (t : ℕ) (k : Fin K) (s : State) (a : Action)
    (j : Fin (T * Fintype.card (FedRest State Action K))) (data : FedSamples State Action T K 1) :
    mvpPaddedRevealIncrement (revealOrder State Action T K) (rowLaw M T K)
        (testF M η K τ Q₀ T s₀ t k s a) j.val data =
      targetTerm M η K τ Q₀ T t k s a data (revealOrder State Action T K j) := by
  simp only [mvpPaddedRevealIncrement, dif_pos j.isLt, Fin.eta]
  set i := revealOrder State Action T K j with hi
  set code := onlineRevealedCode (mvpRevealedPrefix (revealOrder State Action T K) j.val) data
  by_cases h1 : i.2.1 = (s, a)
  · by_cases h2 : i.1.1.val < t
    · have hrun : fedRun M η K τ Q₀ (smOf M T K (extendPrefix T K s₀ j.val code)) i.1.1.val =
          fedRun M η K τ Q₀ (smOf M T K data) i.1.1.val :=
        fedRun_congr M η K τ Q₀ _ _ _ (fun t' h1' h2' =>
          smOf_extendPrefix M T K s₀ j data t' h1' h2')
      have hF : testF M η K τ Q₀ T s₀ t k s a j code = fun x =>
          cfun η K τ t k i.1.1.val i.1.2 *
            greedyValue (fedRun M η K τ Q₀ (smOf M T K data) i.1.1.val i.1.2) x := by
        funext x
        simp only [testF, ← hi, if_pos h1, if_pos h2, hrun]
      rw [hF, FiniteDistribution.expectation_mul]
      simp only [targetTerm, if_pos h1, if_pos h2, noiseW]
      simp only [rowLaw]
      rw [h1, ← data_eq_smOf M T K data i s a h1]
      ring
    · have hF : testF M η K τ Q₀ T s₀ t k s a j code = fun _ => 0 := by
        funext x
        simp only [testF, ← hi, if_pos h1, if_neg h2]
      rw [hF]
      simp [targetTerm, h1, h2]
  · have hF : testF M η K τ Q₀ T s₀ t k s a j code = fun _ => 0 := by
      funext x
      simp only [testF, ← hi, if_neg h1]
    rw [hF]
    simp [targetTerm, h1]

theorem sum_targetTerm (t : ℕ) (ht : t ≤ T) (k : Fin K) (s : State) (a : Action)
    (data : FedSamples State Action T K 1) :
    ∑ i, targetTerm M η K τ Q₀ T t k s a data i = noiseG M η K τ Q₀ (smOf M T K data) t k s a := by
  unfold targetTerm
  rw [sum_target T K t ht s a (fun u jj => cfun η K τ t k u jj *
    noiseW M η K τ Q₀ (smOf M T K data) u jj s a)]
  unfold noiseG
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [cfun, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k), Finset.mul_sum,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun jj _ => ?_
  ring

/-- **Azuma–Hoeffding for one target.** -/
theorem noiseG_tail (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hτ : 1 ≤ τ)
    (hητ : η * ((τ : ℝ) - 1) ≤ 1 / (K : ℝ))
    (hQ₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount))
    (t : ℕ) (ht : t ≤ T) (k : Fin K) (s : State) (a : Action) (δ' : ℝ) (hδ' : 0 < δ')
    (hδ'1 : δ' < 1) :
    1 - δ' < (fedSamplingLaw M T K 1).real {data |
      |noiseG M η K τ Q₀ (smOf M T K data) t k s a| ≤
        Real.sqrt (2 * ((1 / (1 - M.discount)) ^ 2 * (2 * η / K)) * Real.log (2 / δ'))} := by
  set N := T * Fintype.card (FedRest State Action K)
  set order := revealOrder State Action T K
  set d := rowLaw M T K
  set μ := onlineStackProductLaw d with hμdef
  have hμ : fedSamplingLaw M T K 1 = μ := rfl
  rw [hμ]
  haveI : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  set H := 1 / (1 - M.discount) with hH
  have hg : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hHpos : 0 ≤ H := by positivity
  set s₀ : State := Classical.choice M.state_nonempty
  set F := testF M η K τ Q₀ T s₀ t k s a
  set X : ℕ → FedSamples State Action T K 1 → ℝ := fun n =>
    mvpPaddedRevealIncrement order d F n with hX
  set Bf : FedIndex State Action T K 1 → ℝ := fun i =>
    if i.2.1 = (s, a) then (if i.1.1.val < t then |cfun η K τ t k i.1.1.val i.1.2| * H else 0)
    else 0 with hBf
  set B : ℕ → ℝ := fun n => if h : n < N then Bf (order ⟨n, h⟩) else 0 with hB
  have hXm : ∀ n, Measurable (X n) := fun n => measurable_of_countable _
  have hXeq : ∀ n data, X n data =
      if h : n < N then targetTerm M η K τ Q₀ T t k s a data (order ⟨n, h⟩) else 0 := by
    intro n data
    by_cases h : n < N
    · rw [dif_pos h]
      exact increment_eq M η K τ Q₀ T s₀ t k s a ⟨n, h⟩ data
    · rw [dif_neg h]
      simp only [hX, mvpPaddedRevealIncrement]
      exact dif_neg h
  have hXb : ∀ n data, |X n data| ≤ B n := by
    intro n data
    rw [hXeq]
    simp only [hB]
    split_ifs with h
    · simp only [targetTerm, hBf]
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (noiseW_abs_le M η K τ Q₀ _ hη0 hη1 hQ₀ _ _ s a) (abs_nonneg _)
      · simp
      · simp
    · simp
  have hXc : ∀ n, μ[X n | mvpRevealFiltration (Outcome := State) order n] =ᵐ[μ] 0 :=
    fun n => mvp_paddedRevealIncrement_centered order (revealOrder_injective T K) d F n
  have hXa : ∀ n, StronglyMeasurable[mvpRevealFiltration (Outcome := State) order (n + 1)]
      (X n) := fun n => mvp_paddedRevealIncrement_adapted order d F n
  have hAz := azuma_filtration_strict μ (mvpRevealFiltration (Outcome := State) order)
    X B hXm hXb hXc hXa N δ' hδ' hδ'1
  refine lt_of_lt_of_le hAz (measureReal_mono ?_)
  intro data hdata
  simp only [Set.mem_setOf_eq] at hdata ⊢
  have hsum : ∑ n ∈ Finset.range N, X n data = noiseG M η K τ Q₀ (smOf M T K data) t k s a := by
    rw [Finset.sum_congr rfl (fun n _ => hXeq n data)]
    rw [sum_reindex T K (targetTerm M η K τ Q₀ T t k s a data)]
    exact sum_targetTerm M η K τ Q₀ T t ht k s a data
  rw [hsum] at hdata
  refine hdata.trans (Real.sqrt_le_sqrt ?_)
  have hsq : ∑ n ∈ Finset.range N, B n ^ 2 ≤ H ^ 2 * (2 * η / K) := by
    have hBsq : ∀ n ∈ Finset.range N, B n ^ 2 =
        if h : n < N then (fun i : FedIndex State Action T K 1 =>
          if i.2.1 = (s, a) then (if i.1.1.val < t then
            H ^ 2 * cfun η K τ t k i.1.1.val i.1.2 ^ 2 else 0) else 0) (order ⟨n, h⟩) else 0 := by
      intro n _
      simp only [hB, hBf]
      split_ifs <;> simp [mul_pow, sq_abs, mul_comm]
    rw [Finset.sum_congr rfl hBsq]
    refine (sum_reindex T K (fun i : FedIndex State Action T K 1 =>
          if i.2.1 = (s, a) then (if i.1.1.val < t then
            H ^ 2 * cfun η K τ t k i.1.1.val i.1.2 ^ 2 else 0) else 0)).trans_le ?_
    rw [sum_target T K t ht s a (fun u jj => H ^ 2 * cfun η K τ t k u jj ^ 2)]
    simp only [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg H)
    exact agent_coef_sq_sum_le η τ hη0 hη1 hτ k hητ t
  have hlog : 0 ≤ Real.log (2 / δ') := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ']
    linarith
  have := mul_le_mul_of_nonneg_right hsq hlog
  nlinarith

end Target

end StatisticalRL.Ch7Rest.FedSync
