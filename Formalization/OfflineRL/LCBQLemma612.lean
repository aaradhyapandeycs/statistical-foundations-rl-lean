import Formalization.OfflineRL.LCBQFreedman612

/-!
# LCB-Q, Lemma 6.12 (restricted to `log(SAT/δ) ≥ 1`)

`lem:lcbq-alpha-xi-psi-phi-bound`, `chapters/offlineRL.tex:2309–2324`; proof `:4786–5496`.

For `c_b ≥ 4` there is a constant `C = 400000 + 5600 c_b` such that, whenever
`log(SAT/δ) ≥ 1`, with probability at least `1 − δ`:
`α_j → 0`; `ξ = Σ_j ξ_j ≤ C/(1-γ)²`; `θ = Σ_j θ_j ≤ C √(C⋆STι²/(1-γ)⁵)`; and
`ψ + φ = Σ_j ψ_j + Σ_j φ_j ≤ C C⋆ι²/(1-γ)³` (the last two when `C⋆ < ∞`).

The probability event is the intersection of five events, each at confidence `δ/5`: the
martingale event of Lemma 6.9 (which gives pessimism, Lemma 6.10), the prefix-count event, the
two gated Freedman events and the event that no sample hits a poorly covered pair `(s,π⋆(s))`.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Filter Topology

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A]


section ScalarFinal

theorem psi_phi_final {Cs ι x H L K₀ ψ φ C : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hCs1 : 1 ≤ Cs)
    (hι : 1 ≤ ι) (hH : H ≤ 5 * ι / x) (hL0 : 0 ≤ L) (hL : L ≤ 4 * ι)
    (hK : K₀ = 504 * Cs / x ^ 2 * (4 * H * L + 1 + 10 * L))
    (hψ : ψ ≤ 2 * K₀ + 168 * Cs / x ^ 2 + 168 / x ^ 2) (hφ : φ ≤ 4 * K₀) (hC : 366240 ≤ C) :
    ψ + φ ≤ C * Cs * ι ^ 2 / x ^ 3 := by
  set X := Cs * ι ^ 2 / x ^ 3 with hX
  have hX0 : 0 ≤ X := by positivity
  have hHL : H * L ≤ 20 * ι ^ 2 / x := by
    calc H * L ≤ 5 * ι / x * (4 * ι) := mul_le_mul hH hL hL0 (by positivity)
      _ = 20 * ι ^ 2 / x := by ring
  have hrest : 1 + 10 * L ≤ 41 * ι ^ 2 / x := by
    have hι2' : 1 ≤ ι ^ 2 := one_le_pow₀ hι
    have hιι : ι ≤ ι ^ 2 := le_self_pow₀ hι two_ne_zero
    have h1 : 1 + 10 * L ≤ 41 * ι ^ 2 := by linarith
    refine h1.trans ?_
    rw [le_div_iff₀ hx0]
    have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ 41 * ι ^ 2)
    linarith
  have hin : 4 * H * L + 1 + 10 * L ≤ 121 * ι ^ 2 / x := by
    have e : 121 * ι ^ 2 / x = 4 * (20 * ι ^ 2 / x) + 41 * ι ^ 2 / x := by ring
    linarith
  have hK₀X : K₀ ≤ 60984 * X := by
    rw [hK]
    calc 504 * Cs / x ^ 2 * (4 * H * L + 1 + 10 * L) ≤ 504 * Cs / x ^ 2 * (121 * ι ^ 2 / x) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = 60984 * X := by rw [hX]; field_simp; ring
  have h2 : x ^ 3 ≤ x ^ 2 := pow_le_pow_of_le_one hx0.le hx1 (by norm_num)
  have hι2 : 1 ≤ ι ^ 2 := one_le_pow₀ hι
  have hsmall : 1 / x ^ 2 ≤ X := by
    rw [hX, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 1 ≤ Cs * ι ^ 2 := one_le_mul_of_one_le_of_one_le hCs1 hι2
    have := mul_le_mul_of_nonneg_right h1 (pow_nonneg hx0.le 2)
    linarith
  have hCsmall : Cs / x ^ 2 ≤ X := by
    rw [hX, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul hι2 h2 (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ Cs)
    linarith
  have e1 : 168 * Cs / x ^ 2 = 168 * (Cs / x ^ 2) := by ring
  have e2 : (168 : ℝ) / x ^ 2 = 168 * (1 / x ^ 2) := by ring
  have hgoal : C * Cs * ι ^ 2 / x ^ 3 = C * X := by rw [hX]; ring
  rw [hgoal]
  have hsum : ψ + φ ≤ 366240 * X := by rw [e1, e2] at hψ; linarith
  exact hsum.trans (mul_le_mul_of_nonneg_right hC hX0)

theorem log_ratio_le {S A : Type*} [Fintype S] [Fintype A] (M : DiscountedMDP S A) {T : ℕ}
    {δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ) :
    Real.log (2 * T / (δ / 5)) ≤ 3 + iota S A T δ := by
  haveI := M.state_nonempty; haveI := M.action_nonempty
  have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hSA : (1 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A := one_le_mul_of_one_le_of_one_le hS hA
  have hTX : (T : ℝ) / δ ≤ (Fintype.card S : ℝ) * Fintype.card A * T / δ :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left (by positivity) hSA) hδ.le
  have hL' : Real.log (2 * T / (δ / 5)) = Real.log 10 + Real.log (T / δ) := by
    rw [show 2 * (T : ℝ) / (δ / 5) = 10 * (T / δ) by field_simp; ring]
    exact Real.log_mul (by norm_num) (by positivity)
  have h1 : Real.log (T / δ) ≤ iota S A T δ := Real.log_le_log (by positivity) hTX
  have h10 := log_ten_le_three
  linarith

end ScalarFinal

section Main

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  (ρ : FiniteDistribution S) (πstar : S → A) (db : FiniteDistribution (S × A))

/-- The constant of `Lemma6_12_restricted`. -/
noncomputable def lemma612Const (cb : ℝ) : ℝ := 400000 + 5600 * cb

/-- The pathwise conclusion of Lemma 6.12 on one data sequence. -/
def lemma612Conclusion {T : ℕ} (data : Fin T → (S × A) × S) : Prop :=
  let γ := M.discount
  let ι := iota S A T δ
  let Cs := concentrability M ρ πstar db
  let C := lemma612Const cb
  Tendsto (alphaSeq M cb δ sel π₀ data ρ πstar) atTop (𝓝 0) ∧
  (∃ ξ, HasSum (xiSeq M cb δ sel π₀ data ρ πstar) ξ ∧ ξ ≤ C / (1 - γ) ^ 2) ∧
  (∃ θ, HasSum (thetaSeq M cb δ sel π₀ data ρ πstar) θ ∧
    (Cs ≠ ⊤ → θ ≤ C * Real.sqrt (Cs.toReal * Fintype.card S * T * ι ^ 2 / (1 - γ) ^ 5))) ∧
  (∃ ψ φ, HasSum (psiSeq M cb δ sel π₀ data ρ πstar db) ψ ∧
    HasSum (phiSeq M cb δ sel π₀ data ρ πstar db) φ ∧
    (Cs ≠ ⊤ → ψ + φ ≤ C * Cs.toReal * ι ^ 2 / (1 - γ) ^ 3))

theorem thetaSeq_summable {T : ℕ} (data : Fin T → (S × A) × S)
    (hι : 1 ≤ iota S A T δ) : Summable (thetaSeq M cb δ sel π₀ data ρ πstar) := by
  set κ := kappa M.discount (horizon M.discount (iota S A T δ))
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hκ1 : κ < 1 := kappa_lt_one M hι
  have hθ : thetaSeq M cb δ sel π₀ data ρ πstar = fun j => ∑ t ∈ Finset.Icc 1 T,
      κ ^ j * ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s *
        betaTrunc cb M.discount (iota S A T δ) (horizon M.discount (iota S A T δ))
          ((run M cb δ sel π₀ data t).count s (πstar s)) := by
    funext j
    simp only [thetaSeq, Finset.mul_sum]
    rfl
  rw [hθ]
  exact summable_sum fun t _ => by
    simpa using summable_kappa_occ M hκ0 hκ1 (detPolicy πstar) ρ
      (fun s => betaTrunc cb M.discount (iota S A T δ) (horizon M.discount (iota S A T δ))
        ((run M cb δ sel π₀ data t).count s (πstar s))) 0

/-- The deterministic assembly: on the five events, the conclusion holds. -/
theorem lemma612Conclusion_of_events (hcb : 4 ≤ cb) {T : ℕ} (hT : 1 ≤ T) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hι : 1 ≤ iota S A T δ) (data : Fin T → (S × A) × S)
    (hC : concentrability M ρ πstar db ≠ ⊤ →
      (∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤ optValue M s) ∧
      prefixCountEvent db data δ ∧
      (∀ u : Fin T, δ / (5 * Fintype.card S * T) ≤ db.prob (data u).1 ∨
        (data u).1.2 ≠ πstar (data u).1.1) ∧
      (let κ := kappa M.discount (horizon M.discount (iota S A T δ))
       let thr := δ / (5 * Fintype.card S * T)
       let H := horizon M.discount (iota S A T δ)
       let K₀ := 504 * (concentrability M ρ πstar db).toReal / (1 - M.discount) ^ 2 *
         (4 * H * Real.log (2 * T / (δ / 5)) + 1 + 10 * Real.log (2 * T / (δ / 5)))
       (|∑ u : Fin T, (ratioI M ρ πstar db κ thr (data u).1 *
            visitDeltaSum M cb δ sel π₀ data u.val (data u).1.1 (data u).1.2 -
          edI M ρ πstar db κ thr (visitDeltaSum M cb δ sel π₀ data u.val))| ≤
        (∑ u : Fin T, edI M ρ πstar db κ thr (visitDeltaSum M cb δ sel π₀ data u.val)) /
          (2 * H) + K₀) ∧
       (|∑ u : Fin T, (ratioI M ρ πstar db κ thr (data u).1 *
            (M.transition (data u).1.1 (data u).1.2).expectation (delta M cb δ sel π₀ data u.val) -
          edI M ρ πstar db κ thr
            (fun s a => (M.transition s a).expectation (delta M cb δ sel π₀ data u.val)))| ≤
        (∑ u : Fin T, edI M ρ πstar db κ thr
            (fun s a => (M.transition s a).expectation (delta M cb δ sel π₀ data u.val))) /
          (2 * H) + K₀))) :
    lemma612Conclusion M cb δ sel π₀ ρ πstar db data := by
  have hcb0 : 0 ≤ cb := by linarith
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hx1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
  set C := lemma612Const cb with hCdef
  have hC168 : 168 ≤ C := by rw [hCdef]; unfold lemma612Const; linarith
  refine ⟨alphaSeq_tendsto_zero M cb δ sel π₀ data ρ πstar hcb0 hι, ?_, ?_, ?_⟩
  · obtain ⟨ξ, hξ, hξle⟩ := xiSeq_hasSum_le M cb δ sel π₀ data ρ πstar hT hδ hδ1 hι
    exact ⟨ξ, hξ, hξle.trans (div_le_div_of_nonneg_right hC168 (by positivity))⟩
  · by_cases hCs : concentrability M ρ πstar db = ⊤
    · exact ⟨_, (thetaSeq_summable M cb δ sel π₀ ρ πstar data hι).hasSum,
        fun h => absurd hCs h⟩
    · obtain ⟨_, hcount, _⟩ := hC hCs
      obtain ⟨θ, hθ, hθle⟩ := thetaSeq_hasSum_le M cb δ sel π₀ data ρ πstar db hcb0 hT hδ hδ1 hι
        hCs hcount
      refine ⟨θ, hθ, fun _ => hθle.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      unfold lemma612Const; linarith
  · refine ⟨_, _, psiSeq_hasSum M cb δ sel π₀ data ρ πstar db hι,
      phiSeq_hasSum M cb δ sel π₀ data ρ πstar db hι, fun hCs => ?_⟩
    obtain ⟨hpess, -, hIc, hZψ, hZφ⟩ := hC hCs
    set Cs := (concentrability M ρ πstar db).toReal with hCsdef
    have hCs1 : 1 ≤ Cs := one_le_concentrability M ρ πstar db hCs
    set ι := iota S A T δ with hιdef
    set H := horizon M.discount ι with hHdef
    set L := Real.log (2 * T / (δ / 5)) with hLdef
    set K₀ := 504 * Cs / (1 - M.discount) ^ 2 * (4 * H * L + 1 + 10 * L) with hK₀
    have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hL0 : 0 ≤ L := by
      rw [hLdef]; apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
    have hK₀0 : 0 ≤ K₀ := by positivity
    have hψ := psiTotal_le M cb δ sel π₀ data ρ πstar db hcb0 hT hδ hδ1 hι hCs hpess K₀ hK₀0 hZψ
    have hφ := phiTotal_le M cb δ sel π₀ data ρ πstar db hT hδ hδ1 hpess hIc K₀ hK₀0 hZφ
    have hLι : L ≤ 4 * ι := by
      have := log_ratio_le M (T := T) hT hδ
      linarith
    have hC' : 366240 ≤ C := by rw [hCdef]; unfold lemma612Const; linarith
    exact psi_phi_final hx0 hx1 hCs1 hι (horizon_le M hι) hL0 hLι hK₀ hψ hφ hC'

end Main

section Prob

theorem inter_five_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {E₁ E₂ E₃ E₄ E₅ : Set Ω} {ε : ℝ}
    (h₁ : MeasurableSet E₁) (h₂ : MeasurableSet E₂) (h₃ : MeasurableSet E₃)
    (h₄ : MeasurableSet E₄) (h₅ : MeasurableSet E₅)
    (p₁ : 1 - ε ≤ μ.real E₁) (p₂ : 1 - ε ≤ μ.real E₂) (p₃ : 1 - ε ≤ μ.real E₃)
    (p₄ : 1 - ε ≤ μ.real E₄) (p₅ : 1 - ε ≤ μ.real E₅) :
    1 - 5 * ε ≤ μ.real (E₁ ∩ E₂ ∩ E₃ ∩ E₄ ∩ E₅) := by
  have hm : MeasurableSet (E₁ ∩ E₂ ∩ E₃ ∩ E₄ ∩ E₅) :=
    ((((h₁.inter h₂).inter h₃).inter h₄).inter h₅)
  have hc := probReal_compl_eq_one_sub (μ := μ) hm
  have hu : μ.real (E₁ ∩ E₂ ∩ E₃ ∩ E₄ ∩ E₅)ᶜ ≤
      μ.real E₁ᶜ + μ.real E₂ᶜ + μ.real E₃ᶜ + μ.real E₄ᶜ + μ.real E₅ᶜ := by
    simp only [Set.compl_inter]
    refine (measureReal_union_le _ _).trans ?_
    gcongr
    refine (measureReal_union_le _ _).trans ?_
    gcongr
    refine (measureReal_union_le _ _).trans ?_
    gcongr
    exact measureReal_union_le _ _
  rw [probReal_compl_eq_one_sub h₁, probReal_compl_eq_one_sub h₂, probReal_compl_eq_one_sub h₃,
    probReal_compl_eq_one_sub h₄, probReal_compl_eq_one_sub h₅] at hu
  linarith

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  (ρ : FiniteDistribution S) (πstar : S → A) (db : FiniteDistribution (S × A))

set_option maxHeartbeats 1000000 in
/-- **Lemma 6.12, restricted to `log(SAT/δ) ≥ 1`** (library form): for `c_b ≥ 4`, with
probability at least `1 − δ` the conclusion `lemma612Conclusion` holds. -/
theorem lemma612_prob (hcb : 4 ≤ cb) (T : ℕ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : 1 ≤ iota S A T δ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ ≤ μ.real {ω | lemma612Conclusion M cb δ sel π₀ ρ πstar db (X ω)} := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  have hcb0 : 0 ≤ cb := by linarith
  have hT : 1 ≤ T := by
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · subst h0; simp [iota] at hι; linarith
    · exact h0
  have hpre : ∀ P : (Fin T → (S × A) × S) → Prop, MeasurableSet {ω | P (X ω)} :=
    fun P => hX (Set.toFinite {x | P x}).measurableSet
  by_cases hCs : concentrability M ρ πstar db = ⊤
  · have huniv : {ω | lemma612Conclusion M cb δ sel π₀ ρ πstar db (X ω)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lemma612Conclusion_of_events M cb δ sel π₀ ρ πstar db hcb hT hδ hδ1 hι (X ω)
        (fun h => absurd hCs h)
    rw [huniv, probReal_univ]; linarith
  have hlaw := iid_map_eq_pi M db μ X hX hind hmarg
  set jr := JointRow.jointRow db M.transition with hjr
  have hν : μ.map X = onlineStackProductLaw (fun _ : Fin T => jr) := hlaw
  have hlift : ∀ B : Set (Fin T → (S × A) × S),
      μ.real (X ⁻¹' B) = (onlineStackProductLaw (fun _ : Fin T => jr)).real B := by
    intro B
    rw [← hν, map_measureReal_apply hX (Set.toFinite B).measurableSet]
  obtain ⟨x₀⟩ : Nonempty ((S × A) × S) :=
    ⟨((M.state_nonempty.some, M.action_nonempty.some), M.state_nonempty.some)⟩
  -- the five events
  set E₁ := {ω | martingaleEvent M cb δ sel π₀ (X ω) (δ / 5)} with hE₁
  set E₂ := {ω | prefixCountEvent db (X ω) δ} with hE₂
  set E₃ := {ω | ∀ u : Fin T, δ / (5 * Fintype.card S * T) ≤ db.prob (X ω u).1 ∨
    (X ω u).1.2 ≠ πstar (X ω u).1.1} with hE₃
  have p₁ : 1 - δ / 5 ≤ μ.real E₁ :=
    (martingaleEvent_prob_conf M cb δ sel π₀ hcb0 db T hδ hδ1 (δ / 5) (by positivity)
      (by linarith) μ X hX hind hmarg).le
  have p₂ : 1 - δ / 5 ≤ μ.real E₂ := prefixCountEvent_prob M db hδ hδ1 hι μ X hX hlaw
  have p₃ : 1 - δ / 5 ≤ μ.real E₃ := icEvent_prob M db πstar hδ μ X hX hmarg
  have hψ := freedman_gated_prob M cb δ sel π₀ ρ πstar db hT hδ hδ1 hι hCs x₀
    (fun data u s a => visitDeltaSum M cb δ sel π₀ data u s a)
    (fun data data' u hu h => funext fun s => funext fun a =>
      visitDeltaSum_congr M cb δ sel π₀ hu.le h s a)
    (fun data u hu hg s a => visitDeltaSum_bounds M cb δ sel π₀ data hcb0 hT hδ hδ1 hu.le
      (fun v hv s => hg v hv.le s) s a)
    _ _ _ rfl rfl rfl
  have hφ := freedman_gated_prob M cb δ sel π₀ ρ πstar db hT hδ hδ1 hι hCs x₀
    (fun data u s a => (M.transition s a).expectation (delta M cb δ sel π₀ data u))
    (fun data data' u _ h => by
      funext s a
      simp only
      rw [delta_congr M cb δ sel π₀ h])
    (fun data u _ hg s a => ⟨FiniteDistribution.expectation_nonneg _ fun x => by
        have := hg u le_rfl x
        simp only [delta]; linarith,
      FiniteDistribution.expectation_le_const _ fun x => delta_le M cb δ sel π₀ data hcb0 u x⟩)
    _ _ _ rfl rfl rfl
  rw [← hlift] at hψ hφ
  have h₁ : MeasurableSet E₁ := hpre (fun x => martingaleEvent M cb δ sel π₀ x (δ / 5))
  have h₂ : MeasurableSet E₂ := hpre (fun x => prefixCountEvent db x δ)
  have h₃ : MeasurableSet E₃ := hpre (fun x => ∀ u : Fin T,
    δ / (5 * Fintype.card S * T) ≤ db.prob (x u).1 ∨ (x u).1.2 ≠ πstar (x u).1.1)
  have hall := inter_five_prob μ h₁ h₂ h₃ (hX (Set.toFinite _).measurableSet)
    (hX (Set.toFinite _).measurableSet) p₁ p₂ p₃ hψ hφ
  refine le_trans (by linarith) (hall.trans (measureReal_mono ?_))
  rintro ω ⟨⟨⟨⟨hω₁, hω₂⟩, hω₃⟩, hω₄⟩, hω₅⟩
  have hpess := pess_of_event_fifth M cb δ sel π₀ (X ω) hcb hδ hδ1 hι hω₁
  have hgate : ∀ u, u < T → gateProp M cb δ sel π₀ (X ω) u :=
    fun u hu v hv s => hpess v (by omega) s
  exact lemma612Conclusion_of_events M cb δ sel π₀ ρ πstar db hcb hT hδ hδ1 hι (X ω)
    (fun _ => ⟨hpess, hω₂, hω₃, hω₄ hgate, hω₅ hgate⟩)

end Prob

end StatisticalRL.OfflineRL.LCBQ
