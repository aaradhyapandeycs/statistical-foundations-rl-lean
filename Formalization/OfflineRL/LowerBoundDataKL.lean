import Formalization.OfflineRL.LowerBoundConcentrability
import Formalization.OfflineRL.JointRowLaw
import Formalization.PrelimKL.KLArbitraryFinitePi
import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing
import Formalization.Probability.FiniteDistributionBridge

/-!
# KL divergence of offline datasets for the hard family

`chapters/offlineRL.tex:2798–2892` (Step 3 of the proof of `thm:infinite-lwoer-bound`).

* `jointRow_klDiv`: the one-sample chain rule `eq:single-sample-KL-infinite` (`:2803–2827`): for the
  law `d^b ⊗ P` of one triple `((s,a), s')`,
  `KL(d^b ⊗ P ‖ d^b ⊗ P') = ∑_{(s,a)} d^b(s,a) KL(P(·|s,a) ‖ P'(·|s,a))`, whenever every row of `P`
  is absolutely continuous with respect to the matching row of `P'`. The source uses this
  standard identity without citation.
* `sampleMeasure_klDiv`: KL tensorization for `N` independent copies (Lemma 2.12).
* `lb_jointRow_klDiv_le`, `lb_dataset_klDiv_le`: for the hard family with the behaviour law
  `d^b(s,a) = μ(s)/2`, combining the chain rule with Lemma 6.15 (`lb_transition_kl`, constant
  `c₃ = 16 · 336²`) gives `KL(μ^{b,θ} ‖ μ^{b,θ'}) ≤ c₃ (1-γ)³ ε² / C` (`eq:KL-bound-infinite`,
  `:2873–2890`, before the substitution `C ≥ C⋆_ρ/2`) and `N` times that for the dataset.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.OfflineRL.JointRow

open StatisticalRL

section Generic

variable {X : Type*} [Fintype X]

local instance genericRowMeasurable : MeasurableSpace X := ⊤

local instance genericRowSingleton : MeasurableSingletonClass X :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Atom masses of the row law. -/
theorem rowMeasure_singleton_eq (d : FiniteDistribution X) (x : X) :
    d.rowMeasure {x} = ENNReal.ofReal (d.prob x) :=
  FiniteDistribution.rowMeasure_singleton d x

/-- Real atom masses of the row law. -/
theorem rowMeasure_real_singleton_eq (d : FiniteDistribution X) (x : X) :
    d.rowMeasure.real {x} = d.prob x :=
  FiniteDistribution.rowMeasure_real_singleton d x

/-- Absolute continuity of row laws from the vanishing of atoms. -/
theorem rowMeasure_ac (d d' : FiniteDistribution X) (h : ∀ x, d'.prob x = 0 → d.prob x = 0) :
    d.rowMeasure ≪ d'.rowMeasure := by
  intro s hs
  rw [← Set.biUnion_of_singleton s]
  refine (measure_biUnion_null_iff (Set.toFinite s).countable).mpr fun x hx => ?_
  have hx0 : d'.rowMeasure {x} = 0 := measure_mono_null (Set.singleton_subset_iff.mpr hx) hs
  rw [rowMeasure_singleton_eq, ENNReal.ofReal_eq_zero] at hx0
  rw [rowMeasure_singleton_eq, h x (le_antisymm hx0 (d'.prob_nonneg x)), ENNReal.ofReal_zero]

/-- KL divergence of two row laws with `d ≪ d'`, as the finite atomic expression. -/
theorem rowMeasure_klDiv (d d' : FiniteDistribution X) (h : ∀ x, d'.prob x = 0 → d.prob x = 0) :
    InformationTheory.klDiv d.rowMeasure d'.rowMeasure ≠ ∞ ∧
      (InformationTheory.klDiv d.rowMeasure d'.rowMeasure).toReal =
        GenerativeLowerBound.finiteKLExpression d.prob d'.prob := by
  have hac := rowMeasure_ac d d' h
  refine ⟨GenerativeLowerBound.finite_klDiv_ne_top_of_ac _ _ hac, ?_⟩
  rw [GenerativeLowerBound.finite_klDiv_eq_expression_of_ac _ _ hac]
  simp only [rowMeasure_real_singleton_eq]

/-- KL tensorization for `N` independent copies of one row law (Lemma 2.12). -/
theorem sampleMeasure_klDiv (d d' : FiniteDistribution X) (N : ℕ) :
    InformationTheory.klDiv (d.sampleMeasure N) (d'.sampleMeasure N) =
      N * InformationTheory.klDiv d.rowMeasure d'.rowMeasure := by
  unfold FiniteDistribution.sampleMeasure
  rw [PrelimKL.klDiv_pi_eq_sum (fun _ : Fin N => X) (fun _ => d.rowMeasure)
    (fun _ => d'.rowMeasure)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Generic

section ChainRule

variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance chainStateMeasurable : MeasurableSpace State := ⊤

local instance (priority := high) chainTripleMeasurable :
    MeasurableSpace ((State × Action) × State) := ⊤

/-- **One-sample KL chain rule** (`eq:single-sample-KL-infinite`, `chapters/offlineRL.tex:2803–2827`):
`KL(d^b ⊗ P ‖ d^b ⊗ P') = ∑_{(s,a)} d^b(s,a) KL(P(·|s,a) ‖ P'(·|s,a))` when every row of `P` is
absolutely continuous with respect to the matching row of `P'`; the left side is then finite. -/
theorem jointRow_klDiv (db : FiniteDistribution (State × Action))
    (P P' : State → Action → FiniteDistribution State)
    (hac : ∀ s a t, (P' s a).prob t = 0 → (P s a).prob t = 0) :
    InformationTheory.klDiv (jointRow db P).rowMeasure (jointRow db P').rowMeasure ≠ ∞ ∧
      (InformationTheory.klDiv (jointRow db P).rowMeasure (jointRow db P').rowMeasure).toReal =
        ∑ sa : State × Action, db.prob sa *
          (InformationTheory.klDiv (P sa.1 sa.2).rowMeasure (P' sa.1 sa.2).rowMeasure).toReal := by
  have hacJ : ∀ x, (jointRow db P').prob x = 0 → (jointRow db P).prob x = 0 := by
    intro x hx
    change db.prob x.1 * (P' x.1.1 x.1.2).prob x.2 = 0 at hx
    change db.prob x.1 * (P x.1.1 x.1.2).prob x.2 = 0
    rcases mul_eq_zero.mp hx with h | h
    · rw [h, zero_mul]
    · rw [hac _ _ _ h, mul_zero]
  obtain ⟨hne, heq⟩ := rowMeasure_klDiv (jointRow db P) (jointRow db P') hacJ
  refine ⟨hne, ?_⟩
  rw [heq]
  unfold GenerativeLowerBound.finiteKLExpression
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun sa _ => ?_
  rw [(rowMeasure_klDiv (P sa.1 sa.2) (P' sa.1 sa.2) (hac sa.1 sa.2)).2]
  unfold GenerativeLowerBound.finiteKLExpression
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  change db.prob sa * (P sa.1 sa.2).prob t *
      Real.log (db.prob sa * (P sa.1 sa.2).prob t / (db.prob sa * (P' sa.1 sa.2).prob t)) =
    db.prob sa * ((P sa.1 sa.2).prob t * Real.log ((P sa.1 sa.2).prob t / (P' sa.1 sa.2).prob t))
  by_cases hd : db.prob sa = 0
  · simp [hd]
  · rw [mul_div_mul_left _ _ hd]; ring

end ChainRule

end StatisticalRL.OfflineRL.JointRow

namespace StatisticalRL.OfflineRL.LowerBound

open StatisticalRL.OfflineRL.JointRow

local instance lbDataStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

local instance (priority := high) lbDataTripleMeasurable (m : ℕ) :
    MeasurableSpace ((Option (Fin m) × Bool) × Option (Fin m)) := ⊤

section Family

variable (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
  (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C)

/-- The rows of `M_θ` are absolutely continuous with respect to those of `M_θ'`: the rows at the
positive states have full support and the rows at state `0` do not depend on `θ`. -/
theorem lb_transition_ac (θ θ' : Fin m → Bool) (s : Option (Fin m)) (a : Bool)
    (t : Option (Fin m)) :
    ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition s a).prob t = 0 →
      ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition s a).prob t = 0 := by
  intro h
  cases s with
  | none =>
    have e : (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition none a =
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition none a := rfl
    rw [e]; exact h
  | some i =>
    exfalso
    have hγ0 : 0 < γ := by linarith
    have hg0 := lbGap_nonneg hγ hε
    have hg1 := lbGap_le hγ hγ1 hεmax
    have hμ := lbMu_pos hC hm t
    have hpos : ∀ (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1), x < 1 →
        0 < (lbRow C m hC hm (some i) x hx0 hx1).prob t := by
      intro x hx0 hx1 hxlt
      change 0 < x * (if t = some i then 1 else 0) + (1 - x) * lbMu C m t
      have h1 : 0 < (1 - x) * lbMu C m t := mul_pos (by linarith) hμ
      have h2 : 0 ≤ x * (if t = some i then (1 : ℝ) else 0) := by
        apply mul_nonneg hx0; split <;> norm_num
      linarith
    by_cases ha : a = θ' i
    · have e : (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition (some i) a =
          lbRow C m hC hm (some i) (lbP γ ε) (by unfold lbP; linarith) (by unfold lbP; linarith) := by
        simp only [lbMDP, ha, if_true]
      rw [e] at h
      exact (hpos (lbP γ ε) _ _ (by unfold lbP; linarith)).ne' h
    · have e : (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition (some i) a =
          lbRow C m hC hm (some i) (lbQ γ ε) (by unfold lbQ; linarith) (by unfold lbQ; linarith) := by
        simp only [lbMDP, ha, if_false]
      rw [e] at h
      exact (hpos (lbQ γ ε) _ _ (by unfold lbQ; linarith)).ne' h

/-- One-sample KL bound for the hard family: `KL(μ^{b,θ} ‖ μ^{b,θ'}) ≤ c₃ (1-γ)³ ε² / C` with
`c₃ = 16 · 336²`; the divergence is finite. -/
theorem lb_jointRow_klDiv_le (θ θ' : Fin m → Bool) :
    InformationTheory.klDiv
        (jointRow (lbBehavior C m hC hm) (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition).rowMeasure
        (jointRow (lbBehavior C m hC hm) (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition).rowMeasure
        ≠ ∞ ∧
      InformationTheory.klDiv
        (jointRow (lbBehavior C m hC hm) (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition).rowMeasure
        (jointRow (lbBehavior C m hC hm) (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition).rowMeasure
        ≤ ENNReal.ofReal (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / C) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hC0 : 0 < C := by linarith
  have hγ1' : 0 < 1 - γ := by linarith
  obtain ⟨hne, heq⟩ := jointRow_klDiv (lbBehavior C m hC hm)
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition
    (lb_transition_ac m hm γ ε C hγ hγ1 hε hεmax hC θ θ')
  refine ⟨hne, ?_⟩
  have hCne : C ≠ 0 := hC0.ne'
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  have hmm : (m : ℝ) * (1 / m) = 1 := mul_one_div_cancel hmne
  set K : ℝ := 16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hγ1'.le 3)) (sq_nonneg ε)
  rw [ENNReal.le_ofReal_iff_toReal_le hne (div_nonneg hK0 hC0.le), heq, Fintype.sum_prod_type,
    Fintype.sum_option]
  dsimp only
  have hnone : ∀ a : Bool,
      (lbBehavior C m hC hm).prob (none, a) *
        (InformationTheory.klDiv
          ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition none a).rowMeasure
          ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition none a).rowMeasure).toReal = 0 := by
    intro a
    have e : (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition none a =
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition none a := rfl
    rw [e, InformationTheory.klDiv_self, ENNReal.toReal_zero, mul_zero]
  have hsome : ∀ (i : Fin m) (a : Bool),
      (lbBehavior C m hC hm).prob (some i, a) *
        (InformationTheory.klDiv
          ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition (some i) a).rowMeasure
          ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition (some i) a).rowMeasure).toReal ≤
        (1 / (C * m) / 2) * K := by
    intro i a
    have hdb : (lbBehavior C m hC hm).prob (some i, a) = 1 / (C * m) / 2 := rfl
    rw [hdb]
    refine mul_le_mul_of_nonneg_left ?_
      (div_nonneg (div_nonneg zero_le_one (mul_pos hC0 hmR).le) zero_le_two)
    obtain ⟨h0, h1⟩ := lb_transition_kl m hm γ ε C hγ hγ1 hε hεmax hC θ θ' i a
    by_cases hθ : θ i = θ' i
    · rw [h0 hθ, ENNReal.toReal_zero]
      exact hK0
    · exact ENNReal.toReal_le_of_le_ofReal hK0 (h1 hθ)
  calc _ = ∑ i : Fin m, ∑ a : Bool, (lbBehavior C m hC hm).prob (some i, a) *
          (InformationTheory.klDiv
            ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition (some i) a).rowMeasure
            ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition (some i) a).rowMeasure).toReal := by
        rw [Finset.sum_eq_zero fun a _ => hnone a, zero_add]
    _ ≤ ∑ _i : Fin m, ∑ _a : Bool, (1 / (C * m) / 2) * K :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => hsome i a
    _ = K / C := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_ofNat]
        linear_combination (K / C) * hmm

/-- **Dataset KL bound** (`eq:KL-bound-infinite`, `chapters/offlineRL.tex:2873–2890`, together with
KL tensorization): for `N` iid triples,
`KL(μ^{b,θ}_N ‖ μ^{b,θ'}_N) ≤ N c₃ (1-γ)³ ε² / C` with `c₃ = 16 · 336²`; it is finite. -/
theorem lb_dataset_klDiv_le (θ θ' : Fin m → Bool) (N : ℕ) :
    InformationTheory.klDiv
        ((jointRow (lbBehavior C m hC hm) (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition).sampleMeasure N)
        ((jointRow (lbBehavior C m hC hm) (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition).sampleMeasure N)
        ≠ ∞ ∧
      InformationTheory.klDiv
        ((jointRow (lbBehavior C m hC hm) (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition).sampleMeasure N)
        ((jointRow (lbBehavior C m hC hm) (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ').transition).sampleMeasure N)
        ≤ ENNReal.ofReal (N * (16 * 336 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / C)) := by
  obtain ⟨hne, hle⟩ := lb_jointRow_klDiv_le m hm γ ε C hγ hγ1 hε hεmax hC θ θ'
  rw [sampleMeasure_klDiv]
  refine ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hne, ?_⟩
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
  exact mul_le_mul_of_nonneg_left hle (zero_le _)

end Family

end StatisticalRL.OfflineRL.LowerBound
