import Formalization.OfflineRL.BernsteinInfiniteFixedRow
import Formalization.OfflineRL.BernsteinInfiniteCover
import Formalization.OfflineRL.VILCBDatasetDefinitions
import Formalization.OfflineRL.EmittedLaw

/-!
# Lemma 6.6: the leave-one-out probability layer

Source: `chapters/offlineRL.tex`, Lemma 6.6 (`lem:Bernstein-infinite`, lines 1147–1163; proof from
line 3630). Data model `eq:sampling-offline-inf-iid` (`:28–37`).

The dataset is realized as in `EmittedLaw`: iid labels `(s_i,a_i) ~ ρ`, an independent transition
stack whose coordinate `((s,a),k)` is drawn from `P_{s,a}`, and sample `i` reads the stack at its
label and its past-visit rank. `emitObservation_law` proves that this has exactly the iid triple law.

For fixed labels:
- `P̂_{s,a}` is the empirical row of the `N_{s,a}` stack draws at row `(s,a)`
  (`dataPhat_emit`), with law `P_{s,a}^{⊗N_{s,a}}` (`visitDraw_law`);
- the auxiliary fixed point `Q̂⋆_{s,u}` depends only on stack coordinates with row-state `≠ s`
  (`auxFix_emit_offState`), hence is independent of `P̂_{s,a}` (`indep_offState_draw`). This is
  the conditional independence the source states at `:1126–1128` and `:3970–3972`.

Lemma 6.18 then applies on every grid point and every pair with `N_{s,a} ≥ 27`
(`gridBound_fail_lt`), and the union bound of `:3969–3991` gives failure at most `δ` for each label
sequence (`perLabel_bad_le`). Pairs with `N_{s,a} ≤ 26` hold surely (C23). Integrating over labels
gives the statement under the iid triple law (`bernsteinInfinite_jointLaw`) and for any iid
dataset `X` (`bernsteinInfinite_iid`).

The event's failure level `δ'` is kept separate from the penalty parameter `p.δ`; the printed
lemma is the case `δ' = p.δ`.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineVILCB

open StatisticalRL StatisticalRL.OfflineRL

variable {S A : Type*} [Fintype S] [Fintype A]

namespace Input

/-- The auxiliary fixed point at state `s` depends on the input only through the scalar fields,
the counts, the rewards and the empirical rows at states `≠ s`. -/
theorem auxFix_congr [Nonempty A] (M M' : Input S A) (s : S) (u : ℝ) (hγ : M.γ = M'.γ)
    (hN : M.N = M'.N) (hc : M.count = M'.count) (hr : M.r = M'.r) (hcb : M.cb = M'.cb)
    (hδ : M.δ = M'.δ) (hP : ∀ t, t ≠ s → M.Phat t = M'.Phat t) :
    M.auxFix s u = M'.auxFix s u := by
  have hlog : M.logTerm = M'.logTerm := by
    unfold logTerm
    rw [hγ, hN, hδ]
  have hbAbs : M.bonusAbs = M'.bonusAbs := by
    funext t a
    unfold bonusAbs
    rw [hγ, hN, hc, hcb, hlog]
  have hux : M.uMax s = M'.uMax s := by
    unfold uMax minBonusAbs
    rw [hbAbs]
  have hpess : ∀ Q t a, t ≠ s → M.pess Q t a = M'.pess Q t a := by
    intro Q t a ht
    unfold pess tilde bonus
    rw [hγ, hN, hc, hr, hcb, hlog, hP t ht]
  have haux : ∀ Q, M.auxPess s u Q = M'.auxPess s u Q := by
    intro Q
    funext t a
    by_cases ht : t = s
    · subst ht
      rw [auxPess_self, auxPess_self, hbAbs, hγ]
    · rw [M.auxPess_of_ne s u Q ht, M'.auxPess_of_ne s u Q ht, hpess Q t a ht]
  have hbox : M.box = M'.box := by
    unfold box
    rw [hγ]
  by_cases h : 1 / 2 ≤ M.γ ∧ u ≤ M.uMax s
  · have h' : 1 / 2 ≤ M'.γ ∧ u ≤ M'.uMax s := by rw [← hγ, ← hux]; exact h
    obtain ⟨hb', hf'⟩ := M'.auxFix_spec h'.1 s h'.2
    rw [← hbox] at hb'
    rw [← haux] at hf'
    exact (M.eq_auxFix h.1 s h.2 _ hb' hf').symm
  · have h' : ¬ (1 / 2 ≤ M'.γ ∧ u ≤ M'.uMax s) := by rw [← hγ, ← hux]; exact h
    unfold auxFix
    rw [dif_neg h, dif_neg h']

end Input

namespace LeaveOneOut

theorem finiteDistribution_ext {X : Type*} [Fintype X] {d₁ d₂ : FiniteDistribution X}
    (h : ∀ x, d₁.prob x = d₂.prob x) : d₁ = d₂ := by
  obtain ⟨p₁, _, _⟩ := d₁
  obtain ⟨p₂, _, _⟩ := d₂
  have : p₁ = p₂ := funext h
  subst this
  rfl

/-- A sum of indicators is a filter cardinality, for any decidability instance. -/
theorem sum_ite_one_eq_card {ι : Type*} [Fintype ι] (p : ι → Prop) {inst : DecidablePred p} :
    (∑ i, @ite ℝ (p i) (inst i) 1 0) = ((@Finset.filter ι p inst Finset.univ).card : ℝ) := by
  rw [@Finset.card_filter ι p inst Finset.univ]
  push_cast
  rfl

open Classical in
/-- Visit count of the label sequence (equal to `dataCount` of any emitted dataset). -/
noncomputable def labelCount {N : ℕ} (l : Fin N → S × A) (s : S) (a : A) : ℕ :=
  (Finset.univ.filter fun i => l i = (s, a)).card

omit [Fintype S] [Fintype A] in
theorem labelCount_le {N : ℕ} (l : Fin N → S × A) (s : S) (a : A) : labelCount l s a ≤ N := by
  classical
  unfold labelCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The good event of Lemma 6.6 for a dataset `x`, with failure level `δ'` (`:1147–1163`). -/
def goodSet [Nonempty S] [Nonempty A] (p : Params S A) (P : S → A → FiniteDistribution S)
    (δ' : ℝ) : Set (Fin p.N → (S × A) × S) :=
  {x | ∀ Qstar : S → A → ℝ, (p.input x).pess Qstar = Qstar →
    ∀ (s : S) (a : A), 0 < (p.input x).count s a →
    ∀ Vt : S → ℝ, (∀ t, |Vt t - Input.value Qstar t| ≤ 1 / p.N) →
      (∀ t, |Vt t| ≤ 1 / (1 - p.γ)) →
      (p.input x).Lemma66Bound (P s a) s a (Real.log (4 * p.N / ((1 - p.γ) * δ'))) Vt}

section Emit

open Classical

/-- The emitted dataset for labels `l` and transition stack `st`. -/
noncomputable def emit {N : ℕ} (l : Fin N → S × A) (st : (S × A) × Fin N → S) : Fin N → (S × A) × S :=
  EmittedLaw.emitObservation (l, st)

omit [Fintype S] [Fintype A] in
theorem emit_apply {N : ℕ} (l : Fin N → S × A) (st : (S × A) × Fin N → S) (i : Fin N) :
    emit l st i = (l i, st (l i, RankedPair.visitRankFin l i)) := rfl

omit [Fintype S] [Fintype A] in
theorem dataCount_emit {N : ℕ} (l : Fin N → S × A) (st : (S × A) × Fin N → S) (s : S) (a : A) :
    dataCount (emit l st) s a = labelCount l s a := rfl

omit [Fintype S] [Fintype A] in
theorem visitRank_lt_labelCount {N : ℕ} (l : Fin N → S × A) {i : Fin N} {s : S} {a : A}
    (hi : l i = (s, a)) : RankedPair.visitRank l i < labelCount l s a := by
  unfold RankedPair.visitRank RankedPair.pastVisits labelCount
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [hj.2, hi]
  · simp [hi]
  · simp

/-- The `N_{s,a}` stack draws at row `(s,a)`. -/
noncomputable def visitDraw {N : ℕ} (l : Fin N → S × A) (s : S) (a : A) (st : (S × A) × Fin N → S) :
    Fin (labelCount l s a) → S :=
  fun j => st ((s, a), ⟨j.val, lt_of_lt_of_le j.isLt (labelCount_le l s a)⟩)

omit [Fintype S] [Fintype A] in
/-- The ranks of the visits to `(s,a)` exhaust `{0, …, N_{s,a} - 1}`. -/
theorem exists_visit_of_rank {N : ℕ} (l : Fin N → S × A) (s : S) (a : A)
    (j : Fin (labelCount l s a)) : ∃ i, l i = (s, a) ∧ RankedPair.visitRank l i = j.val := by
  classical
  let I : Finset (Fin N) := Finset.univ.filter fun i => l i = (s, a)
  have hI : ∀ i ∈ I, l i = (s, a) := fun i hi => (Finset.mem_filter.mp hi).2
  let f : ∀ i ∈ I, Fin (labelCount l s a) := fun i hi =>
    ⟨RankedPair.visitRank l i, visitRank_lt_labelCount l (hI i hi)⟩
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (t := Finset.univ) f
    (fun _ _ => Finset.mem_univ _)
    (fun i₁ i₂ h₁ h₂ heq => by
      apply RankedPair.rankedPair_injective l
      simp only [f, Fin.mk.injEq] at heq
      simp only [Prod.mk.injEq]
      exact ⟨(hI i₁ h₁).trans (hI i₂ h₂).symm, heq⟩)
    (by
      rw [Finset.card_univ, Fintype.card_fin]
      unfold labelCount
      apply le_of_eq
      congr 1)
  obtain ⟨i, hi, hji⟩ := hsurj j (Finset.mem_univ j)
  refine ⟨i, hI i hi, ?_⟩
  rw [hji]

omit [Fintype A] in
theorem dataPhat_emit [Nonempty S] {N : ℕ} (l : Fin N → S × A) (st : (S × A) × Fin N → S)
    (s : S) (a : A) (hn : 0 < labelCount l s a) :
    dataPhat (emit l st) s a =
      FiniteDistribution.empiricalRow (labelCount l s a) hn (visitDraw l s a st) := by
  classical
  have h0 : dataCount (emit l st) s a ≠ 0 := by rw [dataCount_emit]; omega
  apply finiteDistribution_ext
  intro t
  unfold dataPhat
  rw [dif_neg h0]
  show ((dataCount (emit l st) s a : ℕ) : ℝ)⁻¹ * _ = ((labelCount l s a : ℕ) : ℝ)⁻¹ * _
  rw [dataCount_emit]
  congr 1
  refine (sum_ite_one_eq_card _).trans (Eq.trans ?_ (sum_ite_one_eq_card _).symm)
  congr 1
  apply Finset.card_bij (fun i hi => (⟨RankedPair.visitRank l i, visitRank_lt_labelCount l (by
      have h : emit l st i = ((s, a), t) := by simpa using hi
      exact congrArg Prod.fst h)⟩ : Fin (labelCount l s a)))
  · intro i hi
    have h : emit l st i = ((s, a), t) := by simpa using hi
    rw [emit_apply, Prod.mk.injEq] at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    calc visitDraw l s a st _ = st (l i, RankedPair.visitRankFin l i) :=
          congrArg st (Prod.ext h.1.symm (Fin.ext rfl))
      _ = t := h.2
  · intro i₁ h₁ i₂ h₂ heq
    have e₁ : emit l st i₁ = ((s, a), t) := by simpa using h₁
    have e₂ : emit l st i₂ = ((s, a), t) := by simpa using h₂
    rw [emit_apply, Prod.mk.injEq] at e₁ e₂
    apply RankedPair.rankedPair_injective l
    simp only [Fin.mk.injEq] at heq
    simp only [Prod.mk.injEq]
    exact ⟨e₁.1.trans e₂.1.symm, heq⟩
  · intro j hj
    obtain ⟨i, hi, hr⟩ := exists_visit_of_rank l s a j
    have hj' : visitDraw l s a st j = t := by simpa using hj
    refine ⟨i, ?_, Fin.ext hr⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [emit_apply, hi]
    refine Prod.ext rfl ?_
    show st ((s, a), RankedPair.visitRankFin l i) = t
    calc st ((s, a), RankedPair.visitRankFin l i) = visitDraw l s a st j :=
          congrArg st (Prod.ext rfl (Fin.ext hr))
      _ = t := hj'

omit [Fintype A] in
theorem dataPhat_emit_offState [Nonempty S] {N : ℕ} (l : Fin N → S × A)
    {s : S} (st st' : (S × A) × Fin N → S) (hagree : ∀ q : (S × A) × Fin N, q.1.1 ≠ s → st q = st' q)
    {t : S} (ht : t ≠ s) (a : A) : dataPhat (emit l st) t a = dataPhat (emit l st') t a := by
  classical
  unfold dataPhat
  by_cases h0 : dataCount (emit l st) t a = 0
  · have h0' : dataCount (emit l st') t a = 0 := by rw [dataCount_emit] at h0 ⊢; exact h0
    rw [dif_pos h0, dif_pos h0']
  · have h0' : dataCount (emit l st') t a ≠ 0 := by rw [dataCount_emit] at h0 ⊢; exact h0
    rw [dif_neg h0, dif_neg h0']
    apply finiteDistribution_ext
    intro t'
    simp only [dataCount_emit]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hl : l i = (t, a)
    · have hq : st (l i, RankedPair.visitRankFin l i) = st' (l i, RankedPair.visitRankFin l i) :=
        hagree _ (by rw [hl]; exact ht)
      rw [emit_apply, emit_apply, hq]
    · rw [emit_apply, emit_apply]
      simp [hl]

theorem auxFix_emit_offState [Nonempty S] [Nonempty A] (p : Params S A)
    (l : Fin p.N → S × A) {s : S} (st st' : (S × A) × Fin p.N → S)
    (hagree : ∀ q : (S × A) × Fin p.N, q.1.1 ≠ s → st q = st' q) (u : ℝ) :
    (p.input (emit l st)).auxFix s u = (p.input (emit l st')).auxFix s u := by
  refine Input.auxFix_congr (p.input (emit l st)) (p.input (emit l st')) s u rfl rfl ?_ rfl rfl rfl
    ?_
  · funext t a
    show dataCount (emit l st) t a = dataCount (emit l st') t a
    rw [dataCount_emit, dataCount_emit]
  · intro t ht
    funext a
    exact dataPhat_emit_offState l st st' hagree ht a

theorem uMax_emit [Nonempty S] [Nonempty A] (p : Params S A) (l : Fin p.N → S × A)
    (st st' : (S × A) × Fin p.N → S) (s : S) :
    (p.input (emit l st)).uMax s = (p.input (emit l st')).uMax s := rfl

theorem uGrid_emit [Nonempty S] [Nonempty A] (p : Params S A) (l : Fin p.N → S × A)
    (st st' : (S × A) × Fin p.N → S) (s : S) :
    (p.input (emit l st)).uGrid s = (p.input (emit l st')).uGrid s := rfl

local instance dataStateMeasurable : MeasurableSpace S := ⊤
local instance dataRowMeasurable : MeasurableSpace (FiniteDistribution S) := ⊤

theorem rowMeasure_isProbability {X : Type*} [Fintype X] (d : FiniteDistribution X) :
    @IsProbabilityMeasure X ⊤ d.rowMeasure := by
  unfold FiniteDistribution.rowMeasure
  exact @PMF.toMeasure.isProbabilityMeasure X ⊤ d.toPMF

theorem transitionStack_isProbability (P : S → A → FiniteDistribution S) (N : ℕ) :
    IsProbabilityMeasure (EmittedLaw.transitionStack P N) := by
  haveI : ∀ r : S × A, IsProbabilityMeasure (P r.1 r.2).rowMeasure :=
    fun r => rowMeasure_isProbability _
  show IsProbabilityMeasure (Measure.pi _)
  infer_instance

/-- The row-`(s,a)` stack draws have law `P_{s,a}^{⊗N_{s,a}}`. -/
theorem visitDraw_law (P : S → A → FiniteDistribution S) {N : ℕ} (l : Fin N → S × A)
    (s : S) (a : A) :
    (EmittedLaw.transitionStack P N).map (visitDraw l s a) =
      (P s a).sampleMeasure (labelCount l s a) := by
  haveI : ∀ r : (S × A) × Fin N, IsProbabilityMeasure (P r.1.1 r.1.2).rowMeasure :=
    fun r => rowMeasure_isProbability _
  have hinj : Function.Injective fun j : Fin (labelCount l s a) =>
      (((s, a), ⟨j.val, lt_of_lt_of_le j.isLt (labelCount_le l s a)⟩) : (S × A) × Fin N) := by
    intro j₁ j₂ h
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and] at h
    exact Fin.ext h
  exact StackProjection.pi_map_comp_injective
    (fun r : (S × A) × Fin N => (P r.1.1 r.1.2).rowMeasure) _ hinj

/-- Leave-one-out independence: any function of the stack coordinates with row-state `≠ s` is
independent of the empirical row at `(s,a)`. -/
theorem indep_offState_draw [Nonempty S] (P : S → A → FiniteDistribution S) {N : ℕ}
    (l : Fin N → S × A) (s : S) (a : A) (hn : 0 < labelCount l s a)
    {β : Type*} [MeasurableSpace β] (F : ((S × A) × Fin N → S) → β)
    (hF : ∀ st st', (∀ q : (S × A) × Fin N, q.1.1 ≠ s → st q = st' q) → F st = F st') :
    IndepFun F (fun st => FiniteDistribution.empiricalRow _ hn (visitDraw l s a st))
      (EmittedLaw.transitionStack P N) := by
  classical
  haveI : ∀ r : (S × A) × Fin N, IsProbabilityMeasure (P r.1.1 r.1.2).rowMeasure :=
    fun r => rowMeasure_isProbability _
  let T₁ : Finset ((S × A) × Fin N) := Finset.univ.filter fun q => q.1.1 ≠ s
  let T₂ : Finset ((S × A) × Fin N) := Finset.univ.filter fun q => q.1.1 = s
  have hdisj : Disjoint T₁ T₂ := by
    rw [Finset.disjoint_filter]
    intro q _ h1 h2
    exact h1 h2
  have hiid : iIndepFun (fun q (st : (S × A) × Fin N → S) => st q)
      (EmittedLaw.transitionStack P N) := by
    unfold EmittedLaw.transitionStack StackProjection.stackLaw
    exact iIndepFun_pi (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
  have hind := hiid.indepFun_finset T₁ T₂ hdisj (fun q => measurable_pi_apply q)
  let ext : (T₁ → S) → ((S × A) × Fin N → S) := fun r q =>
    if h : q ∈ T₁ then r ⟨q, h⟩ else Classical.arbitrary S
  have hmem : ∀ j : Fin (labelCount l s a),
      (((s, a), ⟨j.val, lt_of_lt_of_le j.isLt (labelCount_le l s a)⟩) : (S × A) × Fin N) ∈ T₂ :=
    fun j => by simp [T₂]
  let G : (T₂ → S) → FiniteDistribution S := fun r =>
    FiniteDistribution.empiricalRow _ hn (fun j => r ⟨_, hmem j⟩)
  have h := hind.comp (φ := fun r => F (ext r)) (ψ := G) (measurable_of_countable _)
    (measurable_of_countable _)
  have e₁ : ((fun r => F (ext r)) ∘ fun st (i : T₁) => st i) = F := by
    funext st
    exact hF _ _ fun q hq => by
      have hq1 : q ∈ T₁ := by simp [T₁, hq]
      simp [ext, hq1]
  have e₂ : (G ∘ fun st (i : T₂) => st i) =
      fun st => FiniteDistribution.empiricalRow _ hn (visitDraw l s a st) := rfl
  rw [e₁, e₂] at h
  exact h

/-- Lemma 6.18 applied to one auxiliary value: the grid inequalities fail with probability less
than `8δ₂`. -/
theorem gridBound_fail_lt [Nonempty S] [Nonempty A] (p : Params S A) (hγ : 1 / 2 ≤ p.γ)
    (P : S → A → FiniteDistribution S) (l : Fin p.N → S × A) (s : S) (a : A)
    (hn : 0 < labelCount l s a) (u : ℝ)
    (hu : ∀ st, u ≤ (p.input (emit l st)).uMax s) (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂8 : δ₂ < 1 / 8) :
    (EmittedLaw.transitionStack P p.N).real {st | ¬ (p.input (emit l st)).GridBound (P s a) s a
      (Real.log (1 / δ₂)) (Input.value ((p.input (emit l st)).auxFix s u))} < 8 * δ₂ := by
  classical
  haveI := transitionStack_isProbability P p.N
  set μ := EmittedLaw.transitionStack P p.N
  let V : ((S × A) × Fin p.N → S) → S → ℝ := fun st =>
    Input.value ((p.input (emit l st)).auxFix s u)
  have hind : IndepFun V (fun st => FiniteDistribution.empiricalRow _ hn (visitDraw l s a st)) μ :=
    indep_offState_draw P l s a hn V fun st st' h => by
      simp only [V]
      rw [auxFix_emit_offState p l st st' h u]
  have hrange : ∀ st t, 0 ≤ V st t ∧ V st t ≤ 1 / (1 - p.γ) := fun st t =>
    (p.input (emit l st)).value_auxFix_mem hγ s (hu st) t
  have h618 := BernsteinInfinite.bernsteinInfinite_fixedRow μ (P s a) p.γ p.γ_lt_one δ₂ hδ₂ hδ₂8
    (labelCount l s a) hn (visitDraw l s a) (measurable_of_countable _) (visitDraw_law P l s a)
    V (measurable_of_countable _) hind hrange
  set good := {st : (S × A) × Fin p.N → S |
      |(FiniteDistribution.empiricalRow _ hn (visitDraw l s a st)).expectation (V st) -
          (P s a).expectation (V st)| ≤
        Real.sqrt (4 * (FiniteDistribution.empiricalRow _ hn (visitDraw l s a st)).variance (V st) *
          Real.log (1 / δ₂) / (labelCount l s a)) +
          5 * Real.log (1 / δ₂) / ((1 - p.γ) * (labelCount l s a)) ∧
      (FiniteDistribution.empiricalRow _ hn (visitDraw l s a st)).variance (V st) ≤
        2 * (P s a).variance (V st) +
          5 * Real.log (1 / δ₂) / (3 * (1 - p.γ) ^ 2 * (labelCount l s a))} with hgood
  have hsub : {st | ¬ (p.input (emit l st)).GridBound (P s a) s a (Real.log (1 / δ₂))
      (Input.value ((p.input (emit l st)).auxFix s u))} ⊆ goodᶜ := by
    intro st hst hg
    apply hst
    have hP : (p.input (emit l st)).Phat s a =
        FiniteDistribution.empiricalRow _ hn (visitDraw l s a st) := dataPhat_emit l st s a hn
    unfold Input.GridBound
    rw [hP]
    exact hg
  have hgm : MeasurableSet good := (Set.to_countable _).measurableSet
  have hc := measureReal_compl (μ := μ) hgm
  rw [probReal_univ] at hc
  calc _ ≤ μ.real goodᶜ := measureReal_mono hsub (measure_ne_top μ _)
    _ < 8 * δ₂ := by linarith

/-- Per label sequence: the union bound over pairs with `N_{s,a} ≥ 27` and grid points
(`:3969–3991`, with the C23 repair) gives failure at most `δ'`. -/
theorem perLabel_bad_le [Nonempty S] [Nonempty A] (p : Params S A) (hγ : 1 / 2 ≤ p.γ)
    (P : S → A → FiniteDistribution S) (δ' : ℝ) (hδ' : 0 < δ') (hδ'1 : δ' < 1)
    (l : Fin p.N → S × A) :
    (EmittedLaw.transitionStack P p.N).real {st | emit l st ∉ goodSet p P δ'} ≤ δ' := by
  classical
  haveI := transitionStack_isProbability P p.N
  set μ := EmittedLaw.transitionStack P p.N
  have hNpos : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hk : 0 < 1 - p.γ := sub_pos.mpr p.γ_lt_one
  let st₀ : (S × A) × Fin p.N → S := fun _ => Classical.arbitrary S
  let M₀ := p.input (emit l st₀)
  let Pairs : Finset (S × A) := Finset.univ.filter fun sa => 27 ≤ labelCount l sa.1 sa.2
  set δ₂ : ℝ := (1 - p.γ) * δ' / (16 * (p.N : ℝ) ^ 2) with hδ₂def
  have hδ₂ : 0 < δ₂ := by positivity
  have hδ₂8 : δ₂ < 1 / 8 := by
    have hN1 : (1 : ℝ) ≤ p.N := by exact_mod_cast p.N_pos
    rw [hδ₂def, div_lt_iff₀ (by positivity)]
    have : (1 - p.γ) * δ' < 1 := by nlinarith [p.γ_nonneg]
    nlinarith
  set L := Real.log (16 * (p.N : ℝ) ^ 2 / ((1 - p.γ) * δ')) with hLdef
  have hL : Real.log (1 / δ₂) = L := by
    rw [hδ₂def, one_div_div]
  let B : S × A → ℝ → Set ((S × A) × Fin p.N → S) := fun sa u =>
    {st | ¬ (p.input (emit l st)).GridBound (P sa.1 sa.2) sa.1 sa.2 (Real.log (1 / δ₂))
      (Input.value ((p.input (emit l st)).auxFix sa.1 u))}
  -- the bad event is covered by the grid failures
  have hcover : {st | emit l st ∉ goodSet p P δ'} ⊆
      ⋃ sa ∈ Pairs, ⋃ u ∈ M₀.uGrid sa.1, B sa u := by
    intro st hst
    by_contra hnot
    apply hst
    intro Qstar hfix s a hpos Vt hclose hbd
    have hcN : (p.input (emit l st)).count s a ≤ (p.input (emit l st)).N := by
      show dataCount (emit l st) s a ≤ p.N
      rw [dataCount_emit]
      exact labelCount_le l s a
    refine (p.input (emit l st)).lem66_of_gridBound_or_small hγ (P s a) hδ' hδ'1 Qstar hfix s a
      hpos hcN ?_ Vt hclose hbd
    intro h27 u hu
    by_contra hb
    apply hnot
    have hsa : (s, a) ∈ Pairs := by
      simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and]
      have : (p.input (emit l st)).count s a = labelCount l s a := dataCount_emit l st s a
      omega
    simp only [Set.mem_iUnion]
    refine ⟨(s, a), hsa, u, ?_, ?_⟩
    · rw [← uGrid_emit p l st st₀ s]
      exact hu
    · show ¬ _
      rw [hL]
      exact hb
  -- each grid failure is small
  have hB : ∀ sa ∈ Pairs, ∀ u ∈ M₀.uGrid sa.1, μ.real (B sa u) ≤ 8 * δ₂ := by
    intro sa hsa u hu
    have h27 : 27 ≤ labelCount l sa.1 sa.2 := (Finset.mem_filter.mp hsa).2
    have hn : 0 < labelCount l sa.1 sa.2 := by omega
    have hu' : ∀ st, u ≤ (p.input (emit l st)).uMax sa.1 := fun st => by
      rw [uMax_emit p l st st₀]
      exact M₀.le_uMax_of_mem_uGrid sa.1 hu
    exact (gridBound_fail_lt p hγ P l sa.1 sa.2 hn u hu' δ₂ hδ₂ hδ₂8).le
  -- counting
  have hPairs : (Pairs.card : ℝ) ≤ p.N := by
    have hsub : Pairs ⊆ Finset.univ.image l := by
      intro sa hsa
      have h27 : 27 ≤ labelCount l sa.1 sa.2 := (Finset.mem_filter.mp hsa).2
      have hpos : 0 < labelCount l sa.1 sa.2 := by omega
      unfold labelCount at hpos
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      have hl : l i = (sa.1, sa.2) := by simpa using hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hl⟩
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hgrid : ∀ sa ∈ Pairs, ((M₀.uGrid sa.1).card : ℝ) ≤ 2 * p.N / (1 - p.γ) := by
    intro sa hsa
    have h27 : 27 ≤ labelCount l sa.1 sa.2 := (Finset.mem_filter.mp hsa).2
    have hN5 : 5 ≤ M₀.N := by
      have := labelCount_le l sa.1 sa.2
      show 5 ≤ p.N
      omega
    exact M₀.uGrid_card_le hγ hN5 sa.1
  calc μ.real {st | emit l st ∉ goodSet p P δ'}
      ≤ μ.real (⋃ sa ∈ Pairs, ⋃ u ∈ M₀.uGrid sa.1, B sa u) :=
        measureReal_mono hcover (measure_ne_top μ _)
    _ ≤ ∑ sa ∈ Pairs, μ.real (⋃ u ∈ M₀.uGrid sa.1, B sa u) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ sa ∈ Pairs, ∑ u ∈ M₀.uGrid sa.1, μ.real (B sa u) :=
        Finset.sum_le_sum fun sa _ => measureReal_biUnion_finset_le _ _
    _ ≤ ∑ sa ∈ Pairs, ∑ _u ∈ M₀.uGrid sa.1, 8 * δ₂ :=
        Finset.sum_le_sum fun sa hsa => Finset.sum_le_sum fun u hu => hB sa hsa u hu
    _ = ∑ sa ∈ Pairs, ((M₀.uGrid sa.1).card : ℝ) * (8 * δ₂) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _sa ∈ Pairs, (2 * p.N / (1 - p.γ)) * (8 * δ₂) :=
        Finset.sum_le_sum fun sa hsa => mul_le_mul_of_nonneg_right (hgrid sa hsa) (by positivity)
    _ = (Pairs.card : ℝ) * ((2 * p.N / (1 - p.γ)) * (8 * δ₂)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ p.N * ((2 * p.N / (1 - p.γ)) * (8 * δ₂)) :=
        mul_le_mul_of_nonneg_right hPairs (by positivity)
    _ = δ' := by
        rw [hδ₂def]
        field_simp
        ring

end Emit

/-- **Lemma 6.6, joint-law form.** Under `N` iid triples with the joint law of
`eq:sampling-offline-inf-iid`, the conclusions of Lemma 6.6 hold for every fixed point, every pair
with `N_{s,a} > 0` and every admissible `Ṽ`, with probability at least `1 - δ'`. -/
theorem bernsteinInfinite_jointLaw [Nonempty S] [Nonempty A] (p : Params S A) (hγ : 1 / 2 ≤ p.γ)
    (ρ : FiniteDistribution (S × A)) (P : S → A → FiniteDistribution S) (δ' : ℝ) (hδ' : 0 < δ')
    (hδ'1 : δ' < 1) :
    letI : MeasurableSpace S := ⊤
    letI : MeasurableSpace (S × A) := ⊤
    letI : MeasurableSpace ((S × A) × S) := ⊤
    1 - δ' ≤ ((JointRow.jointRow ρ P).sampleMeasure p.N).real (goodSet p P δ') := by
  classical
  letI : MeasurableSpace S := ⊤
  letI : MeasurableSpace (S × A) := ⊤
  letI : MeasurableSpace ((S × A) × S) := ⊤
  haveI := transitionStack_isProbability P p.N
  haveI : IsProbabilityMeasure ρ.rowMeasure := rowMeasure_isProbability ρ
  haveI : IsProbabilityMeasure (ρ.sampleMeasure p.N) := by
    unfold FiniteDistribution.sampleMeasure; infer_instance
  haveI : IsProbabilityMeasure (JointRow.jointRow ρ P).rowMeasure :=
    rowMeasure_isProbability _
  haveI : IsProbabilityMeasure ((JointRow.jointRow ρ P).sampleMeasure p.N) := by
    unfold FiniteDistribution.sampleMeasure; infer_instance
  set μ₀ := (ρ.sampleMeasure p.N).prod (EmittedLaw.transitionStack P p.N)
  have hG : MeasurableSet (goodSet p P δ') := (Set.to_countable _).measurableSet
  have hbadm : MeasurableSet (EmittedLaw.emitObservation ⁻¹' (goodSet p P δ')ᶜ :
      Set ((Fin p.N → S × A) × ((S × A) × Fin p.N → S))) := (Set.to_countable _).measurableSet
  have hbad : μ₀ (EmittedLaw.emitObservation ⁻¹' (goodSet p P δ')ᶜ) ≤ ENNReal.ofReal δ' := by
    rw [Measure.prod_apply hbadm]
    calc ∫⁻ l, EmittedLaw.transitionStack P p.N
          (Prod.mk l ⁻¹' (EmittedLaw.emitObservation ⁻¹' (goodSet p P δ')ᶜ)) ∂ρ.sampleMeasure p.N
        ≤ ∫⁻ _l, ENNReal.ofReal δ' ∂ρ.sampleMeasure p.N := by
          apply lintegral_mono
          intro l
          dsimp only
          have h := perLabel_bad_le p hγ P δ' hδ' hδ'1 l
          rw [← ofReal_measureReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal δ' := by simp
  have hlaw := EmittedLaw.emitObservation_law ρ P p.N
  have hmap : ((JointRow.jointRow ρ P).sampleMeasure p.N) (goodSet p P δ')ᶜ ≤ ENNReal.ofReal δ' := by
    rw [← hlaw, Measure.map_apply (measurable_of_countable _) hG.compl]
    exact hbad
  have hreal : ((JointRow.jointRow ρ P).sampleMeasure p.N).real (goodSet p P δ')ᶜ ≤ δ' :=
    ENNReal.toReal_le_of_le_ofReal hδ'.le hmap
  have hc := measureReal_compl (μ := (JointRow.jointRow ρ P).sampleMeasure p.N) hG
  rw [probReal_univ] at hc
  linarith

/-- The iid triple law of `eq:sampling-offline-inf-iid`, written as in the Lemma 6.5 entry, is the
joint-row sample law. -/
theorem iidTriples_map_eq_jointRow (ρ : FiniteDistribution (S × A))
    (P : S → A → FiniteDistribution S) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N : ℕ) :
    letI : MeasurableSpace S := ⊤
    letI : MeasurableSpace (S × A) := ⊤
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin N → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ t : (S × A) × S,
        ENNReal.ofReal (ρ.prob t.1 * (P t.1.1 t.1.2).prob t.2) • Measure.dirac t) →
      μ.map X = (JointRow.jointRow ρ P).sampleMeasure N := by
  letI : MeasurableSpace S := ⊤
  letI : MeasurableSpace (S × A) := ⊤
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  classical
  have hrow : (∑ t : (S × A) × S,
      ENNReal.ofReal (ρ.prob t.1 * (P t.1.1 t.1.2).prob t.2) • Measure.dirac t) =
      (JointRow.jointRow ρ P).rowMeasure := by
    refine Measure.ext_iff_singleton.2 fun x => ?_
    rw [Measure.finset_sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator_apply,
      Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ x)]
    unfold FiniteDistribution.rowMeasure
    rw [@PMF.toMeasure_apply_singleton _ ⊤ _ x MeasurableSpace.measurableSet_top]
    unfold FiniteDistribution.toPMF
    rw [PMF.ofFintype_apply]
    rfl
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).comp hX |>.aemeasurable)).1 hind
  simp only [Function.comp_def] at h
  calc μ.map X = μ.map (fun ω i => X ω i) := rfl
    _ = Measure.pi (fun i => μ.map (fun ω => X ω i)) := h
    _ = (JointRow.jointRow ρ P).sampleMeasure N := by
      unfold FiniteDistribution.sampleMeasure
      congr 1
      funext i
      rw [hmarg i, hrow]

/-- **Lemma 6.6, iid-dataset form** (`lem:Bernstein-infinite`, `offlineRL.tex:1147–1163`), with a
failure level `δ'` separate from the penalty parameter `p.δ`. -/
theorem bernsteinInfinite_iid [Nonempty S] [Nonempty A] (p : Params S A) (hγ : 1 / 2 ≤ p.γ)
    (ρ : FiniteDistribution (S × A)) (P : S → A → FiniteDistribution S)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (δ' : ℝ) (hδ' : 0 < δ') (hδ'1 : δ' < 1) :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin p.N → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ t : (S × A) × S,
        ENNReal.ofReal (ρ.prob t.1 * (P t.1.1 t.1.2).prob t.2) • Measure.dirac t) →
      1 - δ' ≤ μ.real {ω | X ω ∈ goodSet p P δ'} := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  have hlaw := iidTriples_map_eq_jointRow ρ P μ p.N X hX hind hmarg
  have hjoint := bernsteinInfinite_jointLaw p hγ ρ P δ' hδ' hδ'1
  have hG : MeasurableSet (goodSet p P δ') := (Set.to_countable _).measurableSet
  have heq : μ.real {ω | X ω ∈ goodSet p P δ'} =
      ((JointRow.jointRow ρ P).sampleMeasure p.N).real (goodSet p P δ') := by
    rw [← hlaw, measureReal_def, measureReal_def, Measure.map_apply hX hG]
    rfl
  rw [heq]
  exact hjoint

end LeaveOneOut

end StatisticalRL.OfflineVILCB
