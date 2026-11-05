import Formalization.Online.Regret.MVP.Main.MVPActualLargeBranch
import Formalization.Online.Regret.MVP.T34.MVPJointSource

/-! Actual-path consumer of the T2/T3/T4 event, with other source events as explicit intermediate premises. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualRegret_large_of_T234_event
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ I W3 : ℝ) (hδ : 0<δ) (hδsmall : δ≤1/100)
    (hopt : mvpHistoryAllStageOptimism (K := K) hH E fallback δ 4 16
      (mvpVarianceHistory H K hH E initial fallback path δ 4 16))
    (h234 : (initial,path) ∈ mvpActualT234Event H K hH E fallback δ I)
    (hd : 1≤(Fintype.card State : ℝ)*Fintype.card Action*H)
    (hI : 1≤I) (hK : (Fintype.card State : ℝ)*Fintype.card Action*H*I≤K)
    (h4 : mvpVarianceW4 H K hH E initial fallback path δ 4 16 ≤
      Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*
        mvpVarianceT6UCB H K hH E initial fallback path δ 4 16*I)+
        (Fintype.card State : ℝ)*Fintype.card Action*H*H*I)
    (h3 : W3 ≤ Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*(H : ℝ)^2*
        mvpVarianceT6UCB H K hH E initial fallback path δ 4 16*I)+
        (Fintype.card State : ℝ)*Fintype.card Action*H*(H : ℝ)^2*I)
    (h5 : mvpActualT5 H K hH E initial fallback path δ 4 16 ≤ W3+
      2*H*mvpVarianceT2 H K hH E initial fallback path δ 4 16+
      Real.sqrt ((H : ℝ)^2*mvpVarianceT6UCB H K hH E initial fallback path δ 4 16*I)+K*(H : ℝ)^2*I)
    (h6 : mvpVarianceT6UCB H K hH E initial fallback path δ 4 16 ≤
      4*H*mvpVarianceT2 H K hH E initial fallback path δ 4 16+
      4*H*mvpVarianceW4 H K hH E initial fallback path δ 4 16+K*(H : ℝ)^2*I) :
    (∑ k : Fin K, mvpActualEpisodeRegret H K hH E initial fallback path k δ 4 16) ≤
      100*Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*K*(H : ℝ)^2)*I := by
  have h5n : 0≤mvpActualT5 H K hH E initial fallback path δ 4 16 := by
    unfold mvpActualT5
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have h6n := mvpVarianceT6UCB_nonneg H K hH E initial fallback path δ 4 16
  have h2 := h234.1
  have ht3 := (le_abs_self _).trans h234.2.1
  have ht4 := (le_abs_self _).trans h234.2.2
  have h2' : mvpVarianceT2 H K hH E initial fallback path δ 4 16 ≤
      (1/2 : ℝ)*Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*
        mvpActualT5 H K hH E initial fallback path δ 4 16*I)+
      (1/2 : ℝ)*((Fintype.card State : ℝ)*Fintype.card Action*H)*H*I := by
    dsimp only [mvpActualT234Event, Set.mem_setOf_eq] at h2
    convert h2 using 1 <;> ring
  apply mvpActualRegret_large_of_components H K hH E initial fallback path δ 4 16
    ((Fintype.card State : ℝ)*Fintype.card Action*H) I
    (mvpActualT5 H K hH E initial fallback path δ 4 16)
    (mvpVarianceT6UCB H K hH E initial fallback path δ 4 16) W3 hδ hδsmall (by norm_num) (by norm_num)
    hopt hd hI hK h5n h6n h2' h4 h3 h5 h6 ht3 ht4
end StatisticalRL.OnlineRL
