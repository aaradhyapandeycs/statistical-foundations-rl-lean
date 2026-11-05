import Formalization.Online.Regret.MVP.Main.MVPActualLargeEvent
import Formalization.Online.Regret.MVP.MVPT5Definitions
import Formalization.Online.Regret.MVP.T6.MVPActualT6LargeConfidence

/-! Same-path source-event consumer with explicit W3/W4 and event probability inputs. The argument δp is the corrected planner allocation. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualRegret_large_of_source_events
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δp : ℝ) (hδ : 0<δp) (hδsmall : δp≤1/100)
    (hopt : mvpHistoryAllStageOptimism (K := K) hH E fallback δp 4 16
      (mvpVarianceHistory H K hH E initial fallback path δp 4 16))
    (h234 : (initial,path) ∈ mvpActualT234Event H K hH E fallback δp
      (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp))
    (hd : 1≤(Fintype.card State : ℝ)*Fintype.card Action*H)
    (hI : 1≤onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)
    (hK : (Fintype.card State : ℝ)*Fintype.card Action*H*
      onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp≤K)
    (h4 : mvpVarianceW4 H K hH E initial fallback path δp 4 16 ≤
      Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*
        mvpVarianceT6UCB H K hH E initial fallback path δp 4 16*
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)+
        (Fintype.card State : ℝ)*Fintype.card Action*H*H*
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)
    (h3 : mvpActualW3 H K hH E initial fallback path δp 4 16 ≤
      Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*(H : ℝ)^2*
        mvpVarianceT6UCB H K hH E initial fallback path δp 4 16*
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)+
        (Fintype.card State : ℝ)*Fintype.card Action*H*(H : ℝ)^2*
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)
    (h5 : mvpActualT5 H K hH E initial fallback path δp 4 16 ≤
      mvpActualW3 H K hH E initial fallback path δp 4 16+
      2*H*mvpVarianceT2 H K hH E initial fallback path δp 4 16+
      Real.sqrt ((H : ℝ)^2*mvpVarianceT6UCB H K hH E initial fallback path δp 4 16*
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)+
      K*(H : ℝ)^2*onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)
    (h6 : (initial,path) ∈ mvpT6SourceEvent H K hH E fallback δp 4 16) :
    (∑ k : Fin K, mvpActualEpisodeRegret H K hH E initial fallback path k δp 4 16) ≤
      100*Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*K*(H : ℝ)^2)*
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp := by
  apply mvpActualRegret_large_of_T234_event H K hH E initial fallback path δp
    (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)
    (mvpActualW3 H K hH E initial fallback path δp 4 16)
    hδ hδsmall hopt h234 hd hI hK h4 h3 h5
  exact h6
end StatisticalRL.OnlineRL
