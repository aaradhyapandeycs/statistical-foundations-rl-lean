import Formalization.Online.Regret.MVP.Main.MVPActualSourceEvents
import Formalization.Online.Regret.MVP.Main.MVPIotaEligibility
import Formalization.Online.Regret.MVP.MVPDecouplingDefinitions

/-! Conditional actual-path consumer of the shared decoupling event. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualRegret_large_of_decoupling
    (H K : ℕ) (hH : 0<H) (hK2 : 2≤K) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hlarge : (Fintype.card State : ℝ)*Fintype.card Action*H*
      onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K
        (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K) ≤ K)
    (hopt : mvpHistoryAllStageOptimism (K := K) hH E fallback
      (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K) 4 16
      (mvpVarianceHistory H K hH E initial fallback path
        (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K) 4 16))
    (h234 : (initial,path) ∈ mvpActualT234Event H K hH E fallback
      (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K)
      (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K
        (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K)))
    (hdec : (initial,path) ∈ mvpActualDecouplingEvent H K hH E fallback
      (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K) 4 16
      (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K
        (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K)))
    (h5 : let p := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
      let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K p
      mvpActualT5 H K hH E initial fallback path p 4 16 ≤
        mvpActualW3 H K hH E initial fallback path p 4 16+
        2*H*mvpVarianceT2 H K hH E initial fallback path p 4 16+
        Real.sqrt ((H : ℝ)^2*mvpVarianceT6UCB H K hH E initial fallback path p 4 16*I)+K*(H : ℝ)^2*I)
    (h6 : (initial,path) ∈ mvpT6SourceEvent H K hH E fallback
      (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K) 4 16) :
    let p := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K p
    (∑ k : Fin K, mvpActualEpisodeRegret H K hH E initial fallback path k p 4 16) ≤
      100*Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*K*(H : ℝ)^2)*I := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  have hs : 0<Fintype.card State := Fintype.card_pos
  have ha : 0<Fintype.card Action := Fintype.card_pos
  have hd := mvp_correctedAllocation_domain_and_log δ (Fintype.card State) (Fintype.card Action) H K
    hδ hδ1 hs ha hH (by omega)
  have hlog := mvp_main_iota_ge_log2 (Fintype.card State) (Fintype.card Action) H K δ hs ha hH hK2 hδ hδ1
  have hlog1 : 1≤Real.log K / Real.log 2 := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num))).2
    simpa only [one_mul] using Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤K by exact_mod_cast hK2)
  have hi : 1≤onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K
      (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K) := le_trans hlog1 hlog
  have hs1 : (1:ℝ)≤Fintype.card State := by exact_mod_cast hs
  have ha1 : (1:ℝ)≤Fintype.card Action := by exact_mod_cast ha
  have hh1 : (1:ℝ)≤H := by exact_mod_cast hH
  have hd1 : (1:ℝ)≤(Fintype.card State:ℝ)*Fintype.card Action*H :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hs1 ha1) hh1
  dsimp only [mvpActualDecouplingEvent, Set.mem_setOf_eq] at hdec
  have h4 := hdec.2.1
  have h3 := hdec.2.2
  apply mvpActualRegret_large_of_source_events H K hH E initial fallback path _ hd.1 hd.2.1
    hopt h234 hd1 hi hlarge ?_ ?_ h5 h6
  · convert h4 using 1 <;> ring
  · convert h3 using 1 <;> ring
end StatisticalRL.OnlineRL
