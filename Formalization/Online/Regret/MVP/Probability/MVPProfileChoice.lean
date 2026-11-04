import Formalization.Online.Regret.MVP.Probability.MVPFiniteChoice
import Formalization.Online.Regret.MVP.Probability.MVPUniformPositiveParts

/-! Fixed finite choices enumerate arbitrary future-dependent vector families. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
variable {State Action Profile Level : Type*} [Fintype State] [Fintype Action]
  [Fintype Profile] [Fintype Level]
local instance : MeasurableSpace State := ⊤
noncomputable local instance mvpChoiceStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpChoiceActionDecidable : DecidableEq Action := Classical.decEq Action

def mvpProfileChoiceIndex (H K : ℕ) := Profile × (Fin H → State → Action → Fin (K+1)) × Level

noncomputable def mvpProfileSelectedTest {H : ℕ} (K : ℕ)
    (family : Profile → (h : Fin H) → FutureCode (State := State) (Action := Action) h K → Finset (State → ℝ))
    (idx : mvpProfileChoiceIndex (Profile := Profile) (Level := Level) (State := State) (Action := Action) H K)
    (h : Fin H) (s : State) (a : Action) (code : FutureCode (State := State) (Action := Action) h K) : State → ℝ :=
  mvpFiniteChoice (family idx.1 h code) 0 (K+1) (idx.2.1 h s a)

theorem mvpProfileSelectedTest_mem {H : ℕ} (K : ℕ)
    (family : Profile → (h : Fin H) → FutureCode (State := State) (Action := Action) h K → Finset (State → ℝ))
    (hzero : ∀ p h code, (0 : State → ℝ) ∈ family p h code)
    (idx : mvpProfileChoiceIndex (Profile := Profile) (Level := Level) (State := State) (Action := Action) H K)
    (h : Fin H) (s : State) (a : Action) (code : FutureCode (State := State) (Action := Action) h K) :
    mvpProfileSelectedTest K family idx h s a code ∈ family idx.1 h code :=
  mvpFiniteChoice_mem _ _ (hzero idx.1 h code) _ _

theorem mvpProfileSelectedTest_covers {H : ℕ} (K : ℕ)
    (family : Profile → (h : Fin H) → FutureCode (State := State) (Action := Action) h K → Finset (State → ℝ))
    (hcard : ∀ p h code, (family p h code).card ≤ K+1)
    (p : Profile) (h : Fin H) (code : FutureCode (State := State) (Action := Action) h K)
    (V : State → ℝ) (hV : V ∈ family p h code) :
    ∃ j : Fin (K+1), mvpFiniteChoice (family p h code) 0 (K+1) j = V :=
  mvpFiniteChoice_surjective_on_family _ _ _ (hcard p h code) V hV
end StatisticalRL.FiniteHorizonGenerative
