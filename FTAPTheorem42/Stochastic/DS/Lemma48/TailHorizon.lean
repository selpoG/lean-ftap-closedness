import FTAPTheorem42.Foundations.Passage
import FTAPTheorem42.Foundations.ConvexProcesses
import FTAPTheorem42.Stochastic.Stopping.CadlagPassageLocalizer
import FTAPTheorem42.Stochastic.DS.Lemma48.NormalizedTail
import FTAPTheorem42.Foundations.MaximalProbability
import FTAPTheorem42.Stochastic.DS.Lemma410.StrategyConvexification
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.DirectStopping

/-! # Deterministic horizons of the martingale passage tail

Only deterministic stopping is commuted with taking the passage tail of one
process. No strategy-dependent stopping is commuted with convexification.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The direct numerical tail has exactly the weighted passage-tail
martingale, independently of the bookkeeping source. -/
theorem direct_tail_martingale_eq
    {P : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
    [F.IsRightContinuous] {D : SpecialSemimartingaleDecomposition P F μ}
    (H : Nat → SIntegrableStrategy D) (weight : Nat → Real) (n : Nat) (c : Real) :
    ((SIntegrableStrategy.processStoppingCalculus D).lemma48TailConvexStrategy
      H weight n c).martingalePart =
      fun t ω => ∑ i ∈ Finset.range n,
        weight i * absolutePassageTail (H i).martingalePart c t ω := by
  funext t ω
  rw [SIntegrableProcessStoppingCalculus.lemma48TailConvexStrategy,
    SIntegrableStrategy.weightedPrefixSum_martingalePart_apply]
  rfl

end FTAPTheorem42
