import FTAPTheorem42.Interface.GainData
import FTAPTheorem42.Stochastic.Market.Source.RealizedSpecialSource

/-! # Realizing the process-level original gain interface -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]
  (source : BoundedSemimartingaleSource S F μ)

omit [SigmaFiniteFiltration μ F] in
/-- A regular graph gain is represented exactly under an equivalent
probability, retaining the specified process rather than selecting another version. -/
theorem OriginalGain.exists_realized
    (Y : OriginalGain source) (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) :
    ∃ R : RealizedStrategy (ℱ := F) Q S, R.gain = Y.gain := by
  let sourceQ := source.ofMutuallyAbsolutelyContinuous hμQ hQμ
  obtain ⟨A⟩ := truncated_integralGraph_of_equivalentMeasure source sourceQ hμQ hQμ Y.integralGraph
  have hApprox := truncatedGraphWitness_elementaryApproximable sourceQ A
  have hApproxY : ElementaryEmeryApproximable (F := F) (μ := Q) S Y.gain := by
    intro T ε hε
    obtain ⟨J, C, hC, hJ⟩ := hApprox T ε hε
    refine ⟨J, C, hC, fun L => ?_⟩
    rw [← integral_congr_ae (elementaryEmeryTestError_congr
      (.refl Q _) A.gain_indistinguishable L T)]
    exact hJ L
  exact hApproxY.exists_realizedStrategy
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      source.stronglyAdapted source.rightContinuous)
    source.rightContinuous Y.adapted Y.rightContinuous Y.leftLimits (hQμ.ae_le Y.zero)

/-- Elementary completion gains have the process-level original graph data. -/
noncomputable def OriginalGain.ofRealized
    (R : RealizedStrategy (ℱ := F) Q S) (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) : OriginalGain source := by
  let Rμ := R.transferMeasure hQμ hμQ S
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      source.stronglyAdapted source.rightContinuous)
  let K := Classical.choose (exists_realized_truncatedGraph source Rμ)
  exact {
    integrand := K
    gain := R.gain
    integralGraph := Classical.choose_spec (exists_realized_truncatedGraph source Rμ)
    adapted := R.gain_stronglyAdapted
    rightContinuous := R.gain_rightContinuous
    leftLimits := R.gain_hasLeftLimits
    zero := hμQ.ae_le (R.gain_initial_eq_zero S source.rightContinuous) }

end FTAPTheorem42.BoundedSourceIntegralMarket
