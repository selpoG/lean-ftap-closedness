import FTAPTheorem42.Stochastic.Integral.General.BoundedPredictableIntegralGraph
import FTAPTheorem42.Stochastic.Integral.Local.Construction.IntegralGraph
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.ControlConvergence
import FTAPTheorem42.Stochastic.Integral.General.IntegralGraphTruncationConvergence
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessApproximation

/-! # Elementary density on a supplied completed source schedule -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ}
  {G : LocallySIntegrableStrategy D}

/-- The completed controls give elementary approximants against the
schedule's actual source gain. The localization error is uniform in tests. -/
theorem CommonScheduleIntegralGraphData.elementaryApproximable
    {H X : Process Ω} (data : CommonScheduleIntegralGraphData G H X)
    (hX : IsStronglyProgressive F X) (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b) :
    ElementaryEmeryApproximable (F := F) (μ := μ) G.stochasticIntegral X := by
  apply elementaryEmeryApproximable_of_stopped
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      G.stochasticIntegral_isStronglyAdapted G.stochasticIntegral_isRightContinuous)
    G.stochasticIntegral_isRightContinuous hX
    data.schedule.isLocalizingSequence.toIsPreLocalizingSequence
  intro k
  have hBoundK p : |(data.coefficient k).coefficient p| ≤ b := by
    rw [data.coefficient_eq k]
    exact hBound p.1 p.2
  obtain ⟨J, C, hC, hConv, _hConv'⟩ := exists_commonElementarySequence_emery
    data.schedule.usualConditions data.schedule.usualConditions
    (data.schedule.quadraticKernel k) (data.schedule.quadraticKernel k)
    (data.schedule.martingale k) (data.schedule.terminal_memLp k)
    (data.schedule.martingale k) (data.schedule.terminal_memLp k)
    (data.coefficient k) (data.coefficient k) rfl b hBoundK
  have hSeq := hConv.congr_sequence (fun n => data.schedule.elementaryGain_sourcePrefix k (J n))
  exact ⟨J, C, hC, hSeq.congr_limit (data.stoppedGain_eq k).symm⟩

/-- An arbitrary source schedule supplies the bounded rows of any existing
bounded-coefficient graph. Gain uniqueness identifies their stored gain. -/
theorem IsIntegralGraph.elementaryApproximable_of_bounded
    (schedule : LocalCompletedM2ASchedule G)
    {H X : Process Ω} (h : IsIntegralGraph G H X)
    (hX : IsStronglyProgressive F X) (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b) :
    ElementaryEmeryApproximable (F := F) (μ := μ) G.stochasticIntegral X := by
  have hH : IsStronglyPredictable F H :=
    h.representative_integrand ▸ h.representative.val.integrand_isPredictable
  obtain ⟨R, hR, hGain⟩ := exists_boundedPredictable_actualLocal schedule H hH b hBound
  have hRX : ProcessIndistinguishable μ R.val.stochasticIntegral X :=
    IsIntegralGraph.gain_indistinguishable ⟨⟨R, hR, .refl μ _⟩⟩ h
  let data : CommonScheduleIntegralGraphData G H X := {
    schedule := schedule
    coefficient := boundedPredictableCoefficient schedule H hH b hBound
    coefficient_eq := fun _ => rfl
    stoppedGain_eq := fun n =>
      (hRX.symm.stoppedProcess (schedule.localizer n)).trans (hGain n) }
  exact data.elementaryApproximable hX b hBound

/-- Bounded-cut convergence and one source schedule give elementary density
for every truncation graph, including unbounded coefficients. -/
theorem TruncatedIntegralGraphWitness.elementaryApproximable
    (schedule : LocalCompletedM2ASchedule G)
    {H X : Process Ω} (A : TruncatedIntegralGraphWitness G H X) :
    ElementaryEmeryApproximable (F := F) (μ := μ) G.stochasticIntegral A.regularGain := by
  have hProg n := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    (A.approximant n).val.stochasticIntegral_isStronglyAdapted
    (A.approximant n).val.stochasticIntegral_isRightContinuous
  apply ElementaryEmeryApproximable.of_converges
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      G.stochasticIntegral_isStronglyAdapted G.stochasticIntegral_isRightContinuous)
    G.stochasticIntegral_isRightContinuous hProg
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      A.regularGain_adapted A.regularGain_right) _ A.convergence
  intro n
  exact IsIntegralGraph.elementaryApproximable_of_bounded schedule
    ⟨⟨A.approximant n, A.approximant_integrand n, .refl μ _⟩⟩ (hProg n)
    ((n : Real) + 1) (integralCoefficientTruncation_abs_le H n)

end FTAPTheorem42.LocalCompletedM2A
