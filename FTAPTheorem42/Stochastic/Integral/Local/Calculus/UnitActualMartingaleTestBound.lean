import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.UnitCompletedLocalHorizon
import FTAPTheorem42.Stochastic.Integral.Local.Construction.BoundedCoordinateSemantics

/-! # Uniform martingale test bounds for unit intrinsic actual integrands -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.LocalCompletedM2A

open SIntegrableFiniteVariationBridge BoundedMartingaleQuadraticEnergy.Data

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  [F.IsRightContinuous] {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {G : LocallySIntegrableStrategy D}

/-- Any intrinsic actual integrand bounded by one inherits the source
martingale's uniform test bound on the same finite horizon. Its own graph
schedule supplies all L² coordinates and is removed before taking the bound. -/
theorem actual_unitIntegrand_martingale_testError_bound
    (T : NNReal) (b : Real)
    (hBound : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError G.martingalePart 0 J T ω ∂μ) ≤ b)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (hH : ∀ t ω, |H.val.integrand t ω| ≤ 1) :
    ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError H.val.martingalePart 0 J T ω ∂μ) ≤ b := by
  let w := actualGraphWitness H
  let schedule := w.schedule
  let Z := H.val.centeredMartingalePart
  have hZP : IsStronglyProgressive F Z := by
    apply StronglyAdapted.isStronglyProgressive_of_rightContinuous
    · intro t
      exact (H.val.martingalePart_isStronglyAdapted t).sub
        ((H.val.martingalePart_isStronglyAdapted 0).mono (F.mono zero_le))
    · exact fun ω t => (H.val.martingalePart_isRightContinuous ω t).sub continuousWithinAt_const
  have hZeroP : IsStronglyProgressive F (0 : Process Ω) := fun _ => stronglyMeasurable_zero
  have hGP : IsStronglyProgressive F G.martingalePart :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      G.martingalePart_isStronglyAdapted G.martingalePart_isRightContinuous
  have hLocal n : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError (stoppedProcess Z (schedule.localizer n))
        (stoppedProcess 0 (schedule.localizer n)) J T ω ∂μ) ≤ b := by
    obtain ⟨hEnergy, hSem⟩ := w.toScheduleGraphRepresentation.coordinate_martingaleSemantics n
    let Q := schedule.quadraticKernel n
    let E := schedule.variationBridge n
    let K : FiniteHorizonM2ACoefficient E Q := {
      coefficient := Function.uncurry H.val.integrand
      coefficient_isStronglyMeasurable := H.val.integrand_isPredictable
      coefficient_memLp_variation := MemLp.of_bound
        H.val.integrand_isPredictable.aestronglyMeasurable 1
        (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hH p.1 p.2)
      coefficient_memLp_energy := hEnergy }
    have hK : ∀ t ω, |K.integrand t ω| ≤ 1 := by
      intro t ω
      change |(finiteHorizonPredictableStrip (schedule.horizon n)).indicator
        (Function.uncurry H.val.integrand) (t, ω)| ≤ 1
      by_cases hp : (t, ω) ∈ finiteHorizonPredictableStrip (Omega := Ω) (schedule.horizon n)
      · simpa only [Set.indicator_of_mem hp, Function.uncurry_apply_pair] using hH t ω
      · simp [hp]
    have hAE : Function.uncurry K.integrand =ᵐ[Q.predictableEnergyMeasure]
        Function.uncurry H.val.integrand :=
      finiteHorizonCoefficient_ae_eq Q _
    have hCompleted := finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
      schedule.usualConditions Q (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous (schedule.terminal_memLp n)
      (Function.uncurry K.integrand) K.integrand_isStronglyPredictable K.integrand_memLp_energy
      (Function.uncurry H.val.integrand) H.val.integrand_isPredictable hEnergy hAE
    have hPrefix := schedule.sourcePrefix_martingalePart n
    change ProcessIndistinguishable μ (schedule.sourcePrefix n).martingalePart
      (stoppedProcess (stoppedProcess G.martingalePart
        (fun _ : Ω => (schedule.horizon n : WithTop NNReal))) (schedule.localizer n)) at hPrefix
    rw [stoppedProcess_stoppedProcess_of_le_right (schedule.localizer_le_horizon n)] at hPrefix
    have hPrefixBound : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
        (∫ ω, elementaryEmeryTestError
          (schedule.sourcePrefix n).martingalePart 0 J T ω ∂μ) ≤ b := by
      intro J
      rw [integral_congr_ae (elementaryEmeryTestError_congr hPrefix
        (ProcessIndistinguishable.refl μ 0) J T)]
      have hStop := integral_elementaryEmeryTestError_finiteStopped_le (μ := μ)
        G.martingalePart 0 hGP hZeroP G.martingalePart_isRightContinuous
        (fun _ _ => continuousWithinAt_const) (scheduleFiniteLocalizer schedule n)
        (scheduleFiniteLocalizer_isStoppingTime schedule n) J T
      simp only [coe_scheduleFiniteLocalizer] at hStop
      change (∫ ω, elementaryEmeryTestError
        (stoppedProcess G.martingalePart (schedule.localizer n)) 0 J T ω ∂μ) ≤ _ at hStop
      exact hStop.trans (hBound J)
    have hTests := finiteHorizonCompletedMartingalePart_testError_bound_on_horizon
      schedule.usualConditions Q (schedule.martingale n) (schedule.terminal_memLp n)
      K hK T b hPrefixBound
    intro J
    rw [integral_congr_ae (elementaryEmeryTestError_congr (hSem.trans hCompleted.symm)
      (show ProcessIndistinguishable μ (stoppedProcess 0 (schedule.localizer n)) 0 from
        Eventually.of_forall fun _ _ => rfl) J T)]
    exact hTests J
  have hGlobal := integral_elementaryEmeryTestError_bound_of_localizingSequence
    Z 0 hZP hZeroP schedule.isLocalizingSequence.toIsPreLocalizingSequence T b hLocal
  intro J
  have hCenter : elementaryEmeryTestError Z 0 J T =
      elementaryEmeryTestError H.val.martingalePart 0 J T := by
    unfold elementaryEmeryTestError
    rw [show ElementaryStrategy.gain Z J.strategy.toElementary =
      ElementaryStrategy.gain H.val.martingalePart J.strategy.toElementary from
        ElementaryStrategy.gain_sub_initial _ _]
  rw [← hCenter]
  exact hGlobal J

/-- For a zero-based actual martingale, the unit test recovers its capped
maximum. This will control the downside of Hahn restrictions. -/
theorem actual_unitIntegrand_martingale_envelope_bound
    (T : NNReal) (b : Real)
    (hBound : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError G.martingalePart 0 J T ω ∂μ) ≤ b)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (hH : ∀ t ω, |H.val.integrand t ω| ≤ 1)
    (hZero : H.val.martingalePart 0 =ᵐ[μ] 0) :
    (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      H.val.martingalePart T ω ∂μ) ≤ b := by
  have hEq := elementaryEmeryTestError_horizonUnit (F := F)
    (Y := 0) hZero T
  simp only [Pi.zero_apply, sub_zero] at hEq
  rw [← integral_congr_ae hEq]
  exact actual_unitIntegrand_martingale_testError_bound T b hBound H hH _

end FTAPTheorem42.LocalCompletedM2A
