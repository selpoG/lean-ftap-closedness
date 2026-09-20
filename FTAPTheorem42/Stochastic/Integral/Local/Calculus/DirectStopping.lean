import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualStopping
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy

/-! # Direct finite stopping of intrinsic graphs

The coordinate constructor stops the actual gain and both components literally.
Its graph is supplied by completed stopping locality on the same schedule.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.SIntegrableStrategy

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ}

/-- Literal stopping of a globally BV coordinate record. This asserts only
coordinate regularity; the intrinsic graph theorem below supplies actuality. -/
noncomputable def closedStopTop (H : SIntegrableStrategy D)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ) : SIntegrableStrategy D where
  integrand := PredictableProcess.restrict (stochasticIntervalIocZeroTop τ) H.integrand
  stochasticIntegral := stoppedProcess H.stochasticIntegral τ
  martingalePart := stoppedProcess H.martingalePart τ
  finiteVariationPart := stoppedProcess H.finiteVariationPart τ
  finiteVariationMeasure := 0
  integrand_isPredictable := PredictableProcess.isStronglyPredictable_restrict
    (IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hτ) H.integrand_isPredictable
  stochasticIntegral_isStronglyAdapted :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      H.stochasticIntegral_isStronglyAdapted hτ H.stochasticIntegral_isRightContinuous
  stochasticIntegral_isRightContinuous :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
      H.stochasticIntegral_isRightContinuous
  martingalePart_isLocalMartingale :=
    H.martingalePart_isLocalMartingale.stoppedProcess_of_rightContinuous
      H.martingalePart_isRightContinuous hτ
  martingalePart_isStronglyAdapted :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      H.martingalePart_isStronglyAdapted hτ H.martingalePart_isRightContinuous
  martingalePart_isRightContinuous :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
      H.martingalePart_isRightContinuous
  finiteVariationPart_isPredictable :=
    IsStronglyPredictable.stoppedProcess_of_stoppingTime_withTop
      H.finiteVariationPart_isPredictable τ hτ
  finiteVariationPart_isRightContinuous :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
      H.finiteVariationPart_isRightContinuous
  finiteVariationPart_isBoundedVariation := by
    intro ω
    by_cases hTop : τ ω = ⊤
    · simpa only [stoppedProcess, hTop, min_eq_left le_top,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] using
        H.finiteVariationPart_isBoundedVariation ω
    · lift τ ω to NNReal using hTop with u hu
      simp only [stoppedProcess, ← hu, ← WithTop.coe_min,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      exact FiniteVariationStoppedPath.boundedVariationOn_stopAt
          (H.finiteVariationPart_isBoundedVariation ω) u
  integral_decomposition := H.integral_decomposition.stoppedProcess τ
  source_decomposition := H.source_decomposition

/-- Direct process stopping supplies the narrow stopping interface. -/
noncomputable def processStoppingCalculus (D : SpecialSemimartingaleDecomposition S F μ) :
    SIntegrableProcessStoppingCalculus D where
  stopAtTop := fun τ hτ H => H.closedStopTop τ hτ
  stopAtTop_integrand := fun _ _ _ => rfl
  stochasticIntegral_stopAtTop := fun _ _ _ => ProcessIndistinguishable.refl μ _
  martingalePart_stopAtTop := fun _ _ _ => ProcessIndistinguishable.refl μ _
  finiteVariationPart_stopAtTop := fun _ _ _ => ProcessIndistinguishable.refl μ _
  martingalePart_stopAtTop_hasLeftLimits := fun τ _ _ h => h.stoppedProcess τ
  stochasticIntegral_stopAtTop_hasLeftLimits := fun τ _ _ h => h.stoppedProcess τ

end FTAPTheorem42.SIntegrableStrategy

namespace FTAPTheorem42.LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {G : LocallySIntegrableStrategy D}

/-- Finite stopping constructed directly on the actual carrier, without a
raw predictable-restriction or stopping calculus. -/
noncomputable def actualFiniteClosedStop
    (H : ActualSIntegrableStrategy (realizationModel G))
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal))) :
    ActualSIntegrableStrategy (realizationModel G) := by
  let V := H.val.toLocally.finiteClosedStopOfRightContinuous τ hτ
  refine ⟨V, ?_⟩
  obtain ⟨w⟩ := H.property
  let σ : Ω → WithTop NNReal := fun ω => τ ω
  let B := stochasticIntervalIocZeroTop σ
  let hB := IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hτ
  refine ⟨{
    schedule := w.schedule
    coefficient := fun n => (w.coefficient n).restrictPredictable B hB
    coefficient_eq := fun n => ?_
    stoppedGain_eq := fun n => ?_ }⟩
  · rw [FiniteHorizonM2ACoefficient.restrictPredictable_coefficient, w.coefficient_eq n]
    have hSet : B = stochasticIntervalIocZero τ := by
      ext ⟨t, ω⟩
      change (t, ω) ∈ stochasticIntervalIocZeroTop σ ↔
        (t, ω) ∈ stochasticIntervalIocZero τ
      rw [mem_stochasticIntervalIocZeroTop_iff, mem_stochasticIntervalIocZero_iff]
      exact and_congr_right fun _ => WithTop.coe_le_coe
    rw [hSet]
    rfl
  · have hOld := (w.stoppedGain_eq n).stoppedProcess σ
    have hCompleted := finiteHorizonCompletedM2AGain_restrict_stochasticIntervalTop
      w.schedule.usualConditions (w.schedule.quadraticKernel n)
      (w.schedule.variationBridge n) (w.schedule.martingale n)
      (w.schedule.terminal_memLp n) (w.coefficient n) σ hτ
    have hComm : stoppedProcess (stoppedProcess H.val.stochasticIntegral σ)
        (w.schedule.localizer n) =
        stoppedProcess (stoppedProcess H.val.stochasticIntegral (w.schedule.localizer n)) σ := by
      rw [stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']
      congr 1
      funext ω
      exact min_comm _ _
    change ProcessIndistinguishable μ
      (stoppedProcess (stoppedProcess H.val.stochasticIntegral σ) (w.schedule.localizer n)) _
    rw [hComm]
    exact hOld.trans hCompleted.symm

end FTAPTheorem42.LocalCompletedM2A
