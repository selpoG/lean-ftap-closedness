/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalSpecialDecomposition
import FTAPTheorem42.Stochastic.Decomposition.Source.RegularizedSpecialSemimartingale

/-!
# The regularized source data under an equivalent tilted measure

The tilted envelope is constructed before the special decomposition.  This
module supplies the source-side part of the next boundary: transfer the
bounded source to the equivalent measure, apply the schedule-free global
special-decomposition producer, and expose the regularity needed by the
existing centered-source construction.

No stochastic-integral calculus, component graph, or market realization is
claimed here.  Those are deliberately separate obligations for the selected
strategy sequence.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Source-side Q data -/

/-- A bounded source transferred to `Q`, together with the canonical global
special-decomposition certificate produced from that transferred source.

The `global` field is the strengthened certificate: in addition to the
standard special-semimartingale fields it retains adaptedness, càdlàg
regularity, left limits, and local bounded variation of both coordinates.
The source measure `Q` is a parameter of `sourceQ`; no decomposition is
transported abstractly between measures.
-/
structure TiltedRegularizedSourceData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Q : Measure Omega} [IsProbabilityMeasure Q]
    (sourceQ : BoundedSemimartingaleSource S F Q) where
  global : HorizonFactorialGrid.BoundedSemimartingaleGlobalSpecialDecompositionData
    sourceQ

namespace TiltedRegularizedSourceData

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {Q : Measure Omega} [IsProbabilityMeasure Q]
  {sourceQ : BoundedSemimartingaleSource S F Q}

/-! The following canonical accessors intentionally use the strengthened
global certificate directly.  In particular, the right-continuity input is
not recovered from an arbitrary special decomposition representative. -/

/-- The special decomposition carried by the global source certificate. -/
noncomputable def decomposition
    (data : TiltedRegularizedSourceData sourceQ) :
    SpecialSemimartingaleDecomposition S F Q :=
  data.global.toSpecialSemimartingaleDecomposition

theorem martingalePart_rightContinuous
    (data : TiltedRegularizedSourceData sourceQ) :
    ∀ omega t,
      ContinuousWithinAt ((data.decomposition).martingalePart · omega)
        (Ici t) t := by
  exact data.global.M_rightContinuous

/-! ## Existing regularized/centered-source route -/

/-- The regularized decomposition selected by the existing centered-source
route, using the global martingale right-continuity certificate directly.  The
raw `decomposition` above remains the canonical global M/A certificate; this
view is only the existing regularization API required by that route. -/
noncomputable def regularizedDecomposition
    [SigmaFiniteFiltration Q F]
    (data : TiltedRegularizedSourceData sourceQ) :
    SpecialSemimartingaleDecomposition S F Q :=
  SpecialSemimartingaleDecomposition.regularizedDecomposition
    data.decomposition sourceQ.usualConditions sourceQ.hasLeftLimits
      sourceQ.stronglyAdapted data.martingalePart_rightContinuous
      sourceQ.rightContinuous

/-- All regularity delivered by the existing null-set regularization is
available from the transferred source data, without new hypotheses. -/
theorem regularizedDecomposition_spec
    [SigmaFiniteFiltration Q F]
    (data : TiltedRegularizedSourceData sourceQ) :
    ProcessIndistinguishable Q
        (data.regularizedDecomposition).martingalePart
        data.decomposition.martingalePart ∧
      ProcessIndistinguishable Q
        (data.regularizedDecomposition).finiteVariationPart
        data.decomposition.finiteVariationPart ∧
      StronglyAdapted F (data.regularizedDecomposition).martingalePart ∧
      (∀ omega t,
        ContinuousWithinAt
          ((data.regularizedDecomposition).martingalePart · omega)
          (Ici t) t) ∧
      ProcessHasLeftLimits (data.regularizedDecomposition).martingalePart ∧
      (∀ omega t,
        ContinuousWithinAt
          ((data.regularizedDecomposition).finiteVariationPart · omega)
          (Ici t) t) := by
  exact SpecialSemimartingaleDecomposition.regularizedDecomposition_spec
    data.decomposition sourceQ.usualConditions sourceQ.hasLeftLimits
      sourceQ.stronglyAdapted data.martingalePart_rightContinuous
      sourceQ.rightContinuous

/-- The centered unit source after the canonical regularization.  This is a
source-side carrier only; it does not assert any market graph semantics. -/
noncomputable def centeredUnitLocallySIntegrableStrategy
    [SigmaFiniteFiltration Q F]
    (data : TiltedRegularizedSourceData sourceQ) :
    LocallySIntegrableStrategy data.regularizedDecomposition :=
  SpecialSemimartingaleDecomposition.regularizedCenteredUnitLocallySIntegrableStrategy
    data.decomposition sourceQ.usualConditions sourceQ.hasLeftLimits
      sourceQ.stronglyAdapted sourceQ.rightContinuous
      data.martingalePart_rightContinuous

theorem centeredUnitLocallySIntegrableStrategy_integrand
    [SigmaFiniteFiltration Q F]
    (data : TiltedRegularizedSourceData sourceQ) :
    data.centeredUnitLocallySIntegrableStrategy.integrand =
      PredictableProcess.unit := by
  have hReg := data.regularizedDecomposition_spec
  exact SpecialSemimartingaleDecomposition.centeredUnitLocallySIntegrableStrategy_integrand
    data.regularizedDecomposition sourceQ.stronglyAdapted
      sourceQ.rightContinuous hReg.2.2.1 hReg.2.2.2.1 hReg.2.2.2.2.2

theorem centeredUnitLocallySIntegrableStrategy_martingalePart_hasLeftLimits
    [SigmaFiniteFiltration Q F]
    (data : TiltedRegularizedSourceData sourceQ) :
    ProcessHasLeftLimits
      data.centeredUnitLocallySIntegrableStrategy.martingalePart := by
  have hReg := data.regularizedDecomposition_spec
  change ProcessHasLeftLimits (fun t omega =>
    data.regularizedDecomposition.martingalePart t omega -
      data.regularizedDecomposition.martingalePart 0 omega)
  exact hReg.2.2.2.2.1.sub
    (ProcessHasLeftLimits.timeConstant
      (data.regularizedDecomposition.martingalePart 0))

end TiltedRegularizedSourceData

end FTAPTheorem42
