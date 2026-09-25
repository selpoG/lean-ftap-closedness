/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedMartingaleIntegralProcess
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryMartingaleIntegral
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryFiniteVariationProcess
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableRealizationModel
import FTAPTheorem42.Stochastic.FiniteVariation.PredictableFiniteVariationLocalMartingale
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableLocalMartingaleL2Control
import FTAPTheorem42.Stochastic.FiniteVariation.CanonicalVariationControl

/-!
# Martingale energy of actual finite-horizon elementary graphs

The bounded-martingale quadratic energy measure is independent of a chosen
elementary grid.  This module connects its exact elementary isometry to the
graph-extensional finite-horizon `M² ⊕ A¹` carrier.  In particular, the
centered terminal martingale distance of two arbitrary actual
representatives is exactly the predictable-energy distance of their stored
integrands.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace PredictableElementaryStrategy

/-- The raw elementary coefficient restricted to the positive deterministic
horizon `(0,T]`. -/
noncomputable def finiteHorizonIntegrand
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (K : PredictableElementaryStrategy F) (T : NNReal) : Process Omega :=
  PredictableProcess.restrict
    (stochasticIntervalIocZero (fun _ : Omega => T)) K.integrand

/-- The running elementary gain, stopped at a deterministic horizon. -/
noncomputable def finiteHorizonGain
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (K : PredictableElementaryStrategy F) (X : Process Omega)
    (T : NNReal) : Process Omega :=
  MeasureTheory.stoppedProcess
    (ElementaryStrategy.gain X K.toElementary)
    (fun _ : Omega => (T : WithTop NNReal))

@[simp]
theorem finiteHorizonGain_apply
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (K : PredictableElementaryStrategy F) (X : Process Omega)
    (T t : NNReal) (omega : Omega) :
    K.finiteHorizonGain X T t omega =
      ElementaryStrategy.gain X K.toElementary (min t T) omega := by
  exact stoppedProcess_const_apply _ _ _ _

end PredictableElementaryStrategy

/-!
## Actual refining-grid M2A approximations

This section places the factorial left-grid approximations of one bounded
predictable elementary coefficient in the same finite-horizon actual
realization carrier.  Thus the previously proved martingale `L²` and
finite-variation `L¹` approximation estimates apply to one sequence of
actual stochastic-integral graphs.
-/

namespace PredictableElementaryStrategy

/-- Finite-horizon restriction does not enlarge the elementary integrand
beyond its pathwise absolute coefficient sum. -/
theorem abs_finiteHorizonIntegrand_le_coefficientAbsSum
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (T t : NNReal)
    (omega : Omega) :
    |H.finiteHorizonIntegrand T t omega| ≤ H.coefficientAbsSum omega := by
  by_cases ht : 0 < t ∧ t ≤ T
  · rw [finiteHorizonIntegrand,
      PredictableProcess.restrict_apply_of_mem
      ((mem_stochasticIntervalIocZero_iff
        (fun _ : Omega => T) t omega).2 ht)]
    exact H.abs_integrand_le_coefficientAbsSum t omega
  · rw [finiteHorizonIntegrand,
      PredictableProcess.restrict_apply_of_notMem
      (fun hmem => ht ((mem_stochasticIntervalIocZero_iff
        (fun _ : Omega => T) t omega).1 hmem)), abs_zero]
    exact H.coefficientAbsSum_nonneg omega

end PredictableElementaryStrategy

/-!
## Actual finite-horizon M2A approximation

The interval-algebra density theorem produces a bounded predictable
elementary strategy for each error tolerance.  Its deterministic blockwise
coefficient bound allows the same witness to enter the concrete
finite-horizon `M² ⊕ A¹` realization.  A second diagonal choice moves every
witness to a factorial-grid aligned actual strategy while retaining
convergence under both predictable controls.

The common `L¹`/`L²` approximation uses one sequence of actual strategies
in a graph-extensional carrier for both component limits.
-/

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

/-- The positive deterministic horizon strip used by the actual elementary
realization. -/
def finiteHorizonPredictableStrip (T : NNReal) : Set (NNReal × Omega) :=
  stochasticIntervalIocZero (fun _ : Omega => T)

theorem measurableSet_finiteHorizonPredictableStrip (T : NNReal) :
    MeasurableSet[F.predictable]
      (finiteHorizonPredictableStrip (Omega := Omega) T) :=
  IsStoppingTime.measurableSet_stochasticIntervalIocZero
    (isStoppingTime_const F T)

/-- Restriction of a raw predictable coefficient to the positive horizon
strip, represented again as a process. -/
noncomputable def finiteHorizonCoefficient
    (T : NNReal) (f : NNReal × Omega → Real) : Process Omega :=
  PredictableProcess.restrict
    (finiteHorizonPredictableStrip (Omega := Omega) T) (Function.curry f)

omit [SigmaFiniteFiltration mu F] in
theorem finiteHorizonCoefficient_ae_eq
    {M : Process Omega} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real) :
    Function.uncurry (finiteHorizonCoefficient T f)
      =ᵐ[Q.predictableEnergyMeasure] f := by
  filter_upwards [Q.ae_time_pos, Q.ae_time_le_horizon]
      with point hPos hLe
  exact PredictableProcess.restrict_apply_of_mem
    ((mem_stochasticIntervalIocZero_iff
      (fun _ : Omega => T) point.1 point.2).2 ⟨hPos, hLe⟩)

theorem finiteHorizonCoefficient_isStronglyPredictable
    (T : NNReal) {f : NNReal × Omega → Real}
    (hf : StronglyMeasurable[F.predictable] f) :
    IsStronglyPredictable F (finiteHorizonCoefficient T f) := by
  apply PredictableProcess.isStronglyPredictable_restrict
    (measurableSet_finiteHorizonPredictableStrip (F := F) T)
  simpa [IsStronglyPredictable] using hf

omit [SigmaFiniteFiltration mu F] in
theorem finiteHorizonCoefficient_memLp
    (E : SIntegrableFiniteVariationBridge G)
    (T : NNReal) {f : NNReal × Omega → Real}
    (hf : MemLp f 1 (canonicalVariationMeasure E)) :
    MemLp (Function.uncurry (finiteHorizonCoefficient T f)) 1
      (canonicalVariationMeasure E) := by
  change MemLp
    ((finiteHorizonPredictableStrip (Omega := Omega) T).indicator f)
      1 (canonicalVariationMeasure E)
  exact MemLp.indicator
    (measurableSet_finiteHorizonPredictableStrip (F := F) T) hf

end SIntegrableFiniteVariationBridge

/-!
## Completing the common finite-horizon M2A approximation

The actual diagonal sequence constructed for the finite-variation and
martingale controls is specialized to the grid-independent quadratic
energy measure.  The same actual strategies converge to the completed
Stieltjes terminal in `L¹`, to the completed martingale terminal in `L²`,
and to the completed martingale process in finite-horizon maximal `L²`.
-/

namespace SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- The horizon restriction of an energy-`L²` predictable coefficient
remains in the same energy space. -/
theorem finiteHorizonCoefficient_memLp_energy_two
    (T : NNReal)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T) {f : NNReal × Omega → Real}
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure) :
    MemLp (Function.uncurry (finiteHorizonCoefficient T f))
      (2 : ENNReal) Q.predictableEnergyMeasure := by
  change MemLp
    ((finiteHorizonPredictableStrip (Omega := Omega) T).indicator f)
      (2 : ENNReal) Q.predictableEnergyMeasure
  exact MemLp.indicator
    (measurableSet_finiteHorizonPredictableStrip (F := F) T) hf

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
