/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalFixedStopGluing
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalSourceIdentity
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy

/-!
# Global special decomposition of a bounded semimartingale source

The component gluing certificate supplies one global martingale coordinate and
one global predictable finite-variation coordinate on a common localizing
schedule.  This module composes their stopped agreements with the already
completed local source decompositions.  The final process identity is obtained
only through `ProcessIndistinguishable.of_stoppedProcess_localizingSequence`.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## Schedule-free source certificate -/

/-- A global special decomposition certificate attached directly to a bounded
semimartingale source.  The certificate deliberately retains the stronger
regularity of the glued coordinates, not just the fields of the standard
decomposition record. -/
structure BoundedSemimartingaleGlobalSpecialDecompositionData
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) where
  M : Process Ω
  A : Process Ω
  M_isStronglyAdapted : StronglyAdapted F M
  M_isLocalMartingale : LocalMartingale M F mu
  M_rightContinuous : ∀ omega t,
    ContinuousWithinAt (M · omega) (Ici t) t
  M_leftLimits : ProcessHasLeftLimits M
  A_isStronglyPredictable : IsStronglyPredictable F A
  A_isStronglyAdapted : StronglyAdapted F A
  A_rightContinuous : ∀ omega t,
    ContinuousWithinAt (A · omega) (Ici t) t
  A_leftLimits : ProcessHasLeftLimits A
  A_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (A · omega) Set.univ
  decomposition : ProcessIndistinguishable mu S
    (fun t omega => M t omega + A t omega)

namespace BoundedSemimartingaleGlobalSpecialDecompositionData

/-- Forget the strengthened source certificate and expose the standard
special-semimartingale decomposition interface. -/
def toSpecialSemimartingaleDecomposition
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    {source : BoundedSemimartingaleSource S F mu}
    (D : BoundedSemimartingaleGlobalSpecialDecompositionData source) :
    SpecialSemimartingaleDecomposition S F mu := {
  martingalePart := D.M
  finiteVariationPart := D.A
  martingalePart_isLocalMartingale := D.M_isLocalMartingale
  finiteVariationPart_isPredictable := D.A_isStronglyPredictable
  finiteVariationPart_isLocallyBoundedVariation := D.A_locallyBoundedVariation
  decomposition := D.decomposition }

end BoundedSemimartingaleGlobalSpecialDecompositionData

/-! ## The global certificate -/

/-- A global pair obtained from one common-stop exhaustion.  The component
regularity and stopped agreements are retained together with the source
identity, so this certificate can be consumed directly by the standard
special-semimartingale decomposition record. -/
structure CommonStopUncenteredFixedStopGlobalSpecialDecompositionData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau) where
  M : Process Ω
  A : Process Ω
  M_isStronglyAdapted : StronglyAdapted F M
  M_isLocalMartingale : LocalMartingale M F mu
  M_rightContinuous : ∀ omega t,
    ContinuousWithinAt (M · omega) (Ici t) t
  M_leftLimits : ProcessHasLeftLimits M
  A_isStronglyPredictable : IsStronglyPredictable F A
  A_isStronglyAdapted : StronglyAdapted F A
  A_rightContinuous : ∀ omega t,
    ContinuousWithinAt (A · omega) (Ici t) t
  A_leftLimits : ProcessHasLeftLimits A
  A_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (A · omega) Set.univ
  decomposition : ProcessIndistinguishable mu S
    (fun t omega => M t omega + A t omega)
  M_stopped : ∀ n, ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess M (tau n))
    (MeasureTheory.stoppedProcess (data.Mρ n) (tau n))
  A_stopped : ∀ n, ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess A (tau n))
    (MeasureTheory.stoppedProcess (data.Aρ n) (tau n))

namespace CommonStopUncenteredFixedStopGlobalSpecialDecompositionData

/-! The schedule certificate can be exported to the schedule-free source
certificate once its localizer bookkeeping is no longer needed. -/
def toBoundedSemimartingaleGlobalSpecialDecompositionData
    {S : Process Ω}
    {T : Nat → NNReal} {eta : Nat → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    {family : CommonStopUncenteredFixedStopFamily T eta hUsual source}
    {tau : Nat → Ω → WithTop NNReal}
    {data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau}
    (D : CommonStopUncenteredFixedStopGlobalSpecialDecompositionData
      T eta hUsual source family tau data) :
    BoundedSemimartingaleGlobalSpecialDecompositionData source := {
  M := D.M
  A := D.A
  M_isStronglyAdapted := D.M_isStronglyAdapted
  M_isLocalMartingale := D.M_isLocalMartingale
  M_rightContinuous := D.M_rightContinuous
  M_leftLimits := D.M_leftLimits
  A_isStronglyPredictable := D.A_isStronglyPredictable
  A_isStronglyAdapted := D.A_isStronglyAdapted
  A_rightContinuous := D.A_rightContinuous
  A_leftLimits := D.A_leftLimits
  A_locallyBoundedVariation := D.A_locallyBoundedVariation
  decomposition := D.decomposition }

end CommonStopUncenteredFixedStopGlobalSpecialDecompositionData

/-! ## Composition of the local stopped identities -/

theorem stoppedProcess_self_of_restarted_martingale
    {S : Process Ω}
    {T : Nat → NNReal} {eta : Nat → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    {tau : Nat → Ω → WithTop NNReal}
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau)
    (n : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Mρ n) (tau n))
      (data.Mρ n) := by
  exact stoppedProcess_self_of_eq_stopped
    (data.restopped n).Mρ_eq_stopped

theorem stoppedProcess_self_of_restarted_finiteVariation
    {S : Process Ω}
    {T : Nat → NNReal} {eta : Nat → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    {tau : Nat → Ω → WithTop NNReal}
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau)
    (n : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Aρ n) (tau n))
      (data.Aρ n) := by
  exact stoppedProcess_self_of_eq_stopped
    (data.restopped n).Aρ_eq_stopped

theorem source_stopped_indistinguishable_globalSum
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau)
    (gluing : CommonStopUncenteredFixedStopGlobalGluingData
      T eta hUsual source family tau data) :
    ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (fun t omega => gluing.M t omega + gluing.A t omega) (tau n))
      (MeasureTheory.stoppedProcess S (tau n)) := by
  have hMRestarted : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Mρ n) (tau n))
      (data.Mρ n) := by
    intro n
    exact stoppedProcess_self_of_restarted_martingale
      (mu := mu) family data n
  have hARestarted : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Aρ n) (tau n))
      (data.Aρ n) := by
    intro n
    exact stoppedProcess_self_of_restarted_finiteVariation
      (mu := mu) family data n
  have hGlobal := source_indistinguishable_of_stopped_components_localizingSequence
    data.isLocalizingSequence gluing.M_stopped gluing.A_stopped
      hMRestarted hARestarted
      (fun n => (data.restopped n).source_indistinguishable)
  intro n
  exact (hGlobal.stoppedProcess (tau n)).symm

/-! ## Parameterized global producer -/

/-- The full common-stop exhaustion and component gluing produce a global
special-semimartingale decomposition for every valid horizon/error schedule. -/
theorem exists_commonStopUncenteredFixedStopGlobalSpecialDecompositionData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hT : Tendsto (fun n => (T n : WithTop NNReal)) atTop (𝓝 ⊤))
    (heta : ∀ m, 0 < eta m)
    (hEta : (∑' m, ENNReal.ofReal (4 * eta m)) ≠ ⊤)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu) :
    ∃ family : CommonStopUncenteredFixedStopFamily T eta hUsual source,
      ∃ tau : Nat → Ω → WithTop NNReal,
        ∃ data : CommonStopUncenteredFixedStopExhaustionData
          T eta hUsual source family tau,
          Nonempty (CommonStopUncenteredFixedStopGlobalSpecialDecompositionData
            T eta hUsual source family tau data) := by
  obtain ⟨family, tau, ⟨data⟩⟩ :=
    exists_commonStopUncenteredFixedStopExhaustion
      T eta hT heta hEta hUsual source
  obtain ⟨gluing⟩ :=
    exists_commonStopUncenteredFixedStopGlobalGluingData
      T eta hUsual source family tau data
  have hSourceStopped :=
    source_stopped_indistinguishable_globalSum
      T eta hUsual source family tau data gluing
  have hSource : ProcessIndistinguishable mu S
      (fun t omega => gluing.M t omega + gluing.A t omega) := by
    apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence
      data.isLocalizingSequence
    intro n
    exact (hSourceStopped n).symm
  exact ⟨family, tau, data, ⟨{
    M := gluing.M
    A := gluing.A
    M_isStronglyAdapted := gluing.M_isStronglyAdapted
    M_isLocalMartingale := gluing.M_isLocalMartingale
    M_rightContinuous := gluing.M_rightContinuous
    M_leftLimits := gluing.M_leftLimits
    A_isStronglyPredictable := gluing.A_isStronglyPredictable
    A_isStronglyAdapted := gluing.A_isStronglyAdapted
    A_rightContinuous := gluing.A_rightContinuous
    A_leftLimits := gluing.A_leftLimits
    A_locallyBoundedVariation := gluing.A_locallyBoundedVariation
    decomposition := hSource
    M_stopped := gluing.M_stopped
    A_stopped := gluing.A_stopped }⟩⟩

/-! ## A schedule-free concrete corollary -/

/-- The canonical geometric schedule used by the global source producer.
The horizon is the natural-number schedule and the error budget is a shifted
geometric series. -/
noncomputable def canonicalGlobalHorizon (n : Nat) : NNReal := n

noncomputable def canonicalGlobalError (n : Nat) : Real :=
  (1 / 4 : Real) * ((1 / 2 : Real) ^ (n + 1))

theorem canonicalGlobalHorizon_tendsto :
    Tendsto (fun n => (canonicalGlobalHorizon n : WithTop NNReal))
      atTop (𝓝 ⊤) := by
  unfold canonicalGlobalHorizon
  change Tendsto (fun n : Nat => (n : WithTop NNReal))
    atTop (𝓝 ⊤)
  exact ENNReal.tendsto_nat_nhds_top

theorem canonicalGlobalError_pos (n : Nat) :
    0 < canonicalGlobalError n := by
  unfold canonicalGlobalError
  positivity

theorem canonicalGlobalError_sum_ne_top :
    (∑' n, ENNReal.ofReal (4 * canonicalGlobalError n)) ≠ ⊤ := by
  have hNonneg : ∀ n : Nat, 0 ≤ 4 * canonicalGlobalError n := by
    intro n
    exact (le_of_lt (mul_pos (by norm_num)
      (canonicalGlobalError_pos n)))
  have hSummable : Summable (fun n : Nat => 4 * canonicalGlobalError n) := by
    have hGeom : Summable (fun n : Nat =>
        ((1 / 2 : Real) ^ (n + 1))) := by
      simpa [pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using (summable_geometric_two.mul_left (1 / 2 : Real))
    simpa [canonicalGlobalError, mul_assoc] using
      hGeom.mul_left (4 * (1 / 4 : Real))
  rw [← ENNReal.ofReal_tsum_of_nonneg hNonneg hSummable]
  exact ENNReal.ofReal_ne_top

theorem exists_boundedSemimartingaleSource_globalSpecialDecompositionData
    {S : Process Ω}
    (source : BoundedSemimartingaleSource S F mu) :
    Nonempty (BoundedSemimartingaleGlobalSpecialDecompositionData source) := by
  obtain ⟨family, tau, data, ⟨global⟩⟩ :=
    exists_commonStopUncenteredFixedStopGlobalSpecialDecompositionData
      canonicalGlobalHorizon canonicalGlobalError
      canonicalGlobalHorizon_tendsto canonicalGlobalError_pos
      canonicalGlobalError_sum_ne_top source.usualConditions source
  exact ⟨global.toBoundedSemimartingaleGlobalSpecialDecompositionData⟩

end HorizonFactorialGrid

end FTAPTheorem42
