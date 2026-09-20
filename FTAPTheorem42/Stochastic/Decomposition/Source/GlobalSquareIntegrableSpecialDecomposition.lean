/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalSquareIntegrableFixedStopGluing
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalSourceIdentity
import FTAPTheorem42.Stochastic.Decomposition.Source.RegularizedSpecialSemimartingale

/-!
# Global special decomposition for the square-integrable envelope route

The square-integrable exhaustion and component-gluing certificates are joined
here with the source-independent stopped identity.  The resulting schedule-
bearing certificate retains the global component regularity and each stopped
agreement; only the source identity is globalized in this module.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## Schedule-free certificate -/

/-- A schedule-free square-integrable global decomposition certificate.  The
strong regularity of both component processes is retained alongside the
standard decomposition fields. -/
structure SquareIntegrableSemimartingaleGlobalSpecialDecompositionData
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    (hS : IsSemimartingale S F mu) where
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

namespace SquareIntegrableSemimartingaleGlobalSpecialDecompositionData

/-- Forget the strengthened pathwise component regularity and expose the
standard special-semimartingale decomposition interface. -/
def toSpecialSemimartingaleDecomposition
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {hS : IsSemimartingale S F mu}
    (D : SquareIntegrableSemimartingaleGlobalSpecialDecompositionData hS) :
    SpecialSemimartingaleDecomposition S F mu := {
  martingalePart := D.M
  finiteVariationPart := D.A
  martingalePart_isLocalMartingale := D.M_isLocalMartingale
  finiteVariationPart_isPredictable := D.A_isStronglyPredictable
  finiteVariationPart_isLocallyBoundedVariation := D.A_locallyBoundedVariation
  decomposition := D.decomposition }

end SquareIntegrableSemimartingaleGlobalSpecialDecompositionData

/-! ## Schedule-bearing source certificate -/

/-- A global square-integrable component pair produced from one retained
common-stop schedule.  The source identity is process-indistinguishable and
the component agreements remain attached to that same schedule. -/
structure SquareIntegrableCommonStopUncenteredFixedStopGlobalSpecialDecompositionData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (family : SquareIntegrableCommonStopUncenteredFixedStopFamily
      (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound)
    (tau : Nat → Ω → WithTop NNReal)
    (data : SquareIntegrableCommonStopUncenteredFixedStopExhaustionData
      (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound
      family tau) where
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

namespace SquareIntegrableCommonStopUncenteredFixedStopGlobalSpecialDecompositionData

/-- Forget the schedule while retaining the source identity and all global
component regularity. -/
def toScheduleFree
    {S : Process Ω}
    {T : Nat → NNReal} {eta : Nat → Real}
    {ξ : Ω → Real} {hξ : MemLp ξ (2 : ENNReal) mu}
    {hUsual : Filtration.UsualConditions mu F}
    {hS : IsSemimartingale S F mu}
    {hSAdapted : StronglyAdapted F S}
    {hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t}
    {hSLeft : ProcessHasLeftLimits S}
    {hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖}
    {family : SquareIntegrableCommonStopUncenteredFixedStopFamily
      (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound}
    {tau : Nat → Ω → WithTop NNReal}
    {data : SquareIntegrableCommonStopUncenteredFixedStopExhaustionData
      (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound
      family tau}
    (D : SquareIntegrableCommonStopUncenteredFixedStopGlobalSpecialDecompositionData
      T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data) :
    SquareIntegrableSemimartingaleGlobalSpecialDecompositionData hS := {
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

end SquareIntegrableCommonStopUncenteredFixedStopGlobalSpecialDecompositionData

/-! ## Composition of the local stopped identities -/

theorem exists_squareIntegrableCommonStopUncenteredFixedStopGlobalSpecialDecompositionData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hT : Tendsto (fun n => (T n : WithTop NNReal)) atTop (𝓝 ⊤))
    (heta : ∀ m, 0 < eta m)
    (hEta : (∑' m, ENNReal.ofReal (4 * eta m)) ≠ ⊤)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) :
    ∃ family : SquareIntegrableCommonStopUncenteredFixedStopFamily
        (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound,
      ∃ tau : Nat → Ω → WithTop NNReal,
        ∃ data : SquareIntegrableCommonStopUncenteredFixedStopExhaustionData
          (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound
          family tau,
          Nonempty (SquareIntegrableCommonStopUncenteredFixedStopGlobalSpecialDecompositionData
            T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data) := by
  obtain ⟨family, tau, ⟨data⟩⟩ :=
    exists_squareIntegrableCommonStopUncenteredFixedStopExhaustion
      T eta hT heta hEta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound
  obtain ⟨gluing⟩ :=
    exists_squareIntegrableCommonStopUncenteredFixedStopGlobalGluingData
      T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data
  have hMRestarted : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Mρ n) (tau n))
      (data.Mρ n) := by
    intro n
    exact stoppedProcess_self_of_eq_stopped
      (data.restopped n).Mρ_eq_stopped
  have hARestarted : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Aρ n) (tau n))
      (data.Aρ n) := by
    intro n
    exact stoppedProcess_self_of_eq_stopped
      (data.restopped n).Aρ_eq_stopped
  have hSource := source_indistinguishable_of_stopped_components_localizingSequence
    data.isLocalizingSequence gluing.M_stopped gluing.A_stopped
      hMRestarted hARestarted
      (fun n => (data.restopped n).source_indistinguishable)
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

/-! ## A concrete schedule-free endpoint -/

/-- A positive growing horizon schedule. -/
noncomputable def canonicalSquareIntegrableGlobalHorizon (n : Nat) : NNReal := n + 1

/-- A positive summable error schedule. -/
noncomputable def canonicalSquareIntegrableGlobalError (n : Nat) : Real :=
  (1 / 4 : Real) * ((1 / 2 : Real) ^ (n + 1))

theorem canonicalSquareIntegrableGlobalHorizon_tendsto :
    Tendsto (fun n => (canonicalSquareIntegrableGlobalHorizon n : WithTop NNReal))
      atTop (𝓝 ⊤) := by
  unfold canonicalSquareIntegrableGlobalHorizon
  rw [WithTop.tendsto_nhds_top_iff]
  intro r
  obtain ⟨N, hN⟩ := exists_nat_ge r
  filter_upwards [eventually_ge_atTop N] with n hNn
  have hrn : r ≤ (n : NNReal) := by
    exact hN.trans (by exact_mod_cast hNn)
  have hrn' : r < (n : NNReal) + 1 := by
    exact lt_of_le_of_lt hrn (lt_add_of_pos_right _ (by norm_num))
  exact WithTop.coe_lt_coe.mpr hrn'

theorem canonicalSquareIntegrableGlobalError_pos (n : Nat) :
    0 < canonicalSquareIntegrableGlobalError n := by
  unfold canonicalSquareIntegrableGlobalError
  positivity

theorem canonicalSquareIntegrableGlobalError_sum_ne_top :
    (∑' n, ENNReal.ofReal (4 * canonicalSquareIntegrableGlobalError n)) ≠ ⊤ := by
  have hNonneg : ∀ n : Nat,
      0 ≤ 4 * canonicalSquareIntegrableGlobalError n := by
    intro n
    exact (le_of_lt (mul_pos (by norm_num)
      (canonicalSquareIntegrableGlobalError_pos n)))
  have hSummable : Summable (fun n : Nat =>
      4 * canonicalSquareIntegrableGlobalError n) := by
    have hGeom : Summable (fun n : Nat =>
        ((1 / 2 : Real) ^ (n + 1))) := by
      simpa [pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using (summable_geometric_two.mul_left (1 / 2 : Real))
    simpa [canonicalSquareIntegrableGlobalError, mul_assoc] using
      hGeom.mul_left (4 * (1 / 4 : Real))
  rw [← ENNReal.ofReal_tsum_of_nonneg hNonneg hSummable]
  exact ENNReal.ofReal_ne_top

theorem exists_squareIntegrableSemimartingaleGlobalSpecialDecompositionData
    {S : Process Ω}
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) :
    Nonempty (SquareIntegrableSemimartingaleGlobalSpecialDecompositionData hS) := by
  obtain ⟨family, tau, data, ⟨global⟩⟩ :=
    exists_squareIntegrableCommonStopUncenteredFixedStopGlobalSpecialDecompositionData
      canonicalSquareIntegrableGlobalHorizon canonicalSquareIntegrableGlobalError
      canonicalSquareIntegrableGlobalHorizon_tendsto
      canonicalSquareIntegrableGlobalError_pos
      canonicalSquareIntegrableGlobalError_sum_ne_top
      ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound
  exact ⟨global.toScheduleFree⟩

end HorizonFactorialGrid

end FTAPTheorem42
