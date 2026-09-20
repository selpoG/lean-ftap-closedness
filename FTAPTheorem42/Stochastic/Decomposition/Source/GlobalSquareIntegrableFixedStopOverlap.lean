/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopOrderedOverlapComponent
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalSquareIntegrableFixedStopFamily

/-!
# Ordered overlap for the square-integrable common-stop family

The level-indexed square-integrable family already contains one completed
fixed-stop package at every horizon and one re-stopped package at every
localizer.  For `n ≤ m`, this module re-stops the stored level `m` at `tau n`
and feeds that package, together with the stored level `n`, to the
source-independent rigidity consumer.  The same minimum-stop bridge then
provides the pairwise compatibility required by gluing.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## One ordered pair -/

/-- The level-`m` package re-stopped at `tau n`, and the source-independent
rigidity certificate comparing it with the stored level-`n` package. -/
structure SquareIntegrableCommonStopUncenteredFixedStopOrderedOverlapData
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
      family tau)
    (n m : Nat) (hnm : n ≤ m) where
  Mmn : Process Ω
  Amn : Process Ω
  restopped_m_at_tau_n :
    CommonStopUncenteredRestoppedComponentData
      (family.level m).alpha_stopping
      ((family.level m).toComponentView)
      (tau n)
      (data.isLocalizingSequence.isStoppingTime n)
      (fun omega => data.tau_le_all_alpha n m omega hnm)
      Mmn Amn
  component_overlap :
    CommonStopUncenteredRestoppedOrderedOverlapComponentData
      (family.level n).alpha_stopping
      ((family.level n).toComponentView)
      (family.level m).alpha_stopping
      ((family.level m).toComponentView)
      (tau n)
      (data.isLocalizingSequence.isStoppingTime n)
      (data.tau_le_alpha n)
      (fun omega => data.tau_le_all_alpha n m omega hnm)
      (data.Mρ n) (data.Aρ n) Mmn Amn
  finiteVariation_overlap_at_tau :
    ProcessIndistinguishable mu (data.Aρ n) Amn
  martingale_overlap_at_tau :
    ProcessIndistinguishable mu (data.Mρ n) Mmn

theorem exists_squareIntegrableCommonStopUncenteredFixedStopOrderedOverlapData
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
      family tau)
    (n m : Nat) (hnm : n ≤ m) :
    Nonempty (SquareIntegrableCommonStopUncenteredFixedStopOrderedOverlapData
      T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data n m hnm) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨Mmn, Amn, hRestopped, _hDecomposition⟩ :=
    exists_squareIntegrableCommonStopUncenteredRestoppedComponentData
      (F := F) (mu := mu) (family.level m) (tau n)
      (data.isLocalizingSequence.isStoppingTime n)
      (fun omega => data.tau_le_all_alpha n m omega hnm)
  obtain ⟨hOverlap⟩ :=
    exists_commonStopUncenteredRestoppedOrderedOverlapComponentData
      (F := F) (mu := mu) hUsual
      (hAlphaN := (family.level n).alpha_stopping)
      (hViewN := (family.level n).toComponentView)
      (hAlphaM := (family.level m).alpha_stopping)
      (hViewM := (family.level m).toComponentView)
      (rho := tau n)
      (hRho := data.isLocalizingSequence.isStoppingTime n)
      (hRhoLeN := data.tau_le_alpha n)
      (hRhoLeM := fun omega => data.tau_le_all_alpha n m omega hnm)
      (MρN := data.Mρ n) (AρN := data.Aρ n) (MρM := Mmn) (AρM := Amn)
      (hRestoppedN := data.restopped n) (hRestoppedM := hRestopped)
  exact ⟨{
    Mmn := Mmn
    Amn := Amn
    restopped_m_at_tau_n := hRestopped
    component_overlap := hOverlap
    finiteVariation_overlap_at_tau := hOverlap.finiteVariation_overlap_at_rho
    martingale_overlap_at_tau := hOverlap.martingale_overlap_at_rho }⟩

/-! ## Compatibility on the common localizing schedule -/

theorem squareIntegrableCommonStopUncenteredFixedStopExhaustionData_martingale_overlap_of_le
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
      family tau)
    (n m : Nat) (hnm : n ≤ m) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Mρ n)
        (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (data.Mρ m)
        (min (tau n) (tau m))) := by
  obtain ⟨hOverlap⟩ :=
    exists_squareIntegrableCommonStopUncenteredFixedStopOrderedOverlapData
      T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data n m hnm
  have hTauOrder : ∀ᵐ omega ∂mu, tau n omega ≤ tau m omega := by
    filter_upwards [data.isLocalizingSequence.mono] with omega hMono
    exact hMono hnm
  have hLeft : ProcessIndistinguishable mu (data.Mρ n)
      (MeasureTheory.stoppedProcess (family.level n).Msource (tau n)) := by
    rw [(data.restopped n).Mρ_eq_stopped]
    exact ProcessIndistinguishable.refl mu _
  have hRight : ProcessIndistinguishable mu (data.Mρ m)
      (MeasureTheory.stoppedProcess (family.level m).Msource (tau m)) := by
    rw [(data.restopped m).Mρ_eq_stopped]
    exact ProcessIndistinguishable.refl mu _
  have hMmn : ProcessIndistinguishable mu hOverlap.Mmn
      (MeasureTheory.stoppedProcess (family.level m).Msource (tau n)) := by
    rw [hOverlap.component_overlap.restoppedM.Mρ_eq_stopped]
    exact ProcessIndistinguishable.refl mu _
  have hOverlapM : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (family.level n).Msource (tau n))
      (MeasureTheory.stoppedProcess (family.level m).Msource (tau n)) :=
    hLeft.symm.trans (hOverlap.component_overlap.martingale_overlap_at_rho.trans hMmn)
  exact stoppedProcess_stoppedProcess_indistinguishable_of_stopped_overlap_of_ae_le
    hLeft hRight hOverlapM hTauOrder

theorem squareIntegrableCommonStopUncenteredFixedStopExhaustionData_finiteVariation_overlap_of_le
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
      family tau)
    (n m : Nat) (hnm : n ≤ m) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Aρ n)
        (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (data.Aρ m)
        (min (tau n) (tau m))) := by
  obtain ⟨hOverlap⟩ :=
    exists_squareIntegrableCommonStopUncenteredFixedStopOrderedOverlapData
      T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data n m hnm
  have hTauOrder : ∀ᵐ omega ∂mu, tau n omega ≤ tau m omega := by
    filter_upwards [data.isLocalizingSequence.mono] with omega hMono
    exact hMono hnm
  have hLeft : ProcessIndistinguishable mu (data.Aρ n)
      (MeasureTheory.stoppedProcess (family.level n).Ap (tau n)) := by
    rw [(data.restopped n).Aρ_eq_stopped]
    exact ProcessIndistinguishable.refl mu _
  have hRight : ProcessIndistinguishable mu (data.Aρ m)
      (MeasureTheory.stoppedProcess (family.level m).Ap (tau m)) := by
    rw [(data.restopped m).Aρ_eq_stopped]
    exact ProcessIndistinguishable.refl mu _
  have hAmn : ProcessIndistinguishable mu hOverlap.Amn
      (MeasureTheory.stoppedProcess (family.level m).Ap (tau n)) := by
    rw [hOverlap.component_overlap.restoppedM.Aρ_eq_stopped]
    exact ProcessIndistinguishable.refl mu _
  have hOverlapM : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (family.level n).Ap (tau n))
      (MeasureTheory.stoppedProcess (family.level m).Ap (tau n)) :=
    hLeft.symm.trans (hOverlap.component_overlap.finiteVariation_overlap_at_rho.trans hAmn)
  exact stoppedProcess_stoppedProcess_indistinguishable_of_stopped_overlap_of_ae_le
    hLeft hRight hOverlapM hTauOrder

theorem squareIntegrableCommonStopUncenteredFixedStopExhaustionData_martingale_compatibility
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
      family tau) :
    ∀ n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Mρ n)
        (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (data.Mρ m)
        (min (tau n) (tau m))) := by
  intro n m
  rcases le_total n m with hnm | hmn
  · exact squareIntegrableCommonStopUncenteredFixedStopExhaustionData_martingale_overlap_of_le
      T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data n m hnm
  · simpa only [inf_comm] using
      (squareIntegrableCommonStopUncenteredFixedStopExhaustionData_martingale_overlap_of_le
        T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data m n hmn).symm

theorem squareIntegrableCommonStopUncenteredFixedStopExhaustionData_finiteVariation_compatibility
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
      family tau) :
    ∀ n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Aρ n)
        (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (data.Aρ m)
        (min (tau n) (tau m))) := by
  intro n m
  rcases le_total n m with hnm | hmn
  · exact squareIntegrableCommonStopUncenteredFixedStopExhaustionData_finiteVariation_overlap_of_le
      T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data n m hnm
  · simpa only [inf_comm] using
      (squareIntegrableCommonStopUncenteredFixedStopExhaustionData_finiteVariation_overlap_of_le
        T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound family tau data m n hmn).symm

end HorizonFactorialGrid

end FTAPTheorem42
