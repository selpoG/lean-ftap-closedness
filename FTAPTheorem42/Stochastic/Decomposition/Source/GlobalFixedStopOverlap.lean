/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalFixedStopFamily
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopOrderedOverlapComponent
import FTAPTheorem42.Stochastic.Martingale.Basic.CompatibleLocalMartingaleGluing
import FTAPTheorem42.Stochastic.FiniteVariation.CompatibleLocalFiniteVariationGluing
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableStrategyAlgebra

/-!
# Overlap of the common-stop fixed-stop family

The tail-infimum localizers are carried by one exact family of finite-horizon
decompositions.  This module compares two members of that family only after
stopping.  For an ordered pair `n ≤ m`, the level-`m` decomposition is
re-stopped at `tau n`; it is then a second decomposition of the same stopped
source as the stored level-`n` package.  The difference of the two predictable
finite-variation parts is a source-free predictable finite-variation local
martingale, so the rigidity theorem identifies both components.

The final compatibility theorems have exactly the overlap shape consumed by
the two generic gluing constructions.  No gluing is performed here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## Ordered overlap certificate -/

/-- The level-`m` decomposition re-stopped at `tau n`, together with the
source-free comparison certificate against the stored level-`n` package.

The difference process and all of its regularity are retained explicitly:
the later gluing consumer can use either the strong ordered overlap or the
derived all-pairs compatibility without reconstructing the rigidity argument.
-/
structure CommonStopUncenteredFixedStopOrderedOverlapData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau)
    (n m : Nat) (hnm : n ≤ m) where
  /-- The level-`m` package, re-stopped at the smaller localizer. -/
  Mmn : Process Ω
  Amn : Process Ω
  restopped_m_at_tau_n :
    CommonStopUncenteredRestoppedSpecialDecompositionData
      (family.level m).endpoint
      (family.level m).hReg
      (family.level m).pair
      (family.level m).hSigned
      (family.level m).hCentered
      (family.level m).hData
      (tau n)
      (data.isLocalizingSequence.isStoppingTime n)
      (fun omega => data.tau_le_all_alpha n m omega hnm)
      Mmn Amn
  /-- The finite-variation difference used by source-free rigidity. -/
  finiteVariationDifference : Process Ω
  finiteVariationDifference_eq :
    finiteVariationDifference =
      (fun t omega => Amn t omega - data.Aρ n t omega)
  finiteVariationDifference_isLocalMartingale :
    LocalMartingale finiteVariationDifference F mu
  finiteVariationDifference_isStronglyPredictable :
    IsStronglyPredictable F finiteVariationDifference
  finiteVariationDifference_rightContinuous : ∀ omega t,
    ContinuousWithinAt (finiteVariationDifference · omega) (Ici t) t
  finiteVariationDifference_boundedVariation : ∀ omega,
    BoundedVariationOn (finiteVariationDifference · omega) Set.univ
  finiteVariationDifference_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (finiteVariationDifference · omega) Set.univ
  finiteVariationDifference_zero : finiteVariationDifference 0 = 0
  finiteVariationDifference_indistinguishable_oppositeMartingale :
    ProcessIndistinguishable mu finiteVariationDifference
      (fun t omega => data.Mρ n t omega - Mmn t omega)
  finiteVariationDifference_indistinguishable_zero :
    ProcessIndistinguishable mu finiteVariationDifference (fun _ _ => 0)
  /-- Overlap of the finite-variation components before the final extra stop. -/
  finiteVariation_overlap_at_tau :
    ProcessIndistinguishable mu (data.Aρ n) Amn
  /-- Overlap of the martingale components before the final extra stop. -/
  martingale_overlap_at_tau :
    ProcessIndistinguishable mu (data.Mρ n) Mmn

/-! ## Construction of the ordered certificate -/

theorem exists_commonStopUncenteredFixedStopOrderedOverlapData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau)
    (n m : Nat) (hnm : n ≤ m) :
    Nonempty (CommonStopUncenteredFixedStopOrderedOverlapData
      T eta hUsual source family tau data n m hnm) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨Mmn, Amn, hRestopped, _hDecomposition⟩ :=
    exists_commonStopUncenteredRestoppedSpecialDecompositionData
      (F := F) (mu := mu)
      (family.level m).endpoint
      (family.level m).hReg
      (family.level m).pair
      (family.level m).hSigned
      (family.level m).hCentered
      (family.level m).hData
      (tau n)
      (data.isLocalizingSequence.isStoppingTime n)
      (fun omega => data.tau_le_all_alpha n m omega hnm)
  let hViewN : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu)
      (family.level n).endpoint.alpha_stopping
      (family.level n).Msource (family.level n).Ap := {
    Msource_martingale := (family.level n).hData.Msource_martingale
    Msource_stronglyAdapted := (family.level n).hData.Msource_stronglyAdapted
    Msource_rightContinuous := (family.level n).hData.Msource_rightContinuous
    Msource_leftLimits := (family.level n).hData.Msource_leftLimits
    Msource_initial := (family.level n).hData.Msource_initial
    Ap_isStronglyPredictable := (family.level n).hCentered.Ap_isStronglyPredictable
    Ap_isStronglyAdapted := (family.level n).hCentered.Ap_isStronglyAdapted
    Ap_rightContinuous := (family.level n).hCentered.Ap_rightContinuous
    Ap_leftLimits := (family.level n).hCentered.Ap_leftLimits
    Ap_boundedVariation := (family.level n).hCentered.Ap_boundedVariation
    Ap_locallyBoundedVariation := (family.level n).hCentered.Ap_locallyBoundedVariation
    Ap_zero := (family.level n).hCentered.Ap_zero
    source_indistinguishable := (family.level n).hData.source_indistinguishable }
  let hViewM : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu)
      (family.level m).endpoint.alpha_stopping
      (family.level m).Msource (family.level m).Ap := {
    Msource_martingale := (family.level m).hData.Msource_martingale
    Msource_stronglyAdapted := (family.level m).hData.Msource_stronglyAdapted
    Msource_rightContinuous := (family.level m).hData.Msource_rightContinuous
    Msource_leftLimits := (family.level m).hData.Msource_leftLimits
    Msource_initial := (family.level m).hData.Msource_initial
    Ap_isStronglyPredictable := (family.level m).hCentered.Ap_isStronglyPredictable
    Ap_isStronglyAdapted := (family.level m).hCentered.Ap_isStronglyAdapted
    Ap_rightContinuous := (family.level m).hCentered.Ap_rightContinuous
    Ap_leftLimits := (family.level m).hCentered.Ap_leftLimits
    Ap_boundedVariation := (family.level m).hCentered.Ap_boundedVariation
    Ap_locallyBoundedVariation := (family.level m).hCentered.Ap_locallyBoundedVariation
    Ap_zero := (family.level m).hCentered.Ap_zero
    source_indistinguishable := (family.level m).hData.source_indistinguishable }
  let hCoreN : CommonStopUncenteredRestoppedComponentData
      (family.level n).endpoint.alpha_stopping hViewN (tau n)
      (data.isLocalizingSequence.isStoppingTime n)
      (data.tau_le_alpha n) (data.Mρ n) (data.Aρ n) := {
    Mρ_eq_stopped := (data.restopped n).Mρ_eq_stopped
    Aρ_eq_stopped := (data.restopped n).Aρ_eq_stopped
    source_doubleStop_eq := (data.restopped n).source_doubleStop_eq
    source_doubleStop_indistinguishable :=
      (data.restopped n).source_doubleStop_indistinguishable
    Mρ_martingale := (data.restopped n).Mρ_martingale
    Mρ_stronglyAdapted := (data.restopped n).Mρ_stronglyAdapted
    Mρ_rightContinuous := (data.restopped n).Mρ_rightContinuous
    Mρ_leftLimits := (data.restopped n).Mρ_leftLimits
    Mρ_initial := (data.restopped n).Mρ_initial
    Aρ_isStronglyPredictable := (data.restopped n).Aρ_isStronglyPredictable
    Aρ_isStronglyAdapted := (data.restopped n).Aρ_isStronglyAdapted
    Aρ_rightContinuous := (data.restopped n).Aρ_rightContinuous
    Aρ_leftLimits := (data.restopped n).Aρ_leftLimits
    Aρ_boundedVariation := (data.restopped n).Aρ_boundedVariation
    Aρ_locallyBoundedVariation := (data.restopped n).Aρ_locallyBoundedVariation
    Aρ_zero := (data.restopped n).Aρ_zero
    source_indistinguishable := (data.restopped n).source_indistinguishable }
  let hCoreM : CommonStopUncenteredRestoppedComponentData
      (family.level m).endpoint.alpha_stopping hViewM (tau n)
      (data.isLocalizingSequence.isStoppingTime n)
      (fun omega => data.tau_le_all_alpha n m omega hnm) Mmn Amn := {
    Mρ_eq_stopped := hRestopped.Mρ_eq_stopped
    Aρ_eq_stopped := hRestopped.Aρ_eq_stopped
    source_doubleStop_eq := hRestopped.source_doubleStop_eq
    source_doubleStop_indistinguishable :=
      hRestopped.source_doubleStop_indistinguishable
    Mρ_martingale := hRestopped.Mρ_martingale
    Mρ_stronglyAdapted := hRestopped.Mρ_stronglyAdapted
    Mρ_rightContinuous := hRestopped.Mρ_rightContinuous
    Mρ_leftLimits := hRestopped.Mρ_leftLimits
    Mρ_initial := hRestopped.Mρ_initial
    Aρ_isStronglyPredictable := hRestopped.Aρ_isStronglyPredictable
    Aρ_isStronglyAdapted := hRestopped.Aρ_isStronglyAdapted
    Aρ_rightContinuous := hRestopped.Aρ_rightContinuous
    Aρ_leftLimits := hRestopped.Aρ_leftLimits
    Aρ_boundedVariation := hRestopped.Aρ_boundedVariation
    Aρ_locallyBoundedVariation := hRestopped.Aρ_locallyBoundedVariation
    Aρ_zero := hRestopped.Aρ_zero
    source_indistinguishable := hRestopped.source_indistinguishable }
  obtain ⟨hCoreOverlap⟩ :=
    exists_commonStopUncenteredRestoppedOrderedOverlapComponentData
      (F := F) (mu := mu) hUsual
      (hAlphaN := (family.level n).endpoint.alpha_stopping)
      (hViewN := hViewN)
      (hAlphaM := (family.level m).endpoint.alpha_stopping)
      (hViewM := hViewM)
      (rho := tau n)
      (hRho := data.isLocalizingSequence.isStoppingTime n)
      (hRhoLeN := data.tau_le_alpha n)
      (hRhoLeM := fun omega => data.tau_le_all_alpha n m omega hnm)
      (MρN := data.Mρ n) (AρN := data.Aρ n) (MρM := Mmn) (AρM := Amn)
      hCoreN hCoreM
  exact ⟨{
    Mmn := Mmn
    Amn := Amn
    restopped_m_at_tau_n := hRestopped
    finiteVariationDifference := hCoreOverlap.finiteVariationDifference
    finiteVariationDifference_eq := hCoreOverlap.finiteVariationDifference_eq
    finiteVariationDifference_isLocalMartingale :=
      hCoreOverlap.finiteVariationDifference_isLocalMartingale
    finiteVariationDifference_isStronglyPredictable :=
      hCoreOverlap.finiteVariationDifference_isStronglyPredictable
    finiteVariationDifference_rightContinuous :=
      hCoreOverlap.finiteVariationDifference_rightContinuous
    finiteVariationDifference_boundedVariation :=
      hCoreOverlap.finiteVariationDifference_boundedVariation
    finiteVariationDifference_locallyBoundedVariation :=
      hCoreOverlap.finiteVariationDifference_locallyBoundedVariation
    finiteVariationDifference_zero := hCoreOverlap.finiteVariationDifference_zero
    finiteVariationDifference_indistinguishable_oppositeMartingale :=
      hCoreOverlap.finiteVariationDifference_indistinguishable_oppositeMartingale
    finiteVariationDifference_indistinguishable_zero :=
      hCoreOverlap.finiteVariationDifference_indistinguishable_zero
    finiteVariation_overlap_at_tau :=
      hCoreOverlap.finiteVariation_overlap_at_rho
    martingale_overlap_at_tau := hCoreOverlap.martingale_overlap_at_rho }⟩

/-! ## Ordered overlap after stopping -/

theorem commonStopUncenteredFixedStopExhaustionData_martingale_overlap_of_le
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau)
    (n m : Nat) (hnm : n ≤ m) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Mρ n)
        (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (data.Mρ m)
        (min (tau n) (tau m))) := by
  obtain ⟨hOverlap⟩ :=
    exists_commonStopUncenteredFixedStopOrderedOverlapData
      T eta hUsual source family tau data n m hnm
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
    rw [hOverlap.restopped_m_at_tau_n.Mρ_eq_stopped]
    exact ProcessIndistinguishable.refl mu _
  have hOverlapM : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (family.level n).Msource (tau n))
      (MeasureTheory.stoppedProcess (family.level m).Msource (tau n)) :=
    hLeft.symm.trans (hOverlap.martingale_overlap_at_tau.trans hMmn)
  exact stoppedProcess_stoppedProcess_indistinguishable_of_stopped_overlap_of_ae_le
    hLeft hRight hOverlapM hTauOrder

theorem commonStopUncenteredFixedStopExhaustionData_finiteVariation_overlap_of_le
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau)
    (n m : Nat) (hnm : n ≤ m) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Aρ n)
        (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (data.Aρ m)
        (min (tau n) (tau m))) := by
  obtain ⟨hOverlap⟩ :=
    exists_commonStopUncenteredFixedStopOrderedOverlapData
      T eta hUsual source family tau data n m hnm
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
    rw [hOverlap.restopped_m_at_tau_n.Aρ_eq_stopped]
    exact ProcessIndistinguishable.refl mu _
  have hOverlapM : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (family.level n).Ap (tau n))
      (MeasureTheory.stoppedProcess (family.level m).Ap (tau n)) :=
    hLeft.symm.trans (hOverlap.finiteVariation_overlap_at_tau.trans hAmn)
  exact stoppedProcess_stoppedProcess_indistinguishable_of_stopped_overlap_of_ae_le
    hLeft hRight hOverlapM hTauOrder

/-! ## Full pairwise compatibility on the common schedule -/

theorem commonStopUncenteredFixedStopExhaustionData_martingale_compatibility
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau) :
    ∀ n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Mρ n)
        (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (data.Mρ m)
        (min (tau n) (tau m))) := by
  intro n m
  rcases le_total n m with hnm | hmn
  · exact commonStopUncenteredFixedStopExhaustionData_martingale_overlap_of_le
      T eta hUsual source family tau data n m hnm
  · simpa only [inf_comm] using
      (commonStopUncenteredFixedStopExhaustionData_martingale_overlap_of_le
        T eta hUsual source family tau data m n hmn).symm

theorem commonStopUncenteredFixedStopExhaustionData_finiteVariation_compatibility
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau) :
    ∀ n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (data.Aρ n)
        (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (data.Aρ m)
        (min (tau n) (tau m))) := by
  intro n m
  rcases le_total n m with hnm | hmn
  · exact commonStopUncenteredFixedStopExhaustionData_finiteVariation_overlap_of_le
      T eta hUsual source family tau data n m hnm
  · simpa only [inf_comm] using
      (commonStopUncenteredFixedStopExhaustionData_finiteVariation_overlap_of_le
        T eta hUsual source family tau data m n hmn).symm

end HorizonFactorialGrid

end FTAPTheorem42
