/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualRestrictionJump
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.DirectStopping
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePathwiseRestrictionCalculus

/-!
# Actual-first Hahn restriction for Lemma 4.7

The positive Hahn restriction used by Lemma 4.7 is formed with the intrinsic
actual-first restriction, not with the freely constructible raw restriction
record.  Its finite-variation increment, normalization, left-limit, and jump
properties are recorded on that one actual graph.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrablePathwiseRestrictionCalculus.HahnPositive

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The càdlàg intrinsic restriction selected by the positive Hahn set. -/
noncomputable def actualHahnPositiveRestrictionCadlag
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val) :
    ActualSIntegrableStrategy (realizationModel G) :=
  actualRestrictPredictableCadlag
    hGLeft L P.positiveSet P.measurableSet_positiveSet

/-- The actual-first positive Hahn restriction has nonnegative
finite-variation increments which dominate the original increments. -/
theorem actualHahnPositiveRestrictionCadlag_finiteVariation_increment_ae
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val) :
    ∀ᵐ omega ∂mu, forall a b : NNReal, a <= b ->
      0 <= (actualHahnPositiveRestrictionCadlag hGLeft P
          ).val.finiteVariationPart b omega -
          (actualHahnPositiveRestrictionCadlag hGLeft P
            ).val.finiteVariationPart a omega /\
        L.val.finiteVariationPart b omega -
            L.val.finiteVariationPart a omega <=
          (actualHahnPositiveRestrictionCadlag hGLeft P
            ).val.finiteVariationPart b omega -
            (actualHahnPositiveRestrictionCadlag hGLeft P
              ).val.finiteVariationPart a omega := by
  filter_upwards [actualRestrictPredictableCadlag_finiteVariationPart_increment
    hGLeft L P.positiveSet P.measurableSet_positiveSet,
    positive_mass_nonnegative_and_dominates_ae P] with omega hRestrict hHahn
  intro a b hab
  rw [show (actualHahnPositiveRestrictionCadlag hGLeft P).val.finiteVariationPart =
    (actualRestrictPredictableCadlag hGLeft L P.positiveSet
      P.measurableSet_positiveSet).val.finiteVariationPart from rfl,
    hRestrict a b hab]
  exact hHahn a b hab

/-- The actual-first positive Hahn gain starts from zero. -/
theorem actualHahnPositiveRestrictionCadlag_stochasticIntegral_zero
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val) :
    (actualHahnPositiveRestrictionCadlag hGLeft P
      ).val.stochasticIntegral 0 =ᵐ[mu] 0 :=
  actualRestrictPredictableCadlag_stochasticIntegral_zero hGLeft L
    P.positiveSet P.measurableSet_positiveSet

/-- The actual-first positive Hahn martingale has left limits. -/
theorem actualHahnPositiveRestrictionCadlag_martingalePart_hasLeftLimits
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val) :
    ProcessHasLeftLimits
      (actualHahnPositiveRestrictionCadlag hGLeft P
        ).val.martingalePart :=
  actualRestrictPredictableCadlag_martingalePart_hasLeftLimits hGLeft L
    P.positiveSet P.measurableSet_positiveSet

/-- The actual-first positive Hahn gain has left limits. -/
theorem actualHahnPositiveRestrictionCadlag_stochasticIntegral_hasLeftLimits
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val) :
    ProcessHasLeftLimits
      (actualHahnPositiveRestrictionCadlag hGLeft P
        ).val.stochasticIntegral :=
  actualRestrictPredictableCadlag_stochasticIntegral_hasLeftLimits hGLeft L
    P.positiveSet P.measurableSet_positiveSet

/-- A simultaneous lower jump bound survives the actual-first positive Hahn
restriction. -/
theorem actualHahnPositiveRestrictionCadlag_stochasticIntegral_leftJump_lower_bound
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val)
    (hLLeft : ProcessHasLeftLimits L.val.stochasticIntegral)
    {c : Real} (hc : 0 <= c)
    (hJump : ∀ᵐ omega ∂mu, forall t,
      -c <= processLeftJump L.val.stochasticIntegral t omega) :
    ∀ᵐ omega ∂mu, forall t,
      -c <= processLeftJump
        (actualHahnPositiveRestrictionCadlag hGLeft P
          ).val.stochasticIntegral t omega := by
  have hResult : ∀ᵐ omega ∂mu, forall t,
      -c <= processLeftJump
        (actualRestrictPredictableCadlag hGLeft L
          P.positiveSet P.measurableSet_positiveSet
          ).val.stochasticIntegral t omega := by
    filter_upwards [
    actualRestrictPredictableCadlag_stochasticIntegral_leftJump hGLeft L hLLeft
      P.positiveSet P.measurableSet_positiveSet,
    hJump] with omega hRestrictionOmega hOriginalOmega
    intro t
    rw [hRestrictionOmega t]
    unfold predictableRestrictedLeftJump
    split_ifs
    · exact hOriginalOmega t
    · linarith
  simpa only [actualHahnPositiveRestrictionCadlag] using hResult

/-- Stop the actual-first positive Hahn restriction at a finite stopping
time, without leaving the intrinsic carrier. -/
noncomputable def actualStopHahnPositiveCadlag
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal))) :
    ActualSIntegrableStrategy (realizationModel G) :=
  actualFiniteClosedStop (actualHahnPositiveRestrictionCadlag hGLeft P) tau hTau

/-- The stopped actual-first Hahn gain starts from zero. -/
theorem actualStopHahnPositiveCadlag_stochasticIntegral_zero
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal))) :
    (actualStopHahnPositiveCadlag hGLeft P tau hTau
      ).val.stochasticIntegral 0 =ᵐ[mu] 0 := by
  filter_upwards [actualHahnPositiveRestrictionCadlag_stochasticIntegral_zero hGLeft P]
    with omega hZero
  change MeasureTheory.stoppedProcess
    (actualHahnPositiveRestrictionCadlag hGLeft P).val.stochasticIntegral
    (fun omega => (tau omega : WithTop NNReal)) 0 omega = 0
  rw [MeasureTheory.stoppedProcess_eq_of_le bot_le]
  exact hZero

/-- Stopping preserves the increasing finite-variation component of the
actual-first Hahn restriction. -/
theorem actualStopHahnPositiveCadlag_finiteVariation_increment_nonnegative
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal))) :
    ∀ᵐ omega ∂mu, ∀ a b, a <= b ->
      0 <= (actualStopHahnPositiveCadlag hGLeft P tau hTau
        ).val.finiteVariationPart b omega -
        (actualStopHahnPositiveCadlag hGLeft P tau hTau
          ).val.finiteVariationPart a omega := by
  let R := actualHahnPositiveRestrictionCadlag hGLeft P
  filter_upwards [actualHahnPositiveRestrictionCadlag_finiteVariation_increment_ae hGLeft P]
    with omega hIncreasing
  intro a b hab
  change 0 ≤ MeasureTheory.stoppedProcess R.val.finiteVariationPart
    (fun omega => (tau omega : WithTop NNReal)) b omega -
    MeasureTheory.stoppedProcess R.val.finiteVariationPart
      (fun omega => (tau omega : WithTop NNReal)) a omega
  rw [← RightContinuousStoppedMartingale.sample_boundedTime_eq_stoppedProcess,
    ← RightContinuousStoppedMartingale.sample_boundedTime_eq_stoppedProcess]
  apply (hIncreasing _ _ ?_).1
  apply WithTop.coe_le_coe.mp
  rw [RightContinuousStoppedMartingale.coe_boundedTime,
    RightContinuousStoppedMartingale.coe_boundedTime]
  exact min_le_min_right _ (WithTop.coe_le_coe.mpr hab)

/-- Both relevant components of the stopped actual-first Hahn graph have
left limits. -/
theorem actualStopHahnPositiveCadlag_hasLeftLimits
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal))) :
    ProcessHasLeftLimits
        (actualStopHahnPositiveCadlag hGLeft P tau hTau
          ).val.martingalePart /\
      ProcessHasLeftLimits
        (actualStopHahnPositiveCadlag hGLeft P tau hTau
          ).val.stochasticIntegral := by
  exact ⟨(actualHahnPositiveRestrictionCadlag_martingalePart_hasLeftLimits hGLeft P
      ).stoppedProcess _,
    (actualHahnPositiveRestrictionCadlag_stochasticIntegral_hasLeftLimits hGLeft P
      ).stoppedProcess _⟩

/-- The finite stopping time preserves a simultaneous lower jump bound of
the actual-first Hahn gain. -/
theorem actualStopHahnPositiveCadlag_stochasticIntegral_leftJump_lower_bound
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val)
    (hLLeft : ProcessHasLeftLimits L.val.stochasticIntegral)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    {c : Real} (hc : 0 <= c)
    (hJump : ∀ᵐ omega ∂mu, ∀ t,
      -c <= processLeftJump L.val.stochasticIntegral t omega) :
    ∀ᵐ omega ∂mu, ∀ t,
      -c <= processLeftJump
        (actualStopHahnPositiveCadlag hGLeft P tau hTau
          ).val.stochasticIntegral t omega := by
  let R := actualHahnPositiveRestrictionCadlag hGLeft P
  have hLeft := actualHahnPositiveRestrictionCadlag_stochasticIntegral_hasLeftLimits hGLeft P
  filter_upwards [actualHahnPositiveRestrictionCadlag_stochasticIntegral_leftJump_lower_bound
    hGLeft P hLLeft hc hJump] with omega hLower
  intro t
  change -c ≤ processLeftJump (MeasureTheory.stoppedProcess R.val.stochasticIntegral
    (fun omega => (tau omega : WithTop NNReal))) t omega
  by_cases ht : t ≤ tau omega
  · rw [processLeftJump_stoppedProcess_eq_of_le R.val.stochasticIntegral hLeft
      (fun omega => (tau omega : WithTop NNReal)) t omega (WithTop.coe_le_coe.mpr ht)]
    exact hLower t
  · rw [processLeftJump_stoppedProcess_eq_zero_of_lt R.val.stochasticIntegral
      (fun omega => (tau omega : WithTop NNReal)) t omega
      (WithTop.coe_lt_coe.mpr (lt_of_not_ge ht))]
    linarith

/-- The stopped actual-first Hahn restriction satisfies the martingale
increment contraction required by finite aggregation. -/
theorem actualStopHahnPositiveCadlag_martingale_l2
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (T : NNReal) (hTauT : forall omega, tau omega <= T)
    (hM : Martingale L.val.martingalePart F mu)
    (hMIncrement : MemLp
      (fun omega => L.val.martingalePart (tau omega) omega -
        L.val.martingalePart 0 omega) (2 : ENNReal) mu) :
    let U := actualStopHahnPositiveCadlag hGLeft P tau hTau
    Martingale U.val.martingalePart F mu /\
      MemLp (fun omega => U.val.martingalePart T omega -
        U.val.martingalePart 0 omega) (2 : ENNReal) mu /\
      (∫ omega, ‖U.val.martingalePart T omega -
        U.val.martingalePart 0 omega‖ ^ 2 ∂mu) <=
        ∫ omega, ‖L.val.martingalePart (tau omega) omega -
          L.val.martingalePart 0 omega‖ ^ 2 ∂mu := by
  exact actualRestrictPredictableCadlag_stopped_martingale_increment_l2 hGLeft L
    P.positiveSet P.measurableSet_positiveSet tau hTau T hTauT hM hMIncrement

end LocalCompletedM2A

end FTAPTheorem42
