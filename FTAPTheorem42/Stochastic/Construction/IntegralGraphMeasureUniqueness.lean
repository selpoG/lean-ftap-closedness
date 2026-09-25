/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Construction.JointComponentLocalization
import FTAPTheorem42.Stochastic.Integral.General.IntegralGraphTruncationConvergence

/-! # Original-source special graphs enter the general truncation graph

The source itself supplies the left limits needed for inclusion. In particular,
the stopped Mémín realizations now produce general graph certificates on the
constructed equivalent probability. Returning them to the original probability
still requires the bounded-graph measure-transfer theorem.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A global actual strategy retains its raw gain in the general graph. -/
theorem globalActual_isTruncated
    (source : BoundedSemimartingaleSource S F μ)
    (H : ActualSIntegrableStrategy (realizationModel (unitSource source))) :
    IsTruncatedIntegralGraph (unitSource source) H.val.integrand H.val.stochasticIntegral := by
  let _ := source.usualConditions.rightContinuous
  exact IsTruncatedIntegralGraph.of_globalActual
    (((sourceData source).regularizedDecomposition_spec.2.2.2.2.1).sub (.timeConstant _)) H

/-- The existing stopped Mémín realization is consumed as a general graph of
the same original price under the constructed equivalent probability. -/
theorem exists_stopped_truncatedRealization
    (source : BoundedSemimartingaleSource S F μ)
    (H : RealizedStrategy (ℱ := F) μ S) :
    ∃ (Q : Measure Ω), ∃ hQ : IsProbabilityMeasure Q, letI := hQ
    ∃ (sourceQ : BoundedSemimartingaleSource S F Q) (τ : Nat → Ω → NNReal)
      (K : Nat → Process Ω),
      Q ≪ μ ∧ μ ≪ Q ∧
      IsLocalizingSequence F (fun r ω => (τ r ω : WithTop NNReal)) Q ∧
      (∀ r ω, τ r ω ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ r, IsTruncatedIntegralGraph (unitSource sourceQ) (K r)
        (stoppedProcess H.gain (fun ω => (τ r ω : WithTop NNReal))) := by
  obtain ⟨Q, hQ, sourceQ, τ, V, hQμ, hμQ, hLoc, hτT, hV⟩ :=
    exists_stopped_actualRealization source H
  let : IsProbabilityMeasure Q := hQ
  refine ⟨Q, hQ, sourceQ, τ, fun r => (V r).val.integrand, hQμ, hμQ, hLoc, hτT, ?_⟩
  intro r
  obtain ⟨A⟩ := globalActual_isTruncated sourceQ (V r)
  exact ⟨{ A with gain_indistinguishable := A.gain_indistinguishable.trans (hV r) }⟩

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Uniqueness of existing integral certificates across equivalent measures

Both integral certificates are supplied. Common elementary approximants
identify their gains, without transferring either special decomposition.
-/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open LocalCompletedM2A SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

private theorem coordinate_emery_originalSource
    (source : BoundedSemimartingaleSource S F μ)
    (H : ActualSIntegrableStrategy (realizationModel (unitSource source)))
    (w : GraphWitness (unitSource source) H.val) (k : Nat)
    (J : Nat → PredictableElementaryStrategy F)
    {X : Process Ω} (hX : IsStronglyProgressive F X)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hXH : ProcessIndistinguishable μ X H.val.stochasticIntegral)
    (σ : Ω → NNReal) (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop NNReal)))
    (hσle : ∀ ω, (σ ω : WithTop NNReal) ≤ w.schedule.localizer k ω)
    (hConv : ElementaryEmeryConverges μ F
      (fun n => (J n).finiteHorizonGain (w.schedule.sourcePrefix k).stochasticIntegral
        (w.schedule.horizon k))
      (finiteHorizonCompletedM2AGain w.schedule.usualConditions (w.schedule.horizon k)
        (w.schedule.quadraticKernel k) (w.schedule.variationBridge k)
        (w.schedule.martingale k) (w.schedule.terminal_memLp k) (w.coefficient k))) :
    ElementaryEmeryConverges μ F
      (fun n => stoppedProcess (ElementaryStrategy.gain S (J n).toElementary)
        (fun ω => (σ ω : WithTop NNReal)))
      (stoppedProcess X (fun ω => (σ ω : WithTop NNReal))) := by
  let Z n := ElementaryStrategy.gain S (J n).toElementary
  have hCenter n : ElementaryStrategy.gain (unitSource source).stochasticIntegral
      (J n).toElementary = Z n := by
    change ElementaryStrategy.gain (fun t ω => S t ω - S 0 ω) _ = _
    exact ElementaryStrategy.gain_sub_initial S _
  have hOriginal : ElementaryEmeryConverges μ F
      (fun n => stoppedProcess (Z n) (w.schedule.localizer k))
      (stoppedProcess X (w.schedule.localizer k)) := by
    have hSeq := hConv.congr_sequence (fun n => w.schedule.elementaryGain_sourcePrefix k (J n))
    simp only [hCenter] at hSeq
    exact hSeq.congr_limit ((w.stoppedGain_eq k).symm.trans
      (hXH.symm.stoppedProcess (w.schedule.localizer k)))
  have hZ n : IsStronglyProgressive F (Z n) :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      ((J n).stronglyAdapted_gain S
        (StronglyAdapted.isStronglyProgressive_of_rightContinuous
          source.stronglyAdapted source.rightContinuous))
      ((J n).rightContinuous_gain S source.rightContinuous)
  have hFin := hOriginal.finiteStopped
    (fun n => (hZ n).stoppedProcess (w.schedule.isLocalizingSequence.isStoppingTime k))
    (hX.stoppedProcess (w.schedule.isLocalizingSequence.isStoppingTime k))
    (fun n => RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
      ((J n).rightContinuous_gain S source.rightContinuous))
    (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _ hXR) σ hσ
  simpa only [stoppedProcess_stoppedProcess_of_le_right hσle] using hFin

/-- Two existing bounded global integral certificates of the same original
price and coefficient have indistinguishable gains across equivalent
probabilities. This is uniqueness, not existence of a transported certificate. -/
theorem globalActual_gain_indistinguishable_of_equivalentMeasure
    {ν : Measure Ω} [IsProbabilityMeasure ν] [SigmaFiniteFiltration ν F]
    (source : BoundedSemimartingaleSource S F μ)
    (source' : BoundedSemimartingaleSource S F ν)
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (H : ActualSIntegrableStrategy (realizationModel (unitSource source)))
    (H' : ActualSIntegrableStrategy (realizationModel (unitSource source')))
    (hCoeff : H.val.integrand = H'.val.integrand)
    (b : Real) (hBound : ∀ t ω, |H.val.integrand t ω| ≤ b) :
    ProcessIndistinguishable μ H.val.stochasticIntegral H'.val.stochasticIntegral := by
  obtain ⟨w⟩ := H.property
  obtain ⟨w'⟩ := H'.property
  obtain ⟨X, hXA, hXR, _hXL, hXH⟩ := w.exists_cadlagGain
    (((sourceData source).regularizedDecomposition_spec.2.2.2.2.1).sub (.timeConstant _))
  obtain ⟨Y, hYA, hYR, _hYL, hYH⟩ := w'.exists_cadlagGain
    (((sourceData source').regularizedDecomposition_spec.2.2.2.2.1).sub (.timeConstant _))
  have hX := StronglyAdapted.isStronglyProgressive_of_rightContinuous hXA hXR
  have hY := StronglyAdapted.isStronglyProgressive_of_rightContinuous hYA hYR
  let σ : Nat → Ω → NNReal := fun k ω =>
    min (scheduleFiniteLocalizer w.schedule k ω) (scheduleFiniteLocalizer w'.schedule k ω)
  have hσeq k ω : (σ k ω : WithTop NNReal) =
      min (w.schedule.localizer k ω) (w'.schedule.localizer k ω) := by
    simp only [σ, WithTop.coe_min, coe_scheduleFiniteLocalizer]
  have hσ : IsLocalizingSequence F (fun k ω => (σ k ω : WithTop NNReal)) μ := {
    isStoppingTime := fun k => by
      simpa only [hσeq] using (w.schedule.isLocalizingSequence.isStoppingTime k).min
        (w'.schedule.isLocalizingSequence.isStoppingTime k)
    tendsto_top := by
      filter_upwards [w.schedule.isLocalizingSequence.tendsto_top,
        hμν.ae_le w'.schedule.isLocalizingSequence.tendsto_top] with ω hω hω'
      simpa only [hσeq, min_self] using hω.min hω'
    mono := by
      filter_upwards [w.schedule.isLocalizingSequence.mono,
        hμν.ae_le w'.schedule.isLocalizingSequence.mono] with ω hω hω'
      simpa only [hσeq, min_self] using hω.min hω' }
  have hXY : ProcessIndistinguishable μ X Y := by
    apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence hσ
    intro k
    have hCoeffK : (w.coefficient k).coefficient = (w'.coefficient k).coefficient := by
      rw [w.coefficient_eq k, w'.coefficient_eq k, hCoeff]
    have hBoundK p : |(w.coefficient k).coefficient p| ≤ b := by
      rw [w.coefficient_eq k]
      exact hBound p.1 p.2
    obtain ⟨J, C, _hC, hConv, hConv'⟩ := exists_commonElementarySequence_emery
      w.schedule.usualConditions w'.schedule.usualConditions
      (w.schedule.quadraticKernel k) (w'.schedule.quadraticKernel k)
      (w.schedule.martingale k) (w.schedule.terminal_memLp k)
      (w'.schedule.martingale k) (w'.schedule.terminal_memLp k)
      (w.coefficient k) (w'.coefficient k) hCoeffK b hBoundK
    have hLeft := coordinate_emery_originalSource source H w k J hX hXR hXH
      (σ k) (hσ.isStoppingTime k) (fun ω => by rw [hσeq]; exact min_le_left _ _) hConv
    have hRight := coordinate_emery_originalSource source' H' w' k J hY hYR hYH
      (σ k) (hσ.isStoppingTime k) (fun ω => by rw [hσeq]; exact min_le_right _ _) hConv'
    have hJ n : IsStronglyProgressive F (stoppedProcess
        (ElementaryStrategy.gain S (J n).toElementary) (fun ω => (σ k ω : WithTop NNReal))) :=
      (StronglyAdapted.isStronglyProgressive_of_rightContinuous
        ((J n).stronglyAdapted_gain S
          (StronglyAdapted.isStronglyProgressive_of_rightContinuous
            source.stronglyAdapted source.rightContinuous))
        ((J n).rightContinuous_gain S source.rightContinuous)).stoppedProcess (hσ.isStoppingTime k)
    have hYStop := hY.stoppedProcess (hσ.isStoppingTime k)
    have hRightMu := hRight.of_equivalentMeasure hJ hYStop hνμ hμν
    apply ElementaryEmeryConverges.limit_indistinguishable hJ
      (hX.stoppedProcess (hσ.isStoppingTime k)) hYStop
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _ hXR)
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _ hYR) _ hLeft hRightMu
    have hX0 := (hXH.eventuallyEq_at 0).trans w.stochasticIntegral_zero
    have hY0 := (hYH.eventuallyEq_at 0).trans w'.stochasticIntegral_zero
    filter_upwards [hX0, hμν.ae_le hY0] with ω hx hy
    change X (min 0 (σ k ω)) ω = Y (min 0 (σ k ω)) ω
    have hz : (0 : NNReal) ≤ σ k ω := zero_le
    rw [min_eq_left hz]
    exact hx.trans hy.symm
  exact hXH.symm.trans (hXY.trans (hμν.ae_le hYH))

/-- Deterministic stopping extends cross-measure uniqueness to existing
local bounded certificates, without a common global coefficient schedule. -/
theorem actualLocal_gain_indistinguishable_of_equivalentMeasure
    {ν : Measure Ω} [IsProbabilityMeasure ν] [SigmaFiniteFiltration ν F]
    (source : BoundedSemimartingaleSource S F μ)
    (source' : BoundedSemimartingaleSource S F ν)
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (H : ActualLocallySIntegrableStrategy (realizationModel (unitSource source)))
    (H' : ActualLocallySIntegrableStrategy (realizationModel (unitSource source')))
    (hCoeff : H.val.integrand = H'.val.integrand)
    (b : Real) (hBound : ∀ t ω, |H.val.integrand t ω| ≤ b) :
    ProcessIndistinguishable μ H.val.stochasticIntegral H'.val.stochasticIntegral := by
  let τ : Nat → Ω → WithTop NNReal := fun n _ => (((n + 1 : Nat) : NNReal) : WithTop NNReal)
  have hτ : IsLocalizingSequence F τ μ := {
    isStoppingTime := fun n => isStoppingTime_const F ((n + 1 : Nat) : NNReal)
    tendsto_top := Eventually.of_forall fun _ => WithTop.tendsto_coe_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    mono := Eventually.of_forall fun _ n m hnm => by
      dsimp only [τ]
      exact_mod_cast Nat.add_le_add_right hnm 1 }
  apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence hτ
  intro n
  let T : NNReal := (n + 1 : Nat)
  have hT : 0 < T := by dsimp only [T]; positivity
  let A := H.deterministicallyStopped T hT
  let A' := H'.deterministicallyStopped T hT
  have hCoeffA : A.val.integrand = A'.val.integrand := by
    change PredictableProcess.restrict _ H.val.integrand =
      PredictableProcess.restrict _ H'.val.integrand
    rw [hCoeff]
  have hBoundA : ∀ t ω, |A.val.integrand t ω| ≤ max b 0 := by
    intro t ω
    change |PredictableProcess.restrict (stochasticIntervalIocZero (fun _ : Ω => T))
      H.val.integrand t ω| ≤ _
    by_cases ht : (t, ω) ∈ stochasticIntervalIocZero (fun _ : Ω => T)
    · rw [PredictableProcess.restrict_apply_of_mem ht]
      exact (hBound t ω).trans (le_max_left _ _)
    · rw [PredictableProcess.restrict_apply_of_notMem ht, abs_zero]
      exact le_max_right _ _
  exact globalActual_gain_indistinguishable_of_equivalentMeasure source source' hμν hνμ
    A A' hCoeffA (max b 0) hBoundA

end FTAPTheorem42.BoundedSourceIntegralMarket
