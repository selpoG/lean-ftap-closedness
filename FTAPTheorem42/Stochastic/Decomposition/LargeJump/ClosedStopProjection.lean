/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.BoundaryIntegrable
import FTAPTheorem42.Stochastic.Decomposition.Compensator.FiniteLargeJumpB3

/-!
# Closed finite-large-jump variation slices

This module closes one strict-prefix variation slice at a finite refined stop.
The refinement also lies below one localizing coordinate and one càdlàg
absolute-passage localizer.  The closed stopped path is sent directly to the
`L¹` finite-variation value-truncation consumer; no comparison between levels
is asserted here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open FTAPTheorem42.SIntegrableFiniteVariationBridge
open FTAPTheorem42.FiniteLargeJumpProcess

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The retained closed-stop certificate -/

structure FiniteLargeJumpClosedStopProjectionData
    {X : Process Ω} {c : Real} {T : NNReal}
    (hX : LocalMartingale X F mu)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T) (n : ℕ) where
  tau : Ω → NNReal
  tau_isStoppingTime : IsStoppingTime F
    (fun omega => (tau omega : WithTop NNReal))
  tau_le_slice : ∀ omega,
    tau omega ≤ (family.data n).rho omega
  tau_le_localizing : ∀ omega,
    (tau omega : WithTop NNReal) ≤ hX.localSeq n omega
  tau_le_passage : ∀ omega,
    (tau omega : WithTop NNReal) ≤
      absoluteStrictHittingAfter X (cadlagPassageLevel n) omega
  tau_le_horizon : ∀ omega,
    tau omega ≤ finiteLargeJumpVariationHorizon T n
  tau_coe_eq_refined :
    (fun omega => (tau omega : WithTop NNReal)) =
      (fun omega => min ((family.data n).rho omega : WithTop NNReal)
        (min (hX.localSeq n omega)
          (cadlagAbsolutePassageLocalizer X n omega)))
  closed : Process Ω
  closed_eq_stopped :
    closed = MeasureTheory.stoppedProcess
      (FiniteLargeJumpProcess.process X c T)
      (fun omega => (tau omega : WithTop NNReal))
  source_data : NormalizedAdaptedCadlagFiniteVariationL1Data
    (F := F) (mu := mu) closed (finiteLargeJumpVariationHorizon T n)
  projection : ValueTruncationFiniteVariationPredictableLimit
    (F := F) (mu := mu) closed (finiteLargeJumpVariationHorizon T n)

/-! ## The canonical variation-level bound -/

omit [SigmaFiniteFiltration mu F] in
private theorem strictPrefix_before_variationLevel_of_slice
    {A : Process Ω} {T : NNReal} {n : ℕ}
    (slice : VariationLevelFiniteVariationProjectionSlice
      (F := F) (mu := mu) A T n)
    (omega : Ω) {t : NNReal} (ht : t < slice.rho omega) :
    variationOnFromTo (A · omega) Set.univ 0 t ≤
      (variationLevel n : Real) := by
  have hHit : (t : WithTop NNReal) <
      variationLevelHittingTime A (variationLevel n) omega := by
    have ht' : (t : WithTop NNReal) <
        min (variationLevelHittingTime A (variationLevel n) omega)
          (finiteLargeJumpVariationHorizon T n : WithTop NNReal) := by
      rw [← congrFun (coe_variationLevelStop A (variationLevel n)
        (finiteLargeJumpVariationHorizon T n)) omega,
        ← congrFun slice.rho_eq_variationLevelStop omega]
      exact WithTop.coe_lt_coe.mpr ht
    exact ht'.trans_le (min_le_left _ _)
  have hNot := MeasureTheory.notMem_of_lt_hittingAfter
    (u := localVariation A)
    (s := Set.Ioi (variationLevel n : Real))
    (n := (0 : NNReal)) (ω := omega) (k := t) hHit bot_le
  exact le_of_not_gt hNot

/-! ## Variation of the closed boundary correction -/

omit [MeasurableSpace Ω] in
private theorem stoppedProcess_cumulativeVariation_le_strictPrefix_add_boundary
    {A : Process Ω} {tau : Ω → NNReal} {H : NNReal}
    (hTauH : ∀ omega, tau omega ≤ H)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ) :
    ∀ omega,
      localVariation
          (MeasureTheory.stoppedProcess A
            (fun omega => (tau omega : WithTop NNReal))) H omega ≤
        (eVariationOn (strictPrefixProcess A tau · omega)
          (Icc 0 H)).toReal +
          |boundaryJumpProcess A tau H omega| := by
  intro omega
  have hCVar : BoundedVariationOn
      (strictPrefixProcess A tau · omega) Set.univ :=
    strictPrefixProcess_boundedVariation A tau hAVar omega
  have hCNeTop : eVariationOn
      (strictPrefixProcess A tau · omega) (Icc 0 H) ≠ ∞ :=
    ne_top_of_le_ne_top hCVar (eVariationOn.mono _ (Set.subset_univ _))
  have hPath :
      (fun t => MeasureTheory.stoppedProcess A
        (fun omega => (tau omega : WithTop NNReal)) t omega) =
        (fun t => strictPrefixProcess A tau t omega +
          boundaryJumpProcess A tau t omega) := by
    funext t
    have h := strictPrefixProcess_add_postStopSampled_processLeftJump
      A tau t omega
    dsimp [boundaryJumpProcess]
    exact h.symm
  have hVariation : eVariationOn
      (fun t => MeasureTheory.stoppedProcess A
        (fun omega => (tau omega : WithTop NNReal)) t omega)
          (Icc 0 H) ≤
      eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 H) +
        ENNReal.ofReal |boundaryJumpProcess A tau H omega| := by
    rw [hPath]
    calc
      eVariationOn (fun t => strictPrefixProcess A tau t omega +
          boundaryJumpProcess A tau t omega) (Icc 0 H) ≤
          eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 H) +
            eVariationOn (boundaryJumpProcess A tau · omega) (Icc 0 H) :=
        eVariationOn_add_le_real _ _ _
      _ ≤ eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 H) +
          ENNReal.ofReal |boundaryJumpProcess A tau H omega| :=
        add_le_add le_rfl
          (boundaryJumpProcess_eVariationOn_Icc_le hTauH omega)
  have hRhsNeTop : eVariationOn
      (strictPrefixProcess A tau · omega) (Icc 0 H) +
        ENNReal.ofReal |boundaryJumpProcess A tau H omega| ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hCNeTop, ENNReal.ofReal_ne_top⟩
  have hClosedNeTop : eVariationOn
      (fun t => MeasureTheory.stoppedProcess A
        (fun omega => (tau omega : WithTop NNReal)) t omega)
          (Icc 0 H) ≠ ∞ :=
    ne_top_of_le_ne_top hRhsNeTop hVariation
  have hToReal := (ENNReal.toReal_le_toReal hClosedNeTop hRhsNeTop).2
    hVariation
  have hRhsToReal :
      (eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 H) +
        ENNReal.ofReal |boundaryJumpProcess A tau H omega|).toReal =
        (eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 H)).toReal +
          |boundaryJumpProcess A tau H omega| := by
    rw [ENNReal.toReal_add hCNeTop ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (abs_nonneg _)]
  have hCommon : localVariation
        (MeasureTheory.stoppedProcess A
          (fun omega => (tau omega : WithTop NNReal))) H omega =
      (eVariationOn (fun t => MeasureTheory.stoppedProcess A
        (fun omega => (tau omega : WithTop NNReal)) t omega)
          (Icc 0 H)).toReal := by
    rw [commonStopCumulativeVariation_apply,
      variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ H from bot_le),
      Set.univ_inter]
  calc
    localVariation
        (MeasureTheory.stoppedProcess A
          (fun omega => (tau omega : WithTop NNReal))) H omega =
        (eVariationOn (fun t => MeasureTheory.stoppedProcess A
          (fun omega => (tau omega : WithTop NNReal)) t omega)
            (Icc 0 H)).toReal := hCommon
    _ ≤ (eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 H) +
          ENNReal.ofReal |boundaryJumpProcess A tau H omega|).toReal := hToReal
    _ = (eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 H)).toReal +
          |boundaryJumpProcess A tau H omega| := hRhsToReal

/-! ## The direct closed-stop consumer -/

theorem exists_finiteLargeJumpClosedStopProjectionData
    [F.IsRightContinuous]
    {X : Process Ω} {c : Real} {T : NNReal}
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (hXZero : X 0 = 0)
    (hc : 0 < c)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T)
    (hUsual : Filtration.UsualConditions mu F)
    (n : ℕ) :
    Nonempty (FiniteLargeJumpClosedStopProjectionData hX family n) := by
  change ProbabilityTheory.Locally
      (fun Y : Process Ω => MeasureTheory.Martingale Y F mu) F X mu at hX
  let A : Process Ω := FiniteLargeJumpProcess.process X c T
  let H : NNReal := finiteLargeJumpVariationHorizon T n
  let rhoTop : Ω → WithTop NNReal := fun omega =>
    min ((family.data n).rho omega : WithTop NNReal)
      (min (hX.localSeq n omega)
        (cadlagAbsolutePassageLocalizer X n omega))
  have hRhoStopping : IsStoppingTime F rhoTop := by
    dsimp [rhoTop]
    exact (family.rho_isStoppingTime n).min
      ((hX.isLocalizingSequence_localSeq.isStoppingTime n).min
        ((cadlagAbsolutePassageLocalizer_isLocalizingSequence
          (mu := mu) hXAdapted hXRight hXLeft).isStoppingTime n))
  have hRhoFinite : ∀ omega, rhoTop omega ≠ (⊤ : WithTop NNReal) := by
    intro omega
    apply ne_top_of_le_ne_top
      (WithTop.coe_ne_top :
        ((family.data n).rho omega : WithTop NNReal) ≠ ⊤)
    exact min_le_left _ _
  let tau : Ω → NNReal := fun omega =>
    (rhoTop omega).untop (hRhoFinite omega)
  have hTauCoe :
      (fun omega => (tau omega : WithTop NNReal)) = rhoTop := by
    funext omega
    dsimp [tau]
    exact WithTop.coe_untop _ (hRhoFinite omega)
  have hTauStopping : IsStoppingTime F
      (fun omega => (tau omega : WithTop NNReal)) := by
    rw [hTauCoe]
    exact hRhoStopping
  have hTauSliceTop : ∀ omega,
      (tau omega : WithTop NNReal) ≤
        (family.data n).rho omega := by
    intro omega
    rw [show (tau omega : WithTop NNReal) = rhoTop omega from
      congrFun hTauCoe omega]
    exact min_le_left _ _
  have hTauSlice : ∀ omega,
      tau omega ≤ (family.data n).rho omega := by
    intro omega
    exact WithTop.coe_le_coe.mp (hTauSliceTop omega)
  have hTauLocal : ∀ omega,
      (tau omega : WithTop NNReal) ≤ hX.localSeq n omega := by
    intro omega
    rw [show (tau omega : WithTop NNReal) = rhoTop omega from
      congrFun hTauCoe omega]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hTauPassage : ∀ omega,
      (tau omega : WithTop NNReal) ≤
        absoluteStrictHittingAfter X (cadlagPassageLevel n) omega := by
    intro omega
    calc
      (tau omega : WithTop NNReal) ≤
          cadlagAbsolutePassageLocalizer X n omega := by
        rw [show (tau omega : WithTop NNReal) = rhoTop omega from
          congrFun hTauCoe omega]
        exact (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ absoluteStrictHittingAfter X (cadlagPassageLevel n) omega := by
        dsimp [cadlagAbsolutePassageLocalizer]
        exact min_le_left _ _
  have hTauH : ∀ omega, tau omega ≤ H := by
    intro omega
    exact (hTauSlice omega).trans (by
      simpa only [H] using family.rho_le_horizon n omega)
  have hAAdapted : StronglyAdapted F A := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.stronglyAdapted_process
      hXAdapted hXRight hXLeft hc T
  have hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_rightContinuous hXRight hXLeft hc
  have hALeft : ProcessHasLeftLimits A := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_hasLeftLimits hXRight hXLeft hc
  have hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_boundedVariationOn_univ
      hXRight hXLeft hc
  have hAzero : A 0 = 0 := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_zero hXRight hXLeft hc
  have hBefore : ∀ omega t, t < tau omega →
      variationOnFromTo (A · omega) Set.univ 0 t ≤
        (variationLevel n : Real) := by
    intro omega t ht
    exact strictPrefix_before_variationLevel_of_slice
      (family.data n) omega (lt_of_lt_of_le ht (hTauSlice omega))
  have hStrictBound : ∀ omega,
      localVariation
          (strictPrefixProcess A tau) H omega ≤
        (variationLevel n : Real) := by
    exact strictPrefixProcess_cumulativeVariation_bound_of_before
      A tau (variationLevel n) H hAVar hBefore
  let closed : Process Ω := MeasureTheory.stoppedProcess A
    (fun omega => (tau omega : WithTop NNReal))
  have hClosedPath : ∀ omega,
      (closed · omega) =
        (fun t => strictPrefixProcess A tau t omega +
          boundaryJumpProcess A tau t omega) := by
    intro omega
    dsimp [closed]
    funext t
    have h := strictPrefixProcess_add_postStopSampled_processLeftJump
      A tau t omega
    dsimp [boundaryJumpProcess]
    exact h.symm
  have hClosedAdapted : StronglyAdapted F closed := by
    dsimp only [closed]
    exact RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hAAdapted hTauStopping hARight
  have hClosedRight : ∀ omega t,
      ContinuousWithinAt (closed · omega) (Ici t) t := by
    dsimp only [closed]
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous A hARight
  have hClosedLeft : ProcessHasLeftLimits closed := by
    dsimp only [closed]
    exact hALeft.stoppedProcess
      (fun omega => (tau omega : WithTop NNReal))
  have hClosedVar : ∀ omega,
      BoundedVariationOn (closed · omega) Set.univ := by
    intro omega
    rw [hClosedPath omega]
    exact boundedVariationOn_add
      (strictPrefixProcess_boundedVariation A tau hAVar omega)
      (boundaryJumpProcess_boundedVariation A tau omega)
  have hClosedZero : closed 0 = 0 := by
    funext omega
    dsimp [closed]
    change MeasureTheory.stoppedProcess A
        (fun omega => (tau omega : WithTop NNReal)) 0 omega = 0
    rw [MeasureTheory.stoppedProcess_eq_of_le bot_le]
    exact congrFun hAzero omega
  have hClosedConstant : ∀ omega t, H ≤ t →
      closed t omega = closed H omega := by
    intro omega t htt
    dsimp [closed]
    change MeasureTheory.stoppedProcess A
        (fun omega => (tau omega : WithTop NNReal)) t omega =
      MeasureTheory.stoppedProcess A
        (fun omega => (tau omega : WithTop NNReal)) H omega
    rw [stoppedProcess_eq_of_ge A tau ((hTauH omega).trans htt),
      stoppedProcess_eq_of_ge A tau (hTauH omega)]
  have hStrictVariationMeas : Measurable (fun omega =>
      eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 H)) :=
    measurable_strictPrefixVariation_of_regularProcess A tau H
      hAAdapted hARight hALeft hTauStopping
  have hStrictVariationPoint : ∀ omega,
      (eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 H)).toReal ≤
        (variationLevel n : Real) := by
    intro omega
    have hCommon : localVariation
          (strictPrefixProcess A tau) H omega =
        (eVariationOn (strictPrefixProcess A tau · omega)
          (Icc 0 H)).toReal := by
      rw [commonStopCumulativeVariation_apply,
        variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ H from bot_le),
        Set.univ_inter]
    rw [← hCommon]
    exact hStrictBound omega
  have hStrictVariationIntegrable : Integrable (fun omega =>
      (eVariationOn (strictPrefixProcess A tau · omega)
        (Icc 0 H)).toReal) mu := by
    apply Integrable.of_bound (μ := mu)
      hStrictVariationMeas.ennreal_toReal.aestronglyMeasurable
        (variationLevel n : Real)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hStrictVariationPoint omega
  have hJumpIntegrable : Integrable (fun omega =>
      |boundaryJumpProcess A tau H omega|) mu := by
    have hJump :=
      integrable_processLeftJump_at_boundedStoppingTime_of_localizing_and_hitting
        (X := X) (c := c) (T := T) (H := H)
        (r := cadlagPassageLevel n)
        hX hXAdapted hXRight hXLeft hXZero hc
        (cadlagPassageLevel_nonnegative n) hTauStopping n hTauLocal
        hTauPassage hTauH
    have hBoundaryEq : (fun omega => boundaryJumpProcess A tau H omega) =
        (fun omega => processLeftJump A (tau omega) omega) := by
      funext omega
      exact boundaryJumpProcess_at_horizon_eq_processLeftJump hTauH omega
    have hBoundaryEqAbs : (fun omega =>
        |boundaryJumpProcess A tau H omega|) = (fun omega =>
          |processLeftJump A (tau omega) omega|) := by
      funext omega
      exact congrArg abs (congrFun hBoundaryEq omega)
    rw [hBoundaryEqAbs]
    simpa only [A, Real.norm_eq_abs] using hJump.norm
  have hClosedVariationBound : ∀ omega,
      localVariation closed H omega ≤
        (eVariationOn (strictPrefixProcess A tau · omega)
          (Icc 0 H)).toReal +
          |boundaryJumpProcess A tau H omega| := by
    dsimp only [closed]
    exact stoppedProcess_cumulativeVariation_le_strictPrefix_add_boundary
      hTauH hAVar
  have hClosedVariationMeas :
      Measurable (localVariation closed H) :=
    measurable_commonStopCumulativeVariation_of_regularProcess
      hClosedAdapted hClosedRight
  have hClosedVariationIntegrable :
      Integrable (localVariation closed H) mu := by
    have hRhsIntegrable : Integrable (fun omega =>
        (eVariationOn (strictPrefixProcess A tau · omega)
          (Icc 0 H)).toReal +
          |boundaryJumpProcess A tau H omega|) mu :=
      hStrictVariationIntegrable.add hJumpIntegrable
    apply hRhsIntegrable.mono hClosedVariationMeas.aestronglyMeasurable
    filter_upwards [] with omega
    have hClosedNonnegative :
        0 ≤ localVariation closed H omega := by
      rw [commonStopCumulativeVariation_apply]
      exact variationOnFromTo.nonneg_of_le _ _ bot_le
    have hRhsNonnegative : 0 ≤
        (eVariationOn (strictPrefixProcess A tau · omega)
          (Icc 0 H)).toReal +
          |boundaryJumpProcess A tau H omega| :=
      add_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hClosedNonnegative,
      Real.norm_eq_abs, abs_of_nonneg hRhsNonnegative]
    exact hClosedVariationBound omega
  have hClosedData : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) closed H := {
    stronglyAdapted := hClosedAdapted
    rightContinuous := hClosedRight
    hasLeftLimits := hClosedLeft
    boundedVariation := hClosedVar
    zero := hClosedZero
    constant_after := hClosedConstant
    terminalVariation_integrable := hClosedVariationIntegrable }
  obtain ⟨projection⟩ :=
    exists_valueTruncationFiniteVariationPredictableLimit
      (F := F) (mu := mu) hClosedData hUsual
  refine ⟨{
    tau := tau
    tau_isStoppingTime := hTauStopping
    tau_le_slice := hTauSlice
    tau_le_localizing := hTauLocal
    tau_le_passage := hTauPassage
    tau_le_horizon := by simpa only [H] using hTauH
    tau_coe_eq_refined := by simpa only [rhoTop] using hTauCoe
    closed := closed
    closed_eq_stopped := by
      dsimp only [closed, A]
    source_data := by simpa only [H] using hClosedData
    projection := by simpa only [H] using projection }⟩

end HorizonFactorialGrid

end FTAPTheorem42
