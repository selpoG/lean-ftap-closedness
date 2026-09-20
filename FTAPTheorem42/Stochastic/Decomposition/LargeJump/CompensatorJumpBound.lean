/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.GlobalDecomposition
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.Residual
import FTAPTheorem42.Stochastic.Predictable.PredictableCompensatorConstantJumpBound
import FTAPTheorem42.Foundations.MaximalProbability

/-!
# The predictable compensator jump bound for finite large jumps

The raw unit record below is used solely to enumerate the jumps of `-P`.
It makes no assertion of membership in an original-source integral carrier.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace FTAPTheorem42.HorizonFactorialGrid.FiniteLargeJumpClosedStopFamily

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {c : Real} {T : NNReal}
  {hX : LocalMartingale X F mu}
  {family : FiniteLargeJumpValueTruncationFamily (F := F) (mu := mu) X c T}
  {closedFamily : FiniteLargeJumpClosedStopFamily hX family}
  {hUsual : Filtration.UsualConditions mu F}

namespace GlobalDecompositionData

/-- The compensator of the finite large jumps has jumps bounded by the same
constant as the small-jump residual, on one full-measure set. -/
theorem abs_predictableCompensator_leftJump_le
    (d : GlobalDecompositionData hX family closedFamily hUsual)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T → |processLeftJump d.P t omega| ≤ c := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  by_cases hT : 0 < T
  swap
  · have hTZero : T = 0 := le_antisymm (le_of_not_gt hT) bot_le
    exact Eventually.of_forall fun omega t ht => by
      have htZero : t = 0 := le_antisymm (hTZero ▸ ht) bot_le
      subst t
      unfold processLeftJump
      rw [show Function.leftLim (fun s => d.P s omega) 0 = d.P 0 omega from
        leftLim_eq_of_isBot isBot_bot, sub_self, abs_zero]
      exact hc.le
  let L : Process Ω := fun t omega => X t omega - d.Q t omega
  let A : Process Ω := fun t omega => -d.P t omega
  let R := FiniteLargeJumpProcess.smallJumpResidual X c T
  have hLLocal : LocalMartingale L F mu := by
    simpa only [L, sub_eq_add_neg] using
      hX.add_of_rightContinuous d.Q_isLocalMartingale.neg hXRight
        (fun omega t => (d.Q_rightContinuous omega t).neg)
  have hLRight : ∀ omega t, ContinuousWithinAt (L · omega) (Ici t) t :=
    fun omega t => (hXRight omega t).sub (d.Q_rightContinuous omega t)
  have hAPred : IsStronglyPredictable F A := d.P_isStronglyPredictable.neg
  have hAVar : ∀ omega, LocallyBoundedVariationOn (A · omega) univ := by
    intro omega a b ha hb
    exact boundedVariationOn_neg (d.P_locallyBoundedVariation omega a b ha hb)
  have hRA : ProcessIndistinguishable mu R (fun t omega => L t omega + A t omega) := by
    apply Eventually.of_forall
    intro omega t
    dsimp [R, L, A, FiniteLargeJumpProcess.smallJumpResidual]
    rw [d.Q_definition]
    dsimp only
    ring
  let D : SpecialSemimartingaleDecomposition R F mu := {
    martingalePart := L
    finiteVariationPart := A
    martingalePart_isLocalMartingale := hLLocal
    finiteVariationPart_isPredictable := hAPred
    finiteVariationPart_isLocallyBoundedVariation := hAVar
    decomposition := hRA }
  let H : LocallySIntegrableStrategy D := {
    integrand := PredictableProcess.unit
    stochasticIntegral := R
    martingalePart := L
    finiteVariationPart := A
    integrand_isPredictable := PredictableProcess.isStronglyPredictable_unit
    stochasticIntegral_isStronglyAdapted :=
      FiniteLargeJumpProcess.smallJumpResidual_stronglyAdapted hXAdapted hXRight hXLeft hc
    stochasticIntegral_isRightContinuous :=
      FiniteLargeJumpProcess.smallJumpResidual_rightContinuous hXRight hXLeft hc
    martingalePart_isLocalMartingale := hLLocal
    martingalePart_isStronglyAdapted := hXAdapted.sub d.Q_isStronglyAdapted
    martingalePart_isRightContinuous := hLRight
    finiteVariationPart_isPredictable := hAPred
    finiteVariationPart_isRightContinuous := fun omega t => (d.P_rightContinuous omega t).neg
    finiteVariationPart_isLocallyBoundedVariation := hAVar
    integral_decomposition := hRA
    source_decomposition := hRA }
  let HT := H.deterministicallyStopped T hT
  have hRLeft : ProcessHasLeftLimits R :=
    FiniteLargeJumpProcess.smallJumpResidual_hasLeftLimits hXRight hXLeft hc
  have hStopEq : HT.stochasticIntegral = MeasureTheory.stoppedProcess R
      (fun _ : Ω => (T : WithTop NNReal)) := by
    funext t omega
    exact (stoppedProcess_const_apply R T t omega).symm
  have hRJump : ∀ᵐ omega ∂mu, ∀ t,
      |processLeftJump HT.stochasticIntegral t omega| ≤ c := by
    rw [hStopEq]
    apply Eventually.of_forall
    intro omega
    apply abs_processLeftJump_stoppedProcess_le_of_le_horizon_at
      R hRLeft (fun _ => (T : WithTop NNReal)) T (fun _ => c) omega le_rfl hc.le
    intro t ht
    by_cases htZero : t = 0
    · subst t
      unfold processLeftJump
      rw [show Function.leftLim (fun s => R s omega) 0 = R 0 omega from
        leftLim_eq_of_isBot isBot_bot, sub_self, abs_zero]
      exact hc.le
    · exact FiniteLargeJumpProcess.abs_smallJumpResidual_processLeftJump_le
        hXRight hXLeft hc ⟨(pos_iff_ne_zero).2 htZero, ht⟩
  have hML : ProcessHasLeftLimits HT.martingalePart :=
    (hXLeft.sub d.Q_leftLimits).deterministicallyStopped T
  have hBound := HT.abs_finiteVariationLeftJump_le_const hUsual hML hc.le hT hRJump
  have hPLeft :=
    SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      d.P_locallyBoundedVariation
  have hAJump : ∀ t omega, processLeftJump A t omega = -processLeftJump d.P t omega := by
    intro t omega
    simpa only [neg_one_mul] using processLeftJump_const_mul hPLeft (-1) t omega
  have hAStopEq : HT.finiteVariationPart = MeasureTheory.stoppedProcess A
      (fun _ : Ω => (T : WithTop NNReal)) := by
    funext t omega
    exact (stoppedProcess_const_apply A T t omega).symm
  have hALeft : ProcessHasLeftLimits A := by
    simpa only [neg_one_mul] using hPLeft.const_mul (-1)
  filter_upwards [hBound] with omega hOmega
  intro t ht
  have h := hOmega t ht
  rw [hAStopEq, processLeftJump_stoppedProcess_eq_of_le
    A hALeft _ t omega (WithTop.coe_le_coe.mpr ht), hAJump, abs_neg] at h
  exact h

end GlobalDecompositionData

end FTAPTheorem42.HorizonFactorialGrid.FiniteLargeJumpClosedStopFamily
