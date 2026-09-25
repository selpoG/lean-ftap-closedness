/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.DominatedLocalMartingale
import FTAPTheorem42.Stochastic.DS.Lemma47.FirstPassage

/-!
# The stopped martingale in Lemma 4.7

An integrable envelope for the left jumps turns the pathwise first-passage
bound into domination of the rescaled local-martingale component.  Hence that
component is a true martingale.
-/

open Filter MeasureTheory Set
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

omit [MeasurableSpace Ω] in
/-- The first-passage stopped path only needs a jump bound up to a horizon
when the stopping time itself is bounded by that horizon. -/
theorem abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting_of_le_horizon
    (X : Process Ω) (hLeft : ProcessHasLeftLimits X)
    (r J : ℝ) (hJ : 0 ≤ J) (ω : Ω)
    (hInitial : |X 0 ω| ≤ r)
    (σ : Ω → WithTop ℝ≥0)
    (hσHit : σ ω ≤ absoluteStrictHittingAfter X r ω)
    (T : ℝ≥0) (hσT : σ ω ≤ (T : WithTop ℝ≥0))
    (hJump : ∀ t, t ≤ T → |processLeftJump X t ω| ≤ J) :
    ∀ t, |MeasureTheory.stoppedProcess X σ t ω| ≤ r + J := by
  intro t
  let u := RightContinuousStoppedMartingale.boundedTime t σ ω
  rw [← RightContinuousStoppedMartingale.sample_boundedTime_eq_stoppedProcess]
  change |X u ω| ≤ r + J
  have huσ : (u : WithTop ℝ≥0) ≤ σ ω := by
    rw [RightContinuousStoppedMartingale.coe_boundedTime]
    exact min_le_right _ _
  have huHit : (u : WithTop ℝ≥0) ≤
      absoluteStrictHittingAfter X r ω := huσ.trans hσHit
  have huT : u ≤ T := WithTop.coe_le_coe.mp (huσ.trans hσT)
  rcases huHit.eq_or_lt with huEq | huLt
  · have hHitNe : absoluteStrictHittingAfter X r ω ≠ ⊤ := by
      rw [← huEq]
      exact WithTop.coe_ne_top
    have hUntop :
        (absoluteStrictHittingAfter X r ω).untopA = u := by
      rw [WithTop.untopA_eq_untop hHitNe]
      apply WithTop.coe_injective
      rw [WithTop.coe_untop _ hHitNe]
      exact huEq.symm
    have hAt := abs_untopA_absoluteStrictHittingAfter_le_add_leftJump
      X hLeft r ω hInitial hHitNe
    rw [hUntop] at hAt
    exact hAt.trans (add_le_add le_rfl (hJump u huT))
  · exact (abs_le_of_lt_absoluteStrictHittingAfter X r ω u huLt).trans
      (le_add_of_nonneg_right hJ)

/-- Joint first passage additionally clamped at a deterministic horizon. -/
noncomputable def lemma47FirstPassageUpTo
    (H : SIntegrableStrategy D)
    (martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    Ω → WithTop ℝ≥0 :=
  fun ω => min (lemma47FirstPassage H martingaleLevel gainLevel ω)
    (T : WithTop ℝ≥0)

omit [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma47FirstPassageUpTo_isStoppingTime
    (H : SIntegrableStrategy D)
    (martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    IsStoppingTime ℱ
      (lemma47FirstPassageUpTo H martingaleLevel gainLevel T) :=
  (lemma47FirstPassage_isStoppingTime H martingaleLevel gainLevel).min
    (isStoppingTime_const ℱ T)

/-- Rescale the strategy after restricting it to the joint first passage
clamped at `T`. -/
noncomputable def lemma47RescaleAndStopUpTo
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    SIntegrableStrategy D :=
  C.rescaleStopAtTop scale
    (lemma47FirstPassageUpTo H martingaleLevel gainLevel T)
    (lemma47FirstPassageUpTo_isStoppingTime H martingaleLevel gainLevel T) H

omit [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- The whole gain of the finite-horizon first localization is the stopped,
rescaled original gain. -/
theorem lemma47RescaleAndStopUpTo_stochasticIntegral
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    ProcessIndistinguishable μ
      (stochasticIntegral
        (C.lemma47RescaleAndStopUpTo H scale martingaleLevel
          gainLevel T))
      (fun t ω => scale * MeasureTheory.stoppedProcess H.stochasticIntegral
        (lemma47FirstPassageUpTo H martingaleLevel gainLevel T) t ω) := by
  apply rescaleStopAtTop_stochasticIntegral

omit [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma47RescaleAndStopUpTo_martingalePart
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    ProcessIndistinguishable μ
      (C.lemma47RescaleAndStopUpTo H scale martingaleLevel
        gainLevel T).martingalePart
      (fun t ω => scale * MeasureTheory.stoppedProcess H.martingalePart
        (lemma47FirstPassageUpTo H martingaleLevel gainLevel T) t ω) := by
  apply rescaleStopAtTop_martingalePart

/-- A jump envelope only known up to `T` suffices after also clamping the
joint first-passage time at `T`. -/
theorem lemma47RescaleAndStopUpTo_martingale_of_integrableJumpBound
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0)
    (martingaleJump : Ω → ℝ)
    (hMartingaleJumpIntegrable : Integrable martingaleJump μ)
    (hMartingaleJumpNonnegative :
      ∀ᵐ ω ∂μ, 0 ≤ martingaleJump ω)
    (hMartingaleInitial :
      ∀ᵐ ω ∂μ, |H.martingalePart 0 ω| ≤ martingaleLevel)
    (hMartingaleJump : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |processLeftJump H.martingalePart t ω| ≤ martingaleJump ω) :
    Martingale
      (C.lemma47RescaleAndStopUpTo H scale martingaleLevel
        gainLevel T).martingalePart ℱ μ := by
  let Z : Ω → ℝ := fun ω =>
    |scale| * (martingaleLevel + martingaleJump ω)
  have hZIntegrable : Integrable Z μ := by
    exact ((integrable_const martingaleLevel).add
      hMartingaleJumpIntegrable).const_mul |scale|
  apply SIntegrableStrategy.martingalePart_isMartingale_of_integrable_bound
    (C.lemma47RescaleAndStopUpTo H scale martingaleLevel gainLevel T)
    Z hZIntegrable
  filter_upwards [C.lemma47RescaleAndStopUpTo_martingalePart H scale
      martingaleLevel gainLevel T,
    hMartingaleJumpNonnegative, hMartingaleInitial,
    hMartingaleJump] with ω hcomponent hJumpNonnegative hInitial hJump
  intro t
  rw [hcomponent t, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg scale)
  apply abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting_of_le_horizon
    H.martingalePart hMartingaleLeft martingaleLevel
    (martingaleJump ω) hJumpNonnegative ω hInitial
    (lemma47FirstPassageUpTo H martingaleLevel gainLevel T)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact min_le_right _ _
  · exact hJump

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
