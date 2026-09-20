/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.AnnouncedFirstLocalization
import FTAPTheorem42.Stochastic.DS.Lemma47.ExcursionCompletion
import FTAPTheorem42.Foundations.RiskSchedules

/-!
# The localized martingale jump envelope in Lemma 4.7

The first-localized strategy has a martingale component indistinguishable
from an explicit scaled stopped process.  This module promotes that explicit
process to a true martingale and transfers the actual-strategy jump envelope,
including its quantitative `L²` bound, through stopping and scaling.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- The explicit martingale process underlying the first-localized strategy. -/
noncomputable def lemma47LocalizedMartingaleProcess
    (H : SIntegrableStrategy D)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0) : Process Ω :=
  fun t ω => scale * MeasureTheory.stoppedProcess H.martingalePart
    (lemma47FirstPassageUpTo H martingaleLevel gainLevel T) t ω

omit [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma47LocalizedMartingaleProcess_isStronglyAdapted
    (H : SIntegrableStrategy D)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    StronglyAdapted ℱ
      (lemma47LocalizedMartingaleProcess H scale martingaleLevel
        gainLevel T) := by
  have hStopped :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      H.martingalePart_isStronglyAdapted
      (lemma47FirstPassageUpTo_isStoppingTime H martingaleLevel gainLevel T)
      H.martingalePart_isRightContinuous
  intro t
  exact (hStopped t).const_mul scale

omit [ℱ.IsRightContinuous] [IsFiniteMeasure μ]
    [SigmaFiniteFiltration μ ℱ] in
theorem lemma47LocalizedMartingaleProcess_isRightContinuous
    (H : SIntegrableStrategy D)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    ∀ ω t, ContinuousWithinAt
      (lemma47LocalizedMartingaleProcess H scale martingaleLevel
        gainLevel T · ω) (Set.Ici t) t := by
  intro ω t
  exact (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
    H.martingalePart H.martingalePart_isRightContinuous ω t).const_mul scale

omit [ℱ.IsRightContinuous] [IsFiniteMeasure μ]
    [SigmaFiniteFiltration μ ℱ] in
theorem lemma47LocalizedMartingaleProcess_hasLeftLimits
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    ProcessHasLeftLimits
      (lemma47LocalizedMartingaleProcess H scale martingaleLevel
        gainLevel T) :=
  (hMartingaleLeft.stoppedProcess
    (lemma47FirstPassageUpTo H martingaleLevel gainLevel T)).const_mul scale

/-- The explicit scaled stopped process is a true martingale whenever the
actual first-localized strategy component is. -/
theorem lemma47LocalizedMartingaleProcess_isMartingale
    (C : SIntegrableProcessStoppingCalculus D)
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (scale martingaleLevel gainLevel : ℝ)
    (hMartingaleInitial :
      ∀ᵐ ω ∂μ, |H.martingalePart 0 ω| ≤ martingaleLevel)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    {T : ℝ≥0} (hT : 0 < T) :
    Martingale
      (lemma47LocalizedMartingaleProcess H scale martingaleLevel
        gainLevel T) ℱ μ := by
  have hLocalized :=
    C.lemma47RescaleAndStopUpTo_martingale_of_strategy hUsual H
      hMartingaleLeft scale martingaleLevel gainLevel hMartingaleInitial
      gainEnvelope hGainEnvelope hGainBound hT
  apply hLocalized.congr
    (lemma47LocalizedMartingaleProcess_isStronglyAdapted
      H scale martingaleLevel gainLevel T)
  intro t
  exact (C.lemma47RescaleAndStopUpTo_martingalePart
    H scale martingaleLevel gainLevel T).eventuallyEq_at t

omit [ℱ.IsRightContinuous] [IsFiniteMeasure μ]
    [SigmaFiniteFiltration μ ℱ] in
/-- An initially zero canonical martingale remains initially zero after the
first stopping and scaling. -/
theorem lemma47LocalizedMartingaleProcess_zero
    (H : SIntegrableStrategy D)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0)
    (hZero : H.martingalePart 0 =ᵐ[μ] 0) :
    lemma47LocalizedMartingaleProcess H scale martingaleLevel gainLevel T 0
      =ᵐ[μ] 0 := by
  filter_upwards [hZero] with ω hω
  unfold lemma47LocalizedMartingaleProcess
  rw [MeasureTheory.stoppedProcess_eq_of_le bot_le, hω]
  simp

/-- Pointwise nonnegative envelope obtained by scaling the absolute value of
an original jump envelope. -/
def lemma47ScaledJumpEnvelope (scale : ℝ) (J : Ω → ℝ) : Ω → ℝ :=
  fun ω => |scale| * |J ω|

omit [MeasurableSpace Ω] [ℱ.IsRightContinuous] [IsFiniteMeasure μ]
    [SigmaFiniteFiltration μ ℱ] in
theorem lemma47ScaledJumpEnvelope_nonnegative
    (scale : ℝ) (J : Ω → ℝ) :
    0 ≤ lemma47ScaledJumpEnvelope scale J :=
  fun ω => mul_nonneg (abs_nonneg scale) (abs_nonneg (J ω))

omit [ℱ.IsRightContinuous] [IsFiniteMeasure μ]
    [SigmaFiniteFiltration μ ℱ] in
/-- Scaling an `L²` jump envelope multiplies its norm by the absolute
scaling factor. -/
theorem lemma47ScaledJumpEnvelope_memLp_and_norm
    (scale : ℝ) (J : Ω → ℝ)
    (hJ : MemLp J (2 : ℝ≥0∞) μ) :
    MemLp (lemma47ScaledJumpEnvelope scale J) (2 : ℝ≥0∞) μ ∧
      eLpNorm (lemma47ScaledJumpEnvelope scale J) (2 : ℝ≥0∞) μ =
        ENNReal.ofReal |scale| * eLpNorm J (2 : ℝ≥0∞) μ := by
  constructor
  · exact hJ.abs.const_mul |scale|
  · rw [show lemma47ScaledJumpEnvelope scale J =
        (|scale| : ℝ) • fun ω => |J ω| by
      funext ω
      simp only [lemma47ScaledJumpEnvelope, Pi.smul_apply, smul_eq_mul]]
    rw [eLpNorm_const_smul,
      Real.enorm_eq_ofReal (abs_nonneg scale)]
    have hAbs : eLpNorm (fun ω => |J ω|) (2 : ℝ≥0∞) μ =
        eLpNorm J (2 : ℝ≥0∞) μ := by
      simpa only [Real.norm_eq_abs] using
        (eLpNorm_norm (p := (2 : ℝ≥0∞)) (μ := μ) J hJ.aestronglyMeasurable)
    rw [hAbs]

/-- The actual martingale-jump envelope transfers through the first stopping
and scaling.  The resulting norm is controlled by the scale times the
constant-six actual-strategy estimate. -/
theorem lemma47LocalizedMartingaleProcess_jumpEnvelope
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (scale martingaleLevel gainLevel : ℝ)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    {T : ℝ≥0} (hT : 0 < T) :
    ∃ localizedJump : Ω → ℝ,
      MemLp localizedJump (2 : ℝ≥0∞) μ ∧
      (0 ≤ localizedJump) ∧
      (∀ᵐ ω ∂μ, ∀ t,
        |processLeftJump
          (lemma47LocalizedMartingaleProcess H scale martingaleLevel
            gainLevel T) t ω| ≤ localizedJump ω) ∧
      eLpNorm localizedJump (2 : ℝ≥0∞) μ ≤
        ENNReal.ofReal |scale| *
          (6 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ) := by
  obtain ⟨martingaleJump, hJumpMem, hJumpNonnegative,
      hJumpBound, hJumpNorm⟩ :=
    lemma47MartingaleJumpEnvelope_of_strategy hUsual H hMartingaleLeft
      gainEnvelope hGainEnvelope hGainBound hT
  let localizedJump := lemma47ScaledJumpEnvelope scale martingaleJump
  have hLocalizedJump :=
    lemma47ScaledJumpEnvelope_memLp_and_norm
      (μ := μ) scale martingaleJump hJumpMem
  refine ⟨localizedJump, hLocalizedJump.1,
    lemma47ScaledJumpEnvelope_nonnegative scale martingaleJump, ?_, ?_⟩
  · filter_upwards [hJumpNonnegative, hJumpBound] with ω hNonnegative hBound
    intro t
    have hStoppedJump :=
      abs_processLeftJump_stoppedProcess_le_of_le_horizon_at
        H.martingalePart hMartingaleLeft
        (lemma47FirstPassageUpTo H martingaleLevel gainLevel T)
        T martingaleJump ω (min_le_right _ _) hNonnegative hBound t
    change |processLeftJump (fun s ω =>
      scale * MeasureTheory.stoppedProcess H.martingalePart
        (lemma47FirstPassageUpTo H martingaleLevel gainLevel T) s ω) t ω| ≤
          |scale| * |martingaleJump ω|
    rw [processLeftJump_const_mul
      (hMartingaleLeft.stoppedProcess
        (lemma47FirstPassageUpTo H martingaleLevel gainLevel T))
      scale t ω, abs_mul]
    exact (mul_le_mul_of_nonneg_left hStoppedJump (abs_nonneg scale)).trans
      (mul_le_mul_of_nonneg_left (le_abs_self (martingaleJump ω))
        (abs_nonneg scale))
  · rw [hLocalizedJump.2]
    gcongr

/-- At the inverse-square scale used in Lemma 4.7, the localized martingale
has a jump envelope of `L²` norm at most one once the deterministic
constant-six bound fits below `n²`. -/
theorem lemma47LocalizedMartingaleProcess_jumpEnvelope_firstScale
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    {n : ℕ} (hn : 0 < n)
    (martingaleLevel gainLevel : ℝ)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    {normBound : ℝ}
    (hGainNorm : eLpNorm gainEnvelope (2 : ℝ≥0∞) μ ≤
      ENNReal.ofReal normBound)
    (hNumeric : 6 * normBound ≤ (n : ℝ) ^ 2)
    {T : ℝ≥0} (hT : 0 < T) :
    ∃ localizedJump : Ω → ℝ,
      MemLp localizedJump (2 : ℝ≥0∞) μ ∧
      (0 ≤ localizedJump) ∧
      (∀ᵐ ω ∂μ, ∀ t,
        |processLeftJump
          (lemma47LocalizedMartingaleProcess H (lemma47FirstScale n)
            martingaleLevel gainLevel T) t ω| ≤ localizedJump ω) ∧
      eLpNorm localizedJump (2 : ℝ≥0∞) μ ≤ 1 := by
  obtain ⟨localizedJump, hJumpMem, hJumpNonnegative, hJumpBound,
      hJumpNorm⟩ :=
    lemma47LocalizedMartingaleProcess_jumpEnvelope hUsual H
      hMartingaleLeft (lemma47FirstScale n) martingaleLevel gainLevel
      gainEnvelope hGainEnvelope hGainBound hT
  refine ⟨localizedJump, hJumpMem, hJumpNonnegative, hJumpBound,
    hJumpNorm.trans ?_⟩
  exact lemma47FirstScale_mul_six_le_one hn hGainNorm hNumeric

/-- The actual first localization supplies the negative excursion used in
the Lemma 4.7 contradiction.  In particular, the martingale, jump-envelope,
completion, and second-moment inputs are all constructed from the original
strategy rather than postulated as boundary data. -/
theorem lemma47FirstLocalized_negativeExcursion
    [IsProbabilityMeasure μ]
    (C : SIntegrableProcessStoppingCalculus D)
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (hMartingaleZero : H.martingalePart 0 =ᵐ[μ] 0)
    {n : ℕ} (hn : 0 < n)
    {martingaleLevel : ℝ} (hMartingaleLevel : 0 ≤ martingaleLevel)
    (gainLevel : ℝ)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    {normBound : ℝ}
    (hGainNorm : eLpNorm gainEnvelope (2 : ℝ≥0∞) μ ≤
      ENNReal.ofReal normBound)
    (hNumeric : 6 * normBound ≤ (n : ℝ) ^ 2)
    {T : ℝ≥0} (hT : 0 < T)
    {k : ℕ} (hk : 0 < k) {R α : ℝ}
    (hR : 0 < R) (hα : 0 < α) (hαOne : α ≤ 1)
    (hHigh : 7 * α < μ.real {ω |
      R < FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (lemma47LocalizedMartingaleProcess H (lemma47FirstScale n)
          martingaleLevel gainLevel T) T ω})
    (hError : (4 * (k : ℝ) / R) ^ 2 ≤ α)
    {i : ℕ} (hi : i < k) :
    α ^ 2 < μ.real {ω |
      Lemma47ExcursionStopping.increment
        (lemma47LocalizedMartingaleProcess H (lemma47FirstScale n)
          martingaleLevel gainLevel T) T i ω ≤ -α} := by
  let X := lemma47LocalizedMartingaleProcess H (lemma47FirstScale n)
    martingaleLevel gainLevel T
  obtain ⟨jumpEnvelope, hJumpMem, hJumpNonnegative, hJumpBound,
      hJumpNorm⟩ :=
    lemma47LocalizedMartingaleProcess_jumpEnvelope_firstScale hUsual H
      hMartingaleLeft hn martingaleLevel gainLevel gainEnvelope
      hGainEnvelope hGainBound hGainNorm hNumeric hT
  let J : ℕ → Ω → ℝ := fun _ => jumpEnvelope
  have hXMartingale : Martingale X ℱ μ := by
    apply C.lemma47LocalizedMartingaleProcess_isMartingale hUsual H
      hMartingaleLeft (lemma47FirstScale n) martingaleLevel gainLevel
      _ gainEnvelope hGainEnvelope hGainBound hT
    filter_upwards [hMartingaleZero] with ω hZero
    rw [hZero, Pi.zero_apply, abs_zero]
    exact hMartingaleLevel
  have hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t := by
    exact lemma47LocalizedMartingaleProcess_isRightContinuous H
      (lemma47FirstScale n) martingaleLevel gainLevel T
  have hXLeft : ProcessHasLeftLimits X :=
    lemma47LocalizedMartingaleProcess_hasLeftLimits H hMartingaleLeft
      (lemma47FirstScale n) martingaleLevel gainLevel T
  have hXZero : X 0 =ᵐ[μ] 0 :=
    lemma47LocalizedMartingaleProcess_zero H (lemma47FirstScale n)
      martingaleLevel gainLevel T hMartingaleZero
  have hJNonnegative : ∀ j ω, 0 ≤ J j ω := by
    intro j ω
    exact hJumpNonnegative ω
  have hJMem : ∀ j, MemLp (J j) (2 : ℝ≥0∞) μ := by
    intro j
    exact hJumpMem
  have hJNorm : ∀ j, eLpNorm (J j) (2 : ℝ≥0∞) μ ≤ 1 := by
    intro j
    exact hJumpNorm
  have hDisplacementJump : ∀ j, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump
        (Lemma47ExcursionStopping.displacementAfter X
          (Lemma47ExcursionStopping.time X T j)) t ω| ≤ J j ω := by
    intro j
    filter_upwards [hJumpBound] with ω hBound
    exact Lemma47ExcursionStopping.abs_processLeftJump_displacementAfter_le_at
      X hXLeft (Lemma47ExcursionStopping.time X T j) jumpEnvelope ω
        hBound
  have hCompleted : 6 * α <
      μ.real (Lemma47ExcursionStopping.completedEvent X T i) := by
    exact Lemma47ExcursionStopping.probReal_completedEvent_gt_six_mul
      hXMartingale hXRight hXLeft hXZero T J hJNonnegative hJMem
        hDisplacementJump hJNorm hk hR hHigh hError hi
  exact Lemma47ExcursionStopping.probReal_increment_le_neg_sq_gt
    hXMartingale hXRight hXLeft T J hJNonnegative hJMem
      hDisplacementJump i (hJNorm i) hα hαOne hCompleted

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
