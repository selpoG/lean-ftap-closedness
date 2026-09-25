/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.HahnStopping
import FTAPTheorem42.Stochastic.DS.Lemma47.ExcursionOrthogonality
import FTAPTheorem42.Stochastic.DS.Lemma47.FiniteVariationExcursion
import FTAPTheorem42.Stochastic.DS.Lemma47.Probability
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePathwiseRestrictionCalculus

/-!
# The downside stop in Lemma 4.7

The positive Hahn aggregation is stopped at the first strict passage below a
deterministic loss level.  A simultaneous lower jump bound controls the
overshoot.  This module proves the pathwise passage estimate and transfers the
first-localization jump bound through the positive Hahn restriction.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- At a finite lower passage, the overshoot is no larger than the negative
left-jump bound. -/
theorem neg_add_le_untopA_lowerStrictHittingAfter
    (X : Process Ω) (hLeft : ProcessHasLeftLimits X)
    (r J : ℝ) (hJ : 0 ≤ J) (ω : Ω)
    (hInitial : -r ≤ X 0 ω)
    (hJump : ∀ t, -J ≤ processLeftJump X t ω)
    (hτ : lowerStrictHittingAfter X r ω ≠ ⊤) :
    -(r + J) ≤ X ((lowerStrictHittingAfter X r ω).untopA) ω := by
  let τ := (lowerStrictHittingAfter X r ω).untopA
  have hτcoe : (τ : WithTop ℝ≥0) = lowerStrictHittingAfter X r ω := by
    dsimp only [τ]
    rw [WithTop.untopA_eq_untop hτ]
    exact WithTop.coe_untop _ hτ
  change -(r + J) ≤ X τ ω
  by_cases hτ0 : τ = 0
  · rw [hτ0]
    linarith
  · have hτpos : (0 : ℝ≥0) < τ := (pos_iff_ne_zero).2 hτ0
    let : NeBot (𝓝[<] τ) :=
      nhdsLT_neBot_of_exists_lt ⟨0, hτpos⟩
    have hLeftBound :
        -r ≤ Function.leftLim (fun s => X s ω) τ := by
      apply ge_of_tendsto (hLeft ω τ)
      filter_upwards [self_mem_nhdsWithin] with s hs
      apply neg_le_of_lt_lowerStrictHittingAfter X r ω s
      rw [← hτcoe]
      exact WithTop.coe_lt_coe.mpr hs
    have hAt := hJump τ
    unfold processLeftJump at hAt
    linarith

omit [MeasurableSpace Ω] in
/-- Stopping no later than the lower passage gives a uniform pathwise lower
bound by the passage level plus the negative-jump bound. -/
theorem stoppedProcess_lower_bound_of_le_lowerHitting
    (X : Process Ω) (hLeft : ProcessHasLeftLimits X)
    (r J : ℝ) (hJ : 0 ≤ J) (ω : Ω)
    (hInitial : -r ≤ X 0 ω)
    (σ : Ω → WithTop ℝ≥0)
    (hσ : σ ω ≤ lowerStrictHittingAfter X r ω)
    (hJump : ∀ t, -J ≤ processLeftJump X t ω) :
    ∀ t, -(r + J) ≤ MeasureTheory.stoppedProcess X σ t ω := by
  intro t
  let u := RightContinuousStoppedMartingale.boundedTime t σ ω
  rw [← RightContinuousStoppedMartingale.sample_boundedTime_eq_stoppedProcess]
  change -(r + J) ≤ X u ω
  have huHit : (u : WithTop ℝ≥0) ≤ lowerStrictHittingAfter X r ω := by
    rw [RightContinuousStoppedMartingale.coe_boundedTime]
    exact (min_le_right _ _).trans hσ
  rcases huHit.eq_or_lt with huEq | huLt
  · have hHitNe : lowerStrictHittingAfter X r ω ≠ ⊤ := by
      rw [← huEq]
      exact WithTop.coe_ne_top
    have hUntop : (lowerStrictHittingAfter X r ω).untopA = u := by
      rw [WithTop.untopA_eq_untop hHitNe]
      apply WithTop.coe_injective
      rw [WithTop.coe_untop _ hHitNe]
      exact huEq.symm
    have hAt := neg_add_le_untopA_lowerStrictHittingAfter
      X hLeft r J hJ ω hInitial hJump hHitNe
    simpa only [hUntop] using hAt
  · exact (neg_le_of_lt_lowerStrictHittingAfter X r ω u huLt).trans'
      (by linarith)

omit [MeasurableSpace Ω] in
/-- A lower bound on the original process and an absolute first-passage cap
give a deterministic lower bound on every jump of the stopped process. -/
theorem processLeftJump_stoppedProcess_lower_bound_of_le_absoluteHitting
    (X : Process Ω) (hLeft : ProcessHasLeftLimits X)
    (r a : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a) (ω : Ω)
    (hLower : ∀ t, -a ≤ X t ω)
    (σ : Ω → WithTop ℝ≥0)
    (hσ : σ ω ≤ absoluteStrictHittingAfter X r ω) :
    ∀ t, -(r + a) ≤
      processLeftJump (MeasureTheory.stoppedProcess X σ) t ω := by
  intro t
  by_cases ht : (t : WithTop ℝ≥0) ≤ σ ω
  · rw [processLeftJump_stoppedProcess_eq_of_le X hLeft σ t ω ht]
    by_cases ht0 : t = 0
    · subst t
      unfold processLeftJump
      have hleft : Function.leftLim (fun s => X s ω) 0 = X 0 ω :=
        leftLim_eq_of_isBot isBot_bot
      rw [hleft, sub_self]
      linarith
    · have htpos : (0 : ℝ≥0) < t := (pos_iff_ne_zero).2 ht0
      let : NeBot (𝓝[<] t) :=
        nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
      have hLeftUpper :
          Function.leftLim (fun s => X s ω) t ≤ r := by
        apply le_of_tendsto (hLeft ω t)
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hsHit : (s : WithTop ℝ≥0) <
            absoluteStrictHittingAfter X r ω := by
          exact (WithTop.coe_lt_coe.mpr hs).trans_le (ht.trans hσ)
        exact (le_abs_self (X s ω)).trans
          (abs_le_of_lt_absoluteStrictHittingAfter X r ω s hsHit)
      unfold processLeftJump
      linarith [hLower t]
  · rw [processLeftJump_stoppedProcess_eq_zero_of_lt X σ t ω
      (lt_of_not_ge ht)]
    linarith

namespace SIntegrableProcessStoppingCalculus

open SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- The first rescale-and-stop step has deterministic negative jump bound
`scale * (gainLevel + 1)` when the original gain is one-admissible on one
common full-measure set. -/
theorem lemma47RescaleAndStopUpTo_stochasticIntegral_leftJump_lower_bound
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D)
    (hGainLeft : ProcessHasLeftLimits H.stochasticIntegral)
    {scale martingaleLevel gainLevel : ℝ}
    (hScale : 0 ≤ scale) (hGainLevel : 0 ≤ gainLevel)
    (T : ℝ≥0)
    (hLower : ∀ᵐ ω ∂μ, ∀ t, (-1 : ℝ) ≤ H.stochasticIntegral t ω) :
    let Cstop := C
    let L := Cstop.lemma47RescaleAndStopUpTo
      H scale martingaleLevel gainLevel T
    ∀ᵐ ω ∂μ, ∀ t,
      -(scale * (gainLevel + 1)) ≤
        processLeftJump L.stochasticIntegral t ω := by
  let Cstop := C
  let σ := lemma47FirstPassageUpTo H martingaleLevel gainLevel T
  let L := Cstop.lemma47RescaleAndStopUpTo
    H scale martingaleLevel gainLevel T
  filter_upwards [Cstop.lemma47RescaleAndStopUpTo_stochasticIntegral
      H scale martingaleLevel gainLevel T, hLower] with ω hEq hLowerω
  intro t
  have hStopped :=
    processLeftJump_stoppedProcess_lower_bound_of_le_absoluteHitting
      H.stochasticIntegral hGainLeft gainLevel 1 hGainLevel (by norm_num)
      ω hLowerω σ
      ((min_le_left _ _).trans (min_le_right _ _)) t
  have hMul :
      processLeftJump
          (fun s ω => scale * MeasureTheory.stoppedProcess
            H.stochasticIntegral σ s ω) t ω =
        scale * processLeftJump
          (MeasureTheory.stoppedProcess H.stochasticIntegral σ) t ω :=
    processLeftJump_const_mul (hGainLeft.stoppedProcess σ) scale t ω
  have hPath : (fun s => L.stochasticIntegral s ω) =
      fun s => scale * MeasureTheory.stoppedProcess
        H.stochasticIntegral σ s ω := funext hEq
  have hJumpEq : processLeftJump L.stochasticIntegral t ω =
      processLeftJump
        (fun s ω => scale * MeasureTheory.stoppedProcess
          H.stochasticIntegral σ s ω) t ω := by
    unfold processLeftJump
    rw [show L.stochasticIntegral t ω =
        scale * MeasureTheory.stoppedProcess H.stochasticIntegral σ t ω
      from hEq t]
    rw [congrArg (fun f : ℝ≥0 → ℝ => Function.leftLim f t) hPath]
  rw [hJumpEq, hMul]
  have := mul_le_mul_of_nonneg_left hStopped hScale
  linarith

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- The localized gain and martingale component retain pathwise left limits
through the concrete stopping calculus. -/
theorem lemma47RescaleAndStopUpTo_hasLeftLimits
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D)
    (hM : ProcessHasLeftLimits H.martingalePart)
    (hX : ProcessHasLeftLimits H.stochasticIntegral)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    let Cstop := C
    let L := Cstop.lemma47RescaleAndStopUpTo
      H scale martingaleLevel gainLevel T
    ProcessHasLeftLimits L.martingalePart ∧
      ProcessHasLeftLimits L.stochasticIntegral := by
  let Cstop := C
  let σ := lemma47FirstPassageUpTo H martingaleLevel gainLevel T
  let hσ := lemma47FirstPassageUpTo_isStoppingTime
    H martingaleLevel gainLevel T
  exact ⟨Cstop.rescaleStopAtTop_martingalePart_hasLeftLimits
      scale σ hσ H hM,
    Cstop.rescaleStopAtTop_stochasticIntegral_hasLeftLimits
      scale σ hσ H hX⟩

/-- The downside stopping time, clamped at the same deterministic horizon as
the Hahn aggregation. -/
noncomputable def lemma47DownsideTime
    (R : SIntegrableStrategy D) (d : ℝ) (T : ℝ≥0) :
    Ω → WithTop ℝ≥0 :=
  fun ω => min (lowerStrictHittingAfter R.stochasticIntegral d ω)
    (T : WithTop ℝ≥0)

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma47DownsideTime_isStoppingTime
    (R : SIntegrableStrategy D) (d : ℝ) (T : ℝ≥0) :
    IsStoppingTime ℱ (lemma47DownsideTime R d T) :=
  (lowerStrictHittingAfter_isStoppingTime
    R.stochasticIntegral_isStronglyAdapted
    R.stochasticIntegral_isRightContinuous d).min
      (isStoppingTime_const ℱ T)

/-- Stop at the downside passage and apply the final deterministic scale. -/
noncomputable def lemma47StopDownsideAndRescale
    (C : SIntegrableProcessStoppingCalculus D)
    (R : SIntegrableStrategy D) (c d : ℝ) (T : ℝ≥0) :
    SIntegrableStrategy D :=
  C
    |>.rescaleStopAtTop c (lemma47DownsideTime R d T)
      (lemma47DownsideTime_isStoppingTime R d T) R

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- The downside-stopped strategy is constant after its deterministic
horizon. -/
theorem lemma47StopDownsideAndRescale_stochasticIntegral_eq_terminal_of_le
    (C : SIntegrableProcessStoppingCalculus D)
    (R : SIntegrableStrategy D) (c d : ℝ) (T : ℝ≥0) :
    let V := C.lemma47StopDownsideAndRescale R c d T
    ∀ᵐ ω ∂μ, ∀ t, T ≤ t →
      V.stochasticIntegral t ω = V.stochasticIntegral T ω := by
  let Cstop := C
  let U := lemma47DownsideTime R d T
  let V := C.lemma47StopDownsideAndRescale R c d T
  filter_upwards [Cstop.rescaleStopAtTop_stochasticIntegral c U
    (lemma47DownsideTime_isStoppingTime R d T) R] with ω hEq
  intro t ht
  change stochasticIntegral
      (Cstop.rescaleStopAtTop c U
        (lemma47DownsideTime_isStoppingTime R d T) R) t ω =
    stochasticIntegral
      (Cstop.rescaleStopAtTop c U
        (lemma47DownsideTime_isStoppingTime R d T) R) T ω
  rw [hEq t, hEq T]
  have hUT : U ω ≤ (T : WithTop ℝ≥0) := min_le_right _ _
  have hUt : U ω ≤ (t : WithTop ℝ≥0) :=
    hUT.trans (WithTop.coe_le_coe.mpr ht)
  rw [MeasureTheory.stoppedProcess_eq_of_ge hUt,
    MeasureTheory.stoppedProcess_eq_of_ge hUT]

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- The downside-stopped and rescaled gain is bounded below by the passage
level plus one jump overshoot. -/
theorem lemma47StopDownsideAndRescale_lower_bound
    (C : SIntegrableProcessStoppingCalculus D)
    (R : SIntegrableStrategy D)
    (hRLeft : ProcessHasLeftLimits R.stochasticIntegral)
    {c d J : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hJ : 0 ≤ J)
    (T : ℝ≥0)
    (hRZero : R.stochasticIntegral 0 =ᵐ[μ] 0)
    (hJump : ∀ᵐ ω ∂μ, ∀ t,
      -J ≤ processLeftJump R.stochasticIntegral t ω) :
    let V := C.lemma47StopDownsideAndRescale R c d T
    ∀ᵐ ω ∂μ, ∀ t,
      -(c * (d + J)) ≤ V.stochasticIntegral t ω := by
  let Cstop := C
  let U := lemma47DownsideTime R d T
  let V := C.lemma47StopDownsideAndRescale R c d T
  filter_upwards [hRZero, hJump,
    Cstop.rescaleStopAtTop_stochasticIntegral c U
      (lemma47DownsideTime_isStoppingTime R d T) R] with
      ω hZero hJumpω hEq
  intro t
  have hStopped := stoppedProcess_lower_bound_of_le_lowerHitting
    R.stochasticIntegral hRLeft d J hJ ω (by simpa [hZero] using hd)
    U (min_le_left _ _) hJumpω t
  have hScaled := mul_le_mul_of_nonneg_left hStopped hc
  change -(c * (d + J)) ≤ stochasticIntegral
    (Cstop.rescaleStopAtTop c U
      (lemma47DownsideTime_isStoppingTime R d T) R) t ω
  rw [hEq t]
  linarith

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- If the gain never reaches the downside level before `T`, the final gain
is exactly the scaled unstopped gain at `T`. -/
theorem lemma47StopDownsideAndRescale_terminal_eq_of_noPassage
    (C : SIntegrableProcessStoppingCalculus D)
    (R : SIntegrableStrategy D) (c d : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ,
      (T : WithTop ℝ≥0) ≤ lowerStrictHittingAfter R.stochasticIntegral d ω →
        (C.lemma47StopDownsideAndRescale R c d T).stochasticIntegral T ω =
          c * R.stochasticIntegral T ω := by
  let Cstop := C
  filter_upwards [Cstop.rescaleStopAtTop_stochasticIntegral c
    (lemma47DownsideTime R d T)
    (lemma47DownsideTime_isStoppingTime R d T) R] with ω hEq hNoPassage
  change stochasticIntegral
    (Cstop.rescaleStopAtTop c (lemma47DownsideTime R d T)
      (lemma47DownsideTime_isStoppingTime R d T) R) T ω =
        c * R.stochasticIntegral T ω
  rw [hEq T]
  have hU : lemma47DownsideTime R d T ω = (T : WithTop ℝ≥0) := by
    exact min_eq_right hNoPassage
  rw [MeasureTheory.stoppedProcess_eq_of_ge]
  · rw [hU, WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe]
  · rw [hU]

omit [MeasurableSpace Ω] in
/-- An increasing finite-variation component and a bounded martingale
increment prevent a lower passage of the whole gain. -/
theorem le_lowerStrictHittingAfter_of_decomposition
    (X M A : Process Ω) (d : ℝ) (T : ℝ≥0) (ω : Ω)
    (hDecomp : ∀ t, X t ω = M t ω + A t ω)
    (hZero : X 0 ω = 0)
    (hA : ∀ t, t ≤ T → 0 ≤ A t ω - A 0 ω)
    (hM : ∀ t, t ≤ T → |M t ω - M 0 ω| ≤ d) :
    (T : WithTop ℝ≥0) ≤ lowerStrictHittingAfter X d ω := by
  by_contra hnot
  have hlt : lowerStrictHittingAfter X d ω < (T : WithTop ℝ≥0) :=
    lt_of_not_ge hnot
  unfold lowerStrictHittingAfter
    RightContinuousHittingTime.strictHittingAfter at hlt
  rw [MeasureTheory.hittingAfter_lt_iff] at hlt
  obtain ⟨t, ht, hcross⟩ := hlt
  have htT : t ≤ T := ht.2.le
  have hMlower : -d ≤ M t ω - M 0 ω :=
    (neg_le_neg (hM t htT)).trans (neg_abs_le (M t ω - M 0 ω))
  have hAinc := hA t htT
  have hZeroComponents : M 0 ω + A 0 ω = 0 := by
    rw [← hDecomp 0, hZero]
  have hXlower : -d ≤ X t ω := by
    rw [hDecomp t]
    linarith
  change d < -X t ω at hcross
  linarith

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
