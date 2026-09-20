/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.LocalizedJumpEnvelope

/-!
# The high maximum after the first Lemma 4.7 localization

An original martingale maximum above `martingaleLevel`, outside the small
gain-tail event, reaches the martingale side of the joint first passage.
Stopping and positive rescaling therefore leave a high maximum.  This is the
probability bridge between an unbounded witness and the chronological
excursion argument.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- A high finite-horizon maximum of the original martingale survives the
joint first-passage localization away from the `L²`-small gain tail. -/
theorem lemma47LocalizedMartingaleProcess_highMaximum
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (hMartingaleZero : H.martingalePart 0 =ᵐ[μ] 0)
    {scale : ℝ} (hScale : 0 < scale)
    {martingaleLevel : ℝ} (hMartingaleLevel : 0 ≤ martingaleLevel)
    {gainLevel : ℝ} (hGainLevel : 0 < gainLevel)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    {normBound : ℝ} (hNormBound : 0 ≤ normBound)
    (hGainNorm : eLpNorm gainEnvelope (2 : ℝ≥0∞) μ ≤
      ENNReal.ofReal normBound)
    {T : ℝ≥0} (hT : 0 < T)
    {localizedThreshold α : ℝ}
    (hThreshold : localizedThreshold < scale * martingaleLevel)
    (hOriginalHigh : 8 * α < μ.real {ω |
      martingaleLevel <
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          H.martingalePart T ω})
    (hGainError : (normBound / gainLevel) ^ 2 ≤ α) :
    7 * α < μ.real {ω |
      localizedThreshold <
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (lemma47LocalizedMartingaleProcess H scale martingaleLevel
            gainLevel T) T ω} := by
  let X := lemma47LocalizedMartingaleProcess H scale martingaleLevel
    gainLevel T
  obtain ⟨martingaleJump, -, hJumpNonnegative, hJumpBound, -⟩ :=
    lemma47MartingaleJumpEnvelope_of_strategy hUsual H hMartingaleLeft
      gainEnvelope hGainEnvelope hGainBound hT
  have hInitial : ∀ᵐ ω ∂μ,
      |H.martingalePart 0 ω| ≤ martingaleLevel := by
    filter_upwards [hMartingaleZero] with ω hZero
    rw [hZero, Pi.zero_apply, abs_zero]
    exact hMartingaleLevel
  have hXBound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |X t ω| ≤ scale * (martingaleLevel + martingaleJump ω) := by
    filter_upwards [hJumpNonnegative, hJumpBound, hInitial] with
      ω hJumpNonnegativeω hJumpBoundω hInitialω
    intro t ht
    change |scale * MeasureTheory.stoppedProcess H.martingalePart
      (lemma47FirstPassageUpTo H martingaleLevel gainLevel T) t ω| ≤ _
    rw [abs_mul, abs_of_pos hScale]
    apply mul_le_mul_of_nonneg_left _ hScale.le
    exact abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting_of_le_horizon
      H.martingalePart hMartingaleLeft martingaleLevel
      (martingaleJump ω) hJumpNonnegativeω ω hInitialω
      (lemma47FirstPassageUpTo H martingaleLevel gainLevel T)
      ((min_le_left _ _).trans (min_le_left _ _)) T
      (min_le_right _ _) hJumpBoundω t
  have hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t :=
    lemma47LocalizedMartingaleProcess_isRightContinuous H scale
      martingaleLevel gainLevel T
  have hXEnvelope : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |X t ω| ≤
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T ω :=
    FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_ae
      hXRight T hXBound
  have hGainBoundUpTo : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω := by
    filter_upwards [hGainBound] with ω hBound
    exact fun t _ => hBound t
  have hGainEnvelopeDominates : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |H.stochasticIntegral t ω| ≤
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          H.stochasticIntegral T ω :=
    FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_ae
      H.stochasticIntegral_isRightContinuous T hGainBoundUpTo
  let A : Set Ω := {ω | martingaleLevel <
    FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      H.martingalePart T ω}
  let B : Set Ω := {ω | gainLevel <
    FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      H.stochasticIntegral T ω}
  let C : Set Ω := {ω | localizedThreshold <
    FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T ω}
  have hSubset : A ≤ᵐ[μ] Set.union C B := by
    filter_upwards [hXEnvelope, hGainEnvelopeDominates] with
      ω hXEnvelopeω hGainEnvelopeω
    intro hA
    by_cases hB : ω ∈ B
    · exact Set.mem_union_right C hB
    · apply Set.mem_union_left B
      change localizedThreshold <
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T ω
      have hGainEnvelopeLe :
          FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            H.stochasticIntegral T ω ≤ gainLevel := by
        exact le_of_not_gt hB
      have hExists : ∃ t, t ≤ T ∧
          martingaleLevel < |H.martingalePart t ω| := by
        by_contra hNo
        have hAll : ∀ t, t ≤ T →
            |H.martingalePart t ω| ≤ martingaleLevel := by
          intro t ht
          by_contra hNot
          exact hNo ⟨t, ht, lt_of_not_ge hNot⟩
        exact (not_lt_of_ge
          (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_le_of_bound
            H.martingalePart T hAll)) hA
      obtain ⟨t, htT, hMt⟩ := hExists
      let τM := absoluteStrictHittingAfter H.martingalePart
        martingaleLevel ω
      let τS := absoluteStrictHittingAfter H.stochasticIntegral
        gainLevel ω
      have hτMt : τM ≤ (t : WithTop ℝ≥0) := by
        unfold τM absoluteStrictHittingAfter
          RightContinuousHittingTime.strictHittingAfter
        exact MeasureTheory.hittingAfter_le_of_mem bot_le hMt
      have hTτS : (T : WithTop ℝ≥0) ≤ τS := by
        by_contra hNot
        have hτST : τS < (T : WithTop ℝ≥0) := lt_of_not_ge hNot
        unfold τS absoluteStrictHittingAfter
          RightContinuousHittingTime.strictHittingAfter at hτST
        rw [MeasureTheory.hittingAfter_lt_iff] at hτST
        obtain ⟨s, hs, hCross⟩ := hτST
        have hGainAt : |H.stochasticIntegral s ω| ≤ gainLevel :=
          (hGainEnvelopeω s hs.2.le).trans hGainEnvelopeLe
        exact (not_lt_of_ge hGainAt) hCross
      have hτMτS : τM ≤ τS :=
        hτMt.trans ((WithTop.coe_le_coe.mpr htT).trans hTτS)
      have hτMT : τM ≤ (T : WithTop ℝ≥0) :=
        hτMt.trans (WithTop.coe_le_coe.mpr htT)
      have hPassage : lemma47FirstPassage H martingaleLevel gainLevel ω =
          τM := by
        unfold lemma47FirstPassage
        exact min_eq_left hτMτS
      have hPassageUpTo :
          lemma47FirstPassageUpTo H martingaleLevel gainLevel T ω =
            τM := by
        unfold lemma47FirstPassageUpTo
        rw [hPassage, min_eq_left hτMT]
      have hτMFinite : τM ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hτMt
      let u : ℝ≥0 := τM.untopA
      have huCoe : (u : WithTop ℝ≥0) = τM := by
        dsimp only [u]
        rw [WithTop.untopA_eq_untop hτMFinite,
          WithTop.coe_untop _ hτMFinite]
      have huT : u ≤ T := WithTop.coe_le_coe.mp (huCoe.trans_le hτMT)
      have hAt : martingaleLevel ≤ |H.martingalePart u ω| := by
        exact le_abs_untopA_absoluteStrictHittingAfter
          H.martingalePart H.martingalePart_isRightContinuous
          martingaleLevel ω hτMFinite
      have hStopped : MeasureTheory.stoppedProcess H.martingalePart
          (lemma47FirstPassageUpTo H martingaleLevel gainLevel T) u ω =
            H.martingalePart u ω := by
        apply MeasureTheory.stoppedProcess_eq_of_le
        rw [hPassageUpTo, huCoe]
      have hScaled : scale * martingaleLevel ≤ |X u ω| := by
        change scale * martingaleLevel ≤
          |scale * MeasureTheory.stoppedProcess H.martingalePart
            (lemma47FirstPassageUpTo H martingaleLevel gainLevel T) u ω|
        rw [hStopped, abs_mul, abs_of_pos hScale]
        exact mul_le_mul_of_nonneg_left hAt hScale.le
      exact hThreshold.trans_le (hScaled.trans (hXEnvelopeω u huT))
  have hGainTail : μ.real B ≤ α := by
    apply (FactorialChronologicalGrid.probReal_finiteHorizonAbsoluteEnvelope_gt_le
      H.stochasticIntegral_isStronglyAdapted T hGainEnvelope
      hGainBoundUpTo hNormBound hGainLevel hGainNorm).trans
    exact hGainError
  have hAUnion : μ.real A ≤ μ.real (C ∪ B) :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hSubset)
  have hUnion : μ.real A ≤ μ.real C + μ.real B :=
    hAUnion.trans (measureReal_union_le C B)
  change 7 * α < μ.real C
  change 8 * α < μ.real A at hOriginalHigh
  linarith

/-- The original high-martingale event and the `L²` gain bound provide all
probability inputs of the actual negative-excursion theorem. -/
theorem lemma47FirstLocalized_negativeExcursion_of_originalHigh
    (C : SIntegrableProcessStoppingCalculus D)
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (hMartingaleZero : H.martingalePart 0 =ᵐ[μ] 0)
    {n : ℕ} (hn : 0 < n)
    {martingaleLevel : ℝ} (hMartingaleLevel : 0 ≤ martingaleLevel)
    {gainLevel : ℝ} (hGainLevel : 0 < gainLevel)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    {normBound : ℝ} (hNormBound : 0 ≤ normBound)
    (hGainNorm : eLpNorm gainEnvelope (2 : ℝ≥0∞) μ ≤
      ENNReal.ofReal normBound)
    (hJumpNumeric : 6 * normBound ≤ (n : ℝ) ^ 2)
    {T : ℝ≥0} (hT : 0 < T)
    {k : ℕ} (hk : 0 < k) {R α : ℝ}
    (hR : 0 < R) (hRScale : R < lemma47FirstScale n * martingaleLevel)
    (hα : 0 < α) (hαOne : α ≤ 1)
    (hOriginalHigh : 8 * α < μ.real {ω |
      martingaleLevel <
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          H.martingalePart T ω})
    (hGainError : (normBound / gainLevel) ^ 2 ≤ α)
    (hExcursionError : (4 * (k : ℝ) / R) ^ 2 ≤ α)
    {i : ℕ} (hi : i < k) :
    α ^ 2 < μ.real {ω |
      Lemma47ExcursionStopping.increment
        (lemma47LocalizedMartingaleProcess H (lemma47FirstScale n)
          martingaleLevel gainLevel T) T i ω ≤ -α} := by
  have hScale : 0 < lemma47FirstScale n := by
    unfold lemma47FirstScale
    positivity
  have hHigh := lemma47LocalizedMartingaleProcess_highMaximum hUsual H
    hMartingaleLeft hMartingaleZero hScale hMartingaleLevel hGainLevel
    gainEnvelope hGainEnvelope hGainBound hNormBound hGainNorm hT
    hRScale hOriginalHigh hGainError
  exact C.lemma47FirstLocalized_negativeExcursion hUsual H
    hMartingaleLeft hMartingaleZero hn hMartingaleLevel gainLevel
    gainEnvelope hGainEnvelope hGainBound hGainNorm hJumpNumeric hT hk
    hR hα hαOne hHigh hExcursionError hi

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
