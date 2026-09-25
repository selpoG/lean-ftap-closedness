/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.VanishingRisk
import FTAPTheorem42.Stochastic.DS.Lemma47.ActualHahnFiniteAggregation

/-!
# Actual-first vanishing-risk strategy for Lemma 4.7

This module carries the intrinsic Hahn graph through downside stopping and
normalization.  The analytic downside estimate is reused on the underlying
raw record, while the resulting strategy remains in the intrinsic
local-completed carrier by its concrete scalar and stopping calculi.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The normalized Lemma 4.7 strategy formed entirely by intrinsic actual
operations. -/
noncomputable def actualLemma47VanishingRiskStrategy
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (alpha : Real) (n : Nat) (T : NNReal)
    (P : PredictablePathwiseHahnSeparator
      ((SIntegrableStrategy.processStoppingCalculus D).lemma47RescaleAndStopUpTo
          H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T)) :
    ActualSIntegrableStrategy (realizationModel G) :=
  let k := lemma47ExcursionCount alpha n
  let CstopRaw := (SIntegrableStrategy.processStoppingCalculus D)
  let Cscalar := actualScalarCalculus G
  let Cstop := actualStoppingCalculus G CstopRaw
  let L := Cscalar.lemma47RescaleAndStopUpTo Cstop H
    (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T
  let X := SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess
    H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T
  let tau := Lemma47ExcursionStopping.time X T k
  let hTau := Lemma47ExcursionStopping.time_isStoppingTime
    (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isStronglyAdapted
      H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T)
    (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isRightContinuous
      H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T) T k
  let R := actualStopHahnPositiveCadlag hGLeft (L := L) P tau hTau
  Cscalar.lemma47StopDownsideAndRescale Cstop R
    ((k : Real)⁻¹) (lemma47DownsideLevel alpha n) T

/-- The intrinsic vanishing-risk strategy is constant after its selected
deterministic horizon. -/
theorem actualLemma47VanishingRiskStrategy_stochasticIntegral_eq_terminal_of_le
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (alpha : Real) (n : Nat) (T : NNReal)
    (P : PredictablePathwiseHahnSeparator
      ((SIntegrableStrategy.processStoppingCalculus D).lemma47RescaleAndStopUpTo
          H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T)) :
    ∀ᵐ omega ∂mu, ∀ t, T <= t ->
      (actualLemma47VanishingRiskStrategy  hGLeft H alpha n T P
        ).val.stochasticIntegral t omega =
      (actualLemma47VanishingRiskStrategy  hGLeft H alpha n T P
        ).val.stochasticIntegral T omega := by
  let k := lemma47ExcursionCount alpha n
  let CstopRaw := (SIntegrableStrategy.processStoppingCalculus D)
  let Cscalar := actualScalarCalculus G
  let Cstop := actualStoppingCalculus G CstopRaw
  let L := Cscalar.lemma47RescaleAndStopUpTo Cstop H
    (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T
  let X := SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess
    H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T
  let tau := Lemma47ExcursionStopping.time X T k
  let hTau := Lemma47ExcursionStopping.time_isStoppingTime
    (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isStronglyAdapted
      H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T)
    (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isRightContinuous
      H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T) T k
  let R := actualStopHahnPositiveCadlag hGLeft (L := L) P tau hTau
  change ∀ᵐ omega ∂mu, ∀ t, T <= t ->
    (Cscalar.lemma47StopDownsideAndRescale Cstop R
      ((k : Real)⁻¹) (lemma47DownsideLevel alpha n) T
      ).val.stochasticIntegral t omega =
    (Cscalar.lemma47StopDownsideAndRescale Cstop R
      ((k : Real)⁻¹) (lemma47DownsideLevel alpha n) T
      ).val.stochasticIntegral T omega
  exact
    CstopRaw.lemma47StopDownsideAndRescale_stochasticIntegral_eq_terminal_of_le
      R.val ((k : Real)⁻¹) (lemma47DownsideLevel alpha n) T

/-- At one Lemma 4.7 scale, the actual-first restriction produces an actual
strategy with vanishing downside and the required terminal positive mass. -/
theorem actualFirstLocalized_hahnPositive_stopDownside_of_originalHigh
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (hUsual : Filtration.UsualConditions mu F)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (hMartingaleLeft : ProcessHasLeftLimits H.val.martingalePart)
    (hGainLeft : ProcessHasLeftLimits H.val.stochasticIntegral)
    (hMartingaleZero : H.val.martingalePart 0 =ᵐ[mu] 0)
    (hAdmissible : ∀ᵐ omega ∂mu, ∀ t,
      (-1 : Real) <= H.val.stochasticIntegral t omega)
    {n : Nat} (hn : 0 < n)
    {alpha : Real} (hAlpha : 0 < alpha) (hAlphaQuarter : alpha <= 1 / 4)
    (hk : 0 < lemma47ExcursionCount alpha n)
    (gainEnvelope : Omega → Real)
    (hGainEnvelope : MemLp gainEnvelope (2 : ENNReal) mu)
    (hGainBound : ∀ᵐ omega ∂mu, ∀ t,
      |H.val.stochasticIntegral t omega| <= gainEnvelope omega)
    {normBound : Real} (hNormBound : 0 <= normBound)
    (hGainNorm : eLpNorm gainEnvelope (2 : ENNReal) mu <=
      ENNReal.ofReal normBound)
    (hJumpNumeric : 6 * normBound <= (n : Real) ^ 2)
    {T : NNReal} (hT : 0 < T)
    (hOriginalHigh : 8 * alpha < mu.real {omega |
      (n : Real) ^ 3 <
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          H.val.martingalePart T omega})
    (hGainError : (normBound / (n : Real)) ^ 2 <= alpha)
    (hPositiveMass : 0 <= lemma47ExcursionMass alpha normBound n)
    (P : PredictablePathwiseHahnSeparator
      ((SIntegrableStrategy.processStoppingCalculus D).lemma47RescaleAndStopUpTo
          H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T)) :
    let k := lemma47ExcursionCount alpha n
    let CstopRaw := (SIntegrableStrategy.processStoppingCalculus D)
    let Cscalar := actualScalarCalculus G
    let Cstop := actualStoppingCalculus G CstopRaw
    let L := Cscalar.lemma47RescaleAndStopUpTo Cstop H
      (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T
    let X := SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess
      H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T
    let tau := Lemma47ExcursionStopping.time X T k
    let hTau := Lemma47ExcursionStopping.time_isStoppingTime
      (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isStronglyAdapted
        H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T)
      (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isRightContinuous
        H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T) T k
    let R := actualStopHahnPositiveCadlag hGLeft (L := L) P tau hTau
    let V := Cscalar.lemma47StopDownsideAndRescale Cstop R
      ((k : Real)⁻¹) (lemma47DownsideLevel alpha n) T
    (∀ᵐ omega ∂mu, ∀ t,
        -lemma47Downside alpha n <= V.val.stochasticIntegral t omega) /\
      lemma47TerminalMass alpha normBound n <=
        mu.real {omega |
          lemma47TerminalLevel alpha normBound n <=
            V.val.stochasticIntegral T omega} := by
  let k := lemma47ExcursionCount alpha n
  have hk' : 0 < k := hk
  let CstopRaw := (SIntegrableStrategy.processStoppingCalculus D)
  let Cscalar := actualScalarCalculus G
  let Cstop := actualStoppingCalculus G CstopRaw
  let L := Cscalar.lemma47RescaleAndStopUpTo Cstop H
    (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T
  let X := SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess
    H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T
  let tau := Lemma47ExcursionStopping.time X T k
  let hTau := Lemma47ExcursionStopping.time_isStoppingTime
    (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isStronglyAdapted
      H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T)
    (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isRightContinuous
      H.val (lemma47FirstScale n) ((n : Real) ^ 3) (n : Real) T) T k
  let R := actualStopHahnPositiveCadlag hGLeft (L := L) P tau hTau
  let c : Real := (k : Real)⁻¹
  let d : Real := lemma47DownsideLevel alpha n
  let V := Cscalar.lemma47StopDownsideAndRescale Cstop R c d T
  have hAlphaOne : alpha <= 1 := hAlphaQuarter.trans (by norm_num)
  have hAggregation :=
    actualFirstLocalized_hahnPositive_finiteAggregation_of_originalHigh
       hGLeft hUsual H hMartingaleLeft hMartingaleZero hn
      (by positivity : 0 <= (n : Real) ^ 3)
      (by exact_mod_cast hn : 0 < (n : Real))
      gainEnvelope hGainEnvelope hGainBound hNormBound hGainNorm
      hJumpNumeric hT hk'
      (by positivity : 0 < (n : Real) / 2)
      (lemma47_half_lt_firstScale_mul_cube hn)
      hAlpha hAlphaOne hOriginalHigh hGainError
      (lemma47_excursionError_le hAlpha hAlphaQuarter hn)
      hPositiveMass P
  have hLLeftRaw := CstopRaw.lemma47RescaleAndStopUpTo_hasLeftLimits
    H.val hMartingaleLeft hGainLeft (lemma47FirstScale n)
      ((n : Real) ^ 3) (n : Real) T
  have hLLeft : ProcessHasLeftLimits L.val.martingalePart /\
      ProcessHasLeftLimits L.val.stochasticIntegral := by
    exact hLLeftRaw
  have hRLeft := actualStopHahnPositiveCadlag_hasLeftLimits hGLeft (L := L) P tau hTau
  have hRZero := actualStopHahnPositiveCadlag_stochasticIntegral_zero hGLeft (L := L) P tau hTau
  have hRIncreasing :=
    actualStopHahnPositiveCadlag_finiteVariation_increment_nonnegative hGLeft (L := L) P tau hTau
  have hScaleNonnegative : 0 <= lemma47FirstScale n := by
    unfold lemma47FirstScale
    positivity
  have hLJumpRaw :=
    CstopRaw.lemma47RescaleAndStopUpTo_stochasticIntegral_leftJump_lower_bound
      H.val hGainLeft (martingaleLevel := (n : Real) ^ 3)
      hScaleNonnegative (Nat.cast_nonneg n) T hAdmissible
  have hLJump : ∀ᵐ omega ∂mu, ∀ t,
      -(lemma47FirstScale n * ((n : Real) + 1)) <=
        processLeftJump L.val.stochasticIntegral t omega := by
    exact hLJumpRaw
  have hExactJumpNonnegative :
      0 <= lemma47FirstScale n * ((n : Real) + 1) := by positivity
  have hRJumpExact :=
    actualStopHahnPositiveCadlag_stochasticIntegral_leftJump_lower_bound hGLeft (L := L) P
      hLLeft.2 tau hTau hExactJumpNonnegative hLJump
  have hRJump : ∀ᵐ omega ∂mu, ∀ t,
      -(2 / (n : Real)) <=
        processLeftJump R.val.stochasticIntegral t omega := by
    filter_upwards [hRJumpExact] with omega hJumpOmega
    intro t
    exact (neg_le_neg (lemma47FirstScale_mul_succ_le_two_div hn)).trans
      (hJumpOmega t)
  have hc : 0 <= c := inv_nonneg.mpr (Nat.cast_nonneg k)
  have hd : 0 < d := by
    dsimp [d, lemma47DownsideLevel]
    positivity
  have hJ : 0 <= 2 / (n : Real) := by positivity
  have hQuantitativeRaw :=
    CstopRaw.lemma47StopDownsideAndRescale_positiveMass R.val hAggregation.1
      hAggregation.2.1 hAggregation.2.2.1 hRLeft.2 hRZero hRIncreasing
      hAggregation.2.2.2 hc hd hJ hRJump
  have hQuantitative :
      (∀ᵐ omega ∂mu, ∀ t,
          -(c * (d + 2 / (n : Real))) <=
            V.val.stochasticIntegral t omega) /\
        lemma47ExcursionMass alpha normBound n / 2 -
            (4 * Real.sqrt (k : Real) / d) ^ 2 <=
          mu.real {omega |
            c * ((k : Real) * (alpha / 2) *
                lemma47ExcursionMass alpha normBound n / 2 - d) <=
              V.val.stochasticIntegral T omega} := by
    exact hQuantitativeRaw
  have hkReal : (k : Real) ≠ 0 := (Nat.cast_pos.mpr hk').ne'
  have hnReal : (n : Real) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hRiskEq : c * (d + 2 / (n : Real)) =
      lemma47Downside alpha n := by
    dsimp [c, d, k, lemma47DownsideLevel, lemma47Downside]
    field_simp
  have hLevelEq :
      c * ((k : Real) * (alpha / 2) *
          lemma47ExcursionMass alpha normBound n / 2 - d) =
        lemma47TerminalLevel alpha normBound n := by
    dsimp [c, d, k, lemma47DownsideLevel, lemma47TerminalLevel]
    field_simp
    ring
  rcases hQuantitative with ⟨hLower, hMass⟩
  constructor
  · filter_upwards [hLower] with omega hLowerOmega
    intro t
    rw [← hRiskEq]
    exact hLowerOmega t
  · change lemma47ExcursionMass alpha normBound n / 2 -
        (4 * Real.sqrt (k : Real) / d) ^ 2 <=
      mu.real {omega | lemma47TerminalLevel alpha normBound n <=
        V.val.stochasticIntegral T omega}
    rw [← hLevelEq]
    exact hMass

end LocalCompletedM2A

end FTAPTheorem42
