/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.DownsideStopping
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope

/-!
# Vanishing-risk claims in Lemma 4.7

The positive Hahn excursions have already been aggregated into a strategy
whose finite-variation part is increasing and whose martingale terminal
increment has second moment at most `4k`.  This module turns those two facts
into the quantitative terminal estimate used in the NFLVR contradiction.

One continuous-time Doob envelope controls both possible losses: it prevents
the downside passage before the deterministic horizon and bounds the terminal
martingale error.  Thus no independence or continuous-time martingale
regularization beyond the martingale already produced by the first
localization is needed.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus

open SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

omit [IsProbabilityMeasure μ] in
/-- A terminal second-moment bound gives the corresponding real `L²`
seminorm bound. -/
theorem eLpNorm_terminalIncrement_le_two_mul_sqrt
    {Z : Ω → ℝ} (hZ : MemLp Z (2 : ℝ≥0∞) μ) {k : ℕ}
    (hSecond : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤ 4 * k) :
    eLpNorm Z (2 : ℝ≥0∞) μ ≤
      ENNReal.ofReal (2 * Real.sqrt (k : ℝ)) := by
  apply (ENNReal.toReal_le_toReal hZ.eLpNorm_ne_top
    ENNReal.ofReal_ne_top).mp
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hZ,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
  calc
    Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤
        Real.sqrt (4 * (k : ℝ)) := Real.sqrt_le_sqrt hSecond
    _ = 2 * Real.sqrt (k : ℝ) := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [show (4 : ℝ) * (k : ℝ) =
          (2 * Real.sqrt (k : ℝ)) ^ 2 by
        nlinarith [Real.sq_sqrt hk]]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      positivity

/--
Quantitative downside-stopping estimate for an already aggregated positive
Hahn strategy.

If the increasing finite-variation increment exceeds `q` on mass at least
`p`, then after stopping at downside `d` and multiplying by `c`, the terminal
gain exceeds `c * (q - d)` except for the Doob-envelope error.  The same
strategy is bounded below at every time by the downside level plus one jump
overshoot.
-/
theorem lemma47StopDownsideAndRescale_positiveMass
    (C : SIntegrableProcessStoppingCalculus D)
    (R : SIntegrableStrategy D)
    (hRMartingale : Martingale R.martingalePart ℱ μ)
    {k : ℕ}
    (hTerminalMem : MemLp
      (fun ω => R.martingalePart T ω - R.martingalePart 0 ω)
      (2 : ℝ≥0∞) μ)
    (hSecond :
      (∫ ω, ‖R.martingalePart T ω - R.martingalePart 0 ω‖ ^ 2 ∂μ) ≤
        4 * k)
    (hRLeft : ProcessHasLeftLimits R.stochasticIntegral)
    (hRZero : R.stochasticIntegral 0 =ᵐ[μ] 0)
    (hIncreasing : ∀ᵐ ω ∂μ, ∀ a b, a ≤ b →
      0 ≤ R.finiteVariationPart b ω - R.finiteVariationPart a ω)
    {p q c d J : ℝ}
    (hMass : p ≤ μ.real {ω |
      q ≤ R.finiteVariationPart T ω - R.finiteVariationPart 0 ω})
    (hc : 0 ≤ c) (hd : 0 < d) (hJ : 0 ≤ J)
    (hJump : ∀ᵐ ω ∂μ, ∀ t,
      -J ≤ processLeftJump R.stochasticIntegral t ω) :
    let V := C.lemma47StopDownsideAndRescale R c d T
    (∀ᵐ ω ∂μ, ∀ t,
        -(c * (d + J)) ≤ V.stochasticIntegral t ω) ∧
      p - (4 * Real.sqrt (k : ℝ) / d) ^ 2 ≤
        μ.real {ω |
          c * (q - d) ≤ V.stochasticIntegral T ω} := by
  let N : Process Ω := fun t ω =>
    R.martingalePart t ω - R.martingalePart 0 ω
  let G : Ω → ℝ :=
    FactorialChronologicalGrid.martingaleAbsoluteEnvelope N T
  let V := C.lemma47StopDownsideAndRescale R c d T
  have hConstant : Martingale
      (fun _ => R.martingalePart 0) ℱ μ :=
    martingale_const_fun ℱ μ (hRMartingale.stronglyMeasurable 0)
      (hRMartingale.integrable 0)
  have hNMartingale : Martingale N ℱ μ := by
    exact hRMartingale.sub hConstant
  have hNRight : ∀ ω t,
      ContinuousWithinAt (N · ω) (Set.Ici t) t := by
    intro ω t
    exact (R.martingalePart_isRightContinuous ω t).sub
      continuousWithinAt_const
  have hTerminalNorm :
      eLpNorm (N T) (2 : ℝ≥0∞) μ ≤
        ENNReal.ofReal (2 * Real.sqrt (k : ℝ)) := by
    exact eLpNorm_terminalIncrement_le_two_mul_sqrt hTerminalMem hSecond
  have hGMem : MemLp G (2 : ℝ≥0∞) μ :=
    FactorialChronologicalGrid.Martingale.martingaleAbsoluteEnvelope_memLp
      hNMartingale T hTerminalMem
  have hGNorm : eLpNorm G (2 : ℝ≥0∞) μ ≤
      ENNReal.ofReal (4 * Real.sqrt (k : ℝ)) := by
    calc
      eLpNorm G (2 : ℝ≥0∞) μ ≤
          2 * eLpNorm (N T) (2 : ℝ≥0∞) μ :=
        FactorialChronologicalGrid.Martingale.eLpNorm_martingaleAbsoluteEnvelope_le_two_mul
          hNMartingale T hTerminalMem
      _ ≤ 2 * ENNReal.ofReal (2 * Real.sqrt (k : ℝ)) := by
        gcongr
      _ = ENNReal.ofReal (4 * Real.sqrt (k : ℝ)) := by
        rw [← ENNReal.ofReal_ofNat]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have hGDom : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → ‖N t ω‖ ≤ G ω :=
    FactorialChronologicalGrid.Martingale.norm_le_martingaleAbsoluteEnvelope_ae
      hNMartingale T hTerminalMem hNRight
  have hBad : μ.real {ω | d < G ω} ≤
      (4 * Real.sqrt (k : ℝ) / d) ^ 2 := by
    simpa only [G, N,
      FactorialChronologicalGrid.martingaleAbsoluteEnvelope,
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope] using
      (FactorialChronologicalGrid.probReal_finiteHorizonAbsoluteEnvelope_gt_le
        hNMartingale.stronglyAdapted T hGMem hGDom
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hd hGNorm)
  have hLower : ∀ᵐ ω ∂μ, ∀ t,
      -(c * (d + J)) ≤ V.stochasticIntegral t ω :=
    C.lemma47StopDownsideAndRescale_lower_bound R hRLeft hc hd.le hJ T
      hRZero hJump
  have hTerminalEq :=
    C.lemma47StopDownsideAndRescale_terminal_eq_of_noPassage R c d T
  have hSubset :
      {ω | q ≤ R.finiteVariationPart T ω -
        R.finiteVariationPart 0 ω} ≤ᵐ[μ]
      Set.union
        {ω | c * (q - d) ≤ V.stochasticIntegral T ω}
        {ω | d < G ω} := by
    filter_upwards [hRZero, hIncreasing, hGDom,
      R.integral_decomposition, hTerminalEq] with
        ω hZero hIncreasingω hGDomω hDecomp hTerminalEqω
    intro hDrift
    by_cases hBadω : d < G ω
    · exact Set.mem_union_right _ hBadω
    · apply Set.mem_union_left
      have hNBound : ∀ t, t ≤ T →
          |R.martingalePart t ω - R.martingalePart 0 ω| ≤ d := by
        intro t ht
        simpa only [N, Real.norm_eq_abs] using
          (hGDomω t ht).trans (le_of_not_gt hBadω)
      have hNoPassage :
          (T : WithTop ℝ≥0) ≤
            lowerStrictHittingAfter R.stochasticIntegral d ω :=
        le_lowerStrictHittingAfter_of_decomposition
          R.stochasticIntegral R.martingalePart R.finiteVariationPart
          d T ω hDecomp (by simpa only [Pi.zero_apply] using hZero)
          (fun t ht => hIncreasingω 0 t bot_le) hNBound
      have hTerminal := hTerminalEqω hNoPassage
      have hComponentsZero :
          R.martingalePart 0 ω + R.finiteVariationPart 0 ω = 0 := by
        rw [← hDecomp 0, hZero]
        simp only [Pi.zero_apply]
      have hMartingaleLower :
          -d ≤ R.martingalePart T ω - R.martingalePart 0 ω :=
        (neg_le_neg (hNBound T le_rfl)).trans
          (neg_abs_le (R.martingalePart T ω - R.martingalePart 0 ω))
      have hGainLower : q - d ≤ R.stochasticIntegral T ω := by
        change q ≤ R.finiteVariationPart T ω -
          R.finiteVariationPart 0 ω at hDrift
        rw [hDecomp T]
        linarith
      change c * (q - d) ≤ V.stochasticIntegral T ω
      rw [hTerminal]
      exact mul_le_mul_of_nonneg_left hGainLower hc
  have hDriftUnion :
      μ.real {ω | q ≤ R.finiteVariationPart T ω -
          R.finiteVariationPart 0 ω} ≤
        μ.real {ω | c * (q - d) ≤ V.stochasticIntegral T ω} +
          μ.real {ω | d < G ω} := by
    exact (ENNReal.toReal_mono (by finiteness)
      (measure_mono_ae hSubset)).trans
        (measureReal_union_le _ _)
  refine ⟨hLower, ?_⟩
  linarith

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
