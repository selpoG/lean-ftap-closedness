/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.ExcursionOrthogonality
import FTAPTheorem42.Stochastic.DS.Lemma47.FiniteVariationExcursion
import FTAPTheorem42.Stochastic.DS.Lemma47.Probability
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePathwiseRestrictionCalculus
import FTAPTheorem42.Stochastic.DS.Lemma47.ActualHahnRestriction
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualConvexCombination
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.DirectStopping

/-! # Finite Hahn excursion aggregation

Aggregate the martingale and positive-drift estimates for the actual Hahn
restriction, then apply them to the first rescaled and localized strategy. -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal MeasureTheory NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The first `k` positive Hahn-restricted excursions aggregate on the
intrinsic actual carrier, with the same terminal martingale and drift bounds
as in the raw analytic theorem. -/
theorem actualHahnPositiveCadlag_finiteAggregation
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {L : ActualSIntegrableStrategy (realizationModel G)}
    (P : PredictablePathwiseHahnSeparator L.val)
    {X : Process Omega} (hX : Martingale X F mu)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (hLX : ProcessIndistinguishable mu L.val.martingalePart X)
    (T : NNReal) (J : Nat -> Omega -> Real)
    (hJ : ∀ n omega, 0 <= J n omega)
    (hJMem : ∀ n, MemLp (J n) (2 : ENNReal) mu)
    (hJump : ∀ n, ∀ᵐ omega ∂mu, ∀ t,
      |processLeftJump (Lemma47ExcursionStopping.displacementAfter X
        (Lemma47ExcursionStopping.time X T n)) t omega| <= J n omega)
    (hJNorm : ∀ n, eLpNorm (J n) (2 : ENNReal) mu <= 1)
    {k : Nat} (hk : 0 < k)
    {a b : Real} (ha : 0 <= a) (hb : 0 <= b)
    (hMass : ∀ i < k, b <= mu.real {omega |
      a <= Lemma47ExcursionStopping.incrementAlong
        X L.val.finiteVariationPart T i omega}) :
    let tau := Lemma47ExcursionStopping.time X T k
    let hTau := Lemma47ExcursionStopping.time_isStoppingTime
      hX.stronglyAdapted hXRight T k
    let R := actualStopHahnPositiveCadlag hGLeft P tau hTau
    Martingale R.val.martingalePart F mu /\
      MemLp (fun omega => R.val.martingalePart T omega -
        R.val.martingalePart 0 omega) (2 : ENNReal) mu /\
      (∫ omega, ‖R.val.martingalePart T omega -
        R.val.martingalePart 0 omega‖ ^ 2 ∂mu) <= 4 * k /\
      b / 2 <= mu.real {omega |
        (k : Real) * a * b / 2 <=
          R.val.finiteVariationPart T omega -
            R.val.finiteVariationPart 0 omega} := by
  let tau := Lemma47ExcursionStopping.time X T k
  let hTau := Lemma47ExcursionStopping.time_isStoppingTime
    hX.stronglyAdapted hXRight T k
  let R0 := actualHahnPositiveRestrictionCadlag hGLeft P
  let R := actualStopHahnPositiveCadlag hGLeft P tau hTau
  have hLMartingale : Martingale L.val.martingalePart F mu := by
    apply hX.congr L.val.martingalePart_isStronglyAdapted
    intro t
    exact (hLX.eventuallyEq_at t).symm
  have hIncrementEq :
      (fun omega => L.val.martingalePart (tau omega) omega -
        L.val.martingalePart 0 omega) =ᵐ[mu]
        Lemma47ExcursionStopping.accumulatedIncrement X T k := by
    filter_upwards [hLX] with omega hOmega
    unfold tau Lemma47ExcursionStopping.accumulatedIncrement
      Lemma47ExcursionStopping.sample
    rw [hOmega, hOmega]
    simp only [Lemma47ExcursionStopping.time_zero]
  have hAccumulatedMem :=
    Lemma47ExcursionStopping.accumulatedIncrement_memLp_two
      hX.stronglyAdapted hXRight hXLeft T J hJ hJMem hJump k
  have hLIncrementMem : MemLp
      (fun omega => L.val.martingalePart (tau omega) omega -
        L.val.martingalePart 0 omega) (2 : ENNReal) mu :=
    (memLp_congr_ae hIncrementEq).2 hAccumulatedMem
  have hRestricted := actualStopHahnPositiveCadlag_martingale_l2 hGLeft P tau hTau T
    (Lemma47ExcursionStopping.time_le X T k)
      hLMartingale hLIncrementMem
  have hAccumulatedBound :=
    Lemma47ExcursionStopping.integral_sq_accumulatedIncrement_le_four_mul
      hX hXRight hXLeft T J hJ hJMem hJump hJNorm k
  have hBaseBound :
      (∫ omega, ‖L.val.martingalePart (tau omega) omega -
        L.val.martingalePart 0 omega‖ ^ 2 ∂mu) <= 4 * k := by
    calc
      (∫ omega, ‖L.val.martingalePart (tau omega) omega -
          L.val.martingalePart 0 omega‖ ^ 2 ∂mu) =
          ∫ omega,
            Lemma47ExcursionStopping.accumulatedIncrement X T k omega ^ 2
              ∂mu := by
        apply integral_congr_ae
        filter_upwards [hIncrementEq] with omega hOmega
        rw [hOmega]
        simp only [Real.norm_eq_abs, sq_abs]
      _ <= 4 * k := hAccumulatedBound
  have hMartingaleBound :
      (∫ omega, ‖R.val.martingalePart T omega -
        R.val.martingalePart 0 omega‖ ^ 2 ∂mu) <= 4 * k :=
    hRestricted.2.2.trans hBaseBound
  let g : Nat -> Omega -> Real := fun i omega =>
    max (Lemma47ExcursionStopping.incrementAlong
      X R0.val.finiteVariationPart T i omega) 0
  have hR0Increment :=
    actualHahnPositiveRestrictionCadlag_finiteVariation_increment_ae hGLeft P
  have hgMeas : ∀ i ∈ Finset.range k, StronglyMeasurable (g i) := by
    intro i _hi
    have hInc := Lemma47ExcursionStopping.stronglyMeasurable_incrementAlong
      hX.stronglyAdapted hXRight
      R0.val.finiteVariationPart_isPredictable.stronglyAdapted
      R0.val.finiteVariationPart_isRightContinuous T i
    exact continuous_max.comp_stronglyMeasurable
      (hInc.prodMk stronglyMeasurable_const)
  have hgNonnegative : ∀ i ∈ Finset.range k, ∀ omega,
      0 <= g i omega := by
    intro i _hi omega
    exact le_max_right _ _
  have hgMass : ∀ i ∈ Finset.range k,
      b <= mu.real {omega | a <= g i omega} := by
    intro i hi
    have hi : i < k := Finset.mem_range.1 hi
    have hSubset : {omega |
        a <= Lemma47ExcursionStopping.incrementAlong
          X L.val.finiteVariationPart T i omega} ≤ᵐ[mu]
        {omega | a <= g i omega} := by
      filter_upwards [hR0Increment] with omega hOmega hOriginal
      have hDom := (hOmega
        (Lemma47ExcursionStopping.time X T i omega)
        (Lemma47ExcursionStopping.time X T (i + 1) omega)
        (Lemma47ExcursionStopping.time_mono X T i omega)).2
      change a <= max (Lemma47ExcursionStopping.incrementAlong
        X R0.val.finiteVariationPart T i omega) 0
      exact hOriginal.trans (hDom.trans (le_max_left _ _))
    exact (hMass i hi).trans
      (ENNReal.toReal_mono (by finiteness) (measure_mono_ae hSubset))
  have hAggregate := probReal_sum_ge_of_each_ge
    (μ := mu) (Finset.range k)
    (show (Finset.range k).Nonempty from ⟨0, Finset.mem_range.2 hk⟩)
    g hgMeas ha hb hgNonnegative hgMass
  have hAggregate' : b / 2 <= mu.real {omega |
      (k : Real) * a * b / 2 <= ∑ i ∈ Finset.range k, g i omega} := by
    simpa only [Finset.card_range] using hAggregate
  have hStoppedFiniteVariation : ProcessIndistinguishable mu
      R.val.finiteVariationPart
      (finiteStoppedProcess R0.val.finiteVariationPart tau) := by
    exact ProcessIndistinguishable.refl mu _
  have hAggregateToTerminal : {omega |
      (k : Real) * a * b / 2 <= ∑ i ∈ Finset.range k, g i omega} ≤ᵐ[mu]
      {omega | (k : Real) * a * b / 2 <=
        R.val.finiteVariationPart T omega -
          R.val.finiteVariationPart 0 omega} := by
    filter_upwards [hR0Increment, hStoppedFiniteVariation] with
      omega hOmegaIncreasing hOmegaStopped hOmegaAggregate
    have hgEq (i : Nat) (hi : i < k) :
        g i omega = Lemma47ExcursionStopping.incrementAlong
          X R0.val.finiteVariationPart T i omega := by
      unfold g
      rw [max_eq_left]
      exact (hOmegaIncreasing
        (Lemma47ExcursionStopping.time X T i omega)
        (Lemma47ExcursionStopping.time X T (i + 1) omega)
        (Lemma47ExcursionStopping.time_mono X T i omega)).1
    have hSum : (∑ i ∈ Finset.range k, g i omega) =
        R0.val.finiteVariationPart (tau omega) omega -
          R0.val.finiteVariationPart 0 omega := by
      calc
        (∑ i ∈ Finset.range k, g i omega) =
            ∑ i ∈ Finset.range k,
              Lemma47ExcursionStopping.incrementAlong
                X R0.val.finiteVariationPart T i omega := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hgEq i (Finset.mem_range.1 hi)
        _ = R0.val.finiteVariationPart (tau omega) omega -
            R0.val.finiteVariationPart 0 omega := by
          unfold Lemma47ExcursionStopping.incrementAlong
            Lemma47ExcursionStopping.sampleAlong tau
          rw [Finset.sum_range_sub (fun i =>
            R0.val.finiteVariationPart
              (Lemma47ExcursionStopping.time X T i omega) omega)]
          simp only [Lemma47ExcursionStopping.time_zero]
    have hAtT : R.val.finiteVariationPart T omega =
        R0.val.finiteVariationPart (tau omega) omega := by
      rw [hOmegaStopped T]
      unfold finiteStoppedProcess
      rw [MeasureTheory.stoppedProcess_eq_of_ge]
      · simp only [WithTop.untopA_eq_untop WithTop.coe_ne_top,
          WithTop.untop_coe]
      · exact WithTop.coe_le_coe.mpr
          (Lemma47ExcursionStopping.time_le X T k omega)
    have hAtZero : R.val.finiteVariationPart 0 omega =
        R0.val.finiteVariationPart 0 omega := by
      rw [hOmegaStopped 0]
      unfold finiteStoppedProcess
      rw [MeasureTheory.stoppedProcess_eq_of_le]
      exact bot_le
    change (k : Real) * a * b / 2 <=
      R.val.finiteVariationPart T omega -
        R.val.finiteVariationPart 0 omega
    change (k : Real) * a * b / 2 <=
      ∑ i ∈ Finset.range k, g i omega at hOmegaAggregate
    rw [hAtT, hAtZero, ← hSum]
    exact hOmegaAggregate
  refine ⟨hRestricted.1, hRestricted.2.1, hMartingaleBound, ?_⟩
  exact hAggregate'.trans
    (ENNReal.toReal_mono (by finiteness)
      (measure_mono_ae hAggregateToTerminal))

/-- The original high-martingale event produces the stopped actual-first
Hahn strategy together with the martingale and positive-drift bounds needed
by the downside-stopping step of Lemma 4.7. -/
theorem actualFirstLocalized_hahnPositive_finiteAggregation_of_originalHigh
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (hUsual : Filtration.UsualConditions mu F)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (hMartingaleLeft : ProcessHasLeftLimits H.val.martingalePart)
    (hMartingaleZero : H.val.martingalePart 0 =ᵐ[mu] 0)
    {n : Nat} (hn : 0 < n)
    {martingaleLevel : Real} (hMartingaleLevel : 0 <= martingaleLevel)
    {gainLevel : Real} (hGainLevel : 0 < gainLevel)
    (gainEnvelope : Omega → Real)
    (hGainEnvelope : MemLp gainEnvelope (2 : ENNReal) mu)
    (hGainBound : ∀ᵐ omega ∂mu, ∀ t,
      |H.val.stochasticIntegral t omega| <= gainEnvelope omega)
    {normBound : Real} (hNormBound : 0 <= normBound)
    (hGainNorm : eLpNorm gainEnvelope (2 : ENNReal) mu <=
      ENNReal.ofReal normBound)
    (hJumpNumeric : 6 * normBound <= (n : Real) ^ 2)
    {T : NNReal} (hT : 0 < T)
    {k : Nat} (hk : 0 < k) {Rlevel alpha : Real}
    (hRlevel : 0 < Rlevel)
    (hRScale : Rlevel < lemma47FirstScale n * martingaleLevel)
    (hAlpha : 0 < alpha) (hAlphaOne : alpha <= 1)
    (hOriginalHigh : 8 * alpha < mu.real {omega |
      martingaleLevel <
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          H.val.martingalePart T omega})
    (hGainError : (normBound / gainLevel) ^ 2 <= alpha)
    (hExcursionError : (4 * (k : Real) / Rlevel) ^ 2 <= alpha)
    (hPositiveMass : 0 <=
      alpha ^ 2 - (4 * lemma47FirstScale n * normBound / alpha) ^ 2)
    (P : PredictablePathwiseHahnSeparator
      ((SIntegrableStrategy.processStoppingCalculus D).lemma47RescaleAndStopUpTo
          H.val (lemma47FirstScale n) martingaleLevel gainLevel T)) :
    let CstopRaw := (SIntegrableStrategy.processStoppingCalculus D)
    let Cscalar := actualScalarCalculus G
    let Cstop := actualStoppingCalculus G CstopRaw
    let L := Cscalar.lemma47RescaleAndStopUpTo Cstop H
      (lemma47FirstScale n) martingaleLevel gainLevel T
    let X := SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess
      H.val (lemma47FirstScale n) martingaleLevel gainLevel T
    let tau := Lemma47ExcursionStopping.time X T k
    let hTau := Lemma47ExcursionStopping.time_isStoppingTime
      (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isStronglyAdapted
        H.val
        (lemma47FirstScale n) martingaleLevel gainLevel T)
      (SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isRightContinuous
        H.val
        (lemma47FirstScale n) martingaleLevel gainLevel T) T k
    let R := actualStopHahnPositiveCadlag hGLeft (L := L) P tau hTau
    Martingale R.val.martingalePart F mu /\
      MemLp (fun omega => R.val.martingalePart T omega -
        R.val.martingalePart 0 omega) (2 : ENNReal) mu /\
      (∫ omega, ‖R.val.martingalePart T omega -
        R.val.martingalePart 0 omega‖ ^ 2 ∂mu) <= 4 * k /\
      (alpha ^ 2 -
          (4 * lemma47FirstScale n * normBound / alpha) ^ 2) / 2 <=
        mu.real {omega |
          (k : Real) * (alpha / 2) *
              (alpha ^ 2 -
                (4 * lemma47FirstScale n * normBound / alpha) ^ 2) / 2 <=
            R.val.finiteVariationPart T omega -
              R.val.finiteVariationPart 0 omega} := by
  let CstopRaw := (SIntegrableStrategy.processStoppingCalculus D)
  let Cscalar := actualScalarCalculus G
  let Cstop := actualStoppingCalculus G CstopRaw
  let L := Cscalar.lemma47RescaleAndStopUpTo Cstop H
    (lemma47FirstScale n) martingaleLevel gainLevel T
  let X := SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess
    H.val (lemma47FirstScale n) martingaleLevel gainLevel T
  obtain ⟨jumpEnvelope, hJumpMem, hJumpNonnegative, hJumpBound,
      hJumpNorm⟩ :=
    SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_jumpEnvelope_firstScale
      hUsual H.val
      hMartingaleLeft hn martingaleLevel gainLevel gainEnvelope
      hGainEnvelope hGainBound hGainNorm hJumpNumeric hT
  let J : Nat → Omega → Real := fun _ => jumpEnvelope
  have hXMartingale : Martingale X F mu := by
    apply CstopRaw.lemma47LocalizedMartingaleProcess_isMartingale
      hUsual H.val hMartingaleLeft (lemma47FirstScale n)
      martingaleLevel gainLevel _ gainEnvelope hGainEnvelope hGainBound hT
    filter_upwards [hMartingaleZero] with omega hZero
    rw [hZero, Pi.zero_apply, abs_zero]
    exact hMartingaleLevel
  have hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Set.Ici t) t :=
    SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_isRightContinuous
      H.val
      (lemma47FirstScale n) martingaleLevel gainLevel T
  have hXLeft : ProcessHasLeftLimits X :=
    SIntegrableProcessStoppingCalculus.lemma47LocalizedMartingaleProcess_hasLeftLimits
      H.val hMartingaleLeft
      (lemma47FirstScale n) martingaleLevel gainLevel T
  have hLX : ProcessIndistinguishable mu L.val.martingalePart X := by
    change ProcessIndistinguishable mu L.val.martingalePart
      (fun t omega => lemma47FirstScale n *
        MeasureTheory.stoppedProcess H.val.martingalePart
          (SIntegrableProcessStoppingCalculus.lemma47FirstPassageUpTo H.val
            martingaleLevel gainLevel T) t omega)
    exact CstopRaw.lemma47RescaleAndStopUpTo_martingalePart H.val
        (lemma47FirstScale n) martingaleLevel gainLevel T
  have hJNonnegative : ∀ j omega, 0 <= J j omega := by
    intro j omega
    exact hJumpNonnegative omega
  have hJMem : ∀ j, MemLp (J j) (2 : ENNReal) mu := by
    intro j
    exact hJumpMem
  have hJNorm : ∀ j, eLpNorm (J j) (2 : ENNReal) mu <= 1 := by
    intro j
    exact hJumpNorm
  have hDisplacementJump : ∀ j, ∀ᵐ omega ∂mu, ∀ t,
      |processLeftJump
        (Lemma47ExcursionStopping.displacementAfter X
          (Lemma47ExcursionStopping.time X T j)) t omega| <= J j omega := by
    intro j
    filter_upwards [hJumpBound] with omega hBound
    exact Lemma47ExcursionStopping.abs_processLeftJump_displacementAfter_le_at
      X hXLeft (Lemma47ExcursionStopping.time X T j) jumpEnvelope omega
        hBound
  have hMass : ∀ i < k,
      alpha ^ 2 -
          (4 * lemma47FirstScale n * normBound / alpha) ^ 2 <=
        mu.real {omega | alpha / 2 <=
          Lemma47ExcursionStopping.incrementAlong
            X L.val.finiteVariationPart T i omega} := by
    intro i hi
    have hRaw :=
      CstopRaw.lemma47FirstLocalized_finiteVariationExcursion_of_originalHigh
        hUsual H.val hMartingaleLeft hMartingaleZero hn hMartingaleLevel
        hGainLevel gainEnvelope hGainEnvelope hGainBound hNormBound hGainNorm
        hJumpNumeric hT hk hRlevel hRScale hAlpha hAlphaOne hOriginalHigh
        hGainError hExcursionError hi
    exact hRaw.le
  exact actualHahnPositiveCadlag_finiteAggregation hGLeft (L := L) P hXMartingale hXRight hXLeft
    hLX T J
      hJNonnegative hJMem hDisplacementJump hJNorm hk (by positivity)
      hPositiveMass hMass

end LocalCompletedM2A

end FTAPTheorem42
