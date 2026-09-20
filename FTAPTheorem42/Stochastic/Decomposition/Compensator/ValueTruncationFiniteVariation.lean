/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ValueTruncationPredictableLimit
import FTAPTheorem42.Stochastic.FiniteVariation.BoundedVariationLimit
import FTAPTheorem42.Stochastic.Topology.Prelocal.Basic

/-!
# The value-truncation consumer for an `L¹` finite-variation process

This module consumes the value-truncation endpoint for both Jordan components
of a zero-normalized adapted càdlàg finite-variation process.  The only
integrability assumption on the input is the terminal integrability of its
pathwise cumulative variation.  In particular, no deterministic variation
bound and no order-preservation field for arbitrary projections is used.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

omit [MeasurableSpace Ω] in
private theorem eVariationOn_sub_monotone_zero_le
    {P Q : NNReal → Real} {T : NNReal}
    (hPmono : Monotone P) (hQmono : Monotone Q)
    (hPzero : P 0 = 0) (hQzero : Q 0 = 0) :
    eVariationOn (fun t => P t - Q t) (Set.Icc 0 T) ≤
      ENNReal.ofReal (P T + Q T) := by
  have hPvar : eVariationOn P (Set.Icc 0 T) = ENNReal.ofReal (P T) := by
    simpa [hPzero] using
      ((monotoneOn_univ.2 hPmono).eVariationOn_eq
        (show (0 : NNReal) ∈ Set.univ from Set.mem_univ _)
        (show T ∈ Set.univ from Set.mem_univ _))
  have hQvar : eVariationOn Q (Set.Icc 0 T) = ENNReal.ofReal (Q T) := by
    simpa [hQzero] using
      ((monotoneOn_univ.2 hQmono).eVariationOn_eq
        (show (0 : NNReal) ∈ Set.univ from Set.mem_univ _)
        (show T ∈ Set.univ from Set.mem_univ _))
  have hPnonnegative : 0 ≤ P T := by
    rw [← hPzero]
    exact hPmono bot_le
  have hQnonnegative : 0 ≤ Q T := by
    rw [← hQzero]
    exact hQmono bot_le
  calc
    eVariationOn (fun t => P t - Q t) (Set.Icc 0 T) ≤
        eVariationOn P (Set.Icc 0 T) +
          eVariationOn (fun t => -Q t) (Set.Icc 0 T) := by
      simpa only [sub_eq_add_neg] using
        (eVariationOn_add_le_real P (fun t => -Q t) (Set.Icc 0 T))
    _ = ENNReal.ofReal (P T + Q T) := by
      rw [pathVariation_neg, hPvar, hQvar,
        ENNReal.ofReal_add hPnonnegative hQnonnegative]

/-! ## The `L¹` finite-variation input -/

structure NormalizedAdaptedCadlagFiniteVariationL1Data
    (B : Process Ω) (T : NNReal) : Prop where
  stronglyAdapted : StronglyAdapted F B
  rightContinuous : ∀ omega t,
    ContinuousWithinAt (B · omega) (Ici t) t
  hasLeftLimits : ProcessHasLeftLimits B
  boundedVariation : ∀ omega,
    BoundedVariationOn (B · omega) Set.univ
  zero : B 0 = 0
  constant_after : ∀ omega t, T ≤ t →
    B t omega = B T omega
  terminalVariation_integrable :
    Integrable (localVariation B T) mu

/-! ## The two endpoint certificates and their signed recombination -/

structure ValueTruncationFiniteVariationPredictableLimit
    (B : Process Ω) (T : NNReal) where
  plusSource : NormalizedAdaptedCadlagIncreasingProcessData
    (F := F) (commonStopJordanPositive B) T
  plusSource_terminal_integrable :
    Integrable (commonStopJordanPositive B T) mu
  minusSource : NormalizedAdaptedCadlagIncreasingProcessData
    (F := F) (commonStopJordanNegative B) T
  minusSource_terminal_integrable :
    Integrable (commonStopJordanNegative B T) mu
  plusFamily : ValueTruncationProjectionFamily
    (F := F) (mu := mu) (commonStopJordanPositive B) T
  plusTerminal : ValueTruncationProjectionTerminalL1Limit
    (F := F) (mu := mu) plusFamily
  plusCadlag : ValueTruncationProjectionCadlagLimit
    (F := F) (mu := mu) plusFamily plusTerminal
  plusPredictable : ValueTruncationProjectionPredictableLimit
    (F := F) (mu := mu) plusFamily plusTerminal plusCadlag
  minusFamily : ValueTruncationProjectionFamily
    (F := F) (mu := mu) (commonStopJordanNegative B) T
  minusTerminal : ValueTruncationProjectionTerminalL1Limit
    (F := F) (mu := mu) minusFamily
  minusCadlag : ValueTruncationProjectionCadlagLimit
    (F := F) (mu := mu) minusFamily minusTerminal
  minusPredictable : ValueTruncationProjectionPredictableLimit
    (F := F) (mu := mu) minusFamily minusTerminal minusCadlag
  Ap : Process Ω
  Ap_definition : Ap = fun t omega =>
    plusPredictable.Pp t omega - minusPredictable.Pp t omega
  Ap_stronglyPredictable : IsStronglyPredictable F Ap
  Ap_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Ap · omega) (Ici t) t
  Ap_leftLimits : ProcessHasLeftLimits Ap
  Ap_boundedVariation : ∀ omega,
    BoundedVariationOn (Ap · omega) Set.univ
  Ap_terminal_integrable : Integrable (Ap T) mu
  Ap_zero_ae : Ap 0 =ᵐ[mu] 0
  Ap_constant_after : ∀ t, T ≤ t → Ap t =ᵐ[mu] Ap T
  residual : Process Ω
  residual_definition : residual = fun t omega =>
    B t omega - Ap t omega
  residual_stronglyAdapted : StronglyAdapted F residual
  residual_martingale : Martingale residual F mu
  martingale : Process Ω
  martingale_definition : martingale = fun t omega =>
    plusCadlag.M t omega - minusCadlag.M t omega
  martingale_stronglyAdapted : StronglyAdapted F martingale
  martingale_martingale : Martingale martingale F mu
  residual_indistinguishable_martingale :
    ProcessIndistinguishable mu residual martingale
  decomposition : ProcessIndistinguishable mu B
    (fun t omega => martingale t omega + Ap t omega)
  expected_jordan_mass_eq_terminal_variation :
    (∫ omega, plusPredictable.Pp T omega ∂mu) +
      ∫ omega, minusPredictable.Pp T omega ∂mu =
        ∫ omega, localVariation B T omega ∂mu
  expected_abs_terminal_le_variation :
    (∫ omega, |Ap T omega| ∂mu) ≤
      ∫ omega, localVariation B T omega ∂mu
  Ap_totalVariation_measurable :
    Measurable (fun omega => eVariationOn
      (Ap · omega) (Set.Icc 0 T))
  Ap_totalVariation_ae_bound :
    ∀ᵐ omega ∂mu, eVariationOn (Ap · omega) (Set.Icc 0 T) ≤
      ENNReal.ofReal
        (plusPredictable.Pp T omega + minusPredictable.Pp T omega)
  Ap_totalVariation_integrable :
    Integrable (fun omega =>
      (eVariationOn (Ap · omega) (Set.Icc 0 T)).toReal) mu
  Ap_totalVariation_integral_le :
    (∫ omega, (eVariationOn (Ap · omega) (Set.Icc 0 T)).toReal ∂mu) ≤
      ∫ omega, localVariation B T omega ∂mu
  Ap_expected_totalVariation_le :
    (∫⁻ omega, eVariationOn (Ap · omega) (Set.Icc 0 T) ∂mu) ≤
      ∫⁻ omega, ENNReal.ofReal
        (localVariation B T omega) ∂mu

namespace NormalizedAdaptedCadlagFiniteVariationL1Data

variable {B : Process Ω} {T : NNReal}

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem cumulativeVariation_stronglyAdapted
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    StronglyAdapted F (localVariation B) := by
  intro t
  apply Measurable.stronglyMeasurable
  apply @FiniteVariationFactorialApproximation.measurable_variationOnFromTo_of_le
    Ω Real (F t) inferInstance inferInstance inferInstance inferInstance
    (fun s omega => B s omega) t
  · intro s hst
    exact (hB.stronglyAdapted.stronglyMeasurable_le hst).measurable
  · exact hB.rightContinuous

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem cumulativeVariation_monotone
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ omega, Monotone (localVariation B · omega) :=
  commonStopCumulativeVariation_monotone hB.boundedVariation

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem cumulativeVariation_constant_after
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ omega t, T ≤ t →
      localVariation B t omega =
        localVariation B T omega :=
  commonStopCumulativeVariation_constant_after
    hB.boundedVariation hB.constant_after

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem cumulativeVariation_boundedVariation
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ omega,
      BoundedVariationOn
        (localVariation B · omega) Set.univ := by
  have hMono := cumulativeVariation_monotone hB
  have hConst := cumulativeVariation_constant_after hB
  intro omega
  apply (monotoneOn_univ.2 (hMono omega)).boundedVariationOn
    (C := localVariation B T omega)
  intro t _
  have hZero : localVariation B 0 omega = 0 := by
    simpa using congrFun (commonStopCumulativeVariation_zero B) omega
  have hNonnegative : 0 ≤ localVariation B t omega := by
    linarith [hMono omega (show (0 : NNReal) ≤ t from bot_le)]
  rw [abs_of_nonneg hNonnegative]
  by_cases ht : t ≤ T
  · exact hMono omega ht
  · rw [hConst omega t (le_of_not_ge ht)]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem cumulativeVariation_hasLeftLimits
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ProcessHasLeftLimits (localVariation B) := by
  intro omega t
  exact (cumulativeVariation_boundedVariation hB omega).tendsto_leftLim t

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanPositive_stronglyAdapted
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    StronglyAdapted F (commonStopJordanPositive B) := by
  have hCumulative := cumulativeVariation_stronglyAdapted hB
  intro t
  change StronglyMeasurable[F t]
    (fun omega =>
      (localVariation B t omega + B t omega) / 2)
  convert ((hCumulative t).add (hB.stronglyAdapted t)).const_smul
    (1 / 2 : Real) using 1
  ext omega
  dsimp
  ring

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanNegative_stronglyAdapted
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    StronglyAdapted F (commonStopJordanNegative B) := by
  have hCumulative := cumulativeVariation_stronglyAdapted hB
  intro t
  change StronglyMeasurable[F t]
    (fun omega =>
      (localVariation B t omega - B t omega) / 2)
  convert ((hCumulative t).sub (hB.stronglyAdapted t)).const_smul
    (1 / 2 : Real) using 1
  ext omega
  dsimp
  ring

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanPositive_rightContinuous
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ omega t,
      ContinuousWithinAt (commonStopJordanPositive B · omega) (Ici t) t := by
  have hCumulative := commonStopCumulativeVariation_rightContinuous
    hB.boundedVariation hB.rightContinuous
  intro omega t
  change ContinuousWithinAt
    (fun s =>
      (localVariation B s omega + B s omega) / 2)
    (Ici t) t
  exact ((hCumulative omega t).add (hB.rightContinuous omega t)).div_const 2

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanNegative_rightContinuous
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ omega t,
      ContinuousWithinAt (commonStopJordanNegative B · omega) (Ici t) t := by
  have hCumulative := commonStopCumulativeVariation_rightContinuous
    hB.boundedVariation hB.rightContinuous
  intro omega t
  change ContinuousWithinAt
    (fun s =>
      (localVariation B s omega - B s omega) / 2)
    (Ici t) t
  exact ((hCumulative omega t).sub (hB.rightContinuous omega t)).div_const 2

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanPositive_hasLeftLimits
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ProcessHasLeftLimits (commonStopJordanPositive B) := by
  have hCumulative := cumulativeVariation_hasLeftLimits hB
  intro omega t
  apply tendsto_leftLim_of_tendsto
  refine ⟨
    (Function.leftLim (localVariation B · omega) t +
      Function.leftLim (B · omega) t) / 2, ?_⟩
  change Tendsto
    (fun s =>
      (localVariation B s omega + B s omega) / 2)
    (𝓝[<] t)
    (𝓝 ((Function.leftLim (localVariation B · omega) t +
      Function.leftLim (B · omega) t) / 2))
  exact (hCumulative omega t).add (hB.hasLeftLimits omega t) |>.div_const 2

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanNegative_hasLeftLimits
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ProcessHasLeftLimits (commonStopJordanNegative B) := by
  have hCumulative := cumulativeVariation_hasLeftLimits hB
  intro omega t
  apply tendsto_leftLim_of_tendsto
  refine ⟨
    (Function.leftLim (localVariation B · omega) t -
      Function.leftLim (B · omega) t) / 2, ?_⟩
  change Tendsto
    (fun s =>
      (localVariation B s omega - B s omega) / 2)
    (𝓝[<] t)
    (𝓝 ((Function.leftLim (localVariation B · omega) t -
      Function.leftLim (B · omega) t) / 2))
  exact (hCumulative omega t).sub (hB.hasLeftLimits omega t) |>.div_const 2

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanPositive_constant_after
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ omega t, T ≤ t →
      commonStopJordanPositive B t omega =
        commonStopJordanPositive B T omega := by
  have hCumulative := cumulativeVariation_constant_after hB
  intro omega t htt
  rw [commonStopJordanPositive_apply, commonStopJordanPositive_apply,
    hCumulative omega t htt, hB.constant_after omega t htt]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanNegative_constant_after
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ omega t, T ≤ t →
      commonStopJordanNegative B t omega =
        commonStopJordanNegative B T omega := by
  have hCumulative := cumulativeVariation_constant_after hB
  intro omega t htt
  rw [commonStopJordanNegative_apply, commonStopJordanNegative_apply,
    hCumulative omega t htt, hB.constant_after omega t htt]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanPositive_nonnegative
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ t omega, 0 ≤ commonStopJordanPositive B t omega := by
  intro t omega
  have hMono := commonStopJordanPositive_monotone hB.boundedVariation omega
  have hZero : commonStopJordanPositive B 0 omega = 0 := by
    simpa using congrFun (commonStopJordanPositive_zero hB.zero) omega
  linarith [hMono (show (0 : NNReal) ≤ t from bot_le)]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanNegative_nonnegative
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ t omega, 0 ≤ commonStopJordanNegative B t omega := by
  intro t omega
  have hMono := commonStopJordanNegative_monotone hB.boundedVariation omega
  have hZero : commonStopJordanNegative B 0 omega = 0 := by
    simpa using congrFun (commonStopJordanNegative_zero hB.zero) omega
  linarith [hMono (show (0 : NNReal) ≤ t from bot_le)]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanPositive_le_cumulativeVariation
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ t omega,
      commonStopJordanPositive B t omega ≤
        localVariation B t omega := by
  intro t omega
  have hMinus := jordanNegative_nonnegative hB t omega
  rw [commonStopJordanPositive_apply, commonStopJordanNegative_apply] at *
  linarith

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanNegative_le_cumulativeVariation
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    ∀ t omega,
      commonStopJordanNegative B t omega ≤
        localVariation B t omega := by
  intro t omega
  have hPlus := jordanPositive_nonnegative hB t omega
  rw [commonStopJordanPositive_apply, commonStopJordanNegative_apply] at *
  linarith

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanPositive_terminal_integrable
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    Integrable (commonStopJordanPositive B T) mu := by
  apply hB.terminalVariation_integrable.mono_nonneg
    ((jordanPositive_stronglyAdapted hB T).mono (F.le T)).aestronglyMeasurable
  · exact Eventually.of_forall (fun omega => jordanPositive_nonnegative hB T omega)
  · exact Eventually.of_forall
      (fun omega => jordanPositive_le_cumulativeVariation hB T omega)

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordanNegative_terminal_integrable
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    Integrable (commonStopJordanNegative B T) mu := by
  apply hB.terminalVariation_integrable.mono_nonneg
    ((jordanNegative_stronglyAdapted hB T).mono (F.le T)).aestronglyMeasurable
  · exact Eventually.of_forall (fun omega => jordanNegative_nonnegative hB T omega)
  · exact Eventually.of_forall
      (fun omega => jordanNegative_le_cumulativeVariation hB T omega)

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordan_positive_data
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    NormalizedAdaptedCadlagIncreasingProcessData
      (F := F) (commonStopJordanPositive B) T := {
  stronglyAdapted := jordanPositive_stronglyAdapted hB
  rightContinuous := jordanPositive_rightContinuous hB
  hasLeftLimits := jordanPositive_hasLeftLimits hB
  monotone := commonStopJordanPositive_monotone hB.boundedVariation
  zero := commonStopJordanPositive_zero hB.zero
  constant_after := jordanPositive_constant_after hB }

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem jordan_negative_data
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T) :
    NormalizedAdaptedCadlagIncreasingProcessData
      (F := F) (commonStopJordanNegative B) T := {
  stronglyAdapted := jordanNegative_stronglyAdapted hB
  rightContinuous := jordanNegative_rightContinuous hB
  hasLeftLimits := jordanNegative_hasLeftLimits hB
  monotone := commonStopJordanNegative_monotone hB.boundedVariation
  zero := commonStopJordanNegative_zero hB.zero
  constant_after := jordanNegative_constant_after hB }

end NormalizedAdaptedCadlagFiniteVariationL1Data

/-! ## End-to-end finite-variation consumer -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_valueTruncationFiniteVariationPredictableLimit
    [F.IsRightContinuous]
    {B : Process Ω} {T : NNReal}
    (hB : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) B T)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (ValueTruncationFiniteVariationPredictableLimit
      (F := F) (mu := mu) B T) := by
  let hPlus : NormalizedAdaptedCadlagIncreasingProcessData
      (F := F) (commonStopJordanPositive B) T :=
    NormalizedAdaptedCadlagFiniteVariationL1Data.jordan_positive_data hB
  let hMinus : NormalizedAdaptedCadlagIncreasingProcessData
      (F := F) (commonStopJordanNegative B) T :=
    NormalizedAdaptedCadlagFiniteVariationL1Data.jordan_negative_data hB
  have hPlusTerminal : Integrable (commonStopJordanPositive B T) mu :=
    NormalizedAdaptedCadlagFiniteVariationL1Data.jordanPositive_terminal_integrable hB
  have hMinusTerminal : Integrable (commonStopJordanNegative B T) mu :=
    NormalizedAdaptedCadlagFiniteVariationL1Data.jordanNegative_terminal_integrable hB
  obtain ⟨plusFamily⟩ :=
    exists_valueTruncationProjectionFamily
      (F := F) (mu := mu) (commonStopJordanPositive B) T hPlus hUsual
  obtain ⟨plusTerminal⟩ :=
    ValueTruncationProjectionFamily.exists_terminalL1Limit
      (F := F) (mu := mu) plusFamily hPlus hUsual hPlusTerminal
  obtain ⟨plusCadlag⟩ :=
    ValueTruncationProjectionFamily.exists_cadlagLimit
      (F := F) (mu := mu) plusFamily hPlus hUsual plusTerminal
  obtain ⟨plusPredictable⟩ :=
    ValueTruncationProjectionCadlagLimit.exists_predictableLimit
      (F := F) (mu := mu) plusFamily hPlus hUsual plusTerminal plusCadlag
  obtain ⟨minusFamily⟩ :=
    exists_valueTruncationProjectionFamily
      (F := F) (mu := mu) (commonStopJordanNegative B) T hMinus hUsual
  obtain ⟨minusTerminal⟩ :=
    ValueTruncationProjectionFamily.exists_terminalL1Limit
      (F := F) (mu := mu) minusFamily hMinus hUsual hMinusTerminal
  obtain ⟨minusCadlag⟩ :=
    ValueTruncationProjectionFamily.exists_cadlagLimit
      (F := F) (mu := mu) minusFamily hMinus hUsual minusTerminal
  obtain ⟨minusPredictable⟩ :=
    ValueTruncationProjectionCadlagLimit.exists_predictableLimit
      (F := F) (mu := mu) minusFamily hMinus hUsual minusTerminal minusCadlag
  let Ap : Process Ω := fun t omega =>
    plusPredictable.Pp t omega - minusPredictable.Pp t omega
  have hApPredictable : IsStronglyPredictable F Ap := by
    have hPlusPredictable := plusPredictable.Pp_stronglyPredictable
    have hMinusPredictable := minusPredictable.Pp_stronglyPredictable
    unfold IsStronglyPredictable at hPlusPredictable hMinusPredictable ⊢
    dsimp [Ap]
    exact hPlusPredictable.sub hMinusPredictable
  have hApRight : ∀ omega t,
      ContinuousWithinAt (Ap · omega) (Ici t) t := by
    intro omega t
    dsimp [Ap]
    exact (plusPredictable.Pp_rightContinuous omega t).sub
      (minusPredictable.Pp_rightContinuous omega t)
  have hApBV : ∀ omega,
      BoundedVariationOn (Ap · omega) Set.univ := by
    intro omega
    dsimp [Ap]
    exact boundedVariationOn_add
      (plusPredictable.Pp_boundedVariation omega)
      (boundedVariationOn_neg (minusPredictable.Pp_boundedVariation omega))
  have hApLeft : ProcessHasLeftLimits Ap := by
    intro omega t
    exact (hApBV omega).tendsto_leftLim t
  have hApTerminalIntegrable : Integrable (Ap T) mu := by
    dsimp [Ap]
    exact plusPredictable.Pp_terminal_integrable.sub
      minusPredictable.Pp_terminal_integrable
  have hApZero : Ap 0 =ᵐ[mu] 0 := by
    filter_upwards [plusPredictable.Pp_zero_ae, minusPredictable.Pp_zero_ae] with
      omega hPlusZero hMinusZero
    dsimp [Ap]
    rw [hPlusZero, hMinusZero]
    ring
  have hApConstant : ∀ t, T ≤ t → Ap t =ᵐ[mu] Ap T := by
    intro t ht
    filter_upwards [plusPredictable.Pp_constant_after t ht,
      minusPredictable.Pp_constant_after t ht] with omega hPlusConstant hMinusConstant
    dsimp [Ap]
    rw [hPlusConstant, hMinusConstant]
  let residual : Process Ω := fun t omega => B t omega - Ap t omega
  have hResidualStronglyAdapted : StronglyAdapted F residual := by
    dsimp [residual]
    exact hB.stronglyAdapted.sub hApPredictable.stronglyAdapted
  let martingale : Process Ω := fun t omega =>
    plusCadlag.M t omega - minusCadlag.M t omega
  have hMartingaleStronglyAdapted : StronglyAdapted F martingale := by
    dsimp [martingale]
    exact plusCadlag.M_stronglyAdapted.sub minusCadlag.M_stronglyAdapted
  have hMartingale : Martingale martingale F mu := by
    change Martingale (plusCadlag.M - minusCadlag.M) F mu
    exact plusCadlag.M_martingale.sub minusCadlag.M_martingale
  have hResidualIndistinguishable : ProcessIndistinguishable mu residual martingale := by
    filter_upwards [plusPredictable.Pp_indistinguishable_Pcad,
      minusPredictable.Pp_indistinguishable_Pcad] with omega hPlusEq hMinusEq
    intro t
    have hJordan : B t omega =
        commonStopJordanPositive B t omega - commonStopJordanNegative B t omega := by
      rw [commonStopJordanPositive_apply, commonStopJordanNegative_apply]
      ring
    dsimp [residual, Ap, martingale]
    rw [hJordan, hPlusEq t, hMinusEq t,
      plusCadlag.Pcad_definition, minusCadlag.Pcad_definition]
    ring
  have hResidualMartingale : Martingale residual F mu :=
    hMartingale.congr hResidualStronglyAdapted
      (fun t => (hResidualIndistinguishable.eventuallyEq_at t).symm)
  have hDecomposition : ProcessIndistinguishable mu B
      (fun t omega => martingale t omega + Ap t omega) := by
    filter_upwards [hResidualIndistinguishable] with omega hResidualEq
    intro t
    have hEq := hResidualEq t
    dsimp [residual] at hEq
    linarith
  have hExpectedMass :
      (∫ omega, plusPredictable.Pp T omega ∂mu) +
        ∫ omega, minusPredictable.Pp T omega ∂mu =
          ∫ omega, localVariation B T omega ∂mu := by
    have hPlusEq := plusPredictable.Pp_terminal_integral_eq_source
    have hMinusEq := minusPredictable.Pp_terminal_integral_eq_source
    have hJordan : ∀ omega,
        commonStopJordanPositive B T omega +
          commonStopJordanNegative B T omega =
            localVariation B T omega := by
      intro omega
      rw [commonStopJordanPositive_apply, commonStopJordanNegative_apply]
      ring
    calc
      (∫ omega, plusPredictable.Pp T omega ∂mu) +
          ∫ omega, minusPredictable.Pp T omega ∂mu =
          (∫ omega, commonStopJordanPositive B T omega ∂mu) +
            ∫ omega, commonStopJordanNegative B T omega ∂mu := by
        rw [hPlusEq, hMinusEq]
      _ = ∫ omega,
          (commonStopJordanPositive B T omega +
            commonStopJordanNegative B T omega) ∂mu := by
        rw [integral_add hPlusTerminal hMinusTerminal]
      _ = ∫ omega, localVariation B T omega ∂mu := by
        apply integral_congr_ae
        exact Eventually.of_forall hJordan
  have hExpectedAbsBound :
      (∫ omega, |Ap T omega| ∂mu) ≤
        ∫ omega, localVariation B T omega ∂mu := by
    have hAbsIntegrable : Integrable (fun omega => |Ap T omega|) mu := by
      simpa only [Real.norm_eq_abs] using hApTerminalIntegrable.norm
    have hAbsBound : ∀ᵐ omega ∂mu, |Ap T omega| ≤
        plusPredictable.Pp T omega + minusPredictable.Pp T omega := by
      filter_upwards [plusPredictable.Pp_nonnegative_ae,
        minusPredictable.Pp_nonnegative_ae] with
        omega hPlusNonnegative hMinusNonnegative
      dsimp [Ap]
      calc
        |plusPredictable.Pp T omega - minusPredictable.Pp T omega| ≤
            |plusPredictable.Pp T omega| + |minusPredictable.Pp T omega| :=
          abs_sub _ _
        _ = plusPredictable.Pp T omega + minusPredictable.Pp T omega := by
          rw [abs_of_nonneg (hPlusNonnegative T),
            abs_of_nonneg (hMinusNonnegative T)]
    have hPpSumIntegrable : Integrable
        (fun omega => plusPredictable.Pp T omega + minusPredictable.Pp T omega) mu :=
      plusPredictable.Pp_terminal_integrable.add
        minusPredictable.Pp_terminal_integrable
    have hBound := integral_mono_ae hAbsIntegrable hPpSumIntegrable hAbsBound
    calc
      (∫ omega, |Ap T omega| ∂mu) ≤
          ∫ omega, plusPredictable.Pp T omega + minusPredictable.Pp T omega ∂mu :=
        hBound
      _ = (∫ omega, plusPredictable.Pp T omega ∂mu) +
          ∫ omega, minusPredictable.Pp T omega ∂mu := by
        rw [integral_add plusPredictable.Pp_terminal_integrable
          minusPredictable.Pp_terminal_integrable]
      _ = ∫ omega, localVariation B T omega ∂mu :=
        hExpectedMass
  have hApTotalVariationMeasurable :
      Measurable (fun omega => eVariationOn
        (Ap · omega) (Set.Icc 0 T)) := by
    exact SIntegrableFiniteVariationBridge.measurable_prelocalH1FiniteVariation
      Ap T hApPredictable hApRight
  have hApTotalVariationBound :
      ∀ᵐ omega ∂mu, eVariationOn (Ap · omega) (Set.Icc 0 T) ≤
        ENNReal.ofReal
          (plusPredictable.Pp T omega + minusPredictable.Pp T omega) := by
    filter_upwards [plusPredictable.Pp_monotone_ae,
      minusPredictable.Pp_monotone_ae, plusPredictable.Pp_zero_ae,
      minusPredictable.Pp_zero_ae] with omega hPlusMono hMinusMono
      hPlusZero hMinusZero
    dsimp [Ap]
    exact eVariationOn_sub_monotone_zero_le
      (P := fun t => plusPredictable.Pp t omega)
      (Q := fun t => minusPredictable.Pp t omega)
      hPlusMono hMinusMono hPlusZero hMinusZero
  have hPpSumIntegrable : Integrable
      (fun omega => plusPredictable.Pp T omega + minusPredictable.Pp T omega) mu :=
    plusPredictable.Pp_terminal_integrable.add
      minusPredictable.Pp_terminal_integrable
  have hPpSumNonnegative : ∀ᵐ omega ∂mu,
      0 ≤ plusPredictable.Pp T omega + minusPredictable.Pp T omega := by
    filter_upwards [plusPredictable.Pp_nonnegative_ae,
      minusPredictable.Pp_nonnegative_ae] with omega hPlusNonnegative hMinusNonnegative
    exact add_nonneg (hPlusNonnegative T) (hMinusNonnegative T)
  have hPpSumLIntegralNeTop :
      (∫⁻ omega, ENNReal.ofReal
        (plusPredictable.Pp T omega + minusPredictable.Pp T omega) ∂mu) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hPpSumIntegrable
      hPpSumNonnegative]
    exact ENNReal.ofReal_ne_top
  have hApTotalVariationLIntegralBound :
      (∫⁻ omega, eVariationOn (Ap · omega) (Set.Icc 0 T) ∂mu) ≤
        ∫⁻ omega, ENNReal.ofReal
          (plusPredictable.Pp T omega + minusPredictable.Pp T omega) ∂mu :=
    lintegral_mono_ae hApTotalVariationBound
  have hApTotalVariationLIntegralNeTop :
      (∫⁻ omega, eVariationOn (Ap · omega) (Set.Icc 0 T) ∂mu) ≠ ∞ :=
    ne_top_of_le_ne_top hPpSumLIntegralNeTop hApTotalVariationLIntegralBound
  have hApTotalVariationIntegrable : Integrable
      (fun omega =>
        (eVariationOn (Ap · omega) (Set.Icc 0 T)).toReal) mu :=
    integrable_toReal_of_lintegral_ne_top
      hApTotalVariationMeasurable.aemeasurable hApTotalVariationLIntegralNeTop
  have hApTotalVariationLePpSum : ∀ᵐ omega ∂mu,
      (eVariationOn (Ap · omega) (Set.Icc 0 T)).toReal ≤
        plusPredictable.Pp T omega + minusPredictable.Pp T omega := by
    filter_upwards [hApTotalVariationBound, hPpSumNonnegative] with omega
      hVariationBound hSumNonnegative
    have hVariationNeTop :
        eVariationOn (Ap · omega) (Set.Icc 0 T) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hVariationBound
    have hSumNeTop :
        ENNReal.ofReal
          (plusPredictable.Pp T omega + minusPredictable.Pp T omega) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hToRealBound := (ENNReal.toReal_le_toReal hVariationNeTop hSumNeTop).2
      hVariationBound
    have hToRealBound' :
        (eVariationOn (Ap · omega) (Set.Icc 0 T)).toReal ≤
          plusPredictable.Pp T omega + minusPredictable.Pp T omega := by
      simpa only [ENNReal.toReal_ofReal hSumNonnegative] using hToRealBound
    exact hToRealBound'
  have hApTotalVariationIntegralLe :
      (∫ omega, (eVariationOn (Ap · omega) (Set.Icc 0 T)).toReal ∂mu) ≤
        ∫ omega, localVariation B T omega ∂mu := by
    calc
      (∫ omega, (eVariationOn (Ap · omega) (Set.Icc 0 T)).toReal ∂mu) ≤
          ∫ omega, plusPredictable.Pp T omega +
            minusPredictable.Pp T omega ∂mu :=
        integral_mono_ae hApTotalVariationIntegrable hPpSumIntegrable
          hApTotalVariationLePpSum
      _ = (∫ omega, plusPredictable.Pp T omega ∂mu) +
          ∫ omega, minusPredictable.Pp T omega ∂mu := by
        rw [integral_add plusPredictable.Pp_terminal_integrable
          minusPredictable.Pp_terminal_integrable]
      _ = ∫ omega, localVariation B T omega ∂mu :=
        hExpectedMass
  have hApExpectedTotalVariationLe :
      (∫⁻ omega, eVariationOn (Ap · omega) (Set.Icc 0 T) ∂mu) ≤
        ∫⁻ omega, ENNReal.ofReal
          (localVariation B T omega) ∂mu := by
    calc
      (∫⁻ omega, eVariationOn (Ap · omega) (Set.Icc 0 T) ∂mu) ≤
          ∫⁻ omega, ENNReal.ofReal
            (plusPredictable.Pp T omega + minusPredictable.Pp T omega) ∂mu :=
        hApTotalVariationLIntegralBound
      _ = ENNReal.ofReal
          (∫ omega, plusPredictable.Pp T omega +
            minusPredictable.Pp T omega ∂mu) := by
        rw [ofReal_integral_eq_lintegral_ofReal hPpSumIntegrable
          hPpSumNonnegative]
      _ = ENNReal.ofReal
          (∫ omega, localVariation B T omega ∂mu) := by
        rw [integral_add plusPredictable.Pp_terminal_integrable
          minusPredictable.Pp_terminal_integrable, hExpectedMass]
      _ = ∫⁻ omega, ENNReal.ofReal
          (localVariation B T omega) ∂mu := by
        exact ofReal_integral_eq_lintegral_ofReal
          hB.terminalVariation_integrable
          (Eventually.of_forall (fun omega => by
            change (0 : Real) ≤ localVariation B T omega
            have hMono :=
              NormalizedAdaptedCadlagFiniteVariationL1Data.cumulativeVariation_monotone hB omega
            have hZero : localVariation B 0 omega = 0 := by
              simpa using congrFun (commonStopCumulativeVariation_zero B) omega
            have h := hMono (show (0 : NNReal) ≤ T from bot_le)
            change localVariation B 0 omega ≤
              localVariation B T omega at h
            exact hZero.symm ▸ h))
  exact ⟨{
    plusSource := hPlus
    plusSource_terminal_integrable := hPlusTerminal
    minusSource := hMinus
    minusSource_terminal_integrable := hMinusTerminal
    plusFamily := plusFamily
    plusTerminal := plusTerminal
    plusCadlag := plusCadlag
    plusPredictable := plusPredictable
    minusFamily := minusFamily
    minusTerminal := minusTerminal
    minusCadlag := minusCadlag
    minusPredictable := minusPredictable
    Ap := Ap
    Ap_definition := rfl
    Ap_stronglyPredictable := hApPredictable
    Ap_rightContinuous := hApRight
    Ap_leftLimits := hApLeft
    Ap_boundedVariation := hApBV
    Ap_terminal_integrable := hApTerminalIntegrable
    Ap_zero_ae := hApZero
    Ap_constant_after := hApConstant
    residual := residual
    residual_definition := rfl
    residual_stronglyAdapted := hResidualStronglyAdapted
    residual_martingale := hResidualMartingale
    martingale := martingale
    martingale_definition := rfl
    martingale_stronglyAdapted := hMartingaleStronglyAdapted
    martingale_martingale := hMartingale
    residual_indistinguishable_martingale := hResidualIndistinguishable
    decomposition := hDecomposition
    expected_jordan_mass_eq_terminal_variation := hExpectedMass
    expected_abs_terminal_le_variation := hExpectedAbsBound
    Ap_totalVariation_measurable := hApTotalVariationMeasurable
    Ap_totalVariation_ae_bound := hApTotalVariationBound
    Ap_totalVariation_integrable := hApTotalVariationIntegrable
    Ap_totalVariation_integral_le := hApTotalVariationIntegralLe
    Ap_expected_totalVariation_le := hApExpectedTotalVariationLe }⟩

end HorizonFactorialGrid

end FTAPTheorem42
