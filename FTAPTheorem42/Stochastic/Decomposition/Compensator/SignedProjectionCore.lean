/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.PredictableFiniteVariationLocalMartingale

/-!
# Source-free uniqueness of predictable compensators

The uniqueness argument only uses the path properties of two predictable
increasing processes and the martingale property of their residuals.  It is
kept independent of either the bounded or square-integrable construction.
-/

namespace FTAPTheorem42

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open PredictableFiniteVariationLocalMartingale

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## A pathwise bounded-variation helper -/

omit [MeasurableSpace Ω] [SigmaFiniteFiltration mu F] in
theorem boundedVariationOn_of_monotone_nonnegative_constantAfter
    {P : Process Ω} {T : NNReal}
    (hNonnegative : ∀ omega t, 0 ≤ P t omega)
    (hMonotone : ∀ omega, Monotone (P · omega))
    (hConstantAfter : ∀ omega t, T ≤ t → P t omega = P T omega) :
    ∀ omega, BoundedVariationOn (P · omega) Set.univ := by
  intro omega
  apply (monotoneOn_univ.2 (hMonotone omega)).boundedVariationOn
    (C := P T omega)
  intro t _
  rw [abs_of_nonneg (hNonnegative omega t)]
  by_cases ht : t ≤ T
  · exact hMonotone omega ht
  · rw [hConstantAfter omega t (le_of_not_ge ht)]

/-! ## Source-free rigidity and candidate uniqueness -/

omit [SigmaFiniteFiltration mu F] in
theorem predictableFiniteVariationLocalMartingale_eq_zero_of_zero
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    {A : Process Ω}
    (hALocal : LocalMartingale A F mu)
    (hAPredictable : IsStronglyPredictable F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hABoundedVariation : ∀ omega,
      BoundedVariationOn (A · omega) Set.univ)
    (hAZero : A 0 = 0) :
    ProcessIndistinguishable mu A (fun _ _ => 0) :=
  indistinguishable_zero_of_predictableFiniteVariationLocalMartingale
    hUsual A hALocal hAPredictable hARight hABoundedVariation hAZero

end HorizonFactorialGrid

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Source-independent signed projection algebra

The difference of two completed predictable projections is handled here
without referring to the construction of either component.  This is the
common consumer for the bounded and square-integrable routes: only the
pathwise properties of the two projections, their residual martingales, and
the Jordan identity for the regularized finite-variation process are used.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The generic signed projection certificate -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
structure PredictableSignedProjectionCoreData
    {Atilde Aplus Aminus VpPlus VpMinus : Process Ω}
    {T : NNReal} (Ap : Process Ω) : Prop where
  Ap_eq_def : Ap = fun t omega => VpPlus t omega - VpMinus t omega
  Ap_isStronglyPredictable : IsStronglyPredictable F Ap
  Ap_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Ap · omega) (Ici t) t
  Ap_leftLimits : ProcessHasLeftLimits Ap
  Ap_boundedVariation : ∀ omega,
    BoundedVariationOn (Ap · omega) Set.univ
  Ap_zero : Ap 0 = 0
  Ap_constant_after : ∀ omega t, T ≤ t →
    Ap t omega = Ap T omega
  residual_stronglyAdapted : StronglyAdapted F
    (fun t omega => Atilde t omega - Ap t omega)
  residual_martingale : Martingale
    (fun t omega => Atilde t omega - Ap t omega) F mu
  residual_indistinguishable_jordan : ProcessIndistinguishable mu
    (fun t omega => Atilde t omega - Ap t omega)
    (fun t omega =>
      (Aplus t omega - VpPlus t omega) -
        (Aminus t omega - VpMinus t omega))
  signed_decomposition : ProcessIndistinguishable mu Atilde
    (fun t omega => Ap t omega +
      ((Aplus t omega - VpPlus t omega) -
        (Aminus t omega - VpMinus t omega)))

/-! ## Construction from two component certificates -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem exists_predictableSignedProjectionCore
    {Atilde Aplus Aminus VpPlus VpMinus : Process Ω}
    {T : NNReal}
    (hAtildeStronglyAdapted : StronglyAdapted F Atilde)
    (hPlusPredictable : IsStronglyPredictable F VpPlus)
    (hMinusPredictable : IsStronglyPredictable F VpMinus)
    (hPlusRightContinuous : ∀ omega t,
      ContinuousWithinAt (VpPlus · omega) (Ici t) t)
    (hMinusRightContinuous : ∀ omega t,
      ContinuousWithinAt (VpMinus · omega) (Ici t) t)
    (hPlusLeftLimits : ProcessHasLeftLimits VpPlus)
    (hMinusLeftLimits : ProcessHasLeftLimits VpMinus)
    (hPlusNonnegative : ∀ omega t, 0 ≤ VpPlus t omega)
    (hMinusNonnegative : ∀ omega t, 0 ≤ VpMinus t omega)
    (hPlusMonotone : ∀ omega, Monotone (VpPlus · omega))
    (hMinusMonotone : ∀ omega, Monotone (VpMinus · omega))
    (hPlusZero : VpPlus 0 = 0)
    (hMinusZero : VpMinus 0 = 0)
    (hPlusConstantAfter : ∀ omega t, T ≤ t →
      VpPlus t omega = VpPlus T omega)
    (hMinusConstantAfter : ∀ omega t, T ≤ t →
      VpMinus t omega = VpMinus T omega)
    (hPlusResidual : Martingale
      (fun t omega => Aplus t omega - VpPlus t omega) F mu)
    (hMinusResidual : Martingale
      (fun t omega => Aminus t omega - VpMinus t omega) F mu)
    (hJordan : ∀ t omega,
      Atilde t omega = Aplus t omega - Aminus t omega) :
    ∃ Ap : Process Ω,
      PredictableSignedProjectionCoreData (F := F) (mu := mu)
        (Atilde := Atilde) (Aplus := Aplus) (Aminus := Aminus)
        (VpPlus := VpPlus) (VpMinus := VpMinus) (T := T) Ap := by
  let Ap : Process Ω := fun t omega => VpPlus t omega - VpMinus t omega
  have hApPredictable : IsStronglyPredictable F Ap := by
    unfold IsStronglyPredictable at hPlusPredictable hMinusPredictable ⊢
    dsimp [Ap]
    exact hPlusPredictable.sub hMinusPredictable
  have hApRight : ∀ omega t,
      ContinuousWithinAt (Ap · omega) (Ici t) t := by
    intro omega t
    dsimp [Ap]
    exact (hPlusRightContinuous omega t).sub
      (hMinusRightContinuous omega t)
  have hApLeft : ProcessHasLeftLimits Ap := by
    dsimp [Ap]
    exact hPlusLeftLimits.sub hMinusLeftLimits
  have hPlusBV : ∀ omega, BoundedVariationOn (VpPlus · omega) Set.univ :=
    boundedVariationOn_of_monotone_nonnegative_constantAfter
      hPlusNonnegative hPlusMonotone hPlusConstantAfter
  have hMinusBV : ∀ omega, BoundedVariationOn (VpMinus · omega) Set.univ :=
    boundedVariationOn_of_monotone_nonnegative_constantAfter
      hMinusNonnegative hMinusMonotone hMinusConstantAfter
  have hApBV : ∀ omega, BoundedVariationOn (Ap · omega) Set.univ := by
    intro omega
    dsimp [Ap]
    exact boundedVariationOn_add (hPlusBV omega)
      (boundedVariationOn_neg (hMinusBV omega))
  have hApZero : Ap 0 = 0 := by
    funext omega
    dsimp [Ap]
    rw [congrFun hPlusZero omega, congrFun hMinusZero omega]
    ring
  have hApConstantAfter : ∀ omega t, T ≤ t →
      Ap t omega = Ap T omega := by
    intro omega t ht
    dsimp [Ap]
    rw [hPlusConstantAfter omega t ht, hMinusConstantAfter omega t ht]
  have hResidualStronglyAdapted : StronglyAdapted F
      (fun t omega => Atilde t omega - Ap t omega) :=
    hAtildeStronglyAdapted.sub hApPredictable.stronglyAdapted
  have hResidualIndist : ProcessIndistinguishable mu
      (fun t omega => Atilde t omega - Ap t omega)
      (fun t omega =>
        (Aplus t omega - VpPlus t omega) -
          (Aminus t omega - VpMinus t omega)) := by
    filter_upwards [] with omega
    intro t
    have hJordan' := hJordan t omega
    dsimp [Ap]
    rw [hJordan']
    ring
  have hResidualBase : Martingale
      (fun t omega =>
        (Aplus t omega - VpPlus t omega) -
          (Aminus t omega - VpMinus t omega)) F mu :=
    hPlusResidual.sub hMinusResidual
  have hResidualMartingale : Martingale
      (fun t omega => Atilde t omega - Ap t omega) F mu :=
    hResidualBase.congr hResidualStronglyAdapted
      (fun t => (hResidualIndist.eventuallyEq_at t).symm)
  have hSignedDecomposition : ProcessIndistinguishable mu Atilde
      (fun t omega => Ap t omega +
        ((Aplus t omega - VpPlus t omega) -
          (Aminus t omega - VpMinus t omega))) := by
    filter_upwards [] with omega
    intro t
    have hJordan' := hJordan t omega
    dsimp [Ap]
    rw [hJordan']
    ring
  refine ⟨Ap, {
    Ap_eq_def := by rfl
    Ap_isStronglyPredictable := hApPredictable
    Ap_rightContinuous := hApRight
    Ap_leftLimits := hApLeft
    Ap_boundedVariation := hApBV
    Ap_zero := hApZero
    Ap_constant_after := hApConstantAfter
    residual_stronglyAdapted := hResidualStronglyAdapted
    residual_martingale := hResidualMartingale
    residual_indistinguishable_jordan := hResidualIndist
    signed_decomposition := hSignedDecomposition }⟩

end HorizonFactorialGrid

end FTAPTheorem42
