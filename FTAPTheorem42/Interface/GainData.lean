/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Interface.IntegralClosure
import FTAPTheorem42.Foundations.Decomposition

/-! # Original-price gains at the main proof's analytic boundary -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An original-price integral with its regular zero-initial gain. No
representative rows, auxiliary source or localization schedule are stored. -/
structure OriginalGain (source : BoundedSemimartingaleSource S F μ) where
  integrand : Process Ω
  gain : Process Ω
  integralGraph : GeneralIntegralGraph source integrand gain
  adapted : StronglyAdapted F gain
  rightContinuous : ∀ ω t, ContinuousWithinAt (gain · ω) (Ici t) t
  leftLimits : ProcessHasLeftLimits gain
  zero : gain 0 =ᵐ[μ] 0

/-- One regular special decomposition under the chosen equivalent measure. -/
structure OriginalSpecialGain (source : BoundedSemimartingaleSource S F μ) (Q : Measure Ω) where
  original : OriginalGain source
  decomposition : J1Decomposition original.gain F Q
  predictable : IsStronglyPredictable F decomposition.A

/-- A finite-horizon gain has globally bounded variation and its own constant
terminal continuation. These facts are used only by finite tail operations. -/
structure FiniteOriginalSpecialGain (source : BoundedSemimartingaleSource S F μ) (Q : Measure Ω)
    extends OriginalSpecialGain source Q where
  boundedVariation : ∀ ω, BoundedVariationOn (decomposition.A · ω) univ
  eventuallyConstant : ∃ T : NNReal, ∀ᵐ ω ∂Q, ∀ t, T ≤ t →
    original.gain t ω = original.gain T ω

variable {Q : Measure Ω} {source : BoundedSemimartingaleSource S F μ}

/-- The class to which the second application of Lemma 4.7 is made. -/
def OriginalSpecialGain.Normalized (Y : OriginalSpecialGain source Q) : Prop :=
  (∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ Y.original.gain t ω) ∧
    ∃ ξ : Ω → Real, MemLp ξ 2 Q ∧
      (∀ᵐ ω ∂Q, ∀ t, |Y.original.gain t ω| ≤ ξ ω) ∧ eLpNorm ξ 2 Q ≤ 1

end FTAPTheorem42.BoundedSourceIntegralMarket
