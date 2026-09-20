/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingInterval
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# Stopping calculus for stochastic-integrable strategies

Predictability of `(0, τ]` constructs the restricted integrand, but the
stochastic-integral identities are properties of the concrete integration
theory.  This module records those identities separately and derives the
rescaled stopping formulas used at the first stochastic step of Lemma 4.7.
-/

open MeasureTheory
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The process obtained by stopping at a finite random time. -/
noncomputable def finiteStoppedProcess
    (X : Process Ω) (τ : Ω → ℝ≥0) : Process Ω :=
  MeasureTheory.stoppedProcess X (fun ω => (τ ω : WithTop ℝ≥0))

/-- Process stopping and its coordinate identities, independent of arbitrary
predictable-set restriction. Actual graph closure is supplied separately. -/
structure SIntegrableProcessStoppingCalculus
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    (D : SpecialSemimartingaleDecomposition S ℱ μ) where
  stopAtTop : ∀ (τ : Ω → WithTop ℝ≥0), IsStoppingTime ℱ τ →
    SIntegrableStrategy D → SIntegrableStrategy D
  stopAtTop_integrand : ∀ τ hτ H,
    (stopAtTop τ hτ H).integrand =
      PredictableProcess.restrict (stochasticIntervalIocZeroTop τ) H.integrand
  stochasticIntegral_stopAtTop : ∀ τ hτ H,
    ProcessIndistinguishable μ (stochasticIntegral (stopAtTop τ hτ H))
      (MeasureTheory.stoppedProcess H.stochasticIntegral τ)
  martingalePart_stopAtTop : ∀ τ hτ H,
    ProcessIndistinguishable μ (stopAtTop τ hτ H).martingalePart
      (MeasureTheory.stoppedProcess H.martingalePart τ)
  finiteVariationPart_stopAtTop : ∀ τ hτ H,
    ProcessIndistinguishable μ (stopAtTop τ hτ H).finiteVariationPart
      (MeasureTheory.stoppedProcess H.finiteVariationPart τ)
  martingalePart_stopAtTop_hasLeftLimits : ∀ τ hτ H,
    ProcessHasLeftLimits H.martingalePart →
      ProcessHasLeftLimits (stopAtTop τ hτ H).martingalePart
  stochasticIntegral_stopAtTop_hasLeftLimits : ∀ τ hτ H,
    ProcessHasLeftLimits H.stochasticIntegral →
      ProcessHasLeftLimits (stopAtTop τ hτ H).stochasticIntegral

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Stop at a possibly infinite time and rescale. -/
noncomputable abbrev rescaleStopAtTop
    (C : SIntegrableProcessStoppingCalculus D)
    (c : ℝ) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : SIntegrableStrategy D) : SIntegrableStrategy D :=
  SIntegrableStrategy.smul c (C.stopAtTop τ hτ H)

theorem rescaleStopAtTop_stochasticIntegral
    (C : SIntegrableProcessStoppingCalculus D)
    (c : ℝ) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : SIntegrableStrategy D) :
    ProcessIndistinguishable μ
      (stochasticIntegral (C.rescaleStopAtTop c τ hτ H))
      (fun t ω => c * MeasureTheory.stoppedProcess
        H.stochasticIntegral τ t ω) := by
  change ProcessIndistinguishable μ
    (fun t ω => c * stochasticIntegral (C.stopAtTop τ hτ H) t ω) _
  exact (C.stochasticIntegral_stopAtTop τ hτ H).smul c

theorem rescaleStopAtTop_martingalePart
    (C : SIntegrableProcessStoppingCalculus D)
    (c : ℝ) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : SIntegrableStrategy D) :
    ProcessIndistinguishable μ
      (C.rescaleStopAtTop c τ hτ H).martingalePart
      (fun t ω => c * MeasureTheory.stoppedProcess
        H.martingalePart τ t ω) := by
  change ProcessIndistinguishable μ
    (fun t ω => c * (C.stopAtTop τ hτ H).martingalePart t ω) _
  exact (C.martingalePart_stopAtTop τ hτ H).smul c

/-- The concrete stopped martingale version chosen by the integration
calculus retains pathwise left limits; constant rescaling retains them as
well. -/
theorem rescaleStopAtTop_martingalePart_hasLeftLimits
    (C : SIntegrableProcessStoppingCalculus D)
    (c : ℝ) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : SIntegrableStrategy D)
    (hM : ProcessHasLeftLimits H.martingalePart) :
    ProcessHasLeftLimits
      (C.rescaleStopAtTop c τ hτ H).martingalePart := by
  exact (C.martingalePart_stopAtTop_hasLeftLimits τ hτ H hM).const_mul c

theorem rescaleStopAtTop_stochasticIntegral_hasLeftLimits
    (C : SIntegrableProcessStoppingCalculus D)
    (c : ℝ) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : SIntegrableStrategy D)
    (hX : ProcessHasLeftLimits H.stochasticIntegral) :
    ProcessHasLeftLimits
      (stochasticIntegral (C.rescaleStopAtTop c τ hτ H)) := by
  exact (C.stochasticIntegral_stopAtTop_hasLeftLimits τ hτ H hX).const_mul c

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
