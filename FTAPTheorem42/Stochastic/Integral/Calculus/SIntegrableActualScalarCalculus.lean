/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma410.StoppedPrefixMartingale
import FTAPTheorem42.Foundations.MaximalProbability
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableRealizationModel
import FTAPTheorem42.Stochastic.DS.Lemma47.DownsideStopping

/-!
# Stopping actual stochastic-integral strategies

The raw stopping calculus records the process and component identities of a
stopped candidate record.  This module adds the independent carrier-level
fact that stopping an actual stochastic integral remains in the realized
range.  It then packages the passage-stopped prefixes used by the Mémín
control step as actual strategies.
-/

namespace FTAPTheorem42

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A raw stopping calculus preserves membership in an actual realization
carrier. -/
structure SIntegrableActualStoppingCalculus
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (R : SIntegrableRealizationModel D)
    (C : SIntegrableProcessStoppingCalculus D) where
  stopAtTop_isRealized :
    ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
      (H : ActualSIntegrableStrategy R),
      R.IsRealized (C.stopAtTop τ hτ H.val)

namespace SIntegrableActualStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {R : SIntegrableRealizationModel D}
  {C : SIntegrableProcessStoppingCalculus D}

/-- Stop an actual strategy at a possibly infinite stopping time. -/
noncomputable def stopAtTop
    (Cactual : SIntegrableActualStoppingCalculus R C)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : ActualSIntegrableStrategy R) : ActualSIntegrableStrategy R :=
  ⟨C.stopAtTop τ hτ H.val, Cactual.stopAtTop_isRealized τ hτ H⟩

variable [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ]

end SIntegrableActualStoppingCalculus

/-!
## Scalar multiplication on the actual stochastic-integral carrier

The Lemma 4.7 contradiction rescales an actual strategy before the first
localization and once more after the downside stop. This section isolates
closure of the realized carrier under deterministic scalar multiplication
and combines it with actual stopping and Hahn restriction. The resulting
vanishing-risk strategy is the same raw record used by the existing
probability estimates, now equipped with actual membership.
-/

/-- Deterministic scalar multiplication preserves the selected actual
stochastic-integral carrier. -/
structure SIntegrableActualScalarCalculus
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (R : SIntegrableRealizationModel D) where
  smul_isRealized :
    ∀ (c : ℝ) (H : ActualSIntegrableStrategy R),
      R.IsRealized (SIntegrableStrategy.smul c H.val)

namespace SIntegrableActualScalarCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {R : SIntegrableRealizationModel D}

/-- Deterministically rescale an actual strategy. -/
noncomputable def smul
    (Cscalar : SIntegrableActualScalarCalculus R)
    (c : ℝ) (H : ActualSIntegrableStrategy R) :
    ActualSIntegrableStrategy R :=
  ⟨SIntegrableStrategy.smul c H.val,
    Cscalar.smul_isRealized c H⟩

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
@[simp]
theorem smul_val
    (Cscalar : SIntegrableActualScalarCalculus R)
    (c : ℝ) (H : ActualSIntegrableStrategy R) :
    (Cscalar.smul c H).val = SIntegrableStrategy.smul c H.val :=
  rfl

/-- Stop an actual strategy and then apply a deterministic scale. -/
noncomputable def rescaleStopAtTop
    {CstopRaw : SIntegrableProcessStoppingCalculus D}
    (Cscalar : SIntegrableActualScalarCalculus R)
    (Cstop : SIntegrableActualStoppingCalculus R CstopRaw)
    (c : ℝ) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : ActualSIntegrableStrategy R) : ActualSIntegrableStrategy R :=
  Cscalar.smul c (Cstop.stopAtTop τ hτ H)

variable {C : SIntegrableProcessStoppingCalculus D}

/-- The first rescaling and joint first-passage stop in Lemma 4.7 remains
on the actual carrier. -/
noncomputable def lemma47RescaleAndStopUpTo
    (Cscalar : SIntegrableActualScalarCalculus R)
    (Cstop : SIntegrableActualStoppingCalculus R
      (C))
    (H : ActualSIntegrableStrategy R)
    (scale martingaleLevel gainLevel : ℝ) (T : ℝ≥0) :
    ActualSIntegrableStrategy R :=
  Cscalar.rescaleStopAtTop Cstop scale
    (SIntegrableProcessStoppingCalculus.lemma47FirstPassageUpTo
      H.val martingaleLevel gainLevel T)
    (SIntegrableProcessStoppingCalculus.lemma47FirstPassageUpTo_isStoppingTime
      H.val martingaleLevel gainLevel T) H

/-- Stop an actual Hahn-positive strategy at its downside passage and apply
the final deterministic scale. -/
noncomputable def lemma47StopDownsideAndRescale
    (Cscalar : SIntegrableActualScalarCalculus R)
    (Cstop : SIntegrableActualStoppingCalculus R
      (C))
    (H : ActualSIntegrableStrategy R) (c d : ℝ) (T : ℝ≥0) :
    ActualSIntegrableStrategy R :=
  Cscalar.rescaleStopAtTop Cstop c
    (SIntegrableProcessStoppingCalculus.lemma47DownsideTime
      H.val d T)
    (SIntegrableProcessStoppingCalculus.lemma47DownsideTime_isStoppingTime
      H.val d T) H

end SIntegrableActualScalarCalculus

end FTAPTheorem42
