/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy

/-!
# Realized stochastic-integral strategies

`SIntegrableStrategy` and `LocallySIntegrableStrategy` record regularity and
decomposition data, but deliberately do not assert that their components are
the stochastic integrals of the stored integrand against the supplied source
decomposition.  This module separates those raw records from the carrier of a
concrete stochastic-integration model.

A realization model selects the globally finite-variation records that are
actual stochastic integrals.  An actual local strategy additionally certifies
that every positive deterministic stop belongs to that selected carrier.
Stochastic calculi that state integral identities must quantify over these
actual carriers, rather than over every freely constructible raw record.
-/

open MeasureTheory
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The subset of raw strategy records realized by a concrete stochastic-
integration construction.

Realization is a property of the stochastic-integral graph: changing the
auxiliary decomposition data while keeping the integrand equal and the gain
indistinguishable does not leave the realized range. -/
structure SIntegrableRealizationModel
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    (D : SpecialSemimartingaleDecomposition S ℱ μ) where
  IsRealized : SIntegrableStrategy D → Prop
  isRealized_congr :
    ∀ {H K : SIntegrableStrategy D},
      H.integrand = K.integrand →
      ProcessIndistinguishable μ H.stochasticIntegral K.stochasticIntegral →
      IsRealized H → IsRealized K

/-- A globally finite-variation strategy selected by a realization model. -/
abbrev ActualSIntegrableStrategy
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (R : SIntegrableRealizationModel D) :=
  {H : SIntegrableStrategy D // R.IsRealized H}

/-- A locally finite-variation source strategy whose every positive
deterministic stop is selected by the realization model. -/
structure ActualLocallySIntegrableStrategy
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (R : SIntegrableRealizationModel D) where
  val : LocallySIntegrableStrategy D
  deterministicallyStopped_isRealized :
    ∀ (T : ℝ≥0) (hT : 0 < T),
      R.IsRealized (val.deterministicallyStopped T hT)

namespace ActualSIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {R : SIntegrableRealizationModel D}

/-- Forget realization membership pointwise along a strategy sequence. -/
abbrev rawSequence (L : ℕ → ActualSIntegrableStrategy R) :
    ℕ → SIntegrableStrategy D :=
  fun n => (L n).val

/-- Replace the raw representative of an actual stochastic-integral graph
without changing its integrand or gain process. -/
noncomputable def congr
    (H : ActualSIntegrableStrategy R) (K : SIntegrableStrategy D)
    (hIntegrand : H.val.integrand = K.integrand)
    (hGain : ProcessIndistinguishable μ
      H.val.stochasticIntegral K.stochasticIntegral) :
    ActualSIntegrableStrategy R :=
  ⟨K, R.isRealized_congr hIntegrand hGain H.property⟩

end ActualSIntegrableStrategy

namespace ActualLocallySIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {R : SIntegrableRealizationModel D}

/-- A positive deterministic stop of an actual local strategy is an actual
globally finite-variation strategy. -/
noncomputable def deterministicallyStopped
    (G : ActualLocallySIntegrableStrategy R)
    (T : ℝ≥0) (hT : 0 < T) : ActualSIntegrableStrategy R :=
  ⟨G.val.deterministicallyStopped T hT,
    G.deterministicallyStopped_isRealized T hT⟩

end ActualLocallySIntegrableStrategy

end FTAPTheorem42
