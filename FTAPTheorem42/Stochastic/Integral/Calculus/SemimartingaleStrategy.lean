/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Trading.Basic
import FTAPTheorem42.Foundations.Process
import FTAPTheorem42.Foundations.ProcessIndistinguishable
import FTAPTheorem42.Stochastic.Predictable.PredictableHahnDecomposition
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Regularity data for candidate stochastic-integral strategies

This file fixes the concrete continuous-time boundary used by the stochastic
part of Theorem 4.2: real-valued processes indexed by `ℝ≥0`.  It records a
special-semimartingale decomposition and the regularity data carried by one
candidate stochastic-integral strategy.  The candidate record does not assert
that its components are the stochastic integrals of its stored integrand.
Concrete realization membership is therefore represented by a separate
carrier, and existence of either object for a general semimartingale is not
asserted here.
-/

namespace FTAPTheorem42

open MeasureTheory Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Concrete process and decomposition signatures -/

/--
The supplied special-semimartingale decomposition of a price process.

Canonicality and existence are deliberately not fields of this boundary
object.  The finite-variation component is required to be predictable and
pathwise of locally bounded variation; the source identity is process
indistinguishability under the supplied measure.
-/
structure SpecialSemimartingaleDecomposition
    (S : Process Ω)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) where
  martingalePart : Process Ω
  finiteVariationPart : Process Ω
  martingalePart_isLocalMartingale : LocalMartingale martingalePart ℱ μ
  finiteVariationPart_isPredictable : IsStronglyPredictable ℱ finiteVariationPart
  finiteVariationPart_isLocallyBoundedVariation :
    ∀ ω, LocallyBoundedVariationOn (fun t => finiteVariationPart t ω) Set.univ
  decomposition : ProcessIndistinguishable μ S
    (fun t ω => martingalePart t ω + finiteVariationPart t ω)

/-! ## Regularity data for one candidate strategy -/

/-
The `D` parameter records which supplied price decomposition the candidate is
attached to.  The fields below only record regularity and the decomposition of
the candidate output.  In particular, they do not identify either component
with an integral of `integrand` against the corresponding component of `D`.
Integral identities must therefore quantify over an actual-strategy carrier,
not over all values of this freely constructible structure.
-/
structure SIntegrableStrategy
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    (D : SpecialSemimartingaleDecomposition S ℱ μ) where
  integrand : Process Ω
  stochasticIntegral : Process Ω
  martingalePart : Process Ω
  finiteVariationPart : Process Ω
  finiteVariationMeasure : PredictableSignedMeasure.Measure ℱ
  integrand_isPredictable : IsStronglyPredictable ℱ integrand
  stochasticIntegral_isStronglyAdapted : StronglyAdapted ℱ stochasticIntegral
  stochasticIntegral_isRightContinuous :
    ∀ ω t, ContinuousWithinAt (stochasticIntegral · ω) (Set.Ici t) t
  martingalePart_isLocalMartingale : LocalMartingale martingalePart ℱ μ
  martingalePart_isStronglyAdapted : StronglyAdapted ℱ martingalePart
  martingalePart_isRightContinuous :
    ∀ ω t, ContinuousWithinAt (martingalePart · ω) (Set.Ici t) t
  finiteVariationPart_isPredictable : IsStronglyPredictable ℱ finiteVariationPart
  finiteVariationPart_isRightContinuous :
    ∀ ω t, ContinuousWithinAt (finiteVariationPart · ω) (Set.Ici t) t
  finiteVariationPart_isBoundedVariation :
    ∀ ω, BoundedVariationOn (fun t => finiteVariationPart t ω) Set.univ
  integral_decomposition : ProcessIndistinguishable μ stochasticIntegral
    (fun t ω => martingalePart t ω + finiteVariationPart t ω)
  source_decomposition : ProcessIndistinguishable μ S
    (fun t ω => D.martingalePart t ω + D.finiteVariationPart t ω)

/-- The martingale coordinate normalized to start at zero.  Unlike the raw
component stored in a special-semimartingale decomposition, this process is
unchanged when a time-constant random variable is moved between the
martingale and finite-variation components. -/
def SIntegrableStrategy.centeredMartingalePart
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D) : Process Ω :=
  fun t ω => H.martingalePart t ω - H.martingalePart 0 ω

/-- The output process stored in candidate strategy data. -/
abbrev stochasticIntegral
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D) : Process Ω :=
  H.stochasticIntegral

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Measurability of terminal gains

For a terminal market strategy, adaptedness of the running gain and almost
sure convergence at infinity imply a.e. strong measurability of its terminal
claim.  Restriction to integer times is enough; no uncountable intersection
of fixed-time measurable events is used.
-/

open Filter MeasureTheory Topology
open scoped NNReal

variable {Omega : Type*} [MeasurableSpace Omega]

namespace GainProcessModel

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega}
  (A : GainProcessModel Omega NNReal)

/-- An adapted running gain with an a.s. continuous-time terminal limit has
an a.e. strongly measurable terminal claim. -/
theorem terminalGain_aestronglyMeasurable_of_adapted_tendsto
    (H : A.Strategy)
    (hAdapted : StronglyAdapted F (A.gain H))
    (hTerminal : ∀ᵐ omega ∂mu,
      Tendsto (fun t : NNReal => A.gain H t omega) atTop
        (nhds (A.terminalGain H omega))) :
    AEStronglyMeasurable (A.terminalGain H) mu := by
  have hGainMeas : ∀ n : Nat,
      AEStronglyMeasurable (A.gain H (n : NNReal)) mu := by
    intro n
    exact ((hAdapted (n : NNReal)).mono (F.le (n : NNReal)))
      |>.aestronglyMeasurable
  have hTerminalInteger : TendstoAE mu
      (fun n : Nat => A.gain H (n : NNReal)) (A.terminalGain H) := by
    filter_upwards [hTerminal] with omega hOmega
    exact hOmega.comp tendsto_natCast_atTop_atTop
  exact aestronglyMeasurable_of_tendsto_ae
    atTop hGainMeas hTerminalInteger

end GainProcessModel

end FTAPTheorem42
