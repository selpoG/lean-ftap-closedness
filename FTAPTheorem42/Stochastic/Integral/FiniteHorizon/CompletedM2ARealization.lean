/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.M2AApproximation
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletion

/-!
# Completed finite-horizon M2A realization

On a fixed horizon, one predictable coefficient can belong simultaneously
to the martingale quadratic-energy `L²` space and the canonical
finite-variation `L¹` space.  The two concrete completions already built for
these controls are assembled here into one semimartingale gain process.

The resulting realization carrier is graph-extensional.  Its membership is
defined by equality with the concrete completed graph, and the canonical
member is constructed immediately; no stochastic-integral range statement
is added as an abstract field.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

/-- Concrete output of the finite-variation process completion. -/
structure CompletedFiniteVariationProcessData
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) where
  cutoff : Nat -> Nat
  cutoff_strictMono : StrictMono cutoff
  process : Process Omega
  process_isStronglyPredictable : IsStronglyPredictable F process
  process_rightContinuous : forall omega t,
    ContinuousWithinAt (process · omega) (Ici t) t
  process_isBoundedVariation : forall omega,
    BoundedVariationOn (process · omega) Set.univ
  approximation_tendsto : ∀ᵐ omega ∂mu,
    TendstoUniformly
        (fun n t => commonFiniteVariationProcessApproximation
          E f hf (cutoff n) t omega)
        (fun t => process t omega) atTop ∧
      Tendsto (fun n => eVariationOn (fun t =>
          process t omega - commonFiniteVariationProcessApproximation
            E f hf (cutoff n) t omega) Set.univ)
        atTop (nhds 0)
  terminal_memLp : MemLp
    (fun omega => limUnder atTop (fun t => process t omega)) 1
      E.referenceMeasure
  terminal_toLp_eq : terminal_memLp.toLp
      (fun omega => limUnder atTop (fun t => process t omega)) =
    finiteVariationTerminalIntegralLp E f hf hVariation

omit [SigmaFiniteFiltration mu F] in
/-- The existing pathwise completion theorem supplies the concrete data
package without an additional realization assumption. -/
theorem exists_completedFiniteVariationProcessData
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) :
    Nonempty (CompletedFiniteVariationProcessData E f hf hVariation) := by
  obtain ⟨cutoff, hCutoff, B, hBPredictable, hBRight, hBVariation,
      hBApproximation, hBTerminal, hBTerminalEq⟩ :=
    exists_commonFiniteVariationProcessLimit
      hUsual E f hf hVariation
  exact ⟨{
    cutoff := cutoff
    cutoff_strictMono := hCutoff
    process := B
    process_isStronglyPredictable := hBPredictable
    process_rightContinuous := hBRight
    process_isBoundedVariation := hBVariation
    approximation_tendsto := hBApproximation
    terminal_memLp := hBTerminal
    terminal_toLp_eq := hBTerminalEq }⟩

/-- A selected finite-variation process completion. -/
noncomputable def completedFiniteVariationProcessData
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) :
    CompletedFiniteVariationProcessData E f hf hVariation :=
  Classical.choice
    (exists_completedFiniteVariationProcessData
      hUsual E f hf hVariation)

/-- The process selected by the canonical finite-variation completion. -/
noncomputable def completedFiniteVariationProcess
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) : Process Omega :=
  (completedFiniteVariationProcessData
    hUsual E f hf hVariation).process

omit [SigmaFiniteFiltration mu F] in
theorem completedFiniteVariationProcess_isStronglyPredictable
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) :
    IsStronglyPredictable F
      (completedFiniteVariationProcess hUsual E f hf hVariation) :=
  (completedFiniteVariationProcessData
    hUsual E f hf hVariation).process_isStronglyPredictable

omit [SigmaFiniteFiltration mu F] in
theorem completedFiniteVariationProcess_rightContinuous
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) :
    forall omega t, ContinuousWithinAt
      (completedFiniteVariationProcess hUsual E f hf hVariation · omega)
        (Ici t) t :=
  (completedFiniteVariationProcessData
    hUsual E f hf hVariation).process_rightContinuous

omit [SigmaFiniteFiltration mu F] in
theorem completedFiniteVariationProcess_isBoundedVariation
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) :
    forall omega, BoundedVariationOn
      (completedFiniteVariationProcess hUsual E f hf hVariation · omega)
        Set.univ :=
  (completedFiniteVariationProcessData
    hUsual E f hf hVariation).process_isBoundedVariation

/-- One coefficient carrying the two concrete finite-horizon integrability
witnesses required by the completed martingale and finite-variation
operators. -/
structure FiniteHorizonM2ACoefficient
    (E : SIntegrableFiniteVariationBridge G)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T) where
  coefficient : NNReal × Omega -> Real
  coefficient_isStronglyMeasurable :
    StronglyMeasurable[F.predictable] coefficient
  coefficient_memLp_variation : MemLp coefficient 1
    (canonicalVariationMeasure E)
  coefficient_memLp_energy : MemLp coefficient (2 : ENNReal)
    Q.predictableEnergyMeasure

namespace FiniteHorizonM2ACoefficient

variable {T : NNReal}

omit [SigmaFiniteFiltration mu F] in
@[ext]
theorem ext
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T}
    {K L : FiniteHorizonM2ACoefficient E Q} (h : K.coefficient = L.coefficient) : K = L := by
  cases K
  cases L
  cases h
  rfl

/-- Restrict the coefficient to the positive deterministic horizon. -/
noncomputable def integrand
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (c : FiniteHorizonM2ACoefficient E Q) : Process Omega :=
  finiteHorizonCoefficient T c.coefficient

omit [SigmaFiniteFiltration mu F] in
theorem integrand_isStronglyPredictable
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (c : FiniteHorizonM2ACoefficient E Q) :
    IsStronglyPredictable F c.integrand :=
  finiteHorizonCoefficient_isStronglyPredictable T
    c.coefficient_isStronglyMeasurable

omit [SigmaFiniteFiltration mu F] in
theorem integrand_memLp_variation
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (c : FiniteHorizonM2ACoefficient E Q) :
    MemLp (Function.uncurry c.integrand) 1
      (canonicalVariationMeasure E) :=
  finiteHorizonCoefficient_memLp E T c.coefficient_memLp_variation

omit [SigmaFiniteFiltration mu F] in
theorem integrand_memLp_energy
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (c : FiniteHorizonM2ACoefficient E Q) :
    MemLp (Function.uncurry c.integrand) (2 : ENNReal)
      Q.predictableEnergyMeasure :=
  finiteHorizonCoefficient_memLp_energy_two T Q
    c.coefficient_memLp_energy

end FiniteHorizonM2ACoefficient

/-- The completed martingale component associated with one common
finite-horizon coefficient. -/
noncomputable def finiteHorizonCompletedMartingalePart
    (hUsual : Filtration.UsualConditions mu F)
    (T : NNReal)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) : Process Omega :=
  finiteHorizonMartingaleIntegralProcess
    hUsual Q hGMartingale G.martingalePart_isRightContinuous
      hGMTerminal (Function.uncurry c.integrand)
      c.integrand_isStronglyPredictable c.integrand_memLp_energy

/-- The completed finite-variation component associated with the same
coefficient. -/
noncomputable def finiteHorizonCompletedFiniteVariationPart
    (hUsual : Filtration.UsualConditions mu F)
    (T : NNReal)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (c : FiniteHorizonM2ACoefficient E Q) : Process Omega :=
  completedFiniteVariationProcess
    hUsual E c.integrand c.integrand_isStronglyPredictable
      c.integrand_memLp_variation

/-- The completed finite-horizon gain is the sum of the two concrete
component completions built from one coefficient. -/
noncomputable def finiteHorizonCompletedM2AGain
    (hUsual : Filtration.UsualConditions mu F)
    (T : NNReal)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) : Process Omega :=
  fun t omega =>
    finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal c t omega +
      finiteHorizonCompletedFiniteVariationPart hUsual T Q E c t omega

/-- The canonical raw strategy whose gain is the completed finite-horizon
`M² ⊕ A¹` graph. -/
noncomputable def finiteHorizonCompletedM2AStrategy
    (hUsual : Filtration.UsualConditions mu F)
    (T : NNReal)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) : SIntegrableStrategy D := by
  let I : Process Omega := finiteHorizonCompletedMartingalePart
    hUsual T Q hGMartingale hGMTerminal c
  let B : Process Omega := finiteHorizonCompletedFiniteVariationPart
    hUsual T Q E c
  have hIMartingale : Martingale I F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hGMartingale G.martingalePart_isRightContinuous
        hGMTerminal (Function.uncurry c.integrand)
        c.integrand_isStronglyPredictable c.integrand_memLp_energy
  have hIRight : forall omega t,
      ContinuousWithinAt (I · omega) (Ici t) t :=
    finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual Q hGMartingale G.martingalePart_isRightContinuous
        hGMTerminal (Function.uncurry c.integrand)
        c.integrand_isStronglyPredictable c.integrand_memLp_energy
  have hBPredictable : IsStronglyPredictable F B :=
    completedFiniteVariationProcess_isStronglyPredictable
      hUsual E c.integrand c.integrand_isStronglyPredictable
        c.integrand_memLp_variation
  have hBRight : forall omega t,
      ContinuousWithinAt (B · omega) (Ici t) t :=
    completedFiniteVariationProcess_rightContinuous
      hUsual E c.integrand c.integrand_isStronglyPredictable
        c.integrand_memLp_variation
  have hBVariation : forall omega,
      BoundedVariationOn (B · omega) Set.univ :=
    completedFiniteVariationProcess_isBoundedVariation
      hUsual E c.integrand c.integrand_isStronglyPredictable
        c.integrand_memLp_variation
  exact {
    integrand := c.integrand
    stochasticIntegral := fun t omega => I t omega + B t omega
    martingalePart := I
    finiteVariationPart := B
    finiteVariationMeasure := 0
    integrand_isPredictable := c.integrand_isStronglyPredictable
    stochasticIntegral_isStronglyAdapted :=
      hIMartingale.stronglyAdapted.add hBPredictable.stronglyAdapted
    stochasticIntegral_isRightContinuous := fun omega t =>
      (hIRight omega t).add (hBRight omega t)
    martingalePart_isLocalMartingale := ProbabilityTheory.Locally.of_prop
      hIMartingale
    martingalePart_isStronglyAdapted := hIMartingale.stronglyAdapted
    martingalePart_isRightContinuous := hIRight
    finiteVariationPart_isPredictable := hBPredictable
    finiteVariationPart_isRightContinuous := hBRight
    finiteVariationPart_isBoundedVariation := hBVariation
    integral_decomposition := ProcessIndistinguishable.refl mu _
    source_decomposition := G.source_decomposition }

/-- The centered martingale coordinate of the canonical completed strategy
is its completed martingale integral. -/
theorem finiteHorizonCompletedM2AStrategy_centeredMartingalePart
    (hUsual : Filtration.UsualConditions mu F)
    (T : NNReal)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AStrategy hUsual T Q E hGMartingale
        hGMTerminal c).centeredMartingalePart
      (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal c) := by
  have hZero :=
    finiteHorizonMartingaleIntegralProcess_zero hUsual Q hGMartingale
      G.martingalePart_isRightContinuous hGMTerminal
        (Function.uncurry c.integrand) c.integrand_isStronglyPredictable
          c.integrand_memLp_energy
  change ProcessIndistinguishable mu
    (fun t omega =>
      finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal c t omega -
        finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal c 0 omega)
    (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
      hGMTerminal c)
  filter_upwards [hZero] with omega hZeroOmega
  intro t
  change finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
    hGMTerminal c 0 omega = 0 at hZeroOmega
  rw [hZeroOmega, sub_zero]

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
