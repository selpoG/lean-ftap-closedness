/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.FiniteVariationTestEstimate
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationPathIntegralControl
import FTAPTheorem42.Stochastic.Predictable.PredictableUnitBoundedElementaryDensity
import FTAPTheorem42.Stochastic.Topology.Emery.Algebra
import FTAPTheorem42.Stochastic.Topology.Emery.MeasureTransfer
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAgreement
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAdditivity
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARealization
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARestriction
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletionGeneralAgreement
import FTAPTheorem42.Stochastic.FiniteVariation.CanonicalVariationControl
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Foundations.ProcessEnvelope
import FTAPTheorem42.Stochastic.Process.UniformProcessLimitUniqueness

/-!
# Completed finite-horizon semantics for a tested elementary row

For one row difference, the arbitrary predictable test is interpreted by
the same completed martingale and finite-variation operators.  The product
coefficient is concrete: it is obtained from the elementary row coefficient
by `FiniteHorizonM2ACoefficient.multiplyPredictable`.  The elementary case
is then identified with the existing binary Emery test, which is the
semantic bridge used by the analytic estimates below.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data
open PredictableUnitBoundedElementaryDensity

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

/-! ## The concrete row coefficient and its completed gain -/

/-! The canonical finite-horizon representative of an arbitrary bounded
predictable test.  The restriction is made before invoking the density
theorem, so the same test is used by the completed coefficient and the raw
stopped gain. -/

noncomputable def horizonRestrictedTest
    (T : NNReal) (h : Process Omega) : Process Omega :=
  finiteHorizonCoefficient T (Function.uncurry h)

theorem horizonRestrictedTest_zero_off_horizon
    {T : NNReal} (h : Process Omega)
    (_hh : IsStronglyPredictable F h) :
    ∀ p, p ∉
      FiniteHorizonPredictableIndicatorRing.horizonCarrier (Omega := Omega) T →
        horizonRestrictedTest T h p.1 p.2 = 0 := by
  intro p hp
  have hp' : p ∉ finiteHorizonPredictableStrip (Omega := Omega) T := by
    intro hStrip
    have hmem : 0 < p.1 ∧ p.1 ≤ T :=
      (mem_stochasticIntervalIocZero_iff (fun _ : Omega => T)
        p.1 p.2).1 hStrip
    exact hp (Set.mem_prod.2 ⟨⟨hmem.1, hmem.2⟩, Set.mem_univ p.2⟩)
  simp only [horizonRestrictedTest, finiteHorizonCoefficient,
    PredictableProcess.restrict_apply_of_notMem hp']

theorem finiteHorizonCompletedM2AGain_indistinguishable_of_integrand_eq
    {T : NNReal}
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c d : FiniteHorizonM2ACoefficient E Q)
    (hEq : c.integrand = d.integrand) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal c)
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal d) := by
  have hM := finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
      (Function.uncurry c.integrand) c.integrand_isStronglyPredictable
      c.integrand_memLp_energy
      (Function.uncurry d.integrand) d.integrand_isStronglyPredictable
      d.integrand_memLp_energy
      (Filter.Eventually.of_forall fun p => by
        exact congrFun (congrFun hEq p.1) p.2)
  have hA := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    hUsual E Q c
  have hA' := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    hUsual E Q d
  have hARaw : ProcessIndistinguishable mu
      (finiteVariationIntegralProcess E c.integrand)
      (finiteVariationIntegralProcess E d.integrand) := by
    exact Filter.Eventually.of_forall (fun omega t => by
      exact congrFun (congrFun (congrArg (finiteVariationIntegralProcess E) hEq)
        t) omega)
  filter_upwards [hM, hA, hARaw, hA'] with omega hMω hAω hARawω hA'ω
  intro t
  change finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
      hGMTerminal c t omega +
      finiteHorizonCompletedFiniteVariationPart hUsual T Q E c t omega =
    finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
      hGMTerminal d t omega +
      finiteHorizonCompletedFiniteVariationPart hUsual T Q E d t omega
  have hMω' :
      finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal c t omega =
      finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal d t omega := by
    exact hMω t
  rw [hMω', hAω t, hARawω t, hA'ω t]

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
