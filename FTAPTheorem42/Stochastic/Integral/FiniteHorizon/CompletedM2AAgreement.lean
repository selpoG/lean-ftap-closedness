/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletionAgreement

/-!
# Agreement of elementary and completed finite-horizon M2A graphs

The completed martingale operator is insensitive to predictable-energy
almost-everywhere changes of its coefficient.  Together with the bounded
finite-variation process agreement, this identifies the completed graph on
every bounded predictable elementary coefficient.  Hence every member of
the elementary actual carrier embeds into the completed actual carrier,
without changing its raw integrand or gain representative.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticEnergy
namespace Data

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {M : Process Omega} {T : NNReal}

/-- The completed martingale process depends only on the coefficient's
quadratic-energy almost-everywhere class. -/
theorem finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure)
    (g : NNReal × Omega -> Real)
    (hgMeas : StronglyMeasurable[F.predictable] g)
    (hg : MemLp g (2 : ENNReal) Q.predictableEnergyMeasure)
    (hfg : f =ᵐ[Q.predictableEnergyMeasure] g) :
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess
        hUsual Q hM hMRight hMT f hfMeas hf)
      (finiteHorizonMartingaleIntegralProcess
        hUsual Q hM hMRight hMT g hgMeas hg) := by
  let I : Process Omega := finiteHorizonMartingaleIntegralProcess
    hUsual Q hM hMRight hMT f hfMeas hf
  let J : Process Omega := finiteHorizonMartingaleIntegralProcess
    hUsual Q hM hMRight hMT g hgMeas hg
  have hI : Martingale I F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hM hMRight hMT f hfMeas hf
  have hJ : Martingale J F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hM hMRight hMT g hgMeas hg
  let hITerminal : MemLp (I T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT f hfMeas hf
  let hJTerminal : MemLp (J T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT g hgMeas hg
  have hCompletedEq :
      finiteHorizonMartingaleTerminalIntegralLp
          Q hM hMRight hMT f hfMeas hf =
        finiteHorizonMartingaleTerminalIntegralLp
          Q hM hMRight hMT g hgMeas hg := by
    apply edist_eq_zero.mp
    rw [edist_finiteHorizonMartingaleTerminalIntegralLp_eq_eLpNorm]
    apply eLpNorm_eq_zero_of_ae_zero
    filter_upwards [hfg] with point hpoint
    change f point - g point = (0 : Real)
    rw [hpoint, sub_self]
  have hTerminalAE : I T =ᵐ[mu] J T :=
    (MemLp.toLp_eq_toLp_iff hITerminal hJTerminal).mp
      ((finiteHorizonMartingaleIntegralProcess_terminal_toLp
          hUsual Q hM hMRight hMT f hfMeas hf).trans
        (hCompletedEq.trans
          (finiteHorizonMartingaleIntegralProcess_terminal_toLp
            hUsual Q hM hMRight hMT g hgMeas hg).symm))
  have hEqAt : forall t, I t =ᵐ[mu] J t := by
    intro t
    by_cases ht : t <= T
    · exact (hI.condExp_ae_eq ht).symm.trans
        ((condExp_congr_ae hTerminalAE).trans (hJ.condExp_ae_eq ht))
    · have hTt : T <= t := le_of_not_ge ht
      exact (finiteHorizonMartingaleIntegralProcess_constantAfter
        hUsual Q hM hMRight hMT f hfMeas hf t hTt).trans
          (hTerminalAE.trans
            (finiteHorizonMartingaleIntegralProcess_constantAfter
              hUsual Q hM hMRight hMT g hgMeas hg t hTt).symm)
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense
    I J NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
    (Filter.Eventually.of_forall
      (finiteHorizonMartingaleIntegralProcess_rightContinuous
        hUsual Q hM hMRight hMT f hfMeas hf))
    (Filter.Eventually.of_forall
      (finiteHorizonMartingaleIntegralProcess_rightContinuous
        hUsual Q hM hMRight hMT g hgMeas hg))
    (fun n => hEqAt _)

end Data
end BoundedMartingaleQuadraticEnergy

namespace SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}
  {T : NNReal}

/-- A bounded elementary coefficient belongs to both concrete completed
control spaces. -/
noncomputable def finiteHorizonM2ACoefficientOfElementary
    (E : SIntegrableFiniteVariationBridge G)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (K : PredictableElementaryStrategy F)
    (C : NNReal) (hCoefficient : forall omega,
      K.coefficientAbsSum omega <= C) :
    FiniteHorizonM2ACoefficient E Q where
  coefficient := Function.uncurry K.integrand
  coefficient_isStronglyMeasurable := K.integrand_isStronglyPredictable
  coefficient_memLp_variation := by
    apply MemLp.of_bound
      K.integrand_isStronglyPredictable.aestronglyMeasurable (C : Real)
    exact Filter.Eventually.of_forall fun point => by
      rw [Real.norm_eq_abs]
      exact (K.abs_integrand_le_coefficientAbsSum point.1 point.2).trans
        (by exact_mod_cast hCoefficient point.2)
  coefficient_memLp_energy := elementaryIntegrand_memLp_two Q K C hCoefficient

omit [SigmaFiniteFiltration mu F] in
@[simp]
theorem finiteHorizonM2ACoefficientOfElementary_integrand
    (E : SIntegrableFiniteVariationBridge G)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (K : PredictableElementaryStrategy F)
    (C : NNReal) (hCoefficient : forall omega,
      K.coefficientAbsSum omega <= C) :
    (finiteHorizonM2ACoefficientOfElementary
      E Q K C hCoefficient).integrand = K.finiteHorizonIntegrand T :=
  rfl

/-- The completed martingale component agrees with the original stopped
elementary martingale gain. -/
theorem finiteHorizonCompletedMartingalePart_indistinguishable_elementary
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K : PredictableElementaryStrategy F)
    (C : NNReal) (hCoefficient : forall omega,
      K.coefficientAbsSum omega <= C) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal
        (finiteHorizonM2ACoefficientOfElementary E Q K C hCoefficient))
      (K.finiteHorizonGain G.martingalePart T) := by
  let c := finiteHorizonM2ACoefficientOfElementary
    E Q K C hCoefficient
  have hRestricted : Function.uncurry c.integrand
      =ᵐ[Q.predictableEnergyMeasure] Function.uncurry K.integrand := by
    exact finiteHorizonCoefficient_ae_eq Q (Function.uncurry K.integrand)
  exact (finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
    (Function.uncurry c.integrand) c.integrand_isStronglyPredictable
      c.integrand_memLp_energy
    (Function.uncurry K.integrand) K.integrand_isStronglyPredictable
      (elementaryIntegrand_memLp_two Q K C hCoefficient) hRestricted).trans
    (finiteHorizonMartingaleIntegralProcess_indistinguishable_elementary
      hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
        K C hCoefficient)

omit [SigmaFiniteFiltration mu F] in
/-- The completed finite-variation component agrees with the original
stopped elementary finite-variation gain. -/
theorem
    finiteHorizonCompletedFiniteVariationPart_indistinguishable_elementary
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (K : PredictableElementaryStrategy F)
    (C : NNReal) (hCoefficient : forall omega,
      K.coefficientAbsSum omega <= C) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E
        (finiteHorizonM2ACoefficientOfElementary E Q K C hCoefficient))
      (K.finiteHorizonGain G.finiteVariationPart T) := by
  let c := finiteHorizonM2ACoefficientOfElementary
    E Q K C hCoefficient
  have hBound : forall t omega, |c.integrand t omega| <= (C : Real) := by
    intro t omega
    rw [finiteHorizonM2ACoefficientOfElementary_integrand]
    exact (K.abs_finiteHorizonIntegrand_le_coefficientAbsSum
      T t omega).trans (by exact_mod_cast hCoefficient omega)
  have hCompleted :=
    completedFiniteVariationProcess_indistinguishable_bounded
      hUsual E c.integrand c.integrand_isStronglyPredictable
        c.integrand_memLp_variation hBound
  have hRawBound : forall t omega, |K.integrand t omega| <= (C : Real) := by
    intro t omega
    exact (K.abs_integrand_le_coefficientAbsSum t omega).trans
      (by exact_mod_cast hCoefficient omega)
  have hRaw := finiteVariationIntegralProcess_indistinguishable_elementaryGain
    E K hRawBound
  apply hCompleted.trans
  filter_upwards [hRaw] with omega homega
  intro t
  change finiteVariationIntegralProcess E
      (finiteHorizonCoefficient T (Function.uncurry K.integrand)) t omega =
    ElementaryStrategy.gain G.finiteVariationPart K.toElementary
      (min t T) omega
  rw [finiteVariationIntegralProcess_finiteHorizonCoefficient]
  exact homega (min t T)

/-- On every bounded elementary coefficient, the sum of the two completed
components is the original stopped elementary gain. -/
theorem finiteHorizonCompletedM2AGain_indistinguishable_elementary
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K : PredictableElementaryStrategy F)
    (C : NNReal) (hCoefficient : forall omega,
      K.coefficientAbsSum omega <= C) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale
        hGMTerminal
        (finiteHorizonM2ACoefficientOfElementary E Q K C hCoefficient))
      (K.finiteHorizonGain G.stochasticIntegral T) := by
  filter_upwards [
    finiteHorizonCompletedMartingalePart_indistinguishable_elementary
      hUsual E Q hGMartingale hGMTerminal K C hCoefficient,
    finiteHorizonCompletedFiniteVariationPart_indistinguishable_elementary
      hUsual E Q K C hCoefficient,
    G.integral_decomposition] with omega hM hA hSource
  intro t
  change _ + _ = ElementaryStrategy.gain G.stochasticIntegral
    K.toElementary (min t T) omega
  rw [hM t, hA t]
  calc
    ElementaryStrategy.gain G.martingalePart K.toElementary (min t T) omega +
        ElementaryStrategy.gain G.finiteVariationPart K.toElementary
          (min t T) omega =
      ElementaryStrategy.gain
        (fun s omega' => G.martingalePart s omega' +
          G.finiteVariationPart s omega') K.toElementary (min t T) omega :=
      (ElementaryStrategy.gain_add_price G.martingalePart
        G.finiteVariationPart K.toElementary (min t T) omega).symm
    _ = ElementaryStrategy.gain G.stochasticIntegral K.toElementary
        (min t T) omega :=
      (ElementaryStrategy.gain_congr_price K.toElementary
        (min t T) omega hSource).symm

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
