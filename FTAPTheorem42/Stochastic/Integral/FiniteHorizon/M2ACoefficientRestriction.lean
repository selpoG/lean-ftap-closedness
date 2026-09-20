/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.M2ACoefficientAlgebra

/-!
# Predictable restriction of finite-horizon M2A coefficients

Restriction to a predictable time--sample set contracts both concrete
control norms.  Hence one common coefficient in the martingale-energy and
finite-variation spaces remains a common coefficient after restriction.
The deterministic horizon cut and the predictable restriction commute
pointwise.
-/

open Filter MeasureTheory Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}
  {T : NNReal}

namespace FiniteHorizonM2ACoefficient

/-- Restrict a common finite-horizon coefficient to a predictable set. -/
noncomputable def restrictPredictable
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (K : FiniteHorizonM2ACoefficient E Q) :
    FiniteHorizonM2ACoefficient E Q where
  coefficient := B.indicator K.coefficient
  coefficient_isStronglyMeasurable :=
    K.coefficient_isStronglyMeasurable.indicator hB
  coefficient_memLp_variation :=
    K.coefficient_memLp_variation.indicator hB
  coefficient_memLp_energy :=
    K.coefficient_memLp_energy.indicator hB

@[simp]
theorem restrictPredictable_coefficient
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (K : FiniteHorizonM2ACoefficient E Q) :
    (K.restrictPredictable B hB).coefficient =
      B.indicator K.coefficient :=
  rfl

/-- Restricting the raw coefficient before the deterministic horizon cut is
the same as predictably restricting the horizon-cut process. -/
theorem restrictPredictable_integrand
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (K : FiniteHorizonM2ACoefficient E Q) :
    (K.restrictPredictable B hB).integrand =
      PredictableProcess.restrict B K.integrand := by
  funext t omega
  by_cases hStrip :
      (t, omega) ∈ finiteHorizonPredictableStrip (Omega := Omega) T
  · by_cases hBmem : (t, omega) ∈ B
    · simp [integrand, finiteHorizonCoefficient,
        PredictableProcess.restrict_apply_of_mem, hStrip, hBmem]
    · simp [integrand, finiteHorizonCoefficient,
        PredictableProcess.restrict_apply_of_mem,
        PredictableProcess.restrict_apply_of_notMem, hStrip, hBmem]
  · by_cases hBmem : (t, omega) ∈ B
    · simp [integrand, finiteHorizonCoefficient,
        PredictableProcess.restrict_apply_of_mem,
        PredictableProcess.restrict_apply_of_notMem, hStrip, hBmem]
    · simp [integrand, finiteHorizonCoefficient,
        PredictableProcess.restrict_apply_of_notMem, hStrip, hBmem]

/-- Keep only coefficients larger than the truncation threshold. This
same predictable cut is used in both control measures. -/
noncomputable def truncationTail
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T}
    (K : FiniteHorizonM2ACoefficient E Q) (n : Nat) : FiniteHorizonM2ACoefficient E Q :=
  K.restrictPredictable {x | (n : Real) + 1 < |K.coefficient x|}
    (measurableSet_lt measurable_const K.coefficient_isStronglyMeasurable.norm.measurable)

/-- The complementary bounded coefficient cut. -/
noncomputable def truncationCut
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T}
    (K : FiniteHorizonM2ACoefficient E Q) (n : Nat) : FiniteHorizonM2ACoefficient E Q :=
  K.restrictPredictable {x | |K.coefficient x| ≤ (n : Real) + 1}
    (measurableSet_le K.coefficient_isStronglyMeasurable.norm.measurable measurable_const)

/-- Bounded cut and complementary tail exactly recover the common coefficient. -/
theorem truncationCut_add_truncationTail
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T}
    (K : FiniteHorizonM2ACoefficient E Q) (n : Nat) :
    (K.truncationCut n).add (K.truncationTail n) = K := by
  apply ext
  funext x
  by_cases hx : |K.coefficient x| ≤ (n : Real) + 1
  · simp [truncationCut, truncationTail, restrictPredictable, add, hx, not_lt.mpr hx]
  · simp [truncationCut, truncationTail, restrictPredictable, add, hx, lt_of_not_ge hx]

/-- Integrability makes coefficient tails small, for any of the concrete
control measures. No finite total mass or bounded coefficient is assumed. -/
theorem truncationTail_tendsto_eLpNorm
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T}
    (K : FiniteHorizonM2ACoefficient E Q)
    (ν : @Measure (NNReal × Omega) F.predictable) (p : ENNReal)
    (hK : MemLp K.coefficient p ν) :
    Tendsto (fun n => eLpNorm (K.truncationTail n).coefficient p ν) atTop (𝓝 0) := by
  classical
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  obtain ⟨M, hM⟩ := hK.eLpNorm_indicator_norm_ge_le
    K.coefficient_isStronglyMeasurable (show 0 < (δ : ENNReal) from hδ)
  obtain ⟨N, hN⟩ := exists_nat_gt M
  refine ⟨N, fun n hn => ?_⟩
  apply le_trans (eLpNorm_mono
    (K.truncationTail n).coefficient_isStronglyMeasurable.aestronglyMeasurable (fun x => ?_))
    (hM.trans (by simpa using hδε.le))
  change ‖({x | (n : Real) + 1 < |K.coefficient x|}.indicator K.coefficient) x‖ ≤ _
  by_cases hx : x ∈ {x | (n : Real) + 1 < |K.coefficient x|}
  · have hx' : (n : Real) + 1 < |K.coefficient x| := hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
    · change M ≤ ‖K.coefficient x‖₊
      simp only [coe_nnnorm, Real.norm_eq_abs]
      exact hN.le.trans ((Nat.cast_le.mpr hn).trans
        ((le_add_of_nonneg_right zero_le_one).trans hx'.le))
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _

/-- The exact same coefficient tail vanishes in both norms required by
completed M² ⊕ A¹ integration. -/
theorem truncationTail_control_convergence
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T}
    (K : FiniteHorizonM2ACoefficient E Q) :
    Tendsto (fun n => eLpNorm (K.truncationTail n).coefficient 1
      (canonicalVariationMeasure E)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (K.truncationTail n).coefficient (2 : ENNReal)
      Q.predictableEnergyMeasure) atTop (𝓝 0) :=
  ⟨K.truncationTail_tendsto_eLpNorm _ _ K.coefficient_memLp_variation,
    K.truncationTail_tendsto_eLpNorm _ _ K.coefficient_memLp_energy⟩

end FiniteHorizonM2ACoefficient

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
