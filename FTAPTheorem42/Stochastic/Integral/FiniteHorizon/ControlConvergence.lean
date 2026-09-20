/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.TruncationConvergence
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAlgebra

/-! # Continuity of completed integrals under both coefficient controls -/

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {G : SIntegrableStrategy D}
  {T : NNReal} {E : SIntegrableFiniteVariationBridge G}

/-- Energy convergence alone controls the completed martingale components. -/
theorem finiteHorizonCompletedMartingalePart_emery_of_controls
    (hUsual : Filtration.UsualConditions μ F)
    (Q : BoundedMartingaleQuadraticKernel.Data F μ G.martingalePart T)
    (hM : Martingale G.martingalePart F μ) (hMT : MemLp (G.martingalePart T) 2 μ)
    (K : Nat → FiniteHorizonM2ACoefficient E Q) (L : FiniteHorizonM2ACoefficient E Q)
    (hEnergy : Tendsto (fun n => eLpNorm ((K n).coefficient - L.coefficient) 2
      Q.predictableEnergyMeasure) atTop (𝓝 0)) :
    ElementaryEmeryConverges μ F
      (fun n => finiteHorizonCompletedMartingalePart hUsual T Q hM hMT (K n))
      (finiteHorizonCompletedMartingalePart hUsual T Q hM hMT L) := by
  let c := fun n => (K n).add (L.smul (-1))
  have hc n : (c n).coefficient = (K n).coefficient - L.coefficient := by
    simp only [c, FiniteHorizonM2ACoefficient.add, FiniteHorizonM2ACoefficient.smul,
      neg_one_smul, sub_eq_add_neg]
  have hZero := finiteHorizonCompletedMartingalePart_emery_zero hUsual Q hM hMT c
    (by simpa only [hc] using hEnergy)
  apply elementaryEmeryConverges_iff_sub_zero.mpr
  apply hZero.congr_sequence
  intro n
  have hAdd := finiteHorizonCompletedMartingalePart_add hUsual Q hM hMT (K n) (L.smul (-1))
  have hNeg := finiteHorizonCompletedMartingalePart_smul hUsual Q hM hMT L (-1)
  filter_upwards [hAdd, hNeg] with ω ha hn
  intro t
  have ha' := ha t
  rw [Pi.add_apply, Pi.add_apply, hn t] at ha'
  change _ = finiteHorizonCompletedMartingalePart hUsual T Q hM hMT (K n) t ω -
    finiteHorizonCompletedMartingalePart hUsual T Q hM hMT L t ω
  simpa only [Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg] using ha'

/-- The martingale components of elementary approximants use the same
coefficients as the gain approximation. -/
theorem finiteHorizonElementaryMartingale_emery_of_controls
    (hUsual : Filtration.UsualConditions μ F)
    (Q : BoundedMartingaleQuadraticKernel.Data F μ G.martingalePart T)
    (hM : Martingale G.martingalePart F μ) (hMT : MemLp (G.martingalePart T) 2 μ)
    (J : Nat → PredictableElementaryStrategy F) (C : Nat → NNReal)
    (hC : ∀ n ω, (J n).coefficientAbsSum ω ≤ C n)
    (L : FiniteHorizonM2ACoefficient E Q)
    (hEnergy : Tendsto (fun n => eLpNorm
      (L.coefficient - Function.uncurry (J n).integrand) 2
      Q.predictableEnergyMeasure) atTop (𝓝 0)) :
    ElementaryEmeryConverges μ F (fun n => (J n).finiteHorizonGain G.martingalePart T)
      (finiteHorizonCompletedMartingalePart hUsual T Q hM hMT L) := by
  let c n := finiteHorizonM2ACoefficientOfElementary E Q (J n) (C n) (hC n)
  have hConv := finiteHorizonCompletedMartingalePart_emery_of_controls hUsual Q hM hMT c L
    (by simpa only [c, finiteHorizonM2ACoefficientOfElementary, eLpNorm_sub_comm] using hEnergy)
  exact hConv.congr_sequence fun n =>
    finiteHorizonCompletedMartingalePart_indistinguishable_elementary
      hUsual E Q hM hMT (J n) (C n) (hC n)

/-- Joint L¹ variation and L² energy convergence of coefficients gives
uniform elementary-test convergence to their completed integral. -/
theorem finiteHorizonCompletedM2AGain_emery_of_controls
    (hUsual : Filtration.UsualConditions μ F)
    (Q : BoundedMartingaleQuadraticKernel.Data F μ G.martingalePart T)
    (hM : Martingale G.martingalePart F μ) (hMT : MemLp (G.martingalePart T) 2 μ)
    (K : Nat → FiniteHorizonM2ACoefficient E Q) (L : FiniteHorizonM2ACoefficient E Q)
    (hVariation : Tendsto (fun n => eLpNorm ((K n).coefficient - L.coefficient) 1
      (canonicalVariationMeasure E)) atTop (𝓝 0))
    (hEnergy : Tendsto (fun n => eLpNorm ((K n).coefficient - L.coefficient) 2
      Q.predictableEnergyMeasure) atTop (𝓝 0)) :
    ElementaryEmeryConverges μ F
      (fun n => finiteHorizonCompletedM2AGain hUsual T Q E hM hMT (K n))
      (finiteHorizonCompletedM2AGain hUsual T Q E hM hMT L) := by
  let c := fun n => (K n).add (L.smul (-1))
  have hc n : (c n).coefficient = (K n).coefficient - L.coefficient := by
    simp only [c, FiniteHorizonM2ACoefficient.add, FiniteHorizonM2ACoefficient.smul,
      neg_one_smul, sub_eq_add_neg]
  have hZero := finiteHorizonCompletedM2AGain_emery_zero hUsual Q hM hMT c
    (by simpa only [hc] using hVariation) (by simpa only [hc] using hEnergy)
  apply elementaryEmeryConverges_iff_sub_zero.mpr
  apply hZero.congr_sequence
  intro n
  have hAdd := finiteHorizonCompletedM2AGain_add hUsual Q E hM hMT (K n) (L.smul (-1))
  have hNeg := finiteHorizonCompletedM2AGain_smul hUsual Q E hM hMT L (-1)
  filter_upwards [hAdd, hNeg] with w ha hn
  intro t
  have ha' := ha t
  rw [Pi.add_apply, Pi.add_apply, hn t] at ha'
  change _ = finiteHorizonCompletedM2AGain hUsual T Q E hM hMT (K n) t w -
    finiteHorizonCompletedM2AGain hUsual T Q E hM hMT L t w
  simpa only [Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg] using ha'

/-- A supplied common elementary approximation can be read as gains of the
original finite-horizon source, not only as completed coefficient values. -/
theorem finiteHorizonElementaryGain_emery_of_controls
    (hUsual : Filtration.UsualConditions μ F)
    (Q : BoundedMartingaleQuadraticKernel.Data F μ G.martingalePart T)
    (hM : Martingale G.martingalePart F μ) (hMT : MemLp (G.martingalePart T) 2 μ)
    (J : Nat → PredictableElementaryStrategy F) (C : Nat → NNReal)
    (hC : ∀ n w, (J n).coefficientAbsSum w ≤ C n)
    (L : FiniteHorizonM2ACoefficient E Q)
    (hVariation : Tendsto (fun n => eLpNorm
      (L.coefficient - Function.uncurry (J n).integrand) 1
      (canonicalVariationMeasure E)) atTop (𝓝 0))
    (hEnergy : Tendsto (fun n => eLpNorm
      (L.coefficient - Function.uncurry (J n).integrand) 2
      Q.predictableEnergyMeasure) atTop (𝓝 0)) :
    ElementaryEmeryConverges μ F (fun n => (J n).finiteHorizonGain G.stochasticIntegral T)
      (finiteHorizonCompletedM2AGain hUsual T Q E hM hMT L) := by
  let c n := finiteHorizonM2ACoefficientOfElementary E Q (J n) (C n) (hC n)
  have hConv := finiteHorizonCompletedM2AGain_emery_of_controls hUsual Q hM hMT c L
    (by simpa only [c, finiteHorizonM2ACoefficientOfElementary, eLpNorm_sub_comm] using hVariation)
    (by simpa only [c, finiteHorizonM2ACoefficientOfElementary, eLpNorm_sub_comm] using hEnergy)
  exact hConv.congr_sequence fun n => finiteHorizonCompletedM2AGain_indistinguishable_elementary
    hUsual E Q hM hMT (J n) (C n) (hC n)

end FTAPTheorem42.SIntegrableFiniteVariationBridge

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

/-! ## One elementary sequence for two completed integral constructions

The controls may arise from different decompositions and probabilities.
Only their finite predictable measures are added; martingale decompositions
are never transported between probabilities.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S U : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration ν F]
  {D : SpecialSemimartingaleDecomposition S F μ}
  {D' : SpecialSemimartingaleDecomposition U F ν}
  {G : SIntegrableStrategy D} {G' : SIntegrableStrategy D'}
  {T T' : NNReal} {E : SIntegrableFiniteVariationBridge G}
  {E' : SIntegrableFiniteVariationBridge G'}

/-- A bounded common coefficient admits the same elementary approximants for
both completed integrals, even under different probability measures. -/
theorem exists_commonElementarySequence_emery
    (hUsual : Filtration.UsualConditions μ F) (hUsual' : Filtration.UsualConditions ν F)
    (Q : BoundedMartingaleQuadraticKernel.Data F μ G.martingalePart T)
    (Q' : BoundedMartingaleQuadraticKernel.Data F ν G'.martingalePart T')
    (hM : Martingale G.martingalePart F μ) (hMT : MemLp (G.martingalePart T) 2 μ)
    (hM' : Martingale G'.martingalePart F ν) (hMT' : MemLp (G'.martingalePart T') 2 ν)
    (K : FiniteHorizonM2ACoefficient E Q) (K' : FiniteHorizonM2ACoefficient E' Q')
    (hCoeff : K.coefficient = K'.coefficient)
    (b : Real) (hBound : ∀ p, |K.coefficient p| ≤ b) :
    ∃ (J : Nat → PredictableElementaryStrategy F) (C : Nat → NNReal),
      (∀ n w, (J n).coefficientAbsSum w ≤ C n) ∧
      ElementaryEmeryConverges μ F (fun n => (J n).finiteHorizonGain G.stochasticIntegral T)
        (finiteHorizonCompletedM2AGain hUsual T Q E hM hMT K) ∧
      ElementaryEmeryConverges ν F (fun n => (J n).finiteHorizonGain G'.stochasticIntegral T')
        (finiteHorizonCompletedM2AGain hUsual' T' Q' E' hM' hMT' K') := by
  let _ := Q.predictableEnergyMeasure_isFinite
  let _ := Q'.predictableEnergyMeasure_isFinite
  let q := Q.predictableEnergyMeasure + Q'.predictableEnergyMeasure
  let v := canonicalVariationMeasure E + canonicalVariationMeasure E'
  have hqZero : q (PredictableIntervalAlgebra.Interval.timeZeroSlice : Set (NNReal × Ω)) = 0 := by
    have hSlice : (PredictableIntervalAlgebra.Interval.timeZeroSlice : Set (NNReal × Ω)) =
        ({0} ×ˢ univ) := by
      ext p
      simp [PredictableIntervalAlgebra.Interval.timeZeroSlice]
    rw [hSlice, Measure.add_apply, Q.predictableEnergyMeasure_timeZeroSlice,
      Q'.predictableEnergyMeasure_timeZeroSlice, zero_add]
  have hvZero : v (PredictableIntervalAlgebra.Interval.timeZeroSlice : Set (NNReal × Ω)) = 0 := by
    rw [Measure.add_apply, canonicalVariationMeasure_timeZeroSlice E,
      canonicalVariationMeasure_timeZeroSlice E', zero_add]
  have hqMem : MemLp K.coefficient 2 q :=
    MemLp.of_bound K.coefficient_isStronglyMeasurable.aestronglyMeasurable b
      (Eventually.of_forall hBound)
  have hvMem : MemLp K.coefficient 1 v :=
    MemLp.of_bound K.coefficient_isStronglyMeasurable.aestronglyMeasurable b
      (Eventually.of_forall hBound)
  let ε : Nat → ENNReal := fun n => ((n + 1 : Nat) : ENNReal)⁻¹
  have hε n : ε n ≠ 0 := ENNReal.inv_ne_zero.mpr (by finiteness)
  have hεLim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Nat.cast_add, Nat.cast_one, Function.comp_def] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hRows n :=
    PredictableIntervalAlgebra.exists_elementary_eLpNorm_sub_lt_two_with_coefficientBound
    q v hqZero hvZero 2 1 (by norm_num) (by norm_num) K.coefficient
    K.coefficient_isStronglyMeasurable hqMem hvMem (hε n)
  choose J hJq hJv C hC using hRows
  have hqLim : Tendsto (fun n => eLpNorm
      (K.coefficient - Function.uncurry (J n).integrand) 2 q) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεLim
      (fun _ => zero_le) (fun n => (hJq n).le)
  have hvLim : Tendsto (fun n => eLpNorm
      (K.coefficient - Function.uncurry (J n).integrand) 1 v) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεLim
      (fun _ => zero_le) (fun n => (hJv n).le)
  refine ⟨J, C, hC, ?_, ?_⟩
  · apply finiteHorizonElementaryGain_emery_of_controls hUsual Q hM hMT J C hC K
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvLim
        (fun _ => zero_le) (fun _ => eLpNorm_le_add_measure_right _ _ _)
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hqLim
        (fun _ => zero_le) (fun _ => eLpNorm_le_add_measure_right _ _ _)
  · apply finiteHorizonElementaryGain_emery_of_controls hUsual' Q' hM' hMT' J C hC K'
    · rw [← hCoeff]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvLim
        (fun _ => zero_le) (fun _ => eLpNorm_le_add_measure_left _ _ _)
    · rw [← hCoeff]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hqLim
        (fun _ => zero_le) (fun _ => eLpNorm_le_add_measure_left _ _ _)

end FTAPTheorem42.SIntegrableFiniteVariationBridge
