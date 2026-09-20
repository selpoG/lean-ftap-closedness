/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.General.CommonScheduleElementaryApproximation
import FTAPTheorem42.Stochastic.Construction.GeneralGraphPasting
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessApproximationRealization

/-! # Elementary approximation of general integral gains

The original bounded price supplies the completed control measures. Their
elementary density passes through localization and bounded coefficient cuts.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Every bounded coefficient certificate can be approximated by original
price elementary gains, uniformly over unit elementary tests. -/
theorem bounded_integralGraph_elementaryApproximable
    (source : BoundedSemimartingaleSource S F μ)
    {H X : Process Ω} (h : IsIntegralGraph (unitSource source) H X)
    (hX : IsStronglyProgressive F X) (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b) :
    ElementaryEmeryApproximable (F := F) (μ := μ) S X := by
  obtain ⟨data⟩ := exists_commonSchedule_of_bounded source h b hBound
  have hApprox := data.elementaryApproximable hX b hBound
  intro T ε hε
  obtain ⟨J, C, hC, hJ⟩ := hApprox T ε hε
  refine ⟨J, C, hC, ?_⟩
  have hCenter : ElementaryStrategy.gain (unitSource source).stochasticIntegral J.toElementary =
      ElementaryStrategy.gain S J.toElementary := by
    change ElementaryStrategy.gain (fun t ω => S t ω - S 0 ω) _ = _
    exact ElementaryStrategy.gain_sub_initial S _
  simpa only [hCenter] using hJ

/-- The regular gain stored in every general graph is in the original
price's elementary-test closure. This includes unbounded coefficients. -/
theorem truncatedGraphWitness_elementaryApproximable
    (source : BoundedSemimartingaleSource S F μ)
    {H X : Process Ω} (A : TruncatedIntegralGraphWitness (unitSource source) H X) :
    ElementaryEmeryApproximable (F := F) (μ := μ) S A.regularGain := by
  have hProg n := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    (A.approximant n).val.stochasticIntegral_isStronglyAdapted
    (A.approximant n).val.stochasticIntegral_isRightContinuous
  apply ElementaryEmeryApproximable.of_converges
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      source.stronglyAdapted source.rightContinuous) source.rightContinuous hProg
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      A.regularGain_adapted A.regularGain_right) _ A.convergence
  intro n
  exact bounded_integralGraph_elementaryApproximable source
    ⟨⟨A.approximant n, A.approximant_integrand n, .refl μ _⟩⟩ (hProg n)
    ((n : Real) + 1) (integralCoefficientTruncation_abs_le H n)

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Identifying general integral gains with the realized completion

Both directions use the same original bounded price. General graph gains
enter the elementary completion through their control approximations;
realized completion gains return through Mémín and stopping-interval pasting.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Every general integral gain has an indistinguishable representative in
the original price's realized elementary completion. -/
theorem truncated_integralGraph_exists_realizedStrategy
    (source : BoundedSemimartingaleSource S F μ)
    {H X : Process Ω} (h : IsTruncatedIntegralGraph (unitSource source) H X) :
    ∃ R : RealizedStrategy (ℱ := F) μ S, ProcessIndistinguishable μ R.gain X := by
  obtain ⟨A⟩ := h
  have hApprox := truncatedGraphWitness_elementaryApproximable source A
  obtain ⟨R, hR⟩ := hApprox.exists_realizedStrategy
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      source.stronglyAdapted source.rightContinuous) source.rightContinuous
    A.regularGain_adapted A.regularGain_right A.regularGain_left A.regularGain_zero
  exact ⟨R, hR.symm ▸ A.gain_indistinguishable⟩

/-- Equality of the whole-time gain domains, modulo indistinguishability.
This preserves the original price, but does not assert terminal convergence
or replace the remaining terminal-market assembly. -/
theorem exists_truncatedIntegralGraph_iff_exists_realizedStrategy
    (source : BoundedSemimartingaleSource S F μ) (X : Process Ω) :
    (∃ H : Process Ω, IsTruncatedIntegralGraph (unitSource source) H X) ↔
      ∃ R : RealizedStrategy (ℱ := F) μ S, ProcessIndistinguishable μ R.gain X := by
  constructor
  · rintro ⟨H, hH⟩
    exact truncated_integralGraph_exists_realizedStrategy source hH
  · rintro ⟨R, hR⟩
    obtain ⟨H, ⟨A⟩⟩ := exists_realized_truncatedGraph source R
    exact ⟨H, ⟨{ A with gain_indistinguishable := A.gain_indistinguishable.trans hR }⟩⟩

end FTAPTheorem42.BoundedSourceIntegralMarket
