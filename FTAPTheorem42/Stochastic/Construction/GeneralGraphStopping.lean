/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Local.Construction.IntegralGraphAlgebra
import FTAPTheorem42.Stochastic.Integral.General.BoundedPredictableIntegralGraph
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AStopping
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessAlgebra
import FTAPTheorem42.Stochastic.Construction.DirectSchedule
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessLocalization

/-! # Stopping the original price's general integral graph

Restriction of actual coefficients gives the stopping law on a common schedule.
Bounded rows use direct schedules, and the law passes to their elementary-test limits.
-/

/-! ## Stopping on a common completed schedule -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42

/-- Magnitude cuts commute with restriction to an arbitrary set. -/
theorem integralCoefficientTruncation_restrict {Ω : Type*}
    (B : Set (NNReal × Ω)) (H : Process Ω) (n : Nat) :
    integralCoefficientTruncation (PredictableProcess.restrict B H) n =
      PredictableProcess.restrict B (integralCoefficientTruncation H n) := by
  funext t ω
  by_cases hp : (t, ω) ∈ B
  · simp only [integralCoefficientTruncation, PredictableProcess.restrict_apply_of_mem hp]
  · simp only [integralCoefficientTruncation, PredictableProcess.restrict_apply_of_notMem hp,
      ite_self]

end FTAPTheorem42

namespace FTAPTheorem42.LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ}
  {G : LocallySIntegrableStrategy D}

omit [SigmaFiniteFiltration μ F] in
/-- Difference of two actual integral graphs preserves their coefficients
and stored gains. -/
theorem IsIntegralGraph.sub {H K X Y : Process Ω}
    (hH : IsIntegralGraph G H X) (hK : IsIntegralGraph G K Y) :
    IsIntegralGraph G (H - K) (X - Y) := by
  change IsIntegralGraph G (fun t ω => H t ω - K t ω) (fun t ω => X t ω - Y t ω)
  simpa only [neg_one_smul, Pi.neg_apply, sub_eq_add_neg] using hH.add (hK.smul (-1))

/-- A common coordinate representation supplies stopping without an input
raw stopping calculus, including for unbounded coefficients. -/
theorem CommonScheduleIntegralGraphData.stopped_isIntegralGraph
    {H X : Process Ω} (data : CommonScheduleIntegralGraphData G H X)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ) :
    IsIntegralGraph G (PredictableProcess.restrict (stochasticIntervalIocZeroTop τ) H)
      (stoppedProcess X τ) := by
  let B := stochasticIntervalIocZeroTop τ
  have hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hτ
  let K n := (data.coefficient n).restrictPredictable B hB
  have hK n : (K n).coefficient = Function.uncurry (PredictableProcess.restrict B H) := by
    change B.indicator (data.coefficient n).coefficient = _
    rw [data.coefficient_eq n]
    rfl
  obtain ⟨R, hR, hGain, _hM, _hA⟩ :=
    exists_actualLocal_of_commonSchedule data.schedule K hK
  refine ⟨⟨R, hR, ?_⟩⟩
  apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence
    data.schedule.isLocalizingSequence
  intro n
  have hStop := finiteHorizonCompletedM2AGain_restrict_stochasticIntervalTop
    data.schedule.usualConditions (data.schedule.quadraticKernel n)
    (data.schedule.variationBridge n) (data.schedule.martingale n)
    (data.schedule.terminal_memLp n) (data.coefficient n) τ hτ
  have h := (hGain n).trans (hStop.trans ((data.stoppedGain_eq n).symm.stoppedProcess τ))
  convert h using 1
  rw [stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']
  congr 1
  funext ω
  exact min_comm _ _

end FTAPTheorem42.LocalCompletedM2A

/-! ## Stopping the original-price graph -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open LocalCompletedM2A

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Common schedules for bounded coefficients give the stored stopped gain
without a raw stopping calculus. -/
theorem bounded_integralGraph_stopped
    (source : BoundedSemimartingaleSource S F μ)
    {H X : Process Ω} (h : IsIntegralGraph (unitSource source) H X)
    (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ) :
    IsIntegralGraph (unitSource source)
      (PredictableProcess.restrict (stochasticIntervalIocZeroTop τ) H)
      (stoppedProcess X τ) := by
  obtain ⟨data⟩ := exists_commonSchedule_of_bounded source h b hBound
  exact data.stopped_isIntegralGraph τ hτ

/-- Finite random stopping preserves the general graph and the original
coefficient restricted to the predictable interval `(0,τ]`. -/
theorem truncated_integralGraph_finiteStopped
    (source : BoundedSemimartingaleSource S F μ)
    {H X : Process Ω} (h : IsTruncatedIntegralGraph (unitSource source) H X)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal))) :
    IsTruncatedIntegralGraph (unitSource source)
      (PredictableProcess.restrict (stochasticIntervalIocZeroTop
        (fun ω => (τ ω : WithTop NNReal))) H)
      (stoppedProcess X (fun ω => (τ ω : WithTop NNReal))) := by
  classical
  obtain ⟨A⟩ := h
  let τTop := fun ω => (τ ω : WithTop NNReal)
  let B := stochasticIntervalIocZeroTop τTop
  have hB := IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hτ
  have hCut n := (integralCoefficientTruncation_restrict B H n).symm
  have hRows n : IsIntegralGraph (unitSource source)
      (integralCoefficientTruncation (PredictableProcess.restrict B H) n)
      (stoppedProcess (A.approximant n).val.stochasticIntegral τTop) := by
    rw [← hCut n]
    exact bounded_integralGraph_stopped source
      ⟨⟨A.approximant n, A.approximant_integrand n, .refl μ _⟩⟩
      ((n : Real) + 1) (integralCoefficientTruncation_abs_le H n) τTop hτ
  have hConv := A.convergence.finiteStopped
    (fun n => StronglyAdapted.isStronglyProgressive_of_rightContinuous
      (A.approximant n).val.stochasticIntegral_isStronglyAdapted
      (A.approximant n).val.stochasticIntegral_isRightContinuous)
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      A.regularGain_adapted A.regularGain_right)
    (fun n => (A.approximant n).val.stochasticIntegral_isRightContinuous)
    A.regularGain_right τ hτ
  refine ⟨{
    integrand_predictable := PredictableProcess.isStronglyPredictable_restrict hB
      A.integrand_predictable
    approximant := fun n => (hRows n).representative
    approximant_integrand := fun n => (hRows n).representative_integrand
    regularGain := stoppedProcess A.regularGain τTop
    regularGain_adapted :=
      RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        A.regularGain_adapted hτ A.regularGain_right
    regularGain_right := RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
      A.regularGain_right
    regularGain_left := A.regularGain_left.stoppedProcess τTop
    regularGain_zero := ?_
    gain_indistinguishable := A.gain_indistinguishable.stoppedProcess τTop
    convergence := hConv.congr_sequence (fun n => (hRows n).representative_gain.symm) }⟩
  filter_upwards [A.regularGain_zero] with ω hω
  change A.regularGain (min 0 (τ ω)) ω = 0
  have hz : (0 : NNReal) ≤ τ ω := zero_le
  rw [min_eq_left hz]
  exact hω

/-- Restriction to a finite stopping interval has the difference of the
endpoint stops as its gain. The two coefficient cuts use the same rows. -/
theorem truncated_integralGraph_finiteInterval
    (source : BoundedSemimartingaleSource S F μ)
    {H X : Process Ω} (h : IsTruncatedIntegralGraph (unitSource source) H X)
    (σ τ : Ω → NNReal)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop NNReal)))
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (hle : ∀ ω, σ ω ≤ τ ω) :
    IsTruncatedIntegralGraph (unitSource source)
      (PredictableProcess.restrict
        (stochasticIntervalIocZeroTop (fun ω => (τ ω : WithTop NNReal)) \
          stochasticIntervalIocZeroTop (fun ω => (σ ω : WithTop NNReal))) H)
      (stoppedProcess X (fun ω => (τ ω : WithTop NNReal)) -
        stoppedProcess X (fun ω => (σ ω : WithTop NNReal))) := by
  classical
  obtain ⟨A⟩ := h
  let σTop := fun ω => (σ ω : WithTop NNReal)
  let τTop := fun ω => (τ ω : WithTop NNReal)
  let Bσ := stochasticIntervalIocZeroTop σTop
  let Bτ := stochasticIntervalIocZeroTop τTop
  let B := Bτ \ Bσ
  have hBσ := IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hσ
  have hBτ := IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hτ
  have hSub : Bσ ⊆ Bτ := by
    intro p hp
    obtain ⟨ht, hs⟩ := (mem_stochasticIntervalIocZeroTop_iff _ _ _).mp hp
    exact (mem_stochasticIntervalIocZeroTop_iff _ _ _).mpr
      ⟨ht, hs.trans (WithTop.coe_le_coe.mpr (hle p.2))⟩
  have hCut n : integralCoefficientTruncation (PredictableProcess.restrict B H) n =
      PredictableProcess.restrict Bτ (integralCoefficientTruncation H n) -
        PredictableProcess.restrict Bσ (integralCoefficientTruncation H n) := by
    funext t ω
    by_cases hs : (t, ω) ∈ Bσ
    · have ht := hSub hs
      have hb : (t, ω) ∉ B := fun h => h.2 hs
      simp only [integralCoefficientTruncation, Pi.sub_apply,
        PredictableProcess.restrict_apply_of_notMem hb,
        PredictableProcess.restrict_apply_of_mem hs,
        PredictableProcess.restrict_apply_of_mem ht, ite_self, sub_self]
    · by_cases ht : (t, ω) ∈ Bτ
      · have hb : (t, ω) ∈ B := ⟨ht, hs⟩
        simp only [integralCoefficientTruncation, Pi.sub_apply,
          PredictableProcess.restrict_apply_of_mem hb,
          PredictableProcess.restrict_apply_of_mem ht,
          PredictableProcess.restrict_apply_of_notMem hs, sub_zero]
      · have hb : (t, ω) ∉ B := fun h => ht h.1
        simp only [integralCoefficientTruncation, Pi.sub_apply,
          PredictableProcess.restrict_apply_of_notMem hb,
          PredictableProcess.restrict_apply_of_notMem ht,
          PredictableProcess.restrict_apply_of_notMem hs, ite_self, sub_self]
  have hRows n : IsIntegralGraph (unitSource source)
      (integralCoefficientTruncation (PredictableProcess.restrict B H) n)
      (stoppedProcess (A.approximant n).val.stochasticIntegral τTop -
        stoppedProcess (A.approximant n).val.stochasticIntegral σTop) := by
    have hRow : IsIntegralGraph (unitSource source) (integralCoefficientTruncation H n)
        (A.approximant n).val.stochasticIntegral :=
      ⟨⟨A.approximant n, A.approximant_integrand n, .refl μ _⟩⟩
    rw [hCut]
    exact (bounded_integralGraph_stopped source hRow ((n : Real) + 1)
      (integralCoefficientTruncation_abs_le H n) τTop hτ).sub
      (bounded_integralGraph_stopped source hRow ((n : Real) + 1)
        (integralCoefficientTruncation_abs_le H n) σTop hσ)
  have hProg n := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    (A.approximant n).val.stochasticIntegral_isStronglyAdapted
    (A.approximant n).val.stochasticIntegral_isRightContinuous
  have hY := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    A.regularGain_adapted A.regularGain_right
  have hConvτ := A.convergence.finiteStopped hProg hY
    (fun n => (A.approximant n).val.stochasticIntegral_isRightContinuous) A.regularGain_right τ hτ
  have hConvσ := A.convergence.finiteStopped hProg hY
    (fun n => (A.approximant n).val.stochasticIntegral_isRightContinuous) A.regularGain_right σ hσ
  have hConv := hConvτ.sub (fun n => (hProg n).stoppedProcess hτ)
    (fun n => (hProg n).stoppedProcess hσ) (hY.stoppedProcess hτ) (hY.stoppedProcess hσ) hConvσ
  refine ⟨{
    integrand_predictable := PredictableProcess.isStronglyPredictable_restrict
      (hBτ.diff hBσ) A.integrand_predictable
    approximant := fun n => (hRows n).representative
    approximant_integrand := fun n => (hRows n).representative_integrand
    regularGain := stoppedProcess A.regularGain τTop - stoppedProcess A.regularGain σTop
    regularGain_adapted :=
      (RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        A.regularGain_adapted hτ A.regularGain_right).sub
      (RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        A.regularGain_adapted hσ A.regularGain_right)
    regularGain_right := fun ω t =>
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
        _ A.regularGain_right ω t).sub
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _ A.regularGain_right ω t)
    regularGain_left := (A.regularGain_left.stoppedProcess τTop).sub
      (A.regularGain_left.stoppedProcess σTop)
    regularGain_zero := ?_
    gain_indistinguishable := (A.gain_indistinguishable.stoppedProcess τTop).sub
      (A.gain_indistinguishable.stoppedProcess σTop)
    convergence := hConv.congr_sequence (fun n => (hRows n).representative_gain.symm) }⟩
  exact Eventually.of_forall fun ω => by
    change A.regularGain (min 0 (τ ω)) ω - A.regularGain (min 0 (σ ω)) ω = 0
    have h0τ : (0 : NNReal) ≤ τ ω := zero_le
    have h0σ : (0 : NNReal) ≤ σ ω := zero_le
    rw [min_eq_left h0τ, min_eq_left h0σ, sub_self]

end FTAPTheorem42.BoundedSourceIntegralMarket
