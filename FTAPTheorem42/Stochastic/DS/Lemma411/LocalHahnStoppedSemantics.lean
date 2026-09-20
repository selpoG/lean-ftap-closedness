/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.UnitActualMartingaleTestBound
import FTAPTheorem42.Stochastic.DS.Lemma47.ActualHahnRestriction
import FTAPTheorem42.Stochastic.DS.Lemma411.FiniteHahnImprovement
import FTAPTheorem42.Stochastic.Topology.J1.Basic

/-! # Intrinsic Hahn restrictions with uniform martingale control -/

namespace FTAPTheorem42.LocalCompletedM2A

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  [F.IsRightContinuous] {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {G : LocallySIntegrableStrategy D}

/-- The existing càdlàg actual Hahn gain retains its positive variation
increments and inherits a uniform martingale test bound from its local
source. There is no L² assumption on the unstopped source. -/
theorem actualHahnPositiveRestrictionCadlag_component_bounds
    (hGL : ProcessHasLeftLimits G.martingalePart) (T : NNReal) (b : Real)
    (hBound : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError G.martingalePart 0 J T ω ∂μ) ≤ b)
    (L : ActualSIntegrableStrategy (realizationModel G))
    (hL : ∀ t ω, |L.val.integrand t ω| ≤ 1)
    (P : PredictablePathwiseHahnSeparator L.val) :
    let R := actualHahnPositiveRestrictionCadlag hGL P
    (∀ᵐ ω ∂μ, ∀ a c : NNReal, a ≤ c →
      0 ≤ R.val.finiteVariationPart c ω - R.val.finiteVariationPart a ω ∧
      L.val.finiteVariationPart c ω - L.val.finiteVariationPart a ω ≤
        R.val.finiteVariationPart c ω - R.val.finiteVariationPart a ω) ∧
    (∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError R.val.martingalePart 0 J T ω ∂μ) ≤ b) ∧
    (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      R.val.martingalePart T ω ∂μ) ≤ b := by
  let R := actualHahnPositiveRestrictionCadlag hGL P
  have hR : ∀ t ω, |R.val.integrand t ω| ≤ 1 := by
    intro t ω
    change |PredictableProcess.restrict P.positiveSet L.val.integrand t ω| ≤ 1
    by_cases hp : (t, ω) ∈ P.positiveSet
    · rw [PredictableProcess.restrict_apply_of_mem hp]
      exact hL t ω
    · rw [PredictableProcess.restrict_apply_of_notMem hp, abs_zero]
      exact zero_le_one
  exact ⟨actualHahnPositiveRestrictionCadlag_finiteVariation_increment_ae hGL P,
    actual_unitIntegrand_martingale_testError_bound T b hBound R hR,
    actual_unitIntegrand_martingale_envelope_bound T b hBound R hR
      (actualRestrictPredictableCadlag_martingalePart_zero
        hGL L P.positiveSet P.measurableSet_positiveSet)⟩

/-- Stop a local actual gain at a positive deterministic horizon and
construct its positive Hahn restriction in the same intrinsic graph. -/
noncomputable def actualHahnOfDeterministicStop
    (hGL : ProcessHasLeftLimits G.martingalePart)
    (L : ActualLocallySIntegrableStrategy (realizationModel G))
    (T : NNReal) (hT : 0 < T) : ActualSIntegrableStrategy (realizationModel G) :=
  actualHahnPositiveRestrictionCadlag hGL
    (SIntegrableFiniteVariationBridge.ofCumulativeVariationNormalized
      (L.deterministicallyStopped T hT).val.finiteVariationPart_isRightContinuous
      ).toPredictablePathwiseHahnSeparator

/-- The finite stop supplies global variation and the bridge supplies its
Hahn separator. The source test bound controls that same actual gain. -/
theorem actualHahnOfDeterministicStop_component_bounds
    (hGL : ProcessHasLeftLimits G.martingalePart)
    (L : ActualLocallySIntegrableStrategy (realizationModel G))
    (hL : ∀ t ω, |L.val.integrand t ω| ≤ 1)
    (T : NNReal) (hT : 0 < T) (b : Real)
    (hBound : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError G.martingalePart 0 J T ω ∂μ) ≤ b) :
    let R := actualHahnOfDeterministicStop hGL L T hT
    (∀ᵐ ω ∂μ, ∀ a c : NNReal, a ≤ c →
      0 ≤ R.val.finiteVariationPart c ω - R.val.finiteVariationPart a ω ∧
      L.val.finiteVariationPart (min c T) ω - L.val.finiteVariationPart (min a T) ω ≤
        R.val.finiteVariationPart c ω - R.val.finiteVariationPart a ω) ∧
    (∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError R.val.martingalePart 0 J T ω ∂μ) ≤ b) ∧
    (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      R.val.martingalePart T ω ∂μ) ≤ b := by
  let A := L.deterministicallyStopped T hT
  have hA : ∀ t ω, |A.val.integrand t ω| ≤ 1 := by
    intro t ω
    change |PredictableProcess.restrict
      (stochasticIntervalIocZero (fun _ : Ω => T)) L.val.integrand t ω| ≤ 1
    by_cases hp : (t, ω) ∈ stochasticIntervalIocZero (fun _ : Ω => T)
    · rw [PredictableProcess.restrict_apply_of_mem hp]
      exact hL t ω
    · rw [PredictableProcess.restrict_apply_of_notMem hp, abs_zero]
      exact zero_le_one
  exact actualHahnPositiveRestrictionCadlag_component_bounds hGL T b hBound A hA
    (SIntegrableFiniteVariationBridge.ofCumulativeVariationNormalized
      A.val.finiteVariationPart_isRightContinuous).toPredictablePathwiseHahnSeparator

/-! ## Jumps and initial values of the finite-horizon intrinsic Hahn gain -/

/-- The deterministic stop and the actual Hahn restriction keep a regular
zero-initial gain and martingale component. Before and at the horizon, each
jump is either the original gain's jump or zero. -/
theorem actualHahnOfDeterministicStop_semantics
    (hGL : ProcessHasLeftLimits G.martingalePart)
    (L : ActualLocallySIntegrableStrategy (realizationModel G))
    (hLL : ProcessHasLeftLimits L.val.stochasticIntegral)
    (T : NNReal) (hT : 0 < T) :
    let V := actualHahnOfDeterministicStop hGL L T hT
    ProcessHasLeftLimits V.val.stochasticIntegral ∧
    V.val.stochasticIntegral 0 =ᵐ[μ] 0 ∧
    V.val.martingalePart 0 =ᵐ[μ] 0 ∧
    (∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      processLeftJump V.val.stochasticIntegral t ω =
        processLeftJump L.val.stochasticIntegral t ω ∨
      processLeftJump V.val.stochasticIntegral t ω = 0) := by
  let A := L.deterministicallyStopped T hT
  let P := (SIntegrableFiniteVariationBridge.ofCumulativeVariationNormalized
    A.val.finiteVariationPart_isRightContinuous).toPredictablePathwiseHahnSeparator
  have hAL : ProcessHasLeftLimits A.val.stochasticIntegral := hLL.deterministicallyStopped T
  refine ⟨actualHahnPositiveRestrictionCadlag_stochasticIntegral_hasLeftLimits hGL P,
    actualHahnPositiveRestrictionCadlag_stochasticIntegral_zero hGL P,
    actualRestrictPredictableCadlag_martingalePart_zero
      hGL A P.positiveSet P.measurableSet_positiveSet, ?_⟩
  filter_upwards [actualRestrictPredictableCadlag_stochasticIntegral_leftJump
    hGL A hAL P.positiveSet P.measurableSet_positiveSet] with ω hω
  intro t ht
  change processLeftJump (actualRestrictPredictableCadlag hGL A
    P.positiveSet P.measurableSet_positiveSet).val.stochasticIntegral t ω = _ ∨ _
  rw [hω t]
  unfold predictableRestrictedLeftJump
  by_cases hp : (t, ω) ∈ P.positiveSet
  · rw [ite_eq_left hp]
    left
    have heq : A.val.stochasticIntegral =
        stoppedProcess L.val.stochasticIntegral (fun _ => (T : WithTop NNReal)) := by
      funext s x
      simp only [A, ActualLocallySIntegrableStrategy.deterministicallyStopped,
        LocallySIntegrableStrategy.deterministicallyStopped, stoppedProcess,
        ← WithTop.coe_min, WithTop.untopD_coe]
    rw [heq]
    exact processLeftJump_stoppedProcess_eq_of_le _ hLL _ t ω
      (WithTop.coe_le_coe.mpr ht)
  · right
    change processLeftJump (actualRestrictPredictableCadlag hGL A
      P.positiveSet P.measurableSet_positiveSet).val.stochasticIntegral t ω = 0
    rw [hω t, predictableRestrictedLeftJump, ite_eq_right hp]

end FTAPTheorem42.LocalCompletedM2A

namespace FTAPTheorem42.LocalCompletedM2A

/-! ## Admissibility of the directly constructed finite Hahn improvement -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S X Y : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  [F.IsRightContinuous] {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {G : LocallySIntegrableStrategy D}

/-- The actual Hahn construction supplies both the variation comparison
and the jump identity needed for closed-stop admissibility. The two inputs
need not live in the auxiliary source's strategy carrier. -/
theorem actualHahnBestOf_finiteStopped_lower_bound
    (hGL : ProcessHasLeftLimits G.martingalePart)
    (L : ActualLocallySIntegrableStrategy (realizationModel G))
    (DX : J1Decomposition X F μ) (DY : J1Decomposition Y F μ)
    (hXL : ProcessHasLeftLimits X) (hYL : ProcessHasLeftLimits Y)
    (hGain : L.val.stochasticIntegral = X - Y)
    (hA : L.val.finiteVariationPart = DX.A - DY.A)
    (hXLower : ∀ᵐ ω ∂μ, ∀ t, (-1 : Real) ≤ X t ω)
    (hYLower : ∀ᵐ ω ∂μ, ∀ t, (-1 : Real) ≤ Y t ω)
    (T : NNReal) (hT : 0 < T) {δ : Real} (hδ : 0 ≤ δ) :
    let V := actualHahnOfDeterministicStop hGL L T hT
    let τ := finiteHahnDownsideTime V.val.martingalePart (DX.N - DY.N) δ T
    ∀ᵐ ω ∂μ, ∀ t, -(1 + δ) ≤
      (Y + V.val.stochasticIntegral) (min t (τ ω)) ω := by
  let A := L.deterministicallyStopped T hT
  let P := (SIntegrableFiniteVariationBridge.ofCumulativeVariationNormalized
    A.val.finiteVariationPart_isRightContinuous).toPredictablePathwiseHahnSeparator
  let V := actualHahnOfDeterministicStop hGL L T hT
  have hLL : ProcessHasLeftLimits L.val.stochasticIntegral := by
    rw [hGain]
    exact hXL.sub hYL
  obtain ⟨hVL, hV0, hN0, hJump⟩ := actualHahnOfDeterministicStop_semantics hGL L hLL T hT
  have hInc := actualHahnPositiveRestrictionCadlag_finiteVariation_increment_ae hGL P
  filter_upwards [hXLower, hYLower, DX.decomposition, DY.decomposition,
    V.val.integral_decomposition, hV0, hN0, hJump, hInc] with
    ω hxLower hyLower hx hy hv hv0 hn0 hj hi
  have hy0 : Y 0 ω = 0 := by
    simp only [hy 0, DY.zeroN, DY.zeroA, Pi.zero_apply, add_zero]
  have hc0 : V.val.finiteVariationPart 0 ω = 0 := by
    have := hv 0
    change V.val.stochasticIntegral 0 ω = 0 at hv0
    change V.val.martingalePart 0 ω = 0 at hn0
    linarith
  apply finiteHahnBestOf_lower_bound T hδ hXL hYL hVL ω hxLower hyLower hy0 hv0 hx hy hv
  · intro t ht
    have h := hi 0 t bot_le
    change 0 ≤ V.val.finiteVariationPart t ω - V.val.finiteVariationPart 0 ω ∧
      L.val.finiteVariationPart (min t T) ω - L.val.finiteVariationPart (min 0 T) ω ≤
        V.val.finiteVariationPart t ω - V.val.finiteVariationPart 0 ω at h
    simpa only [hA, Pi.sub_apply, min_eq_left ht, min_eq_left (show (0 : NNReal) ≤ T from zero_le),
      DX.zeroA, DY.zeroA, Pi.zero_apply, sub_zero, sub_self, hc0] using h
  · simpa only [hGain] using hj

end FTAPTheorem42.LocalCompletedM2A
