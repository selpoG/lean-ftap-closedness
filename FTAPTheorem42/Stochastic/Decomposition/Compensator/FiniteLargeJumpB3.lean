/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.Process
import FTAPTheorem42.Stochastic.Stopping.CadlagPassageLocalizer
import FTAPTheorem42.Stochastic.Decomposition.Compensator.VariationLevelLocalization
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ValueTruncationFiniteVariation
import FTAPTheorem42.Stochastic.Topology.Prelocal.BoundaryConsumer

/-!
# B3: integrable variation localization of the finite large-jump process

The finite large-jump process has finite pathwise variation on every finite
horizon, but this variation is not assumed integrable.  This module uses one
canonical family of strict-prefix variation-level stopping times.  At each
level the strict-prefix path has deterministic variation bound, hence an
`L¹` cumulative variation, and is sent to the value-truncation predictable
finite-variation consumer.

The certificates at different levels are deliberately independent.  The
package records exact source/strict-prefix identities and only identifies two
levels on their common *open* prefix.  In particular, it makes no closed-stop
or projection-compatibility claim.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open FTAPTheorem42.SIntegrableFiniteVariationBridge

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! The deterministic horizons are cofinal in time.  The original finite
large-jump process is already constant after its input horizon `T`, so these
larger horizons do not change the source while making the stopping family
genuinely exhaustive. -/

def finiteLargeJumpVariationHorizon (T : NNReal) (n : ℕ) : NNReal :=
  T + cadlagPassageHorizon n

theorem finiteLargeJumpVariationHorizon_mono (T : NNReal) :
    Monotone (finiteLargeJumpVariationHorizon T) := by
  intro m n hmn
  dsimp [finiteLargeJumpVariationHorizon]
  exact add_le_add_right (cadlagPassageHorizon_monotone hmn) T

theorem finiteLargeJumpVariationHorizon_tendsto_atTop (T : NNReal) :
    Tendsto (finiteLargeJumpVariationHorizon T) atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_)
    (cadlagPassageHorizon_tendsto_atTop)
  dsimp [finiteLargeJumpVariationHorizon]
  exact le_add_of_nonneg_left (by positivity)

/-! ## One strict-prefix `L¹` slice -/

structure VariationLevelFiniteVariationProjectionSlice
    (A : Process Ω) (T : NNReal) (n : ℕ) where
  rho : Ω → NNReal
  rho_eq_variationLevelStop :
    rho = variationLevelStop A (variationLevel n)
      (finiteLargeJumpVariationHorizon T n)
  rho_isStoppingTime : IsStoppingTime F
    (fun omega => (rho omega : WithTop NNReal))
  rho_le_horizon : ∀ omega,
    rho omega ≤ finiteLargeJumpVariationHorizon T n
  localized : Process Ω
  localized_eq_strictPrefix :
    localized = strictPrefixProcess A rho
  localized_eq_of_lt : ∀ {t : NNReal} {omega : Ω},
    t < rho omega → localized t omega = A t omega
  source_data : NormalizedAdaptedCadlagFiniteVariationL1Data
    (F := F) (mu := mu) localized
      (finiteLargeJumpVariationHorizon T n)
  projection : ValueTruncationFiniteVariationPredictableLimit
    (F := F) (mu := mu) localized
      (finiteLargeJumpVariationHorizon T n)

omit [SigmaFiniteFiltration mu F] in
theorem variationLevelFiniteVariationProjection_data_eventually_eq_horizon
    {A : Process Ω} {T : NNReal}
    (data : ∀ n : ℕ,
      VariationLevelFiniteVariationProjectionSlice
        (F := F) (mu := mu) A T n)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ)
    (hAConstant : ∀ omega t, T ≤ t →
      A t omega = A T omega)
    (omega : Ω) :
    ∀ᶠ n : ℕ in atTop,
      (data n).rho omega = finiteLargeJumpVariationHorizon T n := by
  have hLevel : ∀ᶠ n : ℕ in atTop,
      localVariation A
          (finiteLargeJumpVariationHorizon T n) omega ≤
        (variationLevel n : Real) := by
    have hNat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : Real))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hLevelT := hNat.eventually_ge_atTop
      (localVariation A T omega)
    filter_upwards [hLevelT] with n hn
    rw [commonStopCumulativeVariation_constant_after hAVar hAConstant
      omega (finiteLargeJumpVariationHorizon T n)]
    · exact hn
    · dsimp [finiteLargeJumpVariationHorizon]
      exact le_add_of_nonneg_right (by positivity)
  filter_upwards [hLevel] with n hn
  have hHorizonT : T ≤ finiteLargeJumpVariationHorizon T n := by
    dsimp [finiteLargeJumpVariationHorizon]
    exact le_add_of_nonneg_right (by positivity)
  have hAConstantH : ∀ omega' t,
      finiteLargeJumpVariationHorizon T n ≤ t →
        A t omega' = A (finiteLargeJumpVariationHorizon T n) omega' := by
    intro omega' t ht
    rw [hAConstant omega' t (hHorizonT.trans ht),
      hAConstant omega' (finiteLargeJumpVariationHorizon T n) hHorizonT]
  calc
    (data n).rho omega =
        variationLevelStop A (variationLevel n)
          (finiteLargeJumpVariationHorizon T n) omega := by
      have hEq := congrFun (data n).rho_eq_variationLevelStop omega
      exact hEq
    _ = finiteLargeJumpVariationHorizon T n :=
      variationLevelStop_eq_horizon_of_cumulative_le
        A (variationLevel n) (finiteLargeJumpVariationHorizon T n)
        omega hAVar hAConstantH hn

/-! ## One family, with no hidden level-wise compatibility -/

structure FiniteLargeJumpValueTruncationFamily
    (X : Process Ω) (c : Real) (T : NNReal) where
  data : ∀ n : ℕ,
    VariationLevelFiniteVariationProjectionSlice
      (F := F) (mu := mu)
      (FiniteLargeJumpProcess.process X c T) T n
  isLocalizingSequence : ProbabilityTheory.IsLocalizingSequence F
    (fun n omega => ((data n).rho omega : WithTop NNReal)) mu

namespace FiniteLargeJumpValueTruncationFamily

variable {X : Process Ω} {c : Real} {T : NNReal}

omit [SigmaFiniteFiltration mu F] in
theorem rho_isStoppingTime
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T) (n : ℕ) :
    IsStoppingTime F
      (fun omega => ((family.data n).rho omega : WithTop NNReal)) :=
  (family.data n).rho_isStoppingTime

omit [SigmaFiniteFiltration mu F] in
theorem rho_le_horizon
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T) (n : ℕ) (omega : Ω) :
    (family.data n).rho omega ≤ finiteLargeJumpVariationHorizon T n :=
  (family.data n).rho_le_horizon omega

end FiniteLargeJumpValueTruncationFamily

/-! ## Construction for the stochastic finite large-jump process -/

omit [SigmaFiniteFiltration mu F] in
private theorem measurable_cumulativeVariation_of_regularProcess
    {A : Process Ω} {T : NNReal}
    (hA : StronglyAdapted F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t) :
    Measurable (localVariation A T) :=
  SIntegrableFiniteVariationBridge.measurable_commonStopCumulativeVariation_of_regularProcess
    hA hARight

omit [SigmaFiniteFiltration mu F] in
private theorem exists_variationLevelFiniteVariationProjectionSlice
    [F.IsRightContinuous]
    {A : Process Ω} {T : NNReal} (n : ℕ)
    (hA : StronglyAdapted F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t)
    (hALeft : ProcessHasLeftLimits A)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ)
    (hAzero : A 0 = 0)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (VariationLevelFiniteVariationProjectionSlice
      (F := F) (mu := mu) A T n) := by
  obtain ⟨localization⟩ :=
    exists_variationLevelLocalizationData
      (F := F) (mu := mu) A (variationLevel n)
        (finiteLargeJumpVariationHorizon T n)
      hA hARight hALeft hAVar hAzero hUsual
  let localized := localization.localized
  have hLocalizedStrong : StronglyAdapted F localized := by
    simpa only [localized] using localization.localized_data.stronglyAdapted
  have hLocalizedRight : ∀ omega t,
      ContinuousWithinAt (localized · omega) (Ici t) t := by
    simpa only [localized] using localization.localized_data.rightContinuous
  have hLocalizedLeft : ProcessHasLeftLimits localized := by
    simpa only [localized] using localization.localized_data.hasLeftLimits
  have hLocalizedVar : ∀ omega,
      BoundedVariationOn (localized · omega) Set.univ := by
    simpa only [localized] using localization.localized_data.boundedVariation
  have hLocalizedZero : localized 0 = 0 := by
    simpa only [localized] using localization.localized_data.zero
  have hLocalizedConstant : ∀ omega t,
      finiteLargeJumpVariationHorizon T n ≤ t →
        localized t omega =
          localized (finiteLargeJumpVariationHorizon T n) omega := by
    simpa only [localized] using localization.localized_data.constant_after
  have hCumulativeMeasurable :
      Measurable (localVariation localized
        (finiteLargeJumpVariationHorizon T n)) :=
    measurable_cumulativeVariation_of_regularProcess
      hLocalizedStrong hLocalizedRight
  have hCumulativeIntegrable :
      Integrable (localVariation localized
        (finiteLargeJumpVariationHorizon T n)) mu := by
    apply Integrable.of_bound (μ := mu)
      hCumulativeMeasurable.stronglyMeasurable.aestronglyMeasurable
        (variationLevel n : Real)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact localization.localized_data.cumulativeVariation_bound omega
    · rw [commonStopCumulativeVariation_apply]
      exact variationOnFromTo.nonneg_of_le _ _ bot_le
  have hSourceData :
      NormalizedAdaptedCadlagFiniteVariationL1Data
        (F := F) (mu := mu) localized
          (finiteLargeJumpVariationHorizon T n) := {
    stronglyAdapted := hLocalizedStrong
    rightContinuous := hLocalizedRight
    hasLeftLimits := hLocalizedLeft
    boundedVariation := hLocalizedVar
    zero := hLocalizedZero
    constant_after := hLocalizedConstant
    terminalVariation_integrable := hCumulativeIntegrable }
  obtain ⟨projection⟩ :=
    exists_valueTruncationFiniteVariationPredictableLimit
      (F := F) (mu := mu) hSourceData hUsual
  exact ⟨{
    rho := localization.rho
    rho_eq_variationLevelStop := localization.rho_eq_variationLevelStop
    rho_isStoppingTime := localization.rho_isStoppingTime
    rho_le_horizon := localization.rho_le_horizon
    localized := localized
    localized_eq_strictPrefix := by
      simpa only [localized] using localization.localized_eq_strictPrefix
    localized_eq_of_lt := by
      intro t omega ht
      simpa only [localized] using localization.localized_eq_of_lt ht
    source_data := hSourceData
    projection := projection }⟩

omit [SigmaFiniteFiltration mu F] in
theorem exists_finiteLargeJumpValueTruncationFamily
    [F.IsRightContinuous]
    (X : Process Ω) (c : Real) (T : NNReal)
    (hX : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (hc : 0 < c)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T) := by
  let A : Process Ω := FiniteLargeJumpProcess.process X c T
  have hA : StronglyAdapted F A := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.stronglyAdapted_process
      hX hXRight hXLeft hc T
  have hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_rightContinuous hXRight hXLeft hc
  have hALeft : ProcessHasLeftLimits A := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_hasLeftLimits hXRight hXLeft hc
  have hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_boundedVariationOn_univ
      hXRight hXLeft hc
  have hAzero : A 0 = 0 := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_zero hXRight hXLeft hc
  have hAConstant : ∀ omega t, T ≤ t → A t omega = A T omega := by
    intro omega t hTt
    dsimp [A]
    exact FiniteLargeJumpProcess.process_eq_horizon_of_le
      hXRight hXLeft hc hTt
  let data : ∀ n : ℕ,
      VariationLevelFiniteVariationProjectionSlice
        (F := F) (mu := mu) A T n := fun n =>
    Classical.choice (exists_variationLevelFiniteVariationProjectionSlice
      (F := F) (mu := mu) n hA hARight hALeft hAVar hAzero hUsual)
  have hDataMono : ∀ omega m n, m ≤ n →
      (data m).rho omega ≤ (data n).rho omega := by
    intro omega m n hmn
    have hEqm := congrFun (data m).rho_eq_variationLevelStop omega
    have hEqn := congrFun (data n).rho_eq_variationLevelStop omega
    apply WithTop.coe_le_coe.mp
    rw [hEqm, hEqn,
      congrFun (coe_variationLevelStop A (variationLevel m)
        (finiteLargeJumpVariationHorizon T m)) omega,
      congrFun (coe_variationLevelStop A (variationLevel n)
        (finiteLargeJumpVariationHorizon T n)) omega]
    exact min_le_min
      (variationLevelHittingTime_mono A
        (variationLevel_strictMono.monotone hmn) omega)
      (WithTop.coe_le_coe.mpr
        (finiteLargeJumpVariationHorizon_mono T hmn))
  have hDataEventual : ∀ omega, ∀ᶠ n : ℕ in atTop,
      (data n).rho omega = finiteLargeJumpVariationHorizon T n := by
    exact variationLevelFiniteVariationProjection_data_eventually_eq_horizon
      data hAVar hAConstant
  have hDataTop : ∀ᵐ omega ∂mu,
      Tendsto (fun n => ((data n).rho omega : WithTop NNReal))
        atTop (𝓝 ⊤) := by
    filter_upwards [] with omega
    have hHorizonTop : Tendsto
        (fun n =>
          (finiteLargeJumpVariationHorizon T n : WithTop NNReal))
        atTop (𝓝 ⊤) :=
      WithTop.tendsto_coe_atTop.comp
        (finiteLargeJumpVariationHorizon_tendsto_atTop T)
    apply hHorizonTop.congr'
    filter_upwards [hDataEventual omega] with n hn
    exact_mod_cast hn.symm
  have hIsLocalizing : ProbabilityTheory.IsLocalizingSequence F
      (fun n omega => ((data n).rho omega : WithTop NNReal)) mu := by
    refine {
      isStoppingTime := fun n => (data n).rho_isStoppingTime
      mono := ?_
      tendsto_top := hDataTop }
    exact Filter.Eventually.of_forall (fun omega m n hmn =>
      WithTop.coe_le_coe.mpr (hDataMono omega m n hmn))
  refine ⟨{ data := fun n => ?_, isLocalizingSequence := ?_ }⟩
  · simpa only [A] using data n
  · simpa only [A] using hIsLocalizing

end HorizonFactorialGrid

end FTAPTheorem42
