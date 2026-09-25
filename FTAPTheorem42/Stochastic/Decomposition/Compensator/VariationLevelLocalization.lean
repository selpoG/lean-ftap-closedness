/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.JordanFiniteVariation
import FTAPTheorem42.Stochastic.Topology.Emery.CompletedVariationStrictPrefix

/-!
# Variation-level localization for an adapted finite-variation path

The running-supremum prelocal carrier permits an adapted càdlàg finite-
variation component.  This file records the sound finite-horizon slice that
is available from such a path alone: the first strict passage of its
cumulative variation is truncated at a deterministic horizon and the
strict-prefix process is then fed to the square-integrable Jordan consumer.

The strict prefix is essential.  A closed stop can contain the jump at the
passage time and therefore need not have variation bounded by the level.
The process used here keeps the left limit at the passage time, so its
variation is controlled by the variation strictly before that time.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open FTAPTheorem42.SIntegrableFiniteVariationBridge

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The finite variation-level stop -/

noncomputable def variationLevelHittingTime
    (A : Process Ω) (c : NNReal) : Ω → WithTop NNReal :=
  RightContinuousHittingTime.strictHittingAfter
    (localVariation A) (c : Real)

noncomputable def variationLevelStop
    (A : Process Ω) (c T : NNReal) : Ω → NNReal :=
  fun omega =>
    (min (variationLevelHittingTime A c omega) (T : WithTop NNReal)).untopA

omit [MeasurableSpace Ω] in
theorem coe_variationLevelStop
    (A : Process Ω) (c T : NNReal) :
    (fun omega =>
      ((variationLevelStop A c T omega : NNReal) : WithTop NNReal)) =
      (fun omega => min (variationLevelHittingTime A c omega)
        (T : WithTop NNReal)) := by
  funext omega
  let sigma := min (variationLevelHittingTime A c omega)
    (T : WithTop NNReal)
  have hne : sigma ≠ ⊤ := by
    exact ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  change (↑(sigma.untopA) = sigma)
  rw [WithTop.untopA_eq_untop hne]
  exact WithTop.coe_untop _ hne

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem variationLevelStop_isStoppingTime
    (A : Process Ω)
    (hA : StronglyAdapted F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ)
    (hUsual : Filtration.UsualConditions mu F)
    (c T : NNReal) :
    IsStoppingTime F
      (fun omega => (variationLevelStop A c T omega : WithTop NNReal)) := by
  let _ : F.IsRightContinuous := hUsual.rightContinuous
  have hCumulative : StronglyAdapted F (localVariation A) := by
    intro t
    apply Measurable.stronglyMeasurable
    apply @FiniteVariationFactorialApproximation.measurable_variationOnFromTo_of_le
      Ω Real (F t) inferInstance inferInstance inferInstance inferInstance
      (fun s omega => A s omega) t
    · intro s hst
      exact (hA.stronglyMeasurable_le hst).measurable
    · exact hARight
  have hCumulativeRight : ∀ omega t,
      ContinuousWithinAt
        (localVariation A · omega) (Ici t) t := by
    exact commonStopCumulativeVariation_rightContinuous hAVar hARight
  have hHit := RightContinuousHittingTime.strictHittingAfter_isStoppingTime
    hCumulative hCumulativeRight (c : Real)
  rw [coe_variationLevelStop A c T]
  exact hHit.min_const T

omit [MeasurableSpace Ω] in
theorem variationLevelStop_le_horizon
    (A : Process Ω) (c T : NNReal) (omega : Ω) :
    variationLevelStop A c T omega ≤ T := by
  apply WithTop.coe_le_coe.mp
  rw [congrFun (coe_variationLevelStop A c T) omega]
  exact min_le_right _ _

omit [MeasurableSpace Ω] in
private theorem variationLevelStop_before_level
    (A : Process Ω) (c T : NNReal)
    (omega : Ω) {t : NNReal}
    (ht : t < variationLevelStop A c T omega) :
    variationOnFromTo (A · omega) Set.univ 0 t ≤ (c : Real) := by
  have hHit : (t : WithTop NNReal) <
      variationLevelHittingTime A c omega := by
    have ht' : (t : WithTop NNReal) <
        min (variationLevelHittingTime A c omega)
          (T : WithTop NNReal) := by
      rw [← congrFun (coe_variationLevelStop A c T) omega]
      exact WithTop.coe_lt_coe.mpr ht
    exact ht'.trans_le (min_le_left _ _)
  have hNot := MeasureTheory.notMem_of_lt_hittingAfter
    (u := localVariation A) (s := Set.Ioi (c : Real))
    (n := (0 : NNReal)) (ω := omega) (k := t) hHit bot_le
  exact le_of_not_gt hNot

/-! ## The localized Jordan consumer -/

structure VariationLevelLocalizationData
    (A : Process Ω) (c T : NNReal) where
  rho : Ω → NNReal
  /-- The stopping time is the canonical strict-prefix passage at level `c`.

  Keeping this equality in the certificate is important: a later family of
  level localizations must be able to compare its stopping times.  The
  Jordan certificate alone does not determine which representative was
  chosen for `rho`. -/
  rho_eq_variationLevelStop : rho = variationLevelStop A c T
  rho_isStoppingTime : IsStoppingTime F
    (fun omega => (rho omega : WithTop NNReal))
  rho_le_horizon : ∀ omega, rho omega ≤ T
  localized : Process Ω
  localized_eq_strictPrefix : localized = strictPrefixProcess A rho
  localized_eq_of_lt : ∀ {t : NNReal} {omega : Ω},
    t < rho omega → localized t omega = A t omega
  localized_data : AdaptedCadlagFiniteVariationData
    (F := F) localized T c
  jordan : SquareIntegrableJordanProjectionCertificate
    (F := F) (mu := mu) localized T

omit [MeasurableSpace Ω] in
theorem strictPrefixProcess_zero_of_zero
    (A : Process Ω) (rho : Ω → NNReal)
    (hAzero : A 0 = 0) :
    strictPrefixProcess A rho 0 = 0 := by
  funext omega
  by_cases hρ : rho omega = 0
  · rw [strictPrefixProcess_eq_of_ge A rho (by simp [hρ])]
    have hleft : Function.leftLim (fun s : NNReal => A s omega) (0 : NNReal) =
        A 0 omega := leftLim_eq_of_isBot isBot_bot
    rw [hρ, hleft]
    exact congrFun hAzero omega
  · have h0rho : (0 : NNReal) < rho omega :=
      (pos_iff_ne_zero).2 hρ
    rw [strictPrefixProcess_eq_of_lt A rho h0rho]
    exact congrFun hAzero omega

omit [MeasurableSpace Ω] in
theorem strictPrefixProcess_cumulativeVariation_bound_of_before
    (A : Process Ω) (rho : Ω → NNReal) (c T : NNReal)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ)
    (hBefore : ∀ omega t, t < rho omega →
      variationOnFromTo (A · omega) Set.univ 0 t ≤ (c : Real)) :
    ∀ omega,
      localVariation (strictPrefixProcess A rho) T omega ≤
        (c : Real) := by
  intro omega
  have hPVar : BoundedVariationOn
      (strictPrefixProcess A rho · omega) Set.univ :=
    strictPrefixProcess_boundedVariation A rho hAVar omega
  have hEVar := strictPrefixProcess_variation_le_of_before
    A rho omega (hAVar omega) (hBefore omega)
  have hVarNonneg : 0 ≤ variationOnFromTo
      (strictPrefixProcess A rho · omega) Set.univ 0 T :=
    variationOnFromTo.nonneg_of_le _ _ bot_le
  have hVarAbs := variationOnFromTo.abs_le_eVariationOn
    hPVar (a := (0 : NNReal)) (b := T)
  have hVarLe : variationOnFromTo
      (strictPrefixProcess A rho · omega) Set.univ 0 T ≤
      (eVariationOn (strictPrefixProcess A rho · omega) Set.univ).toReal := by
    simpa [abs_of_nonneg hVarNonneg] using hVarAbs
  have hELe : (eVariationOn
      (strictPrefixProcess A rho · omega) Set.univ).toReal ≤ (c : Real) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEVar
    simpa using h
  change variationOnFromTo
      (strictPrefixProcess A rho · omega) Set.univ 0 T ≤ (c : Real)
  exact hVarLe.trans hELe

omit [SigmaFiniteFiltration mu F] in
theorem exists_variationLevelLocalizationData
    (A : Process Ω) (c T : NNReal)
    (hA : StronglyAdapted F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t)
    (hALeft : ProcessHasLeftLimits A)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ)
    (hAzero : A 0 = 0)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (VariationLevelLocalizationData
      (F := F) (mu := mu) A c T) := by
  let rho := variationLevelStop A c T
  let localized := strictPrefixProcess A rho
  have hRho : IsStoppingTime F
      (fun omega => (rho omega : WithTop NNReal)) := by
    dsimp [rho]
    exact variationLevelStop_isStoppingTime A hA hARight hAVar hUsual c T
  have hRhoLe : ∀ omega, rho omega ≤ T := by
    exact variationLevelStop_le_horizon A c T
  have hLocalizedStrong : StronglyAdapted F localized := by
    dsimp [localized]
    exact strictPrefixProcess_stronglyAdapted A rho hA hARight hALeft hRho
  have hLocalizedRight : ∀ omega t,
      ContinuousWithinAt (localized · omega) (Ici t) t := by
    dsimp [localized]
    exact strictPrefixProcess_rightContinuous A rho hARight
  have hLocalizedLeft : ProcessHasLeftLimits localized := by
    dsimp [localized]
    exact strictPrefixProcess_hasLeftLimits A rho hALeft
  have hLocalizedVar : ∀ omega,
      BoundedVariationOn (localized · omega) Set.univ := by
    dsimp [localized]
    exact strictPrefixProcess_boundedVariation A rho hAVar
  have hLocalizedZero : localized 0 = 0 := by
    dsimp [localized]
    exact strictPrefixProcess_zero_of_zero A rho hAzero
  have hBefore : ∀ omega t, t < rho omega →
      variationOnFromTo (A · omega) Set.univ 0 t ≤ (c : Real) := by
    intro omega t ht
    exact variationLevelStop_before_level A c T omega ht
  have hCumulativeBound : ∀ omega,
      localVariation localized T omega ≤ (c : Real) := by
    dsimp [localized]
    exact strictPrefixProcess_cumulativeVariation_bound_of_before
      A rho c T hAVar hBefore
  let hData : AdaptedCadlagFiniteVariationData
      (F := F) localized T c := {
    stronglyAdapted := hLocalizedStrong
    adapted := hLocalizedStrong.adapted
    rightContinuous := hLocalizedRight
    hasLeftLimits := hLocalizedLeft
    boundedVariation := hLocalizedVar
    zero := hLocalizedZero
    constant_after := by
      intro omega t htt
      dsimp [localized]
      exact strictPrefixProcess_constant_after A rho (hRhoLe omega) htt
    cumulativeVariation_bound := hCumulativeBound }
  obtain ⟨hJordan⟩ :=
    AdaptedCadlagFiniteVariationData.exists_squareIntegrableJordanProjectionCertificate
      hData hUsual
  exact ⟨{
    rho := rho
    rho_eq_variationLevelStop := rfl
    rho_isStoppingTime := hRho
    rho_le_horizon := hRhoLe
    localized := localized
    localized_eq_strictPrefix := rfl
    localized_eq_of_lt := by
      intro t omega ht
      change strictPrefixProcess A rho t omega = A t omega
      exact strictPrefixProcess_eq_of_lt A rho ht
    localized_data := hData
    jordan := hJordan }⟩

end HorizonFactorialGrid

/-!
## A coherent family of variation-level localizations

For a fixed finite horizon, the strict-prefix localizer at level `n + 1` is
chosen canonically from the cumulative variation.  This section packages all
levels together.  The package records that the stopping times are increasing,
bounded by the horizon, and eventually equal to the horizon on every path.
It also records agreement of any two localized paths on their common strict
prefix.  No equality at either stopping boundary is asserted; a jump there is
precisely why the strict-prefix convention is used.
-/

namespace HorizonFactorialGrid

open FTAPTheorem42.SIntegrableFiniteVariationBridge

/-! ## Canonical levels and the level stop -/

/-- Positive integer variation thresholds, chosen independently of the
deterministic passage horizon. -/
def variationLevel (n : ℕ) : NNReal := ((n + 1 : ℕ) : NNReal)

theorem variationLevel_strictMono : StrictMono variationLevel := by
  intro m n hmn
  dsimp [variationLevel]
  exact_mod_cast Nat.add_lt_add_right hmn 1

omit [MeasurableSpace Ω] in
theorem variationLevelHittingTime_mono
    (A : Process Ω) {c d : NNReal} (hcd : c ≤ d) (omega : Ω) :
    variationLevelHittingTime A c omega ≤
      variationLevelHittingTime A d omega := by
  unfold variationLevelHittingTime
    RightContinuousHittingTime.strictHittingAfter
  apply MeasureTheory.hittingAfter_anti
  intro x hx
  change (c : Real) < x
  change (d : Real) < x at hx
  exact lt_of_le_of_lt (by exact_mod_cast hcd) hx

omit [MeasurableSpace Ω] in
theorem variationLevelStop_eq_horizon_of_cumulative_le
    (A : Process Ω) (c T : NNReal) (omega : Ω)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ)
    (hAConstant : ∀ omega t, T ≤ t → A t omega = A T omega)
    (hLevel : localVariation A T omega ≤ (c : Real)) :
    variationLevelStop A c T omega = T := by
  have hHitTop : variationLevelHittingTime A c omega = ⊤ := by
    unfold variationLevelHittingTime
      RightContinuousHittingTime.strictHittingAfter
    apply MeasureTheory.hittingAfter_eq_top_iff.mpr
    intro t _ ht
    have hValue : localVariation A t omega ≤
        localVariation A T omega := by
      by_cases htT : t ≤ T
      · exact (commonStopCumulativeVariation_monotone hAVar omega) htT
      · have hTt : T ≤ t := le_of_not_ge htT
        rw [commonStopCumulativeVariation_constant_after hAVar hAConstant
          omega t hTt]
    exact not_lt_of_ge (hValue.trans hLevel) ht
  unfold variationLevelStop
  rw [hHitTop]
  rw [min_eq_right (show (T : WithTop NNReal) ≤ ⊤ from le_top)]
  exact WithTop.untop_coe T

end HorizonFactorialGrid

end FTAPTheorem42
