/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingInterval
import FTAPTheorem42.Stochastic.Martingale.Basic.ZeroInitialLocalMartingaleStopping
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppedProcess

/-!
# Locally finite-variation candidate strategy data

General special semimartingale decompositions only have finite variation on
bounded time intervals.  This module records that natural boundary object and
shows how deterministic stopping turns it into the globally finite-variation
object consumed by the finite-horizon Lemma 4.7 calculus.  As for
`SIntegrableStrategy`, this raw record does not itself assert stochastic-
integral realization; that membership is supplied by a separate model.

The stopped local-martingale property, predictability of the stopped
finite-variation component, and pathwise bounded variation of that component
are derived here.  No predictable signed measure for the original locally
finite-variation process is required.
-/

namespace FTAPTheorem42

open MeasureTheory Set
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace LocalMartingale

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]

/-- Closed stopping preserves right-continuous local martingales with arbitrary
initial values. The same localizing sequence works: its initial-time indicator
commutes with both stops. -/
theorem stoppedProcess_of_rightContinuous
    {M : Process Ω} (hM : LocalMartingale M ℱ μ)
    (hRight : ∀ ω t, ContinuousWithinAt (M · ω) (Set.Ici t) t)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    LocalMartingale (MeasureTheory.stoppedProcess M σ) ℱ μ := by
  refine ⟨hM.localSeq, hM.isLocalizingSequence_localSeq, fun n => ?_⟩
  let B : Set Ω := {ω | (⊥ : WithTop ℝ≥0) < hM.localSeq n ω}
  have hLocalized : Martingale
      (MeasureTheory.stoppedProcess (fun t => B.indicator (M t)) (hM.localSeq n))
      ℱ μ := hM.stoppedProcess_localSeq n
  have hStopped :=
    RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hLocalized hσ
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
        (RightContinuousStoppedMartingale.indicator_rightContinuous M B hRight))
  change Martingale
    (MeasureTheory.stoppedProcess
      (fun t => B.indicator (MeasureTheory.stoppedProcess M σ t)) (hM.localSeq n)) ℱ μ
  rw [MeasureTheory.stoppedProcess_indicator_comm',
    MeasureTheory.stoppedProcess_stoppedProcess, inf_comm,
    ← MeasureTheory.stoppedProcess_stoppedProcess,
    ← MeasureTheory.stoppedProcess_indicator_comm']
  exact hStopped

/-- A right-continuous local martingale remains a local martingale after a
deterministic stop. -/
theorem deterministicallyStopped
    {M : Process Ω} (hM : LocalMartingale M ℱ μ)
    (hRight : ∀ ω t, ContinuousWithinAt (M · ω) (Set.Ici t) t)
    (T : ℝ≥0) :
    LocalMartingale (fun t ω => M (min t T) ω) ℱ μ := by
  have h := hM.stoppedProcess_of_rightContinuous hRight (isStoppingTime_const ℱ T)
  have hEq : MeasureTheory.stoppedProcess M (fun _ => (T : WithTop ℝ≥0)) =
      (fun t ω => M (min t T) ω) := by
    funext t ω
    simp only [MeasureTheory.stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [hEq] at h
  exact h

end LocalMartingale

namespace IsStronglyPredictable

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- A predictable process remains predictable after a positive
deterministic stop. -/
theorem deterministicallyStopped_of_pos
    {X : Process Ω} (hX : IsStronglyPredictable ℱ X)
    (T : ℝ≥0) (hT : 0 < T) :
    IsStronglyPredictable ℱ (fun t ω => X (min t T) ω) := by
  have hClamp :
      @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) ℱ.predictable ℱ.predictable
        (fun p => (min p.1 T, p.2)) := by
    refine @measurable_generateFrom (ℝ≥0 × Ω) (ℝ≥0 × Ω)
      ℱ.predictable _ (fun p => (min p.1 T, p.2)) ?_
    rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
    · change MeasurableSet[ℱ.predictable]
        ((fun p : ℝ≥0 × Ω => (min p.1 T, p.2)) ⁻¹'
          ({(0 : ℝ≥0)} ×ˢ A))
      rw [show (fun p : ℝ≥0 × Ω => (min p.1 T, p.2)) ⁻¹'
          ({(0 : ℝ≥0)} ×ˢ A) = {(0 : ℝ≥0)} ×ˢ A by
        ext p
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hmin, hp⟩
          exact ⟨(min_eq_zero.mp hmin).resolve_right hT.ne', hp⟩
        · rintro ⟨hp, hpA⟩
          rw [hp]
          exact ⟨min_eq_left bot_le, hpA⟩]
      exact measurableSet_predictable_singleton_bot_prod hA
    · by_cases hiT : i < T
      · rw [show (fun p : ℝ≥0 × Ω => (min p.1 T, p.2)) ⁻¹'
            (Set.Ioi i ×ˢ A) = Set.Ioi i ×ˢ A by
          ext p
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioi]
          constructor
          · rintro ⟨hmin, hp⟩
            exact ⟨(lt_min_iff.mp hmin).1, hp⟩
          · rintro ⟨hp, hpA⟩
            exact ⟨lt_min hp hiT, hpA⟩]
        exact measurableSet_predictable_Ioi_prod hA
      · rw [show (fun p : ℝ≥0 × Ω => (min p.1 T, p.2)) ⁻¹'
            (Set.Ioi i ×ˢ A) = ∅ by
          ext p
          constructor
          · rintro ⟨hmin, _⟩
            exact False.elim (hiT (lt_min_iff.mp hmin).2)
          · intro hp
            exact False.elim hp]
        exact @MeasurableSet.empty (ℝ≥0 × Ω) ℱ.predictable
  change StronglyMeasurable[ℱ.predictable]
    (fun p : ℝ≥0 × Ω => X (min p.1 T) p.2)
  simpa only [Function.comp_def, Function.uncurry] using
    (@StronglyMeasurable.comp_measurable
      (ℝ≥0 × Ω) ℝ (ℝ≥0 × Ω) _ ℱ.predictable ℱ.predictable
      (Function.uncurry X) (fun p => (min p.1 T, p.2)) hX hClamp)

end IsStronglyPredictable

/-- Candidate strategy data with the standard locally finite-variation
property on its predictable component. -/
structure LocallySIntegrableStrategy
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    (D : SpecialSemimartingaleDecomposition S ℱ μ) where
  integrand : Process Ω
  stochasticIntegral : Process Ω
  martingalePart : Process Ω
  finiteVariationPart : Process Ω
  integrand_isPredictable : IsStronglyPredictable ℱ integrand
  stochasticIntegral_isStronglyAdapted : StronglyAdapted ℱ stochasticIntegral
  stochasticIntegral_isRightContinuous :
    ∀ ω t, ContinuousWithinAt (stochasticIntegral · ω) (Set.Ici t) t
  martingalePart_isLocalMartingale : LocalMartingale martingalePart ℱ μ
  martingalePart_isStronglyAdapted : StronglyAdapted ℱ martingalePart
  martingalePart_isRightContinuous :
    ∀ ω t, ContinuousWithinAt (martingalePart · ω) (Set.Ici t) t
  finiteVariationPart_isPredictable : IsStronglyPredictable ℱ finiteVariationPart
  finiteVariationPart_isRightContinuous :
    ∀ ω t, ContinuousWithinAt (finiteVariationPart · ω) (Set.Ici t) t
  finiteVariationPart_isLocallyBoundedVariation :
    ∀ ω, LocallyBoundedVariationOn (fun t => finiteVariationPart t ω) Set.univ
  integral_decomposition : ProcessIndistinguishable μ stochasticIntegral
    (fun t ω => martingalePart t ω + finiteVariationPart t ω)
  source_decomposition : ProcessIndistinguishable μ S
    (fun t ω => D.martingalePart t ω + D.finiteVariationPart t ω)

namespace LocallySIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Restrict the integrand of a local strategy to the deterministic interval
`(0, T]`. -/
noncomputable def stoppedIntegrand
    (H : LocallySIntegrableStrategy D) (T : ℝ≥0) : Process Ω :=
  PredictableProcess.restrict
    (stochasticIntervalIocZero (fun _ : Ω => T)) H.integrand

/-- A local strategy's finite-variation component, stopped at `T`, has
bounded variation on the entire nonnegative time axis. -/
theorem stoppedFiniteVariation_isBoundedVariation
    (H : LocallySIntegrableStrategy D) (T : ℝ≥0) (ω : Ω) :
    BoundedVariationOn
      (fun t => H.finiteVariationPart (min t T) ω) Set.univ := by
  exact FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
    (H.finiteVariationPart_isLocallyBoundedVariation ω) T

/--
Stop a locally finite-variation strategy at a positive deterministic horizon
to obtain a strategy with globally bounded variation.

Right continuity and predictability give the deterministic-stopping
identities. Adaptedness, decomposition, and global bounded variation follow
from the local data. The auxiliary `finiteVariationMeasure` field is zero;
it does not represent the pathwise Stieltjes measure. Integral identities
use the actual-strategy certificate and pathwise Stieltjes restriction.
-/
noncomputable def deterministicallyStopped
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
    (H : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T) :
    SIntegrableStrategy D where
  integrand := H.stoppedIntegrand T
  stochasticIntegral := fun t ω => H.stochasticIntegral (min t T) ω
  martingalePart := fun t ω => H.martingalePart (min t T) ω
  finiteVariationPart := fun t ω => H.finiteVariationPart (min t T) ω
  finiteVariationMeasure := 0
  integrand_isPredictable := by
    exact PredictableProcess.isStronglyPredictable_restrict
      (IsStoppingTime.measurableSet_stochasticIntervalIocZero
        (τ := fun _ : Ω => T) (isStoppingTime_const ℱ T))
      H.integrand_isPredictable
  stochasticIntegral_isStronglyAdapted := fun t =>
    (H.stochasticIntegral_isStronglyAdapted (min t T)).mono
      (ℱ.mono (min_le_left t T))
  stochasticIntegral_isRightContinuous := fun ω t => by
    exact FiniteVariationStoppedPath.rightContinuous_stopAt
      (H.stochasticIntegral · ω) (H.stochasticIntegral_isRightContinuous ω) T t
  martingalePart_isLocalMartingale :=
    H.martingalePart_isLocalMartingale.deterministicallyStopped
      H.martingalePart_isRightContinuous T
  martingalePart_isStronglyAdapted := fun t =>
    (H.martingalePart_isStronglyAdapted (min t T)).mono
      (ℱ.mono (min_le_left t T))
  martingalePart_isRightContinuous := fun ω t => by
    exact FiniteVariationStoppedPath.rightContinuous_stopAt
      (H.martingalePart · ω) (H.martingalePart_isRightContinuous ω) T t
  finiteVariationPart_isPredictable :=
    IsStronglyPredictable.deterministicallyStopped_of_pos
      H.finiteVariationPart_isPredictable T hT
  finiteVariationPart_isRightContinuous := fun ω t => by
    exact FiniteVariationStoppedPath.rightContinuous_stopAt
      (H.finiteVariationPart · ω)
        (H.finiteVariationPart_isRightContinuous ω) T t
  finiteVariationPart_isBoundedVariation := H.stoppedFiniteVariation_isBoundedVariation T
  integral_decomposition := by
    filter_upwards [H.integral_decomposition] with ω hω
    intro t
    exact hω (min t T)
  source_decomposition := H.source_decomposition

end LocallySIntegrableStrategy

namespace SIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Forget the global bounded-variation and auxiliary signed-measure data of
a finite-horizon compatibility strategy. -/
noncomputable def toLocally
    (H : SIntegrableStrategy D) : LocallySIntegrableStrategy D where
  integrand := H.integrand
  stochasticIntegral := H.stochasticIntegral
  martingalePart := H.martingalePart
  finiteVariationPart := H.finiteVariationPart
  integrand_isPredictable := H.integrand_isPredictable
  stochasticIntegral_isStronglyAdapted := H.stochasticIntegral_isStronglyAdapted
  stochasticIntegral_isRightContinuous := H.stochasticIntegral_isRightContinuous
  martingalePart_isLocalMartingale := H.martingalePart_isLocalMartingale
  martingalePart_isStronglyAdapted := H.martingalePart_isStronglyAdapted
  martingalePart_isRightContinuous := H.martingalePart_isRightContinuous
  finiteVariationPart_isPredictable := H.finiteVariationPart_isPredictable
  finiteVariationPart_isRightContinuous := H.finiteVariationPart_isRightContinuous
  finiteVariationPart_isLocallyBoundedVariation := fun ω =>
    (H.finiteVariationPart_isBoundedVariation ω).locallyBoundedVariationOn
  integral_decomposition := H.integral_decomposition
  source_decomposition := H.source_decomposition

end SIntegrableStrategy

end FTAPTheorem42

namespace FTAPTheorem42.LocallySIntegrableStrategy

/-! ## Direct finite stopping of raw strategy coordinates

This constructor uses process stopping directly and requires no restriction
calculus. It is a raw coordinate constructor, not an integral graph assertion.
-/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {S : Process Ω} {D : SpecialSemimartingaleDecomposition S F mu}

/-- Finite random stopping turns local path variation into global variation.
All initial values are preserved; no normalization of either component is required. -/
noncomputable def finiteClosedStopOfRightContinuous (H : LocallySIntegrableStrategy D)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal))) : SIntegrableStrategy D where
  integrand := PredictableProcess.restrict (stochasticIntervalIocZero τ) H.integrand
  stochasticIntegral := stoppedProcess H.stochasticIntegral (fun ω => (τ ω : WithTop NNReal))
  martingalePart := stoppedProcess H.martingalePart (fun ω => (τ ω : WithTop NNReal))
  finiteVariationPart := stoppedProcess H.finiteVariationPart (fun ω => (τ ω : WithTop NNReal))
  finiteVariationMeasure := 0
  integrand_isPredictable := PredictableProcess.isStronglyPredictable_restrict
    (IsStoppingTime.measurableSet_stochasticIntervalIocZero hτ) H.integrand_isPredictable
  stochasticIntegral_isStronglyAdapted :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      H.stochasticIntegral_isStronglyAdapted hτ H.stochasticIntegral_isRightContinuous
  stochasticIntegral_isRightContinuous :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
      H.stochasticIntegral_isRightContinuous
  martingalePart_isLocalMartingale :=
    H.martingalePart_isLocalMartingale.stoppedProcess_of_rightContinuous
      H.martingalePart_isRightContinuous hτ
  martingalePart_isStronglyAdapted :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      H.martingalePart_isStronglyAdapted hτ H.martingalePart_isRightContinuous
  martingalePart_isRightContinuous :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
      H.martingalePart_isRightContinuous
  finiteVariationPart_isPredictable :=
    IsStronglyPredictable.stoppedProcess_of_stoppingTime H.finiteVariationPart_isPredictable τ hτ
  finiteVariationPart_isRightContinuous :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
      H.finiteVariationPart_isRightContinuous
  finiteVariationPart_isBoundedVariation := by
    intro ω
    simp only [stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    exact FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
      (H.finiteVariationPart_isLocallyBoundedVariation ω) (τ ω)
  integral_decomposition := by
    filter_upwards [H.integral_decomposition] with ω hω
    intro t
    simp only [stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    exact hω (min t (τ ω))
  source_decomposition := H.source_decomposition

/-- Compatibility constructor for normalized coordinates. -/
noncomputable abbrev finiteClosedStop (H : LocallySIntegrableStrategy D)
    (_hMZero : H.martingalePart 0 = 0) (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal))) : SIntegrableStrategy D :=
  H.finiteClosedStopOfRightContinuous τ hτ

end FTAPTheorem42.LocallySIntegrableStrategy
