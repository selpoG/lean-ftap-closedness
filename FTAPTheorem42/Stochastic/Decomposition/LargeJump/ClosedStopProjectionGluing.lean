/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.ClosedStopProjectionOverlap
import FTAPTheorem42.Stochastic.FiniteVariation.CompatibleLocalFiniteVariationGluing

/-!
# Global gluing of finite-large-jump predictable projections

The ordered overlap of two projection coordinates is transported to the
minimum of their two refined stops.  This is the symmetric compatibility law
required by the generic finite-variation gluing theorem.  The resulting
process is then normalized on its initial-value null set, so that its initial
value is exactly zero without changing any stopped-coordinate identity.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open FTAPTheorem42.SIntegrableFiniteVariationBridge
open FTAPTheorem42.FiniteLargeJumpProcess

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

namespace FiniteLargeJumpClosedStopFamily

variable {X : Process Ω} {c : Real} {T : NNReal}
  {hX : LocalMartingale X F mu}
  {family : FiniteLargeJumpValueTruncationFamily
    (F := F) (mu := mu) X c T}

/-! ## The all-pairs minimum-stop compatibility -/

/-- The projection coordinates agree after stopping both at the minimum of
their refined stopping times.  The ordered overlap theorem is used in the
appropriate direction, while its reflexive instance supplies the required
self-stop identity. -/
theorem projection_minimum_stop_compatibility
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
      (hXLeft : ProcessHasLeftLimits X)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T)
    (closedFamily : FiniteLargeJumpClosedStopFamily
      (F := F) (mu := mu) hX family)
    (hUsual : Filtration.UsualConditions mu F)
    {n m : ℕ} :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (closedFamily.data n).projection.Ap
        (fun omega => min
          ((closedFamily.data n).tau omega : WithTop NNReal)
          ((closedFamily.data m).tau omega : WithTop NNReal)))
      (MeasureTheory.stoppedProcess (closedFamily.data m).projection.Ap
        (fun omega => min
          ((closedFamily.data n).tau omega : WithTop NNReal)
          ((closedFamily.data m).tau omega : WithTop NNReal))) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  rcases le_total m n with hmn | hnm
  · have hTauMono := tau_mono_ae hXAdapted hXRight hXLeft closedFamily
    have hMin : ∀ᵐ omega ∂mu,
        min ((closedFamily.data n).tau omega : WithTop NNReal)
            ((closedFamily.data m).tau omega : WithTop NNReal) =
          ((closedFamily.data m).tau omega : WithTop NNReal) := by
      filter_upwards [hTauMono] with omega hMono
      exact min_eq_right (hMono hmn)
    have hLeft := stoppedProcess_indistinguishable_of_ae_eq
      (mu := mu) (u := (closedFamily.data n).projection.Ap) hMin
    have hRight := stoppedProcess_indistinguishable_of_ae_eq
      (mu := mu) (u := (closedFamily.data m).projection.Ap) hMin
    have hOverlap := projection_overlap_of_le
      hX hXAdapted hXRight hXLeft family closedFamily hUsual hmn
    have hSelf := projection_overlap_of_le
      hX hXAdapted hXRight hXLeft family closedFamily hUsual (le_refl m)
    exact hLeft.trans (hOverlap.trans (hSelf.symm.trans hRight.symm))
  · have hTauMono := tau_mono_ae hXAdapted hXRight hXLeft closedFamily
    have hMin : ∀ᵐ omega ∂mu,
        min ((closedFamily.data n).tau omega : WithTop NNReal)
            ((closedFamily.data m).tau omega : WithTop NNReal) =
          ((closedFamily.data n).tau omega : WithTop NNReal) := by
      filter_upwards [hTauMono] with omega hMono
      exact min_eq_left (hMono hnm)
    have hLeft := stoppedProcess_indistinguishable_of_ae_eq
      (mu := mu) (u := (closedFamily.data n).projection.Ap) hMin
    have hRight := stoppedProcess_indistinguishable_of_ae_eq
      (mu := mu) (u := (closedFamily.data m).projection.Ap) hMin
    have hOverlap := projection_overlap_of_le
      hX hXAdapted hXRight hXLeft family closedFamily hUsual hnm
    have hSelf := projection_overlap_of_le
      hX hXAdapted hXRight hXLeft family closedFamily hUsual (le_refl n)
    exact hLeft.trans (hSelf.trans (hOverlap.symm.trans hRight.symm))

/-! ## The normalized global projection -/

/-- Data for the globally glued predictable finite-variation projection. -/
structure ProjectionGluingData
    (hX : LocalMartingale X F mu)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T)
    (closedFamily : FiniteLargeJumpClosedStopFamily
      (F := F) (mu := mu) hX family)
    (hUsual : Filtration.UsualConditions mu F)
    where
  P : Process Ω
  P_isStronglyPredictable : IsStronglyPredictable F P
  P_rightContinuous : ∀ omega t,
    ContinuousWithinAt (P · omega) (Ici t) t
  P_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (P · omega) Set.univ
  P_zero : P 0 = 0
  P_stopped : ∀ n, ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess P
      (fun omega => ((closedFamily.data n).tau omega : WithTop NNReal)))
    (MeasureTheory.stoppedProcess (closedFamily.data n).projection.Ap
      (fun omega => ((closedFamily.data n).tau omega : WithTop NNReal)))

/-- Glue all predictable projection coordinates and normalize the resulting
process at time zero. -/
theorem exists_projectionGluingData
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T)
    (closedFamily : FiniteLargeJumpClosedStopFamily
      (F := F) (mu := mu) hX family)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (ProjectionGluingData hX family closedFamily hUsual) := by
  let tau : Nat → Ω → WithTop NNReal := fun n omega =>
    ((closedFamily.data n).tau omega : WithTop NNReal)
  let A : Nat → Process Ω := fun n =>
    (closedFamily.data n).projection.Ap
  have hTau : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    simpa only [tau] using closedFamily.isLocalizingSequence
  have hCompatibility : ∀ n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (A n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (A m) (min (tau n) (tau m))) := by
    intro n m
    change ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (closedFamily.data n).projection.Ap
        (fun omega => min
          ((closedFamily.data n).tau omega : WithTop NNReal)
          ((closedFamily.data m).tau omega : WithTop NNReal)))
      (MeasureTheory.stoppedProcess (closedFamily.data m).projection.Ap
        (fun omega => min
          ((closedFamily.data n).tau omega : WithTop NNReal)
          ((closedFamily.data m).tau omega : WithTop NNReal)))
    exact projection_minimum_stop_compatibility
      hX hXAdapted hXRight hXLeft family closedFamily hUsual
  obtain ⟨Praw, hPrawPredictable, hPrawRight, hPrawVariation, hPrawStopped⟩ :=
    CompatibleLocalFiniteVariationGluing.exists_predictable_rightContinuous_locallyBoundedVariation
      hUsual hTau
      (fun n => by
        exact (closedFamily.data n).projection.Ap_stronglyPredictable)
      (fun n omega t => by
        exact (closedFamily.data n).projection.Ap_rightContinuous omega t)
      (fun n omega => by
        exact (closedFamily.data n).projection.Ap_boundedVariation omega)
      hCompatibility
  have hPrawZero : Praw 0 =ᵐ[mu] 0 := by
    have hStoppedZero := (hPrawStopped 0).eventuallyEq_at 0
    filter_upwards [hStoppedZero,
      (closedFamily.data 0).projection.Ap_zero_ae] with omega hStop hApZero
    calc
      Praw 0 omega =
          MeasureTheory.stoppedProcess Praw (tau 0) 0 omega := by
        symm
        exact MeasureTheory.stoppedProcess_eq_of_le bot_le
      _ = MeasureTheory.stoppedProcess (A 0) (tau 0) 0 omega := hStop
      _ = A 0 0 omega := MeasureTheory.stoppedProcess_eq_of_le bot_le
      _ = 0 := hApZero
  let bad : Set Ω := {omega | Praw 0 omega ≠ 0}
  have hbadNull : mu bad = 0 := by
    have hbad : {omega | ¬ Praw 0 omega = 0} = bad := by
      ext omega
      simp [bad]
    rw [← hbad]
    exact ae_iff.mp hPrawZero
  have hbadMeasurable : MeasurableSet[F 0] bad :=
    hUsual.containsNullSetsAtZero bad hbadNull
  let P : Process Ω := ProcessNullSetRegularization.zeroOn bad Praw
  have hPZero : P 0 = 0 := by
    funext omega
    change ProcessNullSetRegularization.zeroOn bad Praw 0 omega = (0 : Real)
    by_cases homega : omega ∈ bad
    · exact ProcessNullSetRegularization.zeroOn_apply_of_mem bad Praw homega
    · have hPrawZeroOmega : Praw 0 omega = 0 := by
        by_contra hne
        exact homega hne
      rw [ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Praw homega]
      exact hPrawZeroOmega
  have hPStopped : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess P (tau n))
      (MeasureTheory.stoppedProcess (A n) (tau n)) := by
    intro n
    exact
      (ProcessNullSetRegularization.zeroOn_indistinguishable hbadNull Praw).stoppedProcess
        (tau n) |>.trans (hPrawStopped n)
  refine ⟨{
    P := P
    P_isStronglyPredictable :=
      ProcessNullSetRegularization.isStronglyPredictable_zeroOn
        hbadMeasurable hPrawPredictable
    P_rightContinuous :=
      ProcessNullSetRegularization.zeroOn_isRightContinuous (fun omega homega => by
        exact hPrawRight omega)
    P_locallyBoundedVariation :=
      ProcessNullSetRegularization.zeroOn_isLocallyBoundedVariation
        (fun omega homega => hPrawVariation omega)
    P_zero := hPZero
    P_stopped := by
      intro n
      simpa only [P, tau, A] using hPStopped n }⟩

end FiniteLargeJumpClosedStopFamily

end HorizonFactorialGrid

end FTAPTheorem42
