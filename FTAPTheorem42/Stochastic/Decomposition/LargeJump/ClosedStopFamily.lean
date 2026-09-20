/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.ClosedStopProjection
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopOrderedOverlapComponent

/-!
# An exhaustive family of refined closed finite-large-jump stops

The one-level closed-stop certificate is selected at every level and the
three localizing sequences used by its refinement are retained explicitly.
The resulting family is only ordered almost everywhere, because the
localizing sequence carried by a local martingale is only almost everywhere
monotone.  Consequently the nested closed-source identity is stated as
process indistinguishability.  No compatibility of the predictable
projections at different levels is asserted.
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

/-! ## The packaged family -/

structure FiniteLargeJumpClosedStopFamily
    {X : Process Ω} {c : Real} {T : NNReal}
    (hX : LocalMartingale X F mu)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T)
    where
  data : ∀ n : ℕ,
    FiniteLargeJumpClosedStopProjectionData hX family n
  isLocalizingSequence : ProbabilityTheory.IsLocalizingSequence F
    (fun n omega => ((data n).tau omega : WithTop NNReal)) mu

namespace FiniteLargeJumpClosedStopFamily

variable {X : Process Ω} {c : Real} {T : NNReal}
  {hX : LocalMartingale X F mu}
  {family : FiniteLargeJumpValueTruncationFamily
    (F := F) (mu := mu) X c T}

/-! ## Almost-everywhere ordering -/

omit [SigmaFiniteFiltration mu F] in
theorem tau_mono_ae
    [F.IsRightContinuous]
    {hX : LocalMartingale X F mu}
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (closedFamily : FiniteLargeJumpClosedStopFamily
      (F := F) (mu := mu) hX family) :
    ∀ᵐ omega ∂mu,
      Monotone (fun n =>
        ((closedFamily.data n).tau omega : WithTop NNReal)) := by
  have hFamilyMono := family.isLocalizingSequence.mono
  have hLocalMono := hX.isLocalizingSequence_localSeq.mono
  have hPassageMono :=
    (cadlagAbsolutePassageLocalizer_isLocalizingSequence
      (mu := mu) hXAdapted hXRight hXLeft).mono
  filter_upwards [hFamilyMono, hLocalMono, hPassageMono]
    with omega hFamily hLocal hPassage
  intro m n hmn
  change ((closedFamily.data m).tau omega : WithTop NNReal) ≤
    ((closedFamily.data n).tau omega : WithTop NNReal)
  rw [congrFun (closedFamily.data m).tau_coe_eq_refined omega,
    congrFun (closedFamily.data n).tau_coe_eq_refined omega]
  exact min_le_min (hFamily hmn) (min_le_min (hLocal hmn) (hPassage hmn))

/-! ## Construction -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_finiteLargeJumpClosedStopFamily
    [F.IsRightContinuous]
    {X : Process Ω} {c : Real} {T : NNReal}
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (hXZero : X 0 = 0)
    (hc : 0 < c)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (FiniteLargeJumpClosedStopFamily
      (F := F) (mu := mu) hX family) := by
  let data : ∀ n : ℕ,
      FiniteLargeJumpClosedStopProjectionData hX family n := fun n =>
    Classical.choice (exists_finiteLargeJumpClosedStopProjectionData
      (F := F) (mu := mu) hX hXAdapted hXRight hXLeft hXZero hc
      family hUsual n)
  have hFamilyLocalizing := family.isLocalizingSequence
  have hLocalizingLocal := hX.isLocalizingSequence_localSeq
  have hPassageLocalizing :=
    cadlagAbsolutePassageLocalizer_isLocalizingSequence
      (mu := mu) hXAdapted hXRight hXLeft
  have hMinLocalizing := hFamilyLocalizing.min
    (hLocalizingLocal.min hPassageLocalizing)
  have hEq :
      (fun n omega => ((data n).tau omega : WithTop NNReal)) =
        (fun n omega => min ((family.data n).rho omega : WithTop NNReal)
          (min (hX.localSeq n omega)
            (cadlagAbsolutePassageLocalizer X n omega))) := by
    funext n omega
    exact congrFun (data n).tau_coe_eq_refined omega
  refine ⟨{ data := data, isLocalizingSequence := ?_ }⟩
  rw [hEq]
  exact hMinLocalizing

/-! ## Nested closed sources -/

omit [SigmaFiniteFiltration mu F] in
theorem closed_stopped_at_le_eq_of_le_ae
    [F.IsRightContinuous]
    {hX : LocalMartingale X F mu}
    (closedFamily : FiniteLargeJumpClosedStopFamily
      (F := F) (mu := mu) hX family)
    (hTauMono : ∀ᵐ omega ∂mu,
      Monotone (fun n =>
        ((closedFamily.data n).tau omega : WithTop NNReal)))
    {m n : ℕ} (hmn : m ≤ n) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (closedFamily.data n).closed
        (fun omega =>
          ((closedFamily.data m).tau omega : WithTop NNReal)))
      (closedFamily.data m).closed := by
  have hTauLe : ∀ᵐ omega ∂mu,
      ((closedFamily.data m).tau omega : WithTop NNReal) ≤
        ((closedFamily.data n).tau omega : WithTop NNReal) := by
    filter_upwards [hTauMono] with omega hMono
    exact hMono hmn
  rw [closedFamily.data n |>.closed_eq_stopped,
    closedFamily.data m |>.closed_eq_stopped]
  exact stoppedProcess_stoppedProcess_indistinguishable_of_ae_le
    (mu := mu) (u := FiniteLargeJumpProcess.process X c T)
    (σ := fun omega =>
      ((closedFamily.data m).tau omega : WithTop NNReal))
    (τ := fun omega =>
      ((closedFamily.data n).tau omega : WithTop NNReal)) hTauLe

omit [SigmaFiniteFiltration mu F] in
theorem closed_stopped_at_le_eq
    [F.IsRightContinuous]
    {hX : LocalMartingale X F mu}
    (closedFamily : FiniteLargeJumpClosedStopFamily
      (F := F) (mu := mu) hX family)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    {m n : ℕ} (hmn : m ≤ n) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (closedFamily.data n).closed
        (fun omega =>
          ((closedFamily.data m).tau omega : WithTop NNReal)))
      (closedFamily.data m).closed := by
  exact closed_stopped_at_le_eq_of_le_ae closedFamily
    (tau_mono_ae hXAdapted hXRight hXLeft closedFamily) hmn

end FiniteLargeJumpClosedStopFamily

end HorizonFactorialGrid

end FTAPTheorem42
