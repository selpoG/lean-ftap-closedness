/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.ClosedStopProjectionGluing
import FTAPTheorem42.Stochastic.Martingale.Basic.CompatibleLocalMartingaleGluing

/-!
# Gluing the residual martingale coordinates of finite-large-jump stops

The closed sources and their predictable projections have compatible stopped
restrictions.  Subtracting these two identities gives the corresponding
all-pairs compatibility for the residual martingale coordinates.  The
existing martingale gluing theorem then supplies one càdlàg local martingale
with the prescribed stopped coordinates.
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

/-! ## Residual compatibility on the minimum stop -/

/-- The residual coordinates agree after stopping both at the minimum of
their refined stopping times. -/
theorem residual_minimum_stop_compatibility
    [F.IsRightContinuous]
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
      (MeasureTheory.stoppedProcess
        (closedFamily.data n).projection.residual
        (fun omega => min
          ((closedFamily.data n).tau omega : WithTop NNReal)
          ((closedFamily.data m).tau omega : WithTop NNReal)))
      (MeasureTheory.stoppedProcess
        (closedFamily.data m).projection.residual
        (fun omega => min
          ((closedFamily.data n).tau omega : WithTop NNReal)
          ((closedFamily.data m).tau omega : WithTop NNReal))) := by
  let tauN : Ω → WithTop NNReal := fun omega =>
    ((closedFamily.data n).tau omega : WithTop NNReal)
  let tauM : Ω → WithTop NNReal := fun omega =>
    ((closedFamily.data m).tau omega : WithTop NNReal)
  let tauMin : Ω → WithTop NNReal := fun omega => min (tauN omega) (tauM omega)
  let Cn : Process Ω := (closedFamily.data n).closed
  let Cm : Process Ω := (closedFamily.data m).closed
  let Pn : Process Ω := (closedFamily.data n).projection.Ap
  let Pm : Process Ω := (closedFamily.data m).projection.Ap
  let Rn : Process Ω := (closedFamily.data n).projection.residual
  let Rm : Process Ω := (closedFamily.data m).projection.residual
  have hTauMono := FiniteLargeJumpClosedStopFamily.tau_mono_ae
    hXAdapted hXRight hXLeft closedFamily
  have hClosed : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess Cn tauMin)
      (MeasureTheory.stoppedProcess Cm tauMin) := by
    rcases le_total m n with hmn | hnm
    · have hMin : ∀ᵐ omega ∂mu, tauMin omega = tauM omega := by
        filter_upwards [hTauMono] with omega hMono
        exact min_eq_right (hMono hmn)
      have hLeft := stoppedProcess_indistinguishable_of_ae_eq
        (mu := mu) (u := Cn) hMin
      have hRight := stoppedProcess_indistinguishable_of_ae_eq
        (mu := mu) (u := Cm) hMin
      have hOverlap :=
        FiniteLargeJumpClosedStopFamily.closed_stopped_at_le_eq_of_le_ae
          closedFamily hTauMono hmn
      have hSelf : ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess Cm tauM) Cm := by
        dsimp [Cm, tauM]
        exact stoppedProcess_self_of_eq_stopped
          (mu := mu) (closedFamily.data m).closed_eq_stopped
      exact hLeft.trans (hOverlap.trans (hSelf.symm.trans hRight.symm))
    · have hMin : ∀ᵐ omega ∂mu, tauMin omega = tauN omega := by
        filter_upwards [hTauMono] with omega hMono
        exact min_eq_left (hMono hnm)
      have hLeft := stoppedProcess_indistinguishable_of_ae_eq
        (mu := mu) (u := Cn) hMin
      have hRight := stoppedProcess_indistinguishable_of_ae_eq
        (mu := mu) (u := Cm) hMin
      have hOverlap :=
        FiniteLargeJumpClosedStopFamily.closed_stopped_at_le_eq_of_le_ae
          closedFamily hTauMono hnm
      have hSelf : ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess Cn tauN) Cn := by
        dsimp [Cn, tauN]
        exact stoppedProcess_self_of_eq_stopped
          (mu := mu) (closedFamily.data n).closed_eq_stopped
      exact hLeft.trans (hSelf.trans (hOverlap.symm.trans hRight.symm))
  have hProjection :=
    FiniteLargeJumpClosedStopFamily.projection_minimum_stop_compatibility
      hX hXAdapted hXRight hXLeft family closedFamily hUsual
      (n := n) (m := m)
  have hSub := ProcessIndistinguishable.sub hClosed hProjection
  have hResidualN :
      MeasureTheory.stoppedProcess Rn tauMin =
        (fun t omega =>
          MeasureTheory.stoppedProcess Cn tauMin t omega -
            MeasureTheory.stoppedProcess Pn tauMin t omega) := by
    funext t omega
    simp only [MeasureTheory.stoppedProcess]
    exact congrFun (congrFun
      (closedFamily.data n).projection.residual_definition
      (min (t : WithTop NNReal) (tauMin omega)).untopA) omega
  have hResidualM :
      MeasureTheory.stoppedProcess Rm tauMin =
        (fun t omega =>
          MeasureTheory.stoppedProcess Cm tauMin t omega -
            MeasureTheory.stoppedProcess Pm tauMin t omega) := by
    funext t omega
    simp only [MeasureTheory.stoppedProcess]
    exact congrFun (congrFun
      (closedFamily.data m).projection.residual_definition
      (min (t : WithTop NNReal) (tauMin omega)).untopA) omega
  rw [hResidualN, hResidualM]
  exact hSub

/-! ## The glued residual martingale -/

structure ResidualMartingaleGluingData
    (hX : LocalMartingale X F mu)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T)
    (closedFamily : FiniteLargeJumpClosedStopFamily
      (F := F) (mu := mu) hX family)
    (hUsual : Filtration.UsualConditions mu F)
    where
  Q : Process Ω
  Q_isStronglyAdapted : StronglyAdapted F Q
  Q_isLocalMartingale : LocalMartingale Q F mu
  Q_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Q · omega) (Ici t) t
  Q_leftLimits : ProcessHasLeftLimits Q
  Q_stopped : ∀ n, ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess Q
      (fun omega => ((closedFamily.data n).tau omega : WithTop NNReal)))
    (MeasureTheory.stoppedProcess (closedFamily.data n).projection.residual
      (fun omega => ((closedFamily.data n).tau omega : WithTop NNReal)))

/-- Glue the residual martingale coordinates along the refined closed-stop
localizing sequence. -/
theorem exists_residualMartingaleGluingData
    [F.IsRightContinuous]
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
    Nonempty (ResidualMartingaleGluingData hX family closedFamily hUsual) := by
  let tau : Nat → Ω → WithTop NNReal := fun n omega =>
    ((closedFamily.data n).tau omega : WithTop NNReal)
  let R : Nat → Process Ω := fun n =>
    (closedFamily.data n).projection.residual
  have hTau : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    simpa only [tau] using closedFamily.isLocalizingSequence
  have hCompatibility : ∀ n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (R n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (R m) (min (tau n) (tau m))) := by
    intro n m
    change ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (closedFamily.data n).projection.residual
        (fun omega => min
          ((closedFamily.data n).tau omega : WithTop NNReal)
          ((closedFamily.data m).tau omega : WithTop NNReal)))
      (MeasureTheory.stoppedProcess
        (closedFamily.data m).projection.residual
        (fun omega => min
          ((closedFamily.data n).tau omega : WithTop NNReal)
          ((closedFamily.data m).tau omega : WithTop NNReal)))
    exact residual_minimum_stop_compatibility
      hX hXAdapted hXRight hXLeft family closedFamily hUsual
  have hRMartingale : ∀ n, Martingale (R n) F mu := by
    intro n
    exact (closedFamily.data n).projection.residual_martingale
  have hRRight : ∀ n omega t,
      ContinuousWithinAt (R n · omega) (Ici t) t := by
    intro n omega t
    dsimp [R]
    rw [(closedFamily.data n).projection.residual_definition]
    exact ((closedFamily.data n).source_data.rightContinuous omega t).sub
      ((closedFamily.data n).projection.Ap_rightContinuous omega t)
  have hRLeft : ∀ n, ProcessHasLeftLimits (R n) := by
    intro n
    dsimp [R]
    rw [(closedFamily.data n).projection.residual_definition]
    exact (closedFamily.data n).source_data.hasLeftLimits.sub
      (closedFamily.data n).projection.Ap_leftLimits
  obtain ⟨Q, hQAdapted, hQLocal, hQRight, hQLeft, hQStopped⟩ :=
    CompatibleLocalMartingaleGluing.exists_cadlag_localMartingale
      hUsual hTau hRMartingale hRRight hRLeft hCompatibility
  refine ⟨{
    Q := Q
    Q_isStronglyAdapted := hQAdapted
    Q_isLocalMartingale := hQLocal
    Q_rightContinuous := hQRight
    Q_leftLimits := hQLeft
    Q_stopped := by
      intro n
      simpa only [tau, R] using hQStopped n }⟩

end FiniteLargeJumpClosedStopFamily

end HorizonFactorialGrid

end FTAPTheorem42
