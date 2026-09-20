/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticLocalizingScheduleSemantics

/-!
# Global quadratic roots and the Davis consumer

The optional quadratic-variation process supplied by a schedule is already
globally glued.  This module evaluates that process at a stopping time to
obtain the quadratic root; it does not glue a separate root process.  The
finite-horizon root and cost identities use bounded-stop quadratic
consistency, while the Davis consumer is the existing one-sided estimate for
the stopped true `M²` coordinates.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalMartingaleQuadratic

open BoundedMartingaleQuadraticKernel
open BoundedMartingaleQuadraticKernel.Data
open SIntegrableFiniteVariationBridge

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {M : Process Omega}

/-! ## Root evaluation and cost -/

/-- The quadratic root of an optional variation process at a finite-valued
random time.  The process itself is not required to be predictable. -/
noncomputable def localQuadraticRootAt
    (Q : Process Omega) (sigma : Omega → NNReal) : Omega → Real :=
  fun omega => Real.sqrt (Q (sigma omega) omega)

/-- The `L¹` quadratic-root cost obtained by evaluating an optional variation
process at a finite-valued random time. -/
noncomputable def localQuadraticRootCostAt
    (Q : Process Omega) (sigma : Omega → NNReal) : ENNReal :=
  ∫⁻ omega, ENNReal.ofReal (localQuadraticRootAt Q sigma omega) ∂mu

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem localizer_root_at_eq_stopped_coordinate
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (QC : GluedQuadraticVariationCertificate C)
    (n : Nat) :
    localQuadraticRootAt QC.variation (C.localizer n) =ᵐ[mu]
      (fun omega => Real.sqrt
        ((C.coordinate n).quadraticData.variation
          (C.localizer n omega) omega)) := by
  let tau : Omega → NNReal := C.localizer n
  have hQData : ∀ᵐ omega ∂mu,
      QC.variation (tau omega) omega =
        (C.coordinate n).quadraticData.variation (tau omega) omega := by
    filter_upwards [QC.variation_stoppedCoordinate n] with omega hOmega
    have hAt := hOmega (tau omega)
    simpa only [tau, stoppedProcess_coe_apply, min_self] using hAt
  filter_upwards [hQData] with omega hData
  change Real.sqrt (QC.variation (tau omega) omega) =
    Real.sqrt ((C.coordinate n).quadraticData.variation
      (tau omega) omega)
  exact congrArg Real.sqrt hData

/-- At every supplied localizer, the global quadratic root agrees almost
everywhere with the terminal root of the stored finite-horizon coordinate.
The terminal-to-localizer step is supplied by the bounded-stop consistency
theorem; constancy of the stored variation after the localizer is not used. -/
theorem localQuadraticRootAt_localizer_ae_eq_coordinate
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (QC : GluedQuadraticVariationCertificate C)
    (n : Nat) :
    localQuadraticRootAt QC.variation (C.localizer n) =ᵐ[mu]
      SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRoot
        (C.coordinate n).quadraticData := by
  let tau : Omega → NNReal := C.localizer n
  let tauTop : Omega → WithTop NNReal := fun omega =>
    (tau omega : WithTop NNReal)
  let N : Process Omega := MeasureTheory.stoppedProcess M tauTop
  have hTau : IsStoppingTime F tauTop := by
    simpa only [tauTop, tau] using C.localizer_isStoppingTime n
  have hTauLe : ∀ omega, tau omega ≤ C.horizon n := by
    intro omega
    exact C.localizer_le_horizon n omega
  have hNMartingale : Martingale N F mu := by
    simpa only [N, tauTop, tau] using (C.coordinate n).source_martingale
  have hNRight : ∀ omega t,
      ContinuousWithinAt (N · omega) (Ici t) t := by
    dsimp [N]
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      M hMRight
  have hNLeft : ProcessHasLeftLimits N := by
    dsimp [N]
    exact hMLeft.stoppedProcess tauTop
  have hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess N tauTop) := by
    have hSelf : MeasureTheory.stoppedProcess N tauTop = N := by
      dsimp [N]
      exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_left
        (u := M) (τ := tauTop) (σ := tauTop) le_rfl
    rw [hSelf]
    exact ProcessIndistinguishable.refl mu N
  have hRootStop :=
    squareIntegrableMartingaleQuadraticRoot_ae_eq_stopped_of_bounded_stop
      (M := N) (N := N) (T := C.horizon n) (U := C.horizon n)
      hUsual hNMartingale hNRight hNLeft
      hNMartingale hNRight hNLeft
      (C.coordinate n).quadraticData (C.coordinate n).quadraticData
      tau hTau hTauLe hTauLe hNDef
  have hRootAt := localizer_root_at_eq_stopped_coordinate C QC n
  filter_upwards [hRootAt, hRootStop] with omega hGlobal hStopped
  rw [hGlobal, hStopped]

/-- The `lintegral` root cost at a supplied localizer agrees with the stored
quadratic root cost. -/
theorem localQuadraticRootCostAt_localizer_eq_coordinate
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (QC : GluedQuadraticVariationCertificate C)
    (n : Nat) :
    localQuadraticRootCostAt (mu := mu) QC.variation (C.localizer n) =
      SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRootCost
        (C.coordinate n).quadraticData := by
  unfold localQuadraticRootCostAt
    SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRootCost
  apply lintegral_congr_ae
  filter_upwards [localQuadraticRootAt_localizer_ae_eq_coordinate
      hUsual hMRight hMLeft C QC n] with omega hOmega
  rw [hOmega]

/-! ## The one-sided Davis consumer -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem localizer_stopped_source_zero
    (hM0 : M 0 = 0)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (n : Nat) :
    (MeasureTheory.stoppedProcess M
      (fun omega => (C.localizer n omega : WithTop NNReal))) 0 = 0 := by
  funext omega
  rw [MeasureTheory.stoppedProcess_eq_of_le bot_le]
  exact congrFun hM0 omega

/-- The supplied finite-horizon `M²` coordinate satisfies the one-sided
constant-six Davis estimate with the global quadratic root at its localizer.
The source is explicitly normalized by `hM0`; no two-sided BDG statement is
asserted. -/
theorem finiteHorizonAbsoluteEnvelope_integral_le_six_localQuadraticRoot
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hM0 : M 0 = 0)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (QC : GluedQuadraticVariationCertificate C)
    (n : Nat) :
    (∫ omega, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      (MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      (C.horizon n) omega ∂mu) ≤
      6 * ∫ omega, localQuadraticRootAt QC.variation
        (C.localizer n) omega ∂mu := by
  let tau : Omega → NNReal := C.localizer n
  let tauTop : Omega → WithTop NNReal := fun omega =>
    (tau omega : WithTop NNReal)
  let N : Process Omega := MeasureTheory.stoppedProcess M tauTop
  have hTau : IsStoppingTime F tauTop := by
    simpa only [tauTop, tau] using C.localizer_isStoppingTime n
  have hTauLe : ∀ omega, tau omega ≤ C.horizon n := by
    intro omega
    exact C.localizer_le_horizon n omega
  have hNMartingale : Martingale N F mu := by
    simpa only [N, tauTop, tau] using (C.coordinate n).source_martingale
  have hNRight : ∀ omega t,
      ContinuousWithinAt (N · omega) (Ici t) t := by
    dsimp [N]
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      M hMRight
  have hNLeft : ProcessHasLeftLimits N := by
    dsimp [N]
    exact hMLeft.stoppedProcess tauTop
  have hN0 : N 0 = 0 := by
    simpa only [N, tauTop, tau] using localizer_stopped_source_zero hM0 C n
  have hNU : MemLp (N (C.horizon n)) (2 : ENNReal) mu := by
    simpa only [N, tauTop, tau] using
      (C.coordinate n).source_terminal_memLp_two
  have hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess N tauTop) := by
    have hSelf : MeasureTheory.stoppedProcess N tauTop = N := by
      dsimp [N]
      exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_left
        (u := M) (τ := tauTop) (σ := tauTop) le_rfl
    rw [hSelf]
    exact ProcessIndistinguishable.refl mu N
  have hDavis :=
    finiteHorizonAbsoluteEnvelope_integral_le_six_stoppedQuadraticRoot
      (M := N) (N := N) (T := C.horizon n) (U := C.horizon n)
      hUsual hNMartingale hNRight hNLeft hN0 hNU
      (C.coordinate n).quadraticData (C.coordinate n).quadraticData
      hNMartingale hNRight hNLeft tau hTau hTauLe hTauLe hNDef
  have hRootAtData : ∀ᵐ omega ∂mu,
      localQuadraticRootAt QC.variation tau omega =
        Real.sqrt ((C.coordinate n).quadraticData.variation
          (tau omega) omega) := by
    filter_upwards [QC.variation_stoppedCoordinate n] with omega hOmega
    have hAt := hOmega (tau omega)
    have hAt' : QC.variation (tau omega) omega =
        (C.coordinate n).quadraticData.variation (tau omega) omega := by
      simpa only [tau, stoppedProcess_coe_apply, min_self] using hAt
    exact congrArg Real.sqrt hAt'
  have hRootIntegral :
      (∫ omega, localQuadraticRootAt QC.variation tau omega ∂mu) =
        ∫ omega, Real.sqrt ((C.coordinate n).quadraticData.variation
          (tau omega) omega) ∂mu := by
    apply integral_congr_ae
    exact hRootAtData
  calc
    (∫ omega, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope N
        (C.horizon n) omega ∂mu) ≤
        6 * ∫ omega, Real.sqrt ((C.coordinate n).quadraticData.variation
          (tau omega) omega) ∂mu := hDavis
    _ = 6 * ∫ omega, localQuadraticRootAt QC.variation tau omega ∂mu := by
      exact congrArg (fun x : Real => 6 * x) hRootIntegral.symm

end LocalMartingaleQuadratic

end FTAPTheorem42
