/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticStoppingConsistency

/-!
# Countable local-to-true quadratic schedules

This module packages a supplied countable family of bounded stopped true
martingales and their finite-horizon quadratic data for one càdlàg local
martingale.  The coordinate data are retained exactly as supplied.  At the
minimum of any two coordinate stops, one further true square-integrable
certificate is constructed from the earlier coordinate by optional sampling.
The bounded-stop quadratic consistency theorem then compares the two stored
variations on that common stop, including their terminal roots and costs.

No predictable version or global gluing of the optional quadratic-variation
process is asserted here: the stored variation is adapted and
right-continuous, but need not itself be predictable when it has jumps.
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

/-! ## The supplied countable schedule -/

/-- A countable family of finite-horizon true `M²` coordinates for one local
martingale.  The certificate at coordinate `n` retains the stopped source
martingale, its terminal `L²` witness, and the selected quadratic data/root
cost.  The localizer is finite-valued and is bounded by that coordinate's
deterministic horizon. -/
structure LocalMartingaleQuadraticSchedule where
  localizer : Nat → Omega → NNReal
  horizon : Nat → NNReal
  isLocalizingSequence :
    ProbabilityTheory.IsLocalizingSequence F
      (fun n omega => (localizer n omega : WithTop NNReal)) mu
  localizer_le_horizon : ∀ n omega, localizer n omega ≤ horizon n
  coordinate : ∀ n,
    SquareIntegrableMartingaleQuadraticJ1Certificate F mu
      (MeasureTheory.stoppedProcess M
        (fun omega => (localizer n omega : WithTop NNReal))) (horizon n)

namespace LocalMartingaleQuadraticSchedule

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- Every schedule coordinate is a stopping time. -/
theorem localizer_isStoppingTime
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (n : Nat) :
    IsStoppingTime F
      (fun omega => (C.localizer n omega : WithTop NNReal)) :=
  C.isLocalizingSequence.isStoppingTime n

end LocalMartingaleQuadraticSchedule

/-! ## Pair data retained after a common stopping -/

/-- The concrete common-stop data and compatibility conclusions for two
coordinates of one local-to-true quadratic schedule. -/
structure LocalMartingaleQuadraticSchedulePair
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (n m : Nat) where
  rho : Omega → NNReal
  rho_eq : rho = fun omega => min (C.localizer n omega) (C.localizer m omega)
  commonCertificate :
    SquareIntegrableMartingaleQuadraticJ1Certificate F mu
      (MeasureTheory.stoppedProcess M
        (fun omega => (rho omega : WithTop NNReal))) (C.horizon n)
  variation_indistinguishable :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (C.coordinate n).quadraticData.variation
        (fun omega => (rho omega : WithTop NNReal)))
      (MeasureTheory.stoppedProcess
        (C.coordinate m).quadraticData.variation
        (fun omega => (rho omega : WithTop NNReal)))
  commonRoot_ae_eq_left :
    squareIntegrableMartingaleQuadraticRoot
        commonCertificate.quadraticData =ᵐ[mu]
      (fun omega => Real.sqrt
        ((C.coordinate n).quadraticData.variation (rho omega) omega))
  commonRoot_ae_eq_right :
    squareIntegrableMartingaleQuadraticRoot
        commonCertificate.quadraticData =ᵐ[mu]
      (fun omega => Real.sqrt
        ((C.coordinate m).quadraticData.variation (rho omega) omega))
  stoppedRoot_ae_eq :
    (fun omega => Real.sqrt
      ((C.coordinate n).quadraticData.variation (rho omega) omega)) =ᵐ[mu]
      (fun omega => Real.sqrt
        ((C.coordinate m).quadraticData.variation (rho omega) omega))
  commonRootCost_eq_left :
    squareIntegrableMartingaleQuadraticRootCost
        commonCertificate.quadraticData =
      ∫⁻ omega, ENNReal.ofReal (Real.sqrt
        ((C.coordinate n).quadraticData.variation (rho omega) omega)) ∂mu
  commonRootCost_eq_right :
    squareIntegrableMartingaleQuadraticRootCost
        commonCertificate.quadraticData =
      ∫⁻ omega, ENNReal.ofReal (Real.sqrt
        ((C.coordinate m).quadraticData.variation (rho omega) omega)) ∂mu
  stoppedRootCost_eq :
    (∫⁻ omega, ENNReal.ofReal (Real.sqrt
      ((C.coordinate n).quadraticData.variation (rho omega) omega)) ∂mu) =
      ∫⁻ omega, ENNReal.ofReal (Real.sqrt
        ((C.coordinate m).quadraticData.variation (rho omega) omega)) ∂mu

/-! ## The common certificate -/

private theorem exists_commonCertificate
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (n m : Nat) :
    Nonempty (SquareIntegrableMartingaleQuadraticJ1Certificate F mu
      (MeasureTheory.stoppedProcess M
        (fun omega =>
          (min (C.localizer n omega) (C.localizer m omega) : WithTop NNReal)))
      (C.horizon n)) := by
  let rho : Omega → NNReal := fun omega =>
    min (C.localizer n omega) (C.localizer m omega)
  let tauTop : Omega → WithTop NNReal := fun omega =>
    (rho omega : WithTop NNReal)
  let N : Process Omega :=
    MeasureTheory.stoppedProcess M
      (fun omega => (C.localizer n omega : WithTop NNReal))
  let Common : Process Omega :=
    MeasureTheory.stoppedProcess M tauTop
  have hTau : IsStoppingTime F tauTop := by
    have hMin := (C.localizer_isStoppingTime n).min
      (C.localizer_isStoppingTime m)
    simpa only [rho, tauTop, WithTop.coe_min] using hMin
  have hTauLeN : ∀ omega, tauTop omega ≤
      (C.localizer n omega : WithTop NNReal) := by
    intro omega
    rw [show tauTop omega =
      min (C.localizer n omega : WithTop NNReal)
        (C.localizer m omega : WithTop NNReal) by
      simp [tauTop, rho]]
    exact min_le_left _ _
  have hTauLeM : ∀ omega, tauTop omega ≤
      (C.localizer m omega : WithTop NNReal) := by
    intro omega
    rw [show tauTop omega =
      min (C.localizer n omega : WithTop NNReal)
        (C.localizer m omega : WithTop NNReal) by
      simp [tauTop, rho]]
    exact min_le_right _ _
  have hTauLeHorizonN : ∀ omega, rho omega ≤ C.horizon n := by
    intro omega
    exact (min_le_left _ _).trans (C.localizer_le_horizon n omega)
  have hNMartingale : Martingale N F mu := by
    simpa only [N] using (C.coordinate n).source_martingale
  have hCommonMartingale : Martingale Common F mu := by
    have hStopped :=
      RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
        hNMartingale hTau (C.coordinate n).source_rightContinuous
    have hNested : MeasureTheory.stoppedProcess N tauTop = Common := by
      dsimp [N, Common]
      exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
        (u := M)
        (τ := fun omega => (C.localizer n omega : WithTop NNReal))
        (σ := tauTop) hTauLeN
    rw [hNested] at hStopped
    exact hStopped
  have hCommonRight : ∀ omega t,
      ContinuousWithinAt (Common · omega) (Ici t) t := by
    dsimp [Common]
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      M hMRight
  have hCommonLeft : ProcessHasLeftLimits Common := by
    dsimp [Common]
    exact hMLeft.stoppedProcess tauTop
  have hNConstant : ∀ omega,
      N (C.horizon n + 1) omega = N (C.horizon n) omega := by
    intro omega
    change MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer n omega : WithTop NNReal))
        (C.horizon n + 1) omega =
      MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer n omega : WithTop NNReal))
        (C.horizon n) omega
    rw [stoppedProcess_coe_apply M (C.localizer n)
      (C.horizon n + 1) omega,
      stoppedProcess_coe_apply M (C.localizer n)
        (C.horizon n) omega]
    rw [min_eq_right ((C.localizer_le_horizon n omega).trans (by norm_num)),
      min_eq_right (C.localizer_le_horizon n omega)]
  have hCommonTerminalMemLp : MemLp (Common (C.horizon n))
      (2 : ENNReal) mu := by
    have hStop :=
      HorizonFactorialGrid.martingale_stoppedProcess_memLp_two_and_integral_sq_le
        hNMartingale (C.coordinate n).source_rightContinuous hTau
        (C.coordinate n).source_terminal_memLp_two hNConstant
    have hNested : MeasureTheory.stoppedProcess N tauTop = Common := by
      dsimp [N, Common]
      exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
        (u := M)
        (τ := fun omega => (C.localizer n omega : WithTop NNReal))
        (σ := tauTop) hTauLeN
    rw [hNested] at hStop
    exact hStop.1
  obtain ⟨hCertificate⟩ :=
    exists_squareIntegrableMartingaleQuadraticJ1Certificate
      hUsual hCommonMartingale hCommonRight hCommonTerminalMemLp
  exact ⟨by
    simpa only [rho, Common, tauTop, WithTop.coe_min] using hCertificate⟩

/-! ## Pairwise process and root compatibility -/

/-- Any two schedule coordinates have compatible stored quadratic variations
after their common finite minimum stop.  A single common stopped true `M²`
certificate is used for both comparisons; neither stored coordinate data is
reselected. -/
theorem exists_localMartingaleQuadraticSchedulePair
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (n m : Nat) :
    Nonempty (LocalMartingaleQuadraticSchedulePair C n m) := by
  let rho : Omega → NNReal := fun omega =>
    min (C.localizer n omega) (C.localizer m omega)
  let tauTop : Omega → WithTop NNReal := fun omega =>
    (rho omega : WithTop NNReal)
  have hTau : IsStoppingTime F tauTop := by
    have hMin := (C.localizer_isStoppingTime n).min
      (C.localizer_isStoppingTime m)
    simpa only [rho, tauTop, WithTop.coe_min] using hMin
  have hTauLeN : ∀ omega, tauTop omega ≤
      (C.localizer n omega : WithTop NNReal) := by
    intro omega
    rw [show tauTop omega =
      min (C.localizer n omega : WithTop NNReal)
        (C.localizer m omega : WithTop NNReal) by
      simp [tauTop, rho]]
    exact min_le_left _ _
  have hTauLeM : ∀ omega, tauTop omega ≤
      (C.localizer m omega : WithTop NNReal) := by
    intro omega
    rw [show tauTop omega =
      min (C.localizer n omega : WithTop NNReal)
        (C.localizer m omega : WithTop NNReal) by
      simp [tauTop, rho]]
    exact min_le_right _ _
  have hTauLeHorizonN : ∀ omega, rho omega ≤ C.horizon n := by
    intro omega
    exact (min_le_left _ _).trans (C.localizer_le_horizon n omega)
  have hTauLeHorizonM : ∀ omega, rho omega ≤ C.horizon m := by
    intro omega
    exact (min_le_right _ _).trans (C.localizer_le_horizon m omega)
  obtain ⟨hCommonCertificate⟩ :=
    exists_commonCertificate hUsual hMRight hMLeft C n m
  let Common : Process Omega :=
    MeasureTheory.stoppedProcess M tauTop
  have hN : Martingale
      (MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer n omega : WithTop NNReal))) F mu :=
    (C.coordinate n).source_martingale
  have hR : Martingale
      (MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer m omega : WithTop NNReal))) F mu :=
    (C.coordinate m).source_martingale
  have hCommonMartingale : Martingale Common F mu := by
    dsimp [Common]
    have hStopped :=
      RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
        hN hTau (C.coordinate n).source_rightContinuous
    have hNested : MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess M
          (fun omega => (C.localizer n omega : WithTop NNReal))) tauTop =
        MeasureTheory.stoppedProcess M tauTop := by
      exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
        (u := M)
        (τ := fun omega => (C.localizer n omega : WithTop NNReal))
        (σ := tauTop) hTauLeN
    rw [hNested] at hStopped
    exact hStopped
  have hCommonRight : ∀ omega t,
      ContinuousWithinAt (Common · omega) (Ici t) t := by
    dsimp [Common]
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      M hMRight
  have hCommonLeft : ProcessHasLeftLimits Common := by
    dsimp [Common]
    exact hMLeft.stoppedProcess tauTop
  have hCommonDefN : ProcessIndistinguishable mu Common
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess M
          (fun omega => (C.localizer n omega : WithTop NNReal))) tauTop) := by
    have hNested : MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess M
          (fun omega => (C.localizer n omega : WithTop NNReal))) tauTop =
        Common := by
      dsimp [Common]
      exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
        (u := M)
        (τ := fun omega => (C.localizer n omega : WithTop NNReal))
        (σ := tauTop) hTauLeN
    rw [hNested]
    exact ProcessIndistinguishable.refl mu Common
  have hCommonDefM : ProcessIndistinguishable mu Common
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess M
          (fun omega => (C.localizer m omega : WithTop NNReal))) tauTop) := by
    have hNested : MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess M
          (fun omega => (C.localizer m omega : WithTop NNReal))) tauTop =
        Common := by
      dsimp [Common]
      exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
        (u := M)
        (τ := fun omega => (C.localizer m omega : WithTop NNReal))
        (σ := tauTop) hTauLeM
    rw [hNested]
    exact ProcessIndistinguishable.refl mu Common
  have hLeftConsistency :
      ProcessIndistinguishable mu hCommonCertificate.quadraticData.variation
        (MeasureTheory.stoppedProcess
          (C.coordinate n).quadraticData.variation tauTop) :=
    variation_processIndistinguishable_of_bounded_stop
      (M := MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      (N := Common) (T := C.horizon n) (U := C.horizon n)
      hUsual hN (C.coordinate n).source_rightContinuous
      (hMLeft.stoppedProcess
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      hCommonMartingale hCommonRight hCommonLeft
      (C.coordinate n).quadraticData hCommonCertificate.quadraticData
      rho hTau hTauLeHorizonN hTauLeHorizonN hCommonDefN
  have hRightConsistency :
      ProcessIndistinguishable mu hCommonCertificate.quadraticData.variation
        (MeasureTheory.stoppedProcess
          (C.coordinate m).quadraticData.variation tauTop) :=
    variation_processIndistinguishable_of_bounded_stop
      (M := MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer m omega : WithTop NNReal)))
      (N := Common) (T := C.horizon m) (U := C.horizon n)
      hUsual hR (C.coordinate m).source_rightContinuous
      (hMLeft.stoppedProcess
        (fun omega => (C.localizer m omega : WithTop NNReal)))
      hCommonMartingale hCommonRight hCommonLeft
      (C.coordinate m).quadraticData hCommonCertificate.quadraticData
      rho hTau hTauLeHorizonM hTauLeHorizonN hCommonDefM
  have hVariation :
      ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess
          (C.coordinate n).quadraticData.variation tauTop)
        (MeasureTheory.stoppedProcess
          (C.coordinate m).quadraticData.variation tauTop) :=
    hLeftConsistency.symm.trans hRightConsistency
  have hRootLeft :=
    squareIntegrableMartingaleQuadraticRoot_ae_eq_stopped_of_bounded_stop
      (M := MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      (N := Common) (T := C.horizon n) (U := C.horizon n)
      hUsual hN (C.coordinate n).source_rightContinuous
      (hMLeft.stoppedProcess
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      hCommonMartingale hCommonRight hCommonLeft
      (C.coordinate n).quadraticData hCommonCertificate.quadraticData
      rho hTau hTauLeHorizonN hTauLeHorizonN hCommonDefN
  have hRootRight :=
    squareIntegrableMartingaleQuadraticRoot_ae_eq_stopped_of_bounded_stop
      (M := MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer m omega : WithTop NNReal)))
      (N := Common) (T := C.horizon m) (U := C.horizon n)
      hUsual hR (C.coordinate m).source_rightContinuous
      (hMLeft.stoppedProcess
        (fun omega => (C.localizer m omega : WithTop NNReal)))
      hCommonMartingale hCommonRight hCommonLeft
      (C.coordinate m).quadraticData hCommonCertificate.quadraticData
      rho hTau hTauLeHorizonM hTauLeHorizonN hCommonDefM
  have hStoppedRoot :
      (fun omega => Real.sqrt
        ((C.coordinate n).quadraticData.variation (rho omega) omega)) =ᵐ[mu]
        (fun omega => Real.sqrt
          ((C.coordinate m).quadraticData.variation (rho omega) omega)) := by
    filter_upwards [hVariation.eventuallyEq_at (C.horizon n)] with omega hOmega
    rw [stoppedProcess_coe_apply (C.coordinate n).quadraticData.variation
      rho (C.horizon n) omega,
      stoppedProcess_coe_apply (C.coordinate m).quadraticData.variation
        rho (C.horizon n) omega,
      min_eq_right (hTauLeHorizonN omega)] at hOmega
    exact congrArg Real.sqrt hOmega
  have hCommonCostLeft :
      squareIntegrableMartingaleQuadraticRootCost
          hCommonCertificate.quadraticData =
        ∫⁻ omega, ENNReal.ofReal (Real.sqrt
          ((C.coordinate n).quadraticData.variation (rho omega) omega)) ∂mu := by
    unfold squareIntegrableMartingaleQuadraticRootCost
    apply lintegral_congr_ae
    filter_upwards [hRootLeft] with omega hOmega
    rw [hOmega]
  have hCommonCostRight :
      squareIntegrableMartingaleQuadraticRootCost
          hCommonCertificate.quadraticData =
        ∫⁻ omega, ENNReal.ofReal (Real.sqrt
          ((C.coordinate m).quadraticData.variation (rho omega) omega)) ∂mu := by
    unfold squareIntegrableMartingaleQuadraticRootCost
    apply lintegral_congr_ae
    filter_upwards [hRootRight] with omega hOmega
    rw [hOmega]
  have hStoppedCost :
      (∫⁻ omega, ENNReal.ofReal (Real.sqrt
        ((C.coordinate n).quadraticData.variation (rho omega) omega)) ∂mu) =
        ∫⁻ omega, ENNReal.ofReal (Real.sqrt
          ((C.coordinate m).quadraticData.variation (rho omega) omega)) ∂mu := by
    apply lintegral_congr_ae
    filter_upwards [hStoppedRoot] with omega hOmega
    rw [hOmega]
  exact ⟨{
    rho := rho
    rho_eq := by rfl
    commonCertificate := by
      simpa only [rho, tauTop, WithTop.coe_min] using hCommonCertificate
    variation_indistinguishable := hVariation
    commonRoot_ae_eq_left := hRootLeft
    commonRoot_ae_eq_right := hRootRight
    stoppedRoot_ae_eq := hStoppedRoot
    commonRootCost_eq_left := hCommonCostLeft
    commonRootCost_eq_right := hCommonCostRight
    stoppedRootCost_eq := hStoppedCost }⟩

end LocalMartingaleQuadratic

end FTAPTheorem42
