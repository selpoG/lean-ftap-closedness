/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticLocalizingScheduleGluing
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticJump

/-!
# Quadratic variation along a localizing schedule

Identify the glued quadratic process on each stopped coordinate and establish its
local martingale and jump identities.
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

/-! ## Coordinate residuals -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem stoppedSource_schedule_stop_eq
    [F.IsRightContinuous]
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (n : Nat) (t : NNReal) (omega : Omega) :
    MeasureTheory.stoppedProcess
        (deterministicallyStoppedProcess
          (MeasureTheory.stoppedProcess M
            (fun omega => (C.localizer n omega : WithTop NNReal)))
          (C.horizon n))
        (fun omega => (C.localizer n omega : WithTop NNReal)) t omega =
      MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer n omega : WithTop NNReal)) t omega := by
  have hTauLe : ∀ omega, (C.localizer n omega : WithTop NNReal) ≤
      (C.horizon n : WithTop NNReal) := by
    intro omega
    exact WithTop.coe_le_coe.mpr (C.localizer_le_horizon n omega)
  have hNested :
      MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess M
            (fun omega => (C.localizer n omega : WithTop NNReal)))
          (fun omega => (C.horizon n : WithTop NNReal)) =
        MeasureTheory.stoppedProcess M
          (fun omega => (C.localizer n omega : WithTop NNReal)) := by
    exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_left
      (u := M)
      (τ := fun omega => (C.localizer n omega : WithTop NNReal))
      (σ := fun omega => (C.horizon n : WithTop NNReal)) hTauLe
  have hOuter :
      MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess
            (MeasureTheory.stoppedProcess M
              (fun omega => (C.localizer n omega : WithTop NNReal)))
            (fun omega => (C.horizon n : WithTop NNReal)))
          (fun omega => (C.localizer n omega : WithTop NNReal)) =
        MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess M
            (fun omega => (C.localizer n omega : WithTop NNReal)))
          (fun omega => (C.localizer n omega : WithTop NNReal)) := by
    exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      (u := MeasureTheory.stoppedProcess M
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      (τ := fun omega => (C.horizon n : WithTop NNReal))
      (σ := fun omega => (C.localizer n omega : WithTop NNReal)) hTauLe
  have hSelf :
      MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess M
            (fun omega => (C.localizer n omega : WithTop NNReal)))
          (fun omega => (C.localizer n omega : WithTop NNReal)) =
        MeasureTheory.stoppedProcess M
          (fun omega => (C.localizer n omega : WithTop NNReal)) := by
    exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_left
      (u := M)
      (τ := fun omega => (C.localizer n omega : WithTop NNReal))
      (σ := fun omega => (C.localizer n omega : WithTop NNReal)) le_rfl
  change MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess M
          (fun omega => (C.localizer n omega : WithTop NNReal)))
        (fun omega => (C.horizon n : WithTop NNReal)))
      (fun omega => (C.localizer n omega : WithTop NNReal)) t omega = _
  rw [hOuter, hSelf]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem coordinate_rawVariation_stop_eq
    [F.IsRightContinuous]
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (n : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (C.coordinate n).quadraticData.variation
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      (fun t omega =>
        (MeasureTheory.stoppedProcess M
          (fun omega => (C.localizer n omega : WithTop NNReal))) t omega ^ 2 -
          (MeasureTheory.stoppedProcess M
            (fun omega => (C.localizer n omega : WithTop NNReal))) 0 omega ^ 2 -
          MeasureTheory.stoppedProcess
            (C.coordinate n).quadraticData.martingalePart
            (fun omega => (C.localizer n omega : WithTop NNReal)) t omega) := by
  let tau : Omega → NNReal := C.localizer n
  let tauTop : Omega → WithTop NNReal := fun omega => (tau omega : WithTop NNReal)
  let N : Process Omega := MeasureTheory.stoppedProcess M tauTop
  let T : NNReal := C.horizon n
  let Y : Process Omega := (C.coordinate n).quadraticData.martingalePart
  have hRaw := (C.coordinate n).quadraticData.variation_indistinguishable_raw
  have hRawStopped := hRaw.stoppedProcess tauTop
  have hSource : ∀ t omega,
      MeasureTheory.stoppedProcess
          (deterministicallyStoppedProcess N T)
          tauTop t omega = N t omega := by
    intro t omega
    exact stoppedSource_schedule_stop_eq C n t omega
  filter_upwards [hRawStopped] with omega hω
  intro t
  have hFormula := stoppedProcess_rawVariation_eq N T Y tau omega t
  change MeasureTheory.stoppedProcess
      (C.coordinate n).quadraticData.variation tauTop t omega = _
  rw [hω t, hFormula, hSource t omega, hSource 0 omega]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem coordinate_residual_stop_eq
    [F.IsRightContinuous]
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (Q : Process Omega)
    (hQStopped : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess Q
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      (MeasureTheory.stoppedProcess
        (C.coordinate n).quadraticData.variation
        (fun omega => (C.localizer n omega : WithTop NNReal))))
    (n : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (fun t omega => M t omega ^ 2 - M 0 omega ^ 2 - Q t omega)
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      (MeasureTheory.stoppedProcess
        (C.coordinate n).quadraticData.martingalePart
        (fun omega => (C.localizer n omega : WithTop NNReal))) := by
  let tau : Omega → NNReal := C.localizer n
  let tauTop : Omega → WithTop NNReal := fun omega => (tau omega : WithTop NNReal)
  let N : Process Omega := MeasureTheory.stoppedProcess M tauTop
  let Y : Process Omega := (C.coordinate n).quadraticData.martingalePart
  let D : Process Omega := (C.coordinate n).quadraticData.variation
  have hQ := hQStopped n
  have hRaw := coordinate_rawVariation_stop_eq C n
  filter_upwards [hQ, hRaw] with omega hQω hRawω
  intro t
  change (M (min t (tau omega)) omega) ^ 2 - M 0 omega ^ 2 -
      Q (min t (tau omega)) omega =
    Y (min t (tau omega)) omega
  have hN : N (min t (tau omega)) omega =
      M (min t (tau omega)) omega := by
    change MeasureTheory.stoppedProcess M tauTop
      (min t (tau omega)) omega = _
    rw [stoppedProcess_coe_apply M tau (min t (tau omega)) omega]
    simp only [min_assoc, min_self]
  have hNZero : N 0 omega = M 0 omega := by
    change MeasureTheory.stoppedProcess M tauTop 0 omega = _
    rw [stoppedProcess_coe_apply M tau 0 omega]
    simp
  have hQωt := hQω t
  have hRawωt := hRawω t
  have hQAt : Q (min t (tau omega)) omega =
      D (min t (tau omega)) omega := by
    simpa only [stoppedProcess_coe_apply] using hQωt
  have hRawAt : D (min t (tau omega)) omega =
      N (min t (tau omega)) omega ^ 2 - N 0 omega ^ 2 -
        Y (min t (tau omega)) omega := by
    have hRawAtM := hRawωt
    rw [stoppedProcess_coe_apply D tau t omega,
      stoppedProcess_coe_apply M tau t omega,
      stoppedProcess_coe_apply M tau 0 omega,
      stoppedProcess_coe_apply Y tau t omega] at hRawAtM
    calc
      D (min t (tau omega)) omega =
          M (min t (tau omega)) omega ^ 2 -
            M (min 0 (tau omega)) omega ^ 2 -
              Y (min t (tau omega)) omega := hRawAtM
      _ = N (min t (tau omega)) omega ^ 2 - N 0 omega ^ 2 -
          Y (min t (tau omega)) omega := by
        have hmin : min (0 : NNReal) (tau omega) = 0 :=
          min_eq_left bot_le
        rw [hN, hNZero, hmin]
  calc
    M (min t (tau omega)) omega ^ 2 - M 0 omega ^ 2 -
        Q (min t (tau omega)) omega =
      N (min t (tau omega)) omega ^ 2 - N 0 omega ^ 2 -
        D (min t (tau omega)) omega := by
          rw [hN, hNZero, hQAt]
    _ = Y (min t (tau omega)) omega := by
      linarith [hRawAt]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem stoppedResidual_stronglyAdapted
    [F.IsRightContinuous]
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (Q : Process Omega)
    (hQAdapted : StronglyAdapted F Q)
    (hQRight : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t)
    (n : Nat) :
    StronglyAdapted F
      (MeasureTheory.stoppedProcess
        (fun t omega => M t omega ^ 2 - M 0 omega ^ 2 - Q t omega)
        (fun omega => (C.localizer n omega : WithTop NNReal))) := by
  let tau : Omega → NNReal := C.localizer n
  let tauTop : Omega → WithTop NNReal := fun omega => (tau omega : WithTop NNReal)
  let R : Process Omega := fun t omega => M t omega ^ 2 - M 0 omega ^ 2 - Q t omega
  have hTau : IsStoppingTime F tauTop := by
    simpa only [tauTop, tau] using C.localizer_isStoppingTime n
  have hNMartingale : Martingale
      (MeasureTheory.stoppedProcess M tauTop) F mu := by
    simpa only [tauTop, tau] using (C.coordinate n).source_martingale
  have hQStoppedAdapted : StronglyAdapted F
      (MeasureTheory.stoppedProcess Q tauTop) :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hQAdapted hTau hQRight
  have hFormula (t : NNReal) :
      (fun omega => MeasureTheory.stoppedProcess R tauTop t omega) =
        (fun omega =>
          MeasureTheory.stoppedProcess M tauTop t omega ^ 2 -
            MeasureTheory.stoppedProcess M tauTop 0 omega ^ 2 -
              MeasureTheory.stoppedProcess Q tauTop t omega) := by
    funext omega
    rw [stoppedProcess_coe_apply R tau t omega,
      stoppedProcess_coe_apply M tau t omega,
      stoppedProcess_coe_apply M tau 0 omega,
      stoppedProcess_coe_apply Q tau t omega]
    dsimp only [R]
    have hmin : min (0 : NNReal) (tau omega) = 0 := min_eq_left bot_le
    rw [hmin]
  intro t
  change StronglyMeasurable[F t]
    (fun omega => MeasureTheory.stoppedProcess R tauTop t omega)
  rw [hFormula t]
  exact ((hNMartingale.stronglyAdapted t).pow 2).sub
    (((hNMartingale.stronglyAdapted 0).mono (F.mono bot_le)).pow 2) |>.sub
      (hQStoppedAdapted t)

/-! ## Residual local-martingale semantics -/

theorem gluedQuadraticVariation_residual_isLocalMartingale
    [F.IsRightContinuous]
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (Q : Process Omega)
    (hQAdapted : StronglyAdapted F Q)
    (hQRight : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t)
    (hQStopped : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess Q
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      (MeasureTheory.stoppedProcess
        (C.coordinate n).quadraticData.variation
        (fun omega => (C.localizer n omega : WithTop NNReal)))) :
    LocalMartingale
      (fun t omega => M t omega ^ 2 - M 0 omega ^ 2 - Q t omega) F mu := by
  let tau : Nat → Omega → WithTop NNReal := fun n omega =>
    (C.localizer n omega : WithTop NNReal)
  have hTau : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    simpa only [tau] using C.isLocalizingSequence
  refine ⟨tau, hTau, fun n => ?_⟩
  let B : Set Omega := {omega | (⊥ : WithTop NNReal) < tau n omega}
  have hB : MeasurableSet[F 0] B := by
    have hEq : B = {omega | tau n omega <= (0 : NNReal)}ᶜ := by
      ext omega
      simp only [B, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
      rw [show (⊥ : WithTop NNReal) = ((0 : NNReal) : WithTop NNReal) by rfl]
    rw [hEq]
    exact (hTau.isStoppingTime n).measurableSet_le 0 |>.compl
  let Y : Process Omega :=
    (C.coordinate n).quadraticData.martingalePart
  have hYStopped : Martingale
      (MeasureTheory.stoppedProcess Y (tau n)) F mu := by
    exact RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      (C.coordinate n).quadraticData.martingalePart_isMartingale
      (hTau.isStoppingTime n)
      (C.coordinate n).quadraticData.martingalePart_rightContinuous
  have hIndicator : Martingale
      (fun t omega => B.indicator
        (MeasureTheory.stoppedProcess Y (tau n) t) omega) F mu :=
    hYStopped.indicator_of_measurableSet_bot hB
  have hTargetAdapted : StronglyAdapted F
      (MeasureTheory.stoppedProcess
        (fun t omega => B.indicator
          (fun omega => M t omega ^ 2 - M 0 omega ^ 2 - Q t omega) omega)
        (tau n)) := by
    rw [MeasureTheory.stoppedProcess_indicator_comm']
    intro t
    have hRStopped := stoppedResidual_stronglyAdapted C Q hQAdapted hQRight n
    exact (hRStopped t).indicator ((F.mono bot_le) B hB)
  apply hIndicator.congr hTargetAdapted
  intro t
  have hCoordinate := coordinate_residual_stop_eq C Q hQStopped n
  have hAt := hCoordinate.eventuallyEq_at t
  filter_upwards [hAt] with omega hOmega
  rw [MeasureTheory.stoppedProcess_indicator_comm']
  change B.indicator (MeasureTheory.stoppedProcess Y (tau n) t) omega =
    B.indicator
      (MeasureTheory.stoppedProcess
        (fun t omega => M t omega ^ 2 - M 0 omega ^ 2 - Q t omega)
        (tau n) t) omega
  by_cases hMem : omega ∈ B
  · simp only [Set.indicator_of_mem hMem]
    exact hOmega.symm
  · simp only [Set.indicator_of_notMem hMem]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem coordinateVariation_hasLeftLimits
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (n : Nat) :
    ProcessHasLeftLimits (C.coordinate n).quadraticData.variation := by
  have hNonnegative : ∀ omega t,
      0 ≤ (C.coordinate n).quadraticData.variation t omega := by
    intro omega t
    have hZero : (C.coordinate n).quadraticData.variation 0 omega = 0 := by
      simpa using congrFun (C.coordinate n).quadraticData.variation_zero omega
    have hMono :=
      (C.coordinate n).quadraticData.variation_monotone omega
        (show (0 : NNReal) ≤ t from bot_le)
    change (C.coordinate n).quadraticData.variation 0 omega ≤
      (C.coordinate n).quadraticData.variation t omega at hMono
    rw [hZero] at hMono
    exact hMono
  have hVariation :=
    HorizonFactorialGrid.boundedVariationOn_of_monotone_nonnegative_constantAfter
      hNonnegative
      (C.coordinate n).quadraticData.variation_monotone
      (C.coordinate n).quadraticData.variation_constantAfter
  intro omega t
  exact (hVariation omega).tendsto_leftLim t

/-! ## Global jump semantics -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem gluedQuadraticVariation_leftJump_eq_sq
    [F.IsRightContinuous]
    (hMLeft : ProcessHasLeftLimits M)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (Q : Process Omega)
    (hQLeft : ProcessHasLeftLimits Q)
    (hQStopped : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess Q
        (fun omega => (C.localizer n omega : WithTop NNReal)))
      (MeasureTheory.stoppedProcess
        (C.coordinate n).quadraticData.variation
        (fun omega => (C.localizer n omega : WithTop NNReal)))) :
    ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump Q t omega = (processLeftJump M t omega) ^ 2 := by
  let tau : Nat → Omega → WithTop NNReal := fun n omega =>
    (C.localizer n omega : WithTop NNReal)
  have hTau : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    simpa only [tau] using C.isLocalizingSequence
  have hStoppedAll : ∀ᵐ omega ∂mu, ∀ n t,
      MeasureTheory.stoppedProcess Q (tau n) t omega =
        MeasureTheory.stoppedProcess
          (C.coordinate n).quadraticData.variation (tau n) t omega := by
    rw [ae_all_iff]
    intro n
    exact hQStopped n
  have hJumpAll : ∀ᵐ omega ∂mu, ∀ n t,
      processLeftJump
          (C.coordinate n).quadraticData.variation t omega =
        processLeftJump
          (deterministicallyStoppedProcess
            (MeasureTheory.stoppedProcess M (tau n)) (C.horizon n))
          t omega ^ 2 := by
    rw [ae_all_iff]
    intro n
    simpa only [tau] using
      (C.coordinate n).quadraticData.processLeftJump_variation_eq_sq
        (hMLeft.stoppedProcess (tau n))
  filter_upwards [hTau.tendsto_top, hStoppedAll, hJumpAll]
      with omega hTop hStopped hJump
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  intro t
  obtain ⟨n, hn⟩ := (hTop (t + 1)).exists
  have htn : (t : WithTop NNReal) ≤ tau n omega := by
    exact (WithTop.coe_le_coe.mpr (by linarith : t ≤ t + 1)).trans hn.le
  let D : Process Omega := (C.coordinate n).quadraticData.variation
  let N : Process Omega := MeasureTheory.stoppedProcess M (tau n)
  let X : Process Omega :=
    deterministicallyStoppedProcess N (C.horizon n)
  have hDLeft : ProcessHasLeftLimits D :=
    coordinateVariation_hasLeftLimits C n
  have hNLeft : ProcessHasLeftLimits N := hMLeft.stoppedProcess (tau n)
  have hXLeft : ProcessHasLeftLimits X :=
    hNLeft.stoppedProcess (fun _ : Omega => (C.horizon n : WithTop NNReal))
  have hXStopped :
      MeasureTheory.stoppedProcess X (tau n) = N := by
    funext s omega'
    exact stoppedSource_schedule_stop_eq C n s omega'
  have hXJump : processLeftJump X t omega =
      processLeftJump N t omega := by
    have hStopJump := processLeftJump_stoppedProcess_eq_of_le
      X hXLeft (tau n) t omega htn
    calc
      processLeftJump X t omega =
          processLeftJump (MeasureTheory.stoppedProcess X (tau n)) t omega :=
        hStopJump.symm
      _ = processLeftJump N t omega := by rw [hXStopped]
  have hNJump : processLeftJump N t omega =
      processLeftJump M t omega :=
    processLeftJump_stoppedProcess_eq_of_le M hMLeft (tau n) t omega htn
  have hStopJump : processLeftJump
      (MeasureTheory.stoppedProcess Q (tau n)) t omega =
        processLeftJump (MeasureTheory.stoppedProcess D (tau n)) t omega := by
    have hPath : (fun s => MeasureTheory.stoppedProcess Q (tau n) s omega) =
        (fun s => MeasureTheory.stoppedProcess D (tau n) s omega) := by
      funext s
      exact hStopped n s
    unfold processLeftJump
    rw [hStopped n t, hPath]
  have hQJump := processLeftJump_stoppedProcess_eq_of_le
    Q hQLeft (tau n) t omega htn
  have hDJump := processLeftJump_stoppedProcess_eq_of_le
    D hDLeft (tau n) t omega htn
  have hCoordinateJump : processLeftJump D t omega =
      (processLeftJump X t omega) ^ 2 := by
    simpa only [D, X] using hJump n t
  calc
    processLeftJump Q t omega =
        processLeftJump (MeasureTheory.stoppedProcess Q (tau n)) t omega :=
      hQJump.symm
    _ = processLeftJump (MeasureTheory.stoppedProcess D (tau n)) t omega := hStopJump
    _ = processLeftJump D t omega := hDJump
    _ = (processLeftJump X t omega) ^ 2 := hCoordinateJump
    _ = (processLeftJump M t omega) ^ 2 := by rw [hXJump, hNJump]

/-! ## Public semantic certificate -/

/-- The global optional quadratic-variation process obtained from a supplied
locally square-integrable schedule.  The certificate records the actual
construction and its semantic consequences; none of these consequences is an
input field of the schedule. -/
structure GluedQuadraticVariationCertificate
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M)) where
  variation : Process Omega
  variation_isStronglyAdapted : StronglyAdapted F variation
  variation_rightContinuous : ∀ omega t,
    ContinuousWithinAt (variation · omega) (Ici t) t
  variation_hasLeftLimits : ProcessHasLeftLimits variation
  variation_monotone : ∀ omega, Monotone (variation · omega)
  variation_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (variation · omega) Set.univ
  variation_zero : variation 0 = 0
  variation_stoppedCoordinate : ∀ n, ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess variation
      (fun omega => (C.localizer n omega : WithTop NNReal)))
    (MeasureTheory.stoppedProcess
      (C.coordinate n).quadraticData.variation
      (fun omega => (C.localizer n omega : WithTop NNReal)))
  squareResidual_isLocalMartingale : LocalMartingale
    (fun t omega => M t omega ^ 2 - M 0 omega ^ 2 - variation t omega) F mu
  leftJump_eq_sq : ∀ᵐ omega ∂mu, ∀ t,
    processLeftJump variation t omega = (processLeftJump M t omega) ^ 2

/-- The supplied gluing theorem carries the same global process into the
quadratic-variation semantic certificate. -/
theorem exists_gluedQuadraticVariationCertificate
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M)) :
    Nonempty (GluedQuadraticVariationCertificate C) := by
  obtain ⟨Q, hQAdapted, hQRight, hQLeft, hQMonotone,
      hQVariation, hQZero, hQStopped⟩ :=
    exists_gluedQuadraticVariation hUsual hMRight hMLeft C
  exact ⟨{
    variation := Q
    variation_isStronglyAdapted := hQAdapted
    variation_rightContinuous := hQRight
    variation_hasLeftLimits := hQLeft
    variation_monotone := hQMonotone
    variation_locallyBoundedVariation := hQVariation
    variation_zero := hQZero
    variation_stoppedCoordinate := hQStopped
    squareResidual_isLocalMartingale :=
      gluedQuadraticVariation_residual_isLocalMartingale
        C Q hQAdapted hQRight hQStopped
    leftJump_eq_sq := gluedQuadraticVariation_leftJump_eq_sq
      hMLeft C Q hQLeft hQStopped }⟩

end LocalMartingaleQuadratic

end FTAPTheorem42
