/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticLocalizingSchedule
import FTAPTheorem42.Stochastic.FiniteVariation.CompatibleLocalFiniteVariationGluing

/-!
# Gluing a supplied local quadratic-variation schedule

The quadratic variation stored by a finite-horizon square-integrable
certificate is an adapted càdlàg increasing process.  It is not, in general,
predictable.  This module therefore glues the stored variation processes as
ordinary adapted processes, using their process-level compatibility on the
overlaps of the supplied localizing sequence.

The result is deliberately conditional on a supplied locally square-integrable
schedule.  It does not construct such a schedule for an arbitrary local
martingale.
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

namespace LocalMartingaleQuadraticSchedule

/-- The stored variations of two schedule coordinates agree after their
common finite minimum stop.  This is the small projection API consumed by the
gluing theorem; the larger pair certificate is unpacked only here. -/
theorem variation_compatible
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M))
    (n m : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (C.coordinate n).quadraticData.variation
        (fun omega =>
          (min (C.localizer n omega) (C.localizer m omega) : WithTop NNReal)))
      (MeasureTheory.stoppedProcess
        (C.coordinate m).quadraticData.variation
        (fun omega =>
          (min (C.localizer n omega) (C.localizer m omega) : WithTop NNReal))) := by
  obtain ⟨hPair⟩ := exists_localMartingaleQuadraticSchedulePair
    hUsual hMRight hMLeft C n m
  have hVariation := hPair.variation_indistinguishable
  rw [hPair.rho_eq] at hVariation
  simpa only [WithTop.coe_min] using hVariation

end LocalMartingaleQuadraticSchedule

/-! ## The supplied schedule as a compatible process family -/

/-- A supplied locally square-integrable schedule yields one global adapted
càdlàg increasing process.  The process is locally of bounded variation and
its stop at each schedule coordinate is indistinguishable from the stored
coordinate variation.

The theorem only glues the supplied coordinates.  In particular, it makes no
claim that an arbitrary local martingale admits such a schedule. -/
theorem exists_gluedQuadraticVariation
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M)) :
    ∃ Q : Process Omega,
      StronglyAdapted F Q ∧
        (∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t) ∧
        ProcessHasLeftLimits Q ∧
        (∀ omega, Monotone (Q · omega)) ∧
        (∀ omega, LocallyBoundedVariationOn (Q · omega) Set.univ) ∧
        Q 0 = 0 ∧
        ∀ n, ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess Q
            (fun omega => (C.localizer n omega : WithTop NNReal)))
          (MeasureTheory.stoppedProcess
            (C.coordinate n).quadraticData.variation
            (fun omega => (C.localizer n omega : WithTop NNReal))) := by
  let A : Nat → Process Omega := fun n =>
    (C.coordinate n).quadraticData.variation
  let tau : Nat → Omega → WithTop NNReal := fun n omega =>
    (C.localizer n omega : WithTop NNReal)
  have hTau : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    simpa only [tau] using C.isLocalizingSequence
  have hAAdapted : ∀ n, StronglyAdapted F (A n) := by
    intro n
    exact (C.coordinate n).quadraticData.variation_isStronglyAdapted
  have hARight : ∀ n omega t,
      ContinuousWithinAt (A n · omega) (Ici t) t := by
    intro n omega t
    exact (C.coordinate n).quadraticData.variation_rightContinuous omega t
  have hAMonotone : ∀ n omega, Monotone (A n · omega) := by
    intro n omega
    exact (C.coordinate n).quadraticData.variation_monotone omega
  have hAZero : ∀ n, A n 0 = 0 := by
    intro n
    exact (C.coordinate n).quadraticData.variation_zero
  have hAConstantAfter : ∀ n omega t,
      C.horizon n ≤ t → A n t omega = A n (C.horizon n) omega := by
    intro n omega t ht
    exact (C.coordinate n).quadraticData.variation_constantAfter omega t ht
  have hACompatible : ∀ n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (A n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (A m) (min (tau n) (tau m))) := by
    intro n m
    have hMin : min (tau n) (tau m) =
        (fun omega => min (tau n omega) (tau m omega)) := by
      funext omega
      rfl
    rw [hMin]
    simpa only [A, tau, WithTop.coe_min] using
      (LocalMartingaleQuadraticSchedule.variation_compatible
        hUsual hMRight hMLeft C n m)
  have hANonnegative : ∀ n omega t, 0 ≤ A n t omega := by
    intro n omega t
    have hZero : A n 0 omega = 0 := by
      simpa only [A, Pi.zero_apply] using congrFun (hAZero n) omega
    have hMono := hAMonotone n omega (show (0 : NNReal) ≤ t from bot_le)
    change A n 0 omega ≤ A n t omega at hMono
    rw [hZero] at hMono
    exact hMono
  have hAVariation : ∀ n omega,
      BoundedVariationOn (A n · omega) Set.univ := by
    intro n
    exact HorizonFactorialGrid.boundedVariationOn_of_monotone_nonnegative_constantAfter
      (P := A n) (T := C.horizon n)
      (hANonnegative n) (hAMonotone n) (hAConstantAfter n)
  have hALeft : ∀ n, ProcessHasLeftLimits (A n) := by
    intro n omega t
    exact (hAVariation n omega).tendsto_leftLim t
  let raw : Process Omega :=
    CompatibleLocalMartingaleGluing.rawLimit A
  have hRawAdapted : StronglyAdapted F raw := by
    intro t
    change StronglyMeasurable[F t]
      (fun omega => limUnder atTop (fun n => A n t omega))
    exact @MeasureTheory.StronglyMeasurable.limUnder
      Nat Omega Real (F t) _ _ atTop _
      (fun n omega => A n t omega) _ _
      (fun n => hAAdapted n t)
  have hRawRegular : ∀ᵐ omega ∂mu,
      (∀ t, ContinuousWithinAt (raw · omega) (Ici t) t) ∧
        ∀ t, Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
          (nhds (Function.leftLim (raw · omega) t)) := by
    simpa only [raw, tau] using
      (CompatibleLocalMartingaleGluing.rawLimit_regular_ae
        hTau hARight hALeft hACompatible)
  have hRawVariation : ∀ᵐ omega ∂mu,
      LocallyBoundedVariationOn (raw · omega) Set.univ := by
    simpa only [raw, tau] using
      (CompatibleLocalFiniteVariationGluing.rawLimit_locallyBoundedVariation_ae
        hTau hAVariation hACompatible)
  have hRawMonotone : ∀ᵐ omega ∂mu, Monotone (raw · omega) := by
    have hCompatAll : ∀ᵐ omega ∂mu, ∀ n m t,
        MeasureTheory.stoppedProcess (A n) (min (tau n) (tau m)) t omega =
          MeasureTheory.stoppedProcess (A m) (min (tau n) (tau m)) t omega := by
      rw [ae_all_iff]
      intro n
      rw [ae_all_iff]
      exact hACompatible n
    filter_upwards [hTau.mono, hTau.tendsto_top, hCompatAll]
        with omega hMono hTop hCompatOmega
    rw [WithTop.tendsto_nhds_top_iff] at hTop
    intro s t hst
    obtain ⟨n, hn⟩ := (hTop (t + 1)).exists
    have hEqS : raw s omega = A n s omega := by
      apply CompatibleLocalMartingaleGluing.rawLimit_eq_of_le hMono
        (fun m u => hCompatOmega n m u)
      exact (WithTop.coe_le_coe.mpr
        ((hst.trans_lt (lt_add_one t)).le)).trans hn.le
    have hEqT : raw t omega = A n t omega := by
      apply CompatibleLocalMartingaleGluing.rawLimit_eq_of_le hMono
        (fun m u => hCompatOmega n m u)
      exact (WithTop.coe_le_coe.mpr (lt_add_one t).le).trans hn.le
    change raw s omega ≤ raw t omega
    rw [hEqS, hEqT]
    exact hAMonotone n omega hst
  have hRawZero : ∀ᵐ omega ∂mu, raw 0 omega = 0 := by
    have hCompatAll : ∀ᵐ omega ∂mu, ∀ m t,
        MeasureTheory.stoppedProcess (A 0) (min (tau 0) (tau m)) t omega =
          MeasureTheory.stoppedProcess (A m) (min (tau 0) (tau m)) t omega := by
      rw [ae_all_iff]
      exact hACompatible 0
    filter_upwards [hTau.mono, hCompatAll] with omega hMono hCompatOmega
    have hEq := CompatibleLocalMartingaleGluing.rawLimit_eq_of_le hMono
      (fun m t => hCompatOmega m t) (show (0 : WithTop NNReal) ≤ tau 0 omega from bot_le)
    have hZero : A 0 0 omega = 0 := by
      simpa only [A, Pi.zero_apply] using congrFun (hAZero 0) omega
    exact (show raw 0 omega = A 0 0 omega by simpa only [raw] using hEq).trans
      hZero
  have hRawGood : ∀ᵐ omega ∂mu,
      ((∀ t, ContinuousWithinAt (raw · omega) (Ici t) t) ∧
        (∀ t, Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
          (nhds (Function.leftLim (raw · omega) t))) ∧
        Monotone (raw · omega) ∧
        LocallyBoundedVariationOn (raw · omega) Set.univ ∧
        raw 0 omega = 0) := by
    filter_upwards [hRawRegular, hRawMonotone, hRawVariation, hRawZero]
      with omega hRegular hMono hVariation hZero
    exact ⟨hRegular.1, hRegular.2, hMono, hVariation, hZero⟩
  let bad : Set Omega := {omega |
    ¬((∀ t, ContinuousWithinAt (raw · omega) (Ici t) t) ∧
      (∀ t, Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
        (nhds (Function.leftLim (raw · omega) t))) ∧
      Monotone (raw · omega) ∧
      LocallyBoundedVariationOn (raw · omega) Set.univ ∧
      raw 0 omega = 0)}
  have hbadNull : mu bad = 0 := by
    simpa only [bad] using ae_iff.mp hRawGood
  have hbadMeasurable : MeasurableSet[F 0] bad :=
    hUsual.containsNullSetsAtZero bad hbadNull
  have hRightOff : ∀ omega, omega ∉ bad → ∀ t,
      ContinuousWithinAt (raw · omega) (Ici t) t := by
    intro omega hω
    have hGood := show
        (∀ t, ContinuousWithinAt (raw · omega) (Ici t) t) ∧
          (∀ t, Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
            (nhds (Function.leftLim (raw · omega) t))) ∧
          Monotone (raw · omega) ∧
          LocallyBoundedVariationOn (raw · omega) Set.univ ∧
          raw 0 omega = 0 by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
    exact hGood.1
  have hLeftOff : ∀ omega, omega ∉ bad → ∀ t,
      Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
        (nhds (Function.leftLim (raw · omega) t)) := by
    intro omega hω
    have hGood := show
        (∀ t, ContinuousWithinAt (raw · omega) (Ici t) t) ∧
          (∀ t, Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
            (nhds (Function.leftLim (raw · omega) t))) ∧
          Monotone (raw · omega) ∧
          LocallyBoundedVariationOn (raw · omega) Set.univ ∧
          raw 0 omega = 0 by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
    exact hGood.2.1
  have hVariationOff : ∀ omega, omega ∉ bad →
      LocallyBoundedVariationOn (raw · omega) Set.univ := by
    intro omega hω
    have hGood := show
        (∀ t, ContinuousWithinAt (raw · omega) (Ici t) t) ∧
          (∀ t, Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
            (nhds (Function.leftLim (raw · omega) t))) ∧
          Monotone (raw · omega) ∧
          LocallyBoundedVariationOn (raw · omega) Set.univ ∧
          raw 0 omega = 0 by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
    exact hGood.2.2.2.1
  have hMonotoneOff : ∀ omega, omega ∉ bad → Monotone (raw · omega) := by
    intro omega hω
    have hGood := show
        (∀ t, ContinuousWithinAt (raw · omega) (Ici t) t) ∧
          (∀ t, Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
            (nhds (Function.leftLim (raw · omega) t))) ∧
          Monotone (raw · omega) ∧
          LocallyBoundedVariationOn (raw · omega) Set.univ ∧
          raw 0 omega = 0 by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
    exact hGood.2.2.1
  have hZeroOff : ∀ omega, omega ∉ bad → raw 0 omega = 0 := by
    intro omega hω
    have hGood := show
        (∀ t, ContinuousWithinAt (raw · omega) (Ici t) t) ∧
          (∀ t, Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
            (nhds (Function.leftLim (raw · omega) t))) ∧
          Monotone (raw · omega) ∧
          LocallyBoundedVariationOn (raw · omega) Set.univ ∧
          raw 0 omega = 0 by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
    exact hGood.2.2.2.2
  let Q : Process Omega := ProcessNullSetRegularization.zeroOn bad raw
  have hQAdapted : StronglyAdapted F Q :=
    ProcessNullSetRegularization.stronglyAdapted_zeroOn
      hbadMeasurable hRawAdapted
  have hQRight : ∀ omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t :=
    ProcessNullSetRegularization.zeroOn_isRightContinuous hRightOff
  have hQLeft : ProcessHasLeftLimits Q :=
    ProcessNullSetRegularization.zeroOn_hasLeftLimits hLeftOff
  have hQVariation : ∀ omega,
      LocallyBoundedVariationOn (Q · omega) Set.univ :=
    ProcessNullSetRegularization.zeroOn_isLocallyBoundedVariation
      hVariationOff
  have hQMonotone : ∀ omega, Monotone (Q · omega) := by
    intro omega s t hst
    by_cases hω : omega ∈ bad
    · simp [Q, hω]
    · simpa only [Q,
        ProcessNullSetRegularization.zeroOn_apply_of_notMem bad raw hω]
        using hMonotoneOff omega hω hst
  have hQZero : Q 0 = 0 := by
    funext omega
    change Q 0 omega = 0
    by_cases hω : omega ∈ bad
    · simp [Q, hω]
    · simpa only [Q,
        ProcessNullSetRegularization.zeroOn_apply_of_notMem bad raw hω]
        using hZeroOff omega hω
  have hQRaw : ProcessIndistinguishable mu Q raw :=
    ProcessNullSetRegularization.zeroOn_indistinguishable hbadNull raw
  have hQStopped : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess Q (tau n))
      (MeasureTheory.stoppedProcess (A n) (tau n)) := by
    intro n
    exact (hQRaw.stoppedProcess (tau n)).trans
      (CompatibleLocalMartingaleGluing.rawLimit_stoppedProcess
        hTau hACompatible n)
  exact ⟨Q, hQAdapted, hQRight, hQLeft, hQMonotone, hQVariation, hQZero, by
    intro n
    simpa only [A, tau] using hQStopped n⟩

end LocalMartingaleQuadratic

end FTAPTheorem42
