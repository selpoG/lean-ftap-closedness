/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.HorizonProjection
import FTAPTheorem42.Stochastic.Martingale.Basic.CompatibleLocalMartingaleGluing

/-! # Gluing the residuals of the same finite-horizon family -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace FTAPTheorem42.HorizonFactorialGrid

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {c : Real} {hX : LocalMartingale X F mu}
  {hUsual : Filtration.UsualConditions mu F}

/-- Apply refined local-martingale gluing to the actual stored residuals,
then normalize local variation and the initial value on a time-zero null set. -/
theorem FiniteLargeJumpHorizonFamily.exists_cadlag_residual
    (family : FiniteLargeJumpHorizonFamily hX c hUsual) :
    ∃ Q : Process Ω, StronglyAdapted F Q ∧ LocalMartingale Q F mu ∧
      (∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t) ∧
      ProcessHasLeftLimits Q ∧
      Q 0 = 0 ∧ (∀ omega, LocallyBoundedVariationOn (Q · omega) Set.univ) ∧
      (∀ᵐ omega ∂mu, ∀ n t, Q (min t (cadlagPassageHorizon n)) omega =
        (family.data n).Q (min t (cadlagPassageHorizon n)) omega) := by
  let tau : Nat → Ω → WithTop NNReal := fun n _ => cadlagPassageHorizon n
  have hTau : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    refine { isStoppingTime := fun n => isStoppingTime_const F (cadlagPassageHorizon n)
             tendsto_top := ?_, mono := ?_ }
    · exact Eventually.of_forall fun _ =>
        WithTop.tendsto_coe_atTop.comp cadlagPassageHorizon_tendsto_atTop
    · exact Eventually.of_forall fun _ _ _ h =>
        WithTop.coe_le_coe.mpr (cadlagPassageHorizon_monotone h)
  have hCompat : ∀ n m, ProcessIndistinguishable mu
      (stoppedProcess (family.data n).Q (min (tau n) (tau m)))
      (stoppedProcess (family.data m).Q (min (tau n) (tau m))) := by
    intro n m
    filter_upwards [family.overlap] with omega hOverlap
    intro t
    have hStop : min (tau n) (tau m) =
        fun _ : Ω => ((min (cadlagPassageHorizon n) (cadlagPassageHorizon m) : NNReal) :
          WithTop NNReal) := by
      funext omega
      simp only [tau, Pi.inf_apply, WithTop.coe_min]
    rw [hStop, stoppedProcess_const_apply, stoppedProcess_const_apply]
    rcases le_total n m with hnm | hmn
    · rw [min_eq_left (cadlagPassageHorizon_monotone hnm)]
      exact (hOverlap n m hnm t).2.1.symm
    · rw [min_eq_right (cadlagPassageHorizon_monotone hmn)]
      exact (hOverlap m n hmn t).2.1
  obtain ⟨Q, hQA, hQM, hQR, hQL, hQS⟩ :=
    CompatibleLocalMartingaleGluing.exists_cadlag_of_localMartingale hUsual hTau
      (fun n => (family.data n).Q_isLocalMartingale) (fun n => (family.data n).Q_zero)
      (fun n => (family.data n).Q_rightContinuous) (fun n => (family.data n).Q_leftLimits)
      hCompat
  have hAgreement : ∀ᵐ omega ∂mu, ∀ n t, Q (min t (cadlagPassageHorizon n)) omega =
      (family.data n).Q (min t (cadlagPassageHorizon n)) omega := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hQS n] with omega hOmega
    intro t
    simpa only [tau, stoppedProcess_const_apply] using hOmega t
  have hRegular : ∀ᵐ omega ∂mu, Q 0 omega = 0 ∧
      LocallyBoundedVariationOn (Q · omega) Set.univ := by
    filter_upwards [hAgreement] with omega hA
    constructor
    · simpa only [show min (0 : NNReal) (cadlagPassageHorizon 0) = 0 from
        min_eq_left bot_le, (family.data 0).Q_zero, Pi.zero_apply] using hA 0 0
    · intro a b ha hb
      obtain ⟨n, hn⟩ := (cadlagPassageHorizon_tendsto_atTop.eventually_ge_atTop b).exists
      have hEq : ∀ s ∈ Set.univ ∩ Icc a b, Q s omega = (family.data n).Q s omega := by
        intro s hs
        simpa only [min_eq_left (hs.2.2.trans hn)] using hA n s
      have hBV := (family.data n).Q_locallyBoundedVariation omega a b ha hb
      unfold BoundedVariationOn at hBV ⊢
      rw [eVariationOn.eq_of_eqOn hEq]
      exact hBV
  let bad : Set Ω := {omega | ¬(Q 0 omega = 0 ∧
    LocallyBoundedVariationOn (Q · omega) Set.univ)}
  have hBad : mu bad = 0 := ae_iff.mp hRegular
  have hOff : ∀ omega, omega ∉ bad → Q 0 omega = 0 ∧
      LocallyBoundedVariationOn (Q · omega) Set.univ := by
    intro omega h
    exact not_not.mp h
  let R := ProcessNullSetRegularization.zeroOn bad Q
  have hRA : StronglyAdapted F R := ProcessNullSetRegularization.stronglyAdapted_zeroOn
    (hUsual.containsNullSetsAtZero bad hBad) hQA
  have hRR : ∀ omega t, ContinuousWithinAt (R · omega) (Ici t) t :=
    ProcessNullSetRegularization.zeroOn_isRightContinuous (fun omega _ => hQR omega)
  have hVersion : ProcessIndistinguishable mu R Q :=
    ProcessNullSetRegularization.zeroOn_indistinguishable hBad Q
  refine ⟨R, hRA, hQM.congr_indistinguishable hRA hRR hVersion.symm, hRR,
    ProcessNullSetRegularization.zeroOn_hasLeftLimits (fun omega _ => hQL omega), ?_,
    ProcessNullSetRegularization.zeroOn_isLocallyBoundedVariation
      (fun omega h => (hOff omega h).2), ?_⟩
  · funext omega
    change ProcessNullSetRegularization.zeroOn bad Q 0 omega = (0 : Real)
    by_cases h : omega ∈ bad
    · exact ProcessNullSetRegularization.zeroOn_apply_of_mem bad Q h
    · rw [ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Q h]
      exact (hOff omega h).1
  · filter_upwards [hVersion, hAgreement] with omega hV hA
    exact fun n t => (hV _).trans (hA n t)

/-- Construct both global components from one original local martingale.
Their sum agrees with the original finite large-jump source on every horizon. -/
theorem exists_largeJumpHorizon_components
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hc : 0 < c) (hUsual : Filtration.UsualConditions mu F) :
    ∃ P Q : Process Ω,
      IsStronglyPredictable F P ∧
      (∀ omega t, ContinuousWithinAt (P · omega) (Ici t) t) ∧
      (∀ omega, LocallyBoundedVariationOn (P · omega) Set.univ) ∧ P 0 = 0 ∧
      (∀ᵐ omega ∂mu, ∀ t, |processLeftJump P t omega| ≤ c) ∧
      StronglyAdapted F Q ∧ LocalMartingale Q F mu ∧
      (∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t) ∧
      ProcessHasLeftLimits Q ∧ Q 0 = 0 ∧
      (∀ omega, LocallyBoundedVariationOn (Q · omega) Set.univ) ∧
      (∀ᵐ omega ∂mu, ∀ n t,
        FiniteLargeJumpProcess.process X c (cadlagPassageHorizon n)
            (min t (cadlagPassageHorizon n)) omega =
          Q (min t (cadlagPassageHorizon n)) omega +
            P (min t (cadlagPassageHorizon n)) omega) := by
  obtain ⟨family, P, hPP, hPR, hPV, hPZ, hPS, hPJ⟩ :=
    exists_finiteLargeJumpHorizonProjection hX hXAdapted hXRight hXLeft hXZero hc hUsual
  obtain ⟨Q, hQA, hQM, hQR, hQL, hQZ, hQV, hQS⟩ := family.exists_cadlag_residual
  refine ⟨P, Q, hPP, hPR, hPV, hPZ, hPJ, hQA, hQM, hQR, hQL, hQZ, hQV, ?_⟩
  filter_upwards [hPS, hQS] with omega hP hQ
  intro n t
  rw [hP n t, hQ n t, (family.data n).Q_definition]
  dsimp only
  ring

end FTAPTheorem42.HorizonFactorialGrid
