/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ProcessBridge

/-!
# Source-independent predictable zero-on versions

The predictable zero-on construction only uses a process-level bridge, the
path properties of the regularized càdlàg process, and primitive predictable
process facts.  It is therefore kept independent of the bounded source and
of the finite-grid bridge consumers.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F] {T : NNReal}

/-- The sample paths on which two processes fail to agree at some time. -/
noncomputable def predictableCompensatorDisagreementSet
    (Ppred Preg : Process Ω) : Set Ω :=
  {omega | ¬ ∀ t, Ppred t omega = Preg t omega}

/-! ## The output certificate -/

structure FactorialGridPredictableCompensatorPredictableVersionData
    (bad : Set Ω) (Ppred Preg Vp : Process Ω) : Prop where
  bad_eq_disagreement :
    bad = predictableCompensatorDisagreementSet Ppred Preg
  bad_null : mu bad = 0
  bad_measurable : MeasurableSet[F 0] bad
  Vp_eq_zeroOn_Ppred : Vp = ProcessNullSetRegularization.zeroOn bad Ppred
  Vp_eq_zeroOn_Preg : Vp = ProcessNullSetRegularization.zeroOn bad Preg
  Vp_indistinguishable_Ppred : ProcessIndistinguishable mu Vp Ppred
  Vp_indistinguishable_Preg : ProcessIndistinguishable mu Vp Preg
  Vp_isStronglyPredictable : IsStronglyPredictable F Vp
  Vp_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Vp · omega) (Ici t) t
  Vp_leftLimits : ProcessHasLeftLimits Vp
  Vp_nonnegative : ∀ omega t, 0 ≤ Vp t omega
  Vp_monotone : ∀ omega, Monotone (Vp · omega)
  Vp_zero : Vp 0 = 0
  Vp_constant_after : ∀ omega t, T ≤ t →
    Vp t omega = Vp T omega

/-! ## The null-set regularization producer -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem exists_predictableCompensatorVersion_of_processBridge
    {Ppred Preg : Process Ω}
    (hPred : IsStronglyPredictable F Ppred)
    (hPred_zero : Ppred 0 = 0)
    (hPreg_rightContinuous : ∀ omega t,
      ContinuousWithinAt (Preg · omega) (Ici t) t)
    (hPreg_leftLimits : ProcessHasLeftLimits Preg)
    (hPreg_nonnegative : ∀ omega t, 0 ≤ Preg t omega)
    (hPreg_monotone : ∀ omega, Monotone (Preg · omega))
    (hPreg_constant_after : ∀ omega t, T ≤ t →
      Preg t omega = Preg T omega)
    (hBridge : ProcessIndistinguishable mu Ppred Preg)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ bad : Set Ω, ∃ Vp : Process Ω,
      FactorialGridPredictableCompensatorPredictableVersionData
        (F := F) (mu := mu) (T := T) bad Ppred Preg Vp := by
  let bad : Set Ω := predictableCompensatorDisagreementSet Ppred Preg
  have hbadNull : mu bad = 0 := by
    simpa only [bad, predictableCompensatorDisagreementSet] using
      (ae_iff.mp hBridge)
  have hbadMeasurable : MeasurableSet[F 0] bad :=
    hUsual.containsNullSetsAtZero bad hbadNull
  have hOff : ∀ omega, omega ∉ bad → ∀ t,
      Ppred t omega = Preg t omega := by
    intro omega hω t
    have hAll : ∀ s, Ppred s omega = Preg s omega := by
      simpa only [bad, predictableCompensatorDisagreementSet,
        Set.mem_ofPred_eq, not_not] using hω
    exact hAll t
  let Vp : Process Ω := ProcessNullSetRegularization.zeroOn bad Ppred
  have hVpPred : IsStronglyPredictable F Vp := by
    dsimp [Vp]
    exact ProcessNullSetRegularization.isStronglyPredictable_zeroOn
      hbadMeasurable hPred
  have hRightOff : ∀ omega, omega ∉ bad → ∀ t,
      ContinuousWithinAt (Ppred · omega) (Ici t) t := by
    intro omega hω t
    have hEq : (Ppred · omega) = (Preg · omega) := by
      funext s
      exact hOff omega hω s
    rw [hEq]
    exact hPreg_rightContinuous omega t
  have hLeftOff : ∀ omega, omega ∉ bad →
      ∀ t, Tendsto (fun s => Ppred s omega) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun s => Ppred s omega) t)) := by
    intro omega hω t
    have hEq : (Ppred · omega) = (Preg · omega) := by
      funext s
      exact hOff omega hω s
    have hPreg := hPreg_leftLimits omega t
    simpa only [hEq] using hPreg
  have hVpRight : ∀ omega t,
      ContinuousWithinAt (Vp · omega) (Ici t) t := by
    dsimp [Vp]
    exact ProcessNullSetRegularization.zeroOn_isRightContinuous hRightOff
  have hVpLeft : ProcessHasLeftLimits Vp := by
    dsimp [Vp]
    exact ProcessNullSetRegularization.zeroOn_hasLeftLimits hLeftOff
  have hVpNonnegative : ∀ omega t, 0 ≤ Vp t omega := by
    intro omega t
    by_cases hω : omega ∈ bad
    · simp [Vp, hω]
    · rw [show Vp t omega = Ppred t omega by
        exact ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Ppred hω]
      rw [hOff omega hω t]
      exact hPreg_nonnegative omega t
  have hVpMonotone : ∀ omega, Monotone (Vp · omega) := by
    intro omega s t hst
    change Vp s omega ≤ Vp t omega
    by_cases hω : omega ∈ bad
    · simp [Vp, hω]
    · have hPs : Vp s omega = Preg s omega := by
        rw [show Vp s omega = Ppred s omega by
          exact ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Ppred hω]
        exact hOff omega hω s
      have hPt : Vp t omega = Preg t omega := by
        rw [show Vp t omega = Ppred t omega by
          exact ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Ppred hω]
        exact hOff omega hω t
      rw [hPs, hPt]
      exact hPreg_monotone omega hst
  have hVpZero : Vp 0 = 0 := by
    funext omega
    by_cases hω : omega ∈ bad
    · simp [Vp, hω]
    · rw [show Vp 0 omega = Ppred 0 omega by
        exact ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Ppred hω]
      exact congrFun hPred_zero omega
  have hVpConstantAfter : ∀ omega t, T ≤ t →
      Vp t omega = Vp T omega := by
    intro omega t ht
    by_cases hω : omega ∈ bad
    · simp [Vp, hω]
    · have hPt : Vp t omega = Preg t omega := by
        rw [show Vp t omega = Ppred t omega by
          exact ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Ppred hω]
        exact hOff omega hω t
      have hPT : Vp T omega = Preg T omega := by
        rw [show Vp T omega = Ppred T omega by
          exact ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Ppred hω]
        exact hOff omega hω T
      rw [hPt, hPT]
      exact hPreg_constant_after omega t ht
  have hVpEqPreg : Vp =
      ProcessNullSetRegularization.zeroOn bad Preg := by
    funext t omega
    by_cases hω : omega ∈ bad
    · simp [Vp, ProcessNullSetRegularization.zeroOn, hω]
    · rw [show Vp t omega = Ppred t omega by
        exact ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Ppred hω,
      ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Preg hω]
      exact hOff omega hω t
  have hVpPredIndist : ProcessIndistinguishable mu Vp Ppred := by
    dsimp [Vp]
    exact ProcessNullSetRegularization.zeroOn_indistinguishable hbadNull Ppred
  have hVpPregIndist : ProcessIndistinguishable mu Vp Preg :=
    hVpPredIndist.trans hBridge
  refine ⟨bad, Vp, {
    bad_eq_disagreement := by rfl
    bad_null := hbadNull
    bad_measurable := hbadMeasurable
    Vp_eq_zeroOn_Ppred := rfl
    Vp_eq_zeroOn_Preg := hVpEqPreg
    Vp_indistinguishable_Ppred := hVpPredIndist
    Vp_indistinguishable_Preg := hVpPregIndist
    Vp_isStronglyPredictable := hVpPred
    Vp_rightContinuous := hVpRight
    Vp_leftLimits := hVpLeft
    Vp_nonnegative := hVpNonnegative
    Vp_monotone := hVpMonotone
    Vp_zero := hVpZero
    Vp_constant_after := hVpConstantAfter }⟩

end HorizonFactorialGrid

/-!
## A predictable pathwise version of the compensator candidate

The process bridge identifies the predictable limsup with the regularized
càdlàg candidate outside one null set, simultaneously at all times.  Under
the usual conditions that exceptional set is measurable at time zero.  We
therefore zero the predictable limsup on it.  The resulting process is
predictable by construction, while its pathwise regularity is inherited from
the càdlàg candidate off the same set.

No predictability of the càdlàg candidate is used.  In particular, the
regularization is performed on the predictable process, not on the candidate.
-/

namespace HorizonFactorialGrid

open BoundedIncreasingProcessData

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F] {T : NNReal}

/-! ## Direct consumer for a common-stop Jordan component -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_predictableCompensatorVersion_of_commonAEJordanComponent
    {V : Process Ω} {C : NNReal}
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg)
    (component : FactorialGridPredictableCompensatorCommonAEJordanComponentData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ bad' : Set Ω, ∃ Vp : Process Ω,
      FactorialGridPredictableCompensatorPredictableVersionData
        (F := F) (mu := mu) (T := T)
        bad'
        (predictableCompensatorLimsup w component.cutoff V F mu T C)
        Preg Vp := by
  let Ppred := predictableCompensatorLimsup w component.cutoff V F mu T C
  let hLimsup := predictableCompensatorLimsup_of_commonAEJordanComponent component
  have hBridge : ProcessIndistinguishable mu Ppred Preg := by
    dsimp [Ppred]
    exact processIndistinguishable_of_commonAEJordanComponent
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon hCad bad Preg hReg
        component hUsual
  exact exists_predictableCompensatorVersion_of_processBridge
    (F := F) (mu := mu) (T := T)
    (Ppred := Ppred) (Preg := Preg)
    hLimsup.Ppred_isStronglyPredictable hLimsup.Ppred_zero
    hReg.Preg_rightContinuous hReg.Preg_leftLimits hReg.Preg_nonnegative
    hReg.Preg_monotone hReg.Preg_constant_after hBridge hUsual

end HorizonFactorialGrid

end FTAPTheorem42
