/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Local.Construction.BoundedCoordinateSemantics
import FTAPTheorem42.Stochastic.Memin.JointPassageLocalizer
import FTAPTheorem42.Stochastic.Integral.Localization.StoppedPassageM2
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableCumulativeVariationBridge
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticProcessLimit

/-!
# Intrinsic completed schedules at the Mémín joint passages

Intersect an existing completed source schedule with the countable infimum
of all Mémín approximant passages.  The resulting localizer is exhaustive,
lies below every approximant passage, and still observes the same raw source.
The source prefix is a further stop of the old true `M²` prefix, so optional
sampling supplies its terminal `L²` bound.  A normalized variation bridge and
the general quadratic-kernel producer then turn the family into a concrete
`LocalCompletedM2ASchedule`.

The final theorem consumes bounded-coordinate semantics: every approximant
integrand belongs to the new common energy space and its completed martingale
integral is the corresponding joint-passage output coordinate.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open BoundedMartingaleQuadraticEnergy.Data
open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The existing source localizer intersected with all approximant passages. -/
noncomputable def intrinsicJointPassageLocalizer
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) :
    Nat -> Omega -> WithTop NNReal :=
  fun n omega => min (base.localizer n omega)
    (data.allApproximantsPassage n omega)

theorem intrinsicJointPassageLocalizer_isStoppingTime
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    IsStoppingTime F (intrinsicJointPassageLocalizer base data n) :=
  (base.isLocalizingSequence.isStoppingTime n).min
    (data.allApproximantsPassage_isStoppingTime n)

omit [F.IsRightContinuous] in
theorem intrinsicJointPassageLocalizer_le_base
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) (omega : Omega) :
    intrinsicJointPassageLocalizer base data n omega <=
      base.localizer n omega :=
  min_le_left _ _

omit [F.IsRightContinuous] in
theorem intrinsicJointPassageLocalizer_le_approximantPassage
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R)
    (n k : Nat) (omega : Omega) :
    intrinsicJointPassageLocalizer base data n omega <=
      data.approximantPassageUpTo n k omega :=
  (min_le_right _ _).trans (iInf_le _ k)

omit [F.IsRightContinuous] in
theorem intrinsicJointPassageLocalizer_le_horizon
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) (omega : Omega) :
    intrinsicJointPassageLocalizer base data n omega <=
      (cadlagPassageHorizon n : WithTop NNReal) :=
  (intrinsicJointPassageLocalizer_le_approximantPassage
    base data n 0 omega).trans (data.approximantPassageUpTo_le_horizon n 0 omega)

/-- The intrinsic joint passages are a genuine localizing sequence. -/
theorem intrinsicJointPassageLocalizer_isLocalizingSequence
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) :
    ProbabilityTheory.IsLocalizingSequence F
      (intrinsicJointPassageLocalizer base data) mu where
  isStoppingTime := intrinsicJointPassageLocalizer_isStoppingTime base data
  mono := by
    filter_upwards [base.isLocalizingSequence.mono] with omega hBase
    intro n m hnm
    exact min_le_min (hBase hnm)
      (data.allApproximantsPassage_mono hnm omega)
  tendsto_top := by
    filter_upwards [base.isLocalizingSequence.tendsto_top,
      data.martingaleTendstoUniformly] with omega hBase hUniform
    rw [WithTop.tendsto_nhds_top_iff]
    intro t
    have hOutput := data.eventually_lt_allApproximantsPassage omega hUniform t
    have hBaseEventually : ∀ᶠ n in atTop,
        (t : WithTop NNReal) < base.localizer n omega := by
      rw [WithTop.tendsto_nhds_top_iff] at hBase
      exact hBase t
    filter_upwards [hBaseEventually, hOutput] with n hnBase hnOutput
    exact lt_min hnBase hnOutput

/-- The finite-valued representative of one intrinsic joint localizer. -/
noncomputable def intrinsicJointPassageFiniteLocalizer
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R)
    (n : Nat) : Omega -> NNReal :=
  RightContinuousStoppedMartingale.boundedTime (cadlagPassageHorizon n)
    (intrinsicJointPassageLocalizer base data n)

omit [F.IsRightContinuous] in
theorem coe_intrinsicJointPassageFiniteLocalizer
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R)
    (n : Nat) (omega : Omega) :
    (intrinsicJointPassageFiniteLocalizer base data n omega :
      WithTop NNReal) = intrinsicJointPassageLocalizer base data n omega := by
  rw [intrinsicJointPassageFiniteLocalizer,
    RightContinuousStoppedMartingale.coe_boundedTime,
    min_eq_right (intrinsicJointPassageLocalizer_le_horizon
      base data n omega)]

/-- The raw source stopped at one intrinsic joint passage. -/
noncomputable def intrinsicJointPassageSourcePrefix
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    SIntegrableStrategy D :=
  (G.deterministicallyStopped (cadlagPassageHorizon n)
    (cadlagPassageHorizon_pos n)).toLocally.finiteClosedStopOfRightContinuous
      (intrinsicJointPassageFiniteLocalizer base data n)
      (by simpa only [coe_intrinsicJointPassageFiniteLocalizer] using
        intrinsicJointPassageLocalizer_isStoppingTime base data n)

theorem intrinsicJointPassageSourcePrefix_stochasticIntegral
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    ProcessIndistinguishable mu
      (intrinsicJointPassageSourcePrefix base data n).stochasticIntegral
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (cadlagPassageHorizon n)
          (cadlagPassageHorizon_pos n)).stochasticIntegral
        (intrinsicJointPassageLocalizer base data n)) := by
  change ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (cadlagPassageHorizon n)
        (cadlagPassageHorizon_pos n)).stochasticIntegral
      (fun omega => (intrinsicJointPassageFiniteLocalizer base data n omega : WithTop NNReal))) _
  rw [show (fun omega =>
      (intrinsicJointPassageFiniteLocalizer base data n omega : WithTop NNReal)) =
    intrinsicJointPassageLocalizer base data n from
      funext (coe_intrinsicJointPassageFiniteLocalizer base data n)]
  exact ProcessIndistinguishable.refl mu _

theorem intrinsicJointPassageSourcePrefix_martingalePart
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    ProcessIndistinguishable mu
      (intrinsicJointPassageSourcePrefix base data n).martingalePart
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (cadlagPassageHorizon n)
          (cadlagPassageHorizon_pos n)).martingalePart
        (intrinsicJointPassageLocalizer base data n)) := by
  change ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (cadlagPassageHorizon n)
        (cadlagPassageHorizon_pos n)).martingalePart
      (fun omega => (intrinsicJointPassageFiniteLocalizer base data n omega : WithTop NNReal))) _
  rw [show (fun omega =>
      (intrinsicJointPassageFiniteLocalizer base data n omega : WithTop NNReal)) =
    intrinsicJointPassageLocalizer base data n from
      funext (coe_intrinsicJointPassageFiniteLocalizer base data n)]
  exact ProcessIndistinguishable.refl mu _

theorem intrinsicJointPassageSourcePrefix_finiteVariationPart
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    ProcessIndistinguishable mu
      (intrinsicJointPassageSourcePrefix base data n).finiteVariationPart
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (cadlagPassageHorizon n)
          (cadlagPassageHorizon_pos n)).finiteVariationPart
        (intrinsicJointPassageLocalizer base data n)) := by
  change ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (cadlagPassageHorizon n)
        (cadlagPassageHorizon_pos n)).finiteVariationPart
      (fun omega => (intrinsicJointPassageFiniteLocalizer base data n omega : WithTop NNReal))) _
  rw [show (fun omega =>
      (intrinsicJointPassageFiniteLocalizer base data n omega : WithTop NNReal)) =
    intrinsicJointPassageLocalizer base data n from
      funext (coe_intrinsicJointPassageFiniteLocalizer base data n)]
  exact ProcessIndistinguishable.refl mu _

/-- The new source martingale is the old true `M²` source martingale
stopped once more at the joint passage. -/
theorem intrinsicJointPassageSourcePrefix_martingalePart_base
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    ProcessIndistinguishable mu
      (intrinsicJointPassageSourcePrefix base data n).martingalePart
      (MeasureTheory.stoppedProcess (base.sourcePrefix n).martingalePart
        (intrinsicJointPassageLocalizer base data n)) := by
  let rho := intrinsicJointPassageLocalizer base data n
  have hNew := intrinsicJointPassageSourcePrefix_martingalePart
    base data n
  have hOld := (base.sourcePrefix_martingalePart n).stoppedProcess rho
  have hNewTarget : MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (cadlagPassageHorizon n)
        (cadlagPassageHorizon_pos n)).martingalePart rho =
      MeasureTheory.stoppedProcess G.martingalePart rho := by
    change MeasureTheory.stoppedProcess
      (fun t omega => G.martingalePart
        (min t (cadlagPassageHorizon n)) omega) rho = _
    exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      (intrinsicJointPassageLocalizer_le_horizon base data n)
  have hOldTarget : MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (base.horizon n)
          (base.horizon_pos n)).martingalePart (base.localizer n)) rho =
      MeasureTheory.stoppedProcess G.martingalePart rho := by
    change MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (fun t omega => G.martingalePart (min t (base.horizon n)) omega)
        (base.localizer n)) rho = _
    rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_right]
    · exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right fun omega =>
          (intrinsicJointPassageLocalizer_le_base base data n omega).trans
            (base.localizer_le_horizon n omega)
    · exact intrinsicJointPassageLocalizer_le_base base data n
  rw [hNewTarget] at hNew
  rw [hOldTarget] at hOld
  exact hNew.trans hOld.symm

/-- The joint source prefix is a true martingale by optional stopping of the
old source prefix. -/
theorem intrinsicJointPassageSourcePrefix_martingale
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    Martingale (intrinsicJointPassageSourcePrefix base data n
      ).martingalePart F mu := by
  let rho := intrinsicJointPassageLocalizer base data n
  have hStopped : Martingale
      (MeasureTheory.stoppedProcess (base.sourcePrefix n).martingalePart rho)
      F mu :=
    RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      (base.martingale n)
      (intrinsicJointPassageLocalizer_isStoppingTime base data n)
      (base.sourcePrefix n).martingalePart_isRightContinuous
  apply hStopped.congr
    (intrinsicJointPassageSourcePrefix base data n
      ).martingalePart_isStronglyAdapted
  intro t
  exact (intrinsicJointPassageSourcePrefix_martingalePart_base
    base data n |>.eventuallyEq_at t).symm

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
/-- A schedule source prefix is constant after its deterministic horizon. -/
private theorem baseSourcePrefix_martingalePart_constantAfter
    (base : LocalCompletedM2ASchedule G) (n : Nat) (t : NNReal)
    (hTt : base.horizon n <= t) :
    (base.sourcePrefix n).martingalePart t =ᵐ[mu]
      (base.sourcePrefix n).martingalePart (base.horizon n) := by
  filter_upwards [base.sourcePrefix_martingalePart n]
      with omega hComponent
  rw [hComponent t, hComponent (base.horizon n)]
  have hTauT := base.localizer_le_horizon n omega
  have hTauT' : base.localizer n omega <= (t : WithTop NNReal) :=
    hTauT.trans (WithTop.coe_le_coe.mpr hTt)
  rw [MeasureTheory.stoppedProcess_eq_of_ge hTauT',
    MeasureTheory.stoppedProcess_eq_of_ge hTauT]

/-- The terminal value of the joint source martingale is square-integrable.
The proof samples the old source prefix at the bounded joint passage. -/
theorem intrinsicJointPassageSourcePrefix_terminal_memLp
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    MemLp ((intrinsicJointPassageSourcePrefix base data n).martingalePart
      (cadlagPassageHorizon n)) (2 : ENNReal) mu := by
  let rho := intrinsicJointPassageLocalizer base data n
  let U := cadlagPassageHorizon n
  let T := base.horizon n
  let M := (base.sourcePrefix n).martingalePart
  let sigma : Omega -> NNReal :=
    RightContinuousStoppedMartingale.boundedTime U rho
  have hRho : IsStoppingTime F rho :=
    intrinsicJointPassageLocalizer_isStoppingTime base data n
  have hSigma : IsStoppingTime F
      (fun omega => (sigma omega : WithTop NNReal)) :=
    RightContinuousStoppedMartingale.boundedTime_isStoppingTime hRho U
  have hSigmaT : forall omega, sigma omega <= T := by
    intro omega
    apply WithTop.coe_le_coe.mp
    rw [RightContinuousStoppedMartingale.coe_boundedTime,
      min_eq_right (intrinsicJointPassageLocalizer_le_horizon
        base data n omega)]
    exact (intrinsicJointPassageLocalizer_le_base
      base data n omega).trans (base.localizer_le_horizon n omega)
  have hConstant : M (T + 1) =ᵐ[mu] M T := by
    exact baseSourcePrefix_martingalePart_constantAfter base n (T + 1)
      (le_add_right (le_refl T))
  have hLater : MemLp (M (T + 1)) (2 : ENNReal) mu :=
    (memLp_congr_ae hConstant).mpr (base.terminal_memLp n)
  have hConditional : MemLp
      (mu[M (T + 1) | hSigma.measurableSpace]) (2 : ENNReal) mu :=
    hLater.condExp (by norm_num)
  have hOptional : (fun omega => M (sigma omega) omega) =ᵐ[mu]
      mu[M (T + 1) | hSigma.measurableSpace] :=
    Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
      (base.martingale n) hSigma hSigmaT
        (base.sourcePrefix n).martingalePart_isRightContinuous
  have hSample : MemLp (fun omega => M (sigma omega) omega)
      (2 : ENNReal) mu :=
    (memLp_congr_ae hOptional).mpr hConditional
  have hStopped : MemLp (MeasureTheory.stoppedProcess M rho U)
      (2 : ENNReal) mu := by
    apply (memLp_congr_ae ?_).mpr hSample
    exact Filter.Eventually.of_forall fun omega => by
      exact (RightContinuousStoppedMartingale.sample_boundedTime_eq_stoppedProcess
        M rho U omega).symm
  exact (memLp_congr_ae
    (intrinsicJointPassageSourcePrefix_martingalePart_base base data n
      |>.eventuallyEq_at U)).mpr hStopped

/-- The normalized finite-variation bridge of a joint source prefix. -/
noncomputable def intrinsicJointPassageVariationBridge
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    SIntegrableFiniteVariationBridge
      (intrinsicJointPassageSourcePrefix base data n) :=
  SIntegrableFiniteVariationBridge.ofCumulativeVariationNormalized
    (intrinsicJointPassageSourcePrefix base data n
      ).finiteVariationPart_isRightContinuous

/-- The quadratic-energy kernel of a joint source prefix. -/
noncomputable def intrinsicJointPassageQuadraticKernel
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    BoundedMartingaleQuadraticKernel.Data F mu
      (intrinsicJointPassageSourcePrefix base data n).martingalePart
      (cadlagPassageHorizon n) :=
  Classical.choice (SquareIntegrableMartingaleQuadraticKernel.exists_data
    base.usualConditions
    (intrinsicJointPassageSourcePrefix_martingale base data n)
    (intrinsicJointPassageSourcePrefix base data n
      ).martingalePart_isRightContinuous
    (cadlagPassageHorizon n)
    (intrinsicJointPassageSourcePrefix_terminal_memLp base data n))

/-- A concrete completed source schedule on the common source/output
passages of the Mémín sequence. -/
noncomputable def intrinsicJointPassageSchedule
    {R : SIntegrableRealizationModel D}
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData R) :
    LocalCompletedM2ASchedule G where
  usualConditions := base.usualConditions
  localizer := intrinsicJointPassageLocalizer base data
  isLocalizingSequence :=
    intrinsicJointPassageLocalizer_isLocalizingSequence base data
  horizon := cadlagPassageHorizon
  horizon_pos := cadlagPassageHorizon_pos
  localizer_le_horizon :=
    intrinsicJointPassageLocalizer_le_horizon base data
  sourcePrefix := intrinsicJointPassageSourcePrefix base data
  sourcePrefix_stochasticIntegral :=
    intrinsicJointPassageSourcePrefix_stochasticIntegral base data
  sourcePrefix_martingalePart :=
    intrinsicJointPassageSourcePrefix_martingalePart base data
  sourcePrefix_finiteVariationPart :=
    intrinsicJointPassageSourcePrefix_finiteVariationPart base data
  martingale := intrinsicJointPassageSourcePrefix_martingale base data
  terminal_memLp :=
    intrinsicJointPassageSourcePrefix_terminal_memLp base data
  variationBridge := intrinsicJointPassageVariationBridge base data
  quadraticKernel := intrinsicJointPassageQuadraticKernel base data

/-- Every intrinsic Mémín approximant has a true `M²` centered output
coordinate on the common joint-passage schedule. -/
theorem intrinsicJointPassage_approximantCoordinate_martingale_l2
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (n k : Nat) :
    let target := intrinsicJointPassageSchedule base data
    let X := actualLocalL2CoordinateProcess
      (target.localizer n) (target.horizon n) (data.approximant k)
    Martingale X F mu ∧
      MemLp (X (target.horizon n)) (2 : ENNReal) mu ∧
      eLpNorm (X (target.horizon n)) (2 : ENNReal) mu <=
        ENNReal.ofReal (cadlagPassageLevel n) +
          6 * eLpNorm data.gainEnvelope (2 : ENNReal) mu := by
  let target := intrinsicJointPassageSchedule base data
  let sigma := intrinsicJointPassageLocalizer base data n
  let T := cadlagPassageHorizon n
  let H := data.approximant k
  let hSigma : IsStoppingTime F sigma :=
    intrinsicJointPassageLocalizer_isStoppingTime base data n
  let P := MeasureTheory.stoppedProcess H.val.martingalePart sigma
  have hSigmaHit : forall omega,
      sigma omega <= absoluteStrictHittingAfter H.val.martingalePart
        (cadlagPassageLevel n) omega := by
    intro omega
    exact (intrinsicJointPassageLocalizer_le_approximantPassage
      base data n k omega).trans (min_le_left _ _)
  have hSigmaT : forall omega, sigma omega <= (T : WithTop NNReal) := by
    intro omega
    exact (intrinsicJointPassageLocalizer_le_approximantPassage
      base data n k omega).trans (min_le_right _ _)
  have hP : Martingale P F mu ∧
      MemLp (P T) (2 : ENNReal) mu ∧
      eLpNorm (P T) (2 : ENNReal) mu <=
        ENNReal.ofReal (cadlagPassageLevel n) +
          6 * eLpNorm data.gainEnvelope (2 : ENNReal) mu := by
    simpa only [P] using
      SIntegrableStoppingCalculus.stoppedProcess_martingale_l2_of_le_hitting_of_strategy
        base.usualConditions H.val (data.approximant_martingaleLeft k)
        (data.approximant_martingaleZero k) data.gainEnvelope
        data.gainEnvelope_memLp (data.approximant_gainBound k)
        (cadlagPassageLevel n) (cadlagPassageLevel_nonnegative n)
        sigma hSigma (cadlagPassageHorizon_pos n) hSigmaHit hSigmaT
  let X := actualLocalL2CoordinateProcess sigma T H
  have hXP : ProcessIndistinguishable mu X P := by
    have hCoordinate : X =
        MeasureTheory.stoppedProcess H.val.centeredMartingalePart sigma := by
      change actualLocalL2CoordinateProcess sigma T H = _
      rw [actualLocalL2CoordinateProcess,
        MeasureTheory.stoppedProcess_stoppedProcess_of_le_left]
      exact hSigmaT
    rw [hCoordinate]
    filter_upwards [data.approximant_martingaleZero k] with omega hZeroOmega
    intro t
    change H.val.martingalePart
          (RightContinuousStoppedMartingale.boundedTime t sigma omega) omega -
        H.val.martingalePart 0 omega =
      H.val.martingalePart
        (RightContinuousStoppedMartingale.boundedTime t sigma omega) omega
    rw [hZeroOmega, Pi.zero_apply, sub_zero]
  have hXMartingale : Martingale X F mu :=
    hP.1.congr
      (actualLocalL2CoordinateProcess_stronglyAdapted hSigma T H)
      (fun t => (hXP.eventuallyEq_at t).symm)
  have hXMem : MemLp (X T) (2 : ENNReal) mu :=
    (memLp_congr_ae (hXP.eventuallyEq_at T)).mpr hP.2.1
  change Martingale X F mu ∧ MemLp (X T) (2 : ENNReal) mu ∧
    eLpNorm (X T) (2 : ENNReal) mu <=
      ENNReal.ofReal (cadlagPassageLevel n) +
        6 * eLpNorm data.gainEnvelope (2 : ENNReal) mu
  exact ⟨hXMartingale, hXMem,
    (eLpNorm_congr_ae (hXP.eventuallyEq_at T)).trans_le hP.2.2⟩

end LocalCompletedM2A

end FTAPTheorem42
