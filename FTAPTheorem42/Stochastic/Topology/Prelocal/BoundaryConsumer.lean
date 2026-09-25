/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ValueTruncationFiniteVariation
import FTAPTheorem42.Stochastic.Topology.Prelocal.Representation
import FTAPTheorem42.Stochastic.Topology.Emery.CompletedRowBridge
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcess
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcessGeneralMeasure
import FTAPTheorem42.Stochastic.Process.UniformProcessLimitUniqueness
import FTAPTheorem42.Stochastic.DS.Lemma47.StoppedMartingale
import FTAPTheorem42.Stochastic.DS.Lemma410.StrategyConvexification
import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Stochastic.DS.Lemma410.StoppedPrefixMartingale
import FTAPTheorem42.Stochastic.Martingale.Basic.ConditionalExpectationL2
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Stochastic.DS.Lemma48.NormalizedTail
import FTAPTheorem42.Foundations.MaximalProbability
import FTAPTheorem42.Stochastic.DS.Lemma49.StoppedTailMartingale
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePathwiseRestrictionCalculus
import FTAPTheorem42.Foundations.CadlagEnvelope
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AStopping
import FTAPTheorem42.Stochastic.Predictable.PredictableRestriction
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableCumulativeVariationBridge
import FTAPTheorem42.Stochastic.Topology.Emery.Completion
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import FTAPTheorem42.Stochastic.Decomposition.Source.RawFiniteVariationRegularizationCore

/-!
# The strict-prefix boundary consumer

The strict-prefix operation removes the value jump at a stopping time.  This
module records the corresponding boundary process and the exact algebra which
returns a stopped martingale plus a finite-variation remainder.  The latter is
the input consumed below by the `L¹` value-truncation predictable
finite-variation producer.

The carrier witness only specifies the target on the open stochastic prefix.
Consequently the global conclusion is stated first for the canonical
representative `N + A`; identifying it with `strictPrefixProcess X tau` needs
the separate target compatibility at the stopping boundary.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

open HorizonFactorialGrid

/-! ## Boundary process and pathwise algebra -/

/-- The process which retains the left jump of `N` from `tau` onwards. -/
noncomputable def boundaryJumpProcess
    (N : Process Ω) (tau : Ω → NNReal) : Process Ω :=
  postStopSampled (processLeftJump N) tau

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_eq_sub
    (N : Process Ω) (tau : Ω → NNReal) :
    boundaryJumpProcess N tau =
      (fun t omega =>
        postStopSampled N tau t omega -
          postStopSampled (fun s omega => Function.leftLim (N · omega) s)
            tau t omega) := by
  funext t omega
  by_cases h : tau omega ≤ t
  · rw [boundaryJumpProcess,
      postStopSampled_eq_of_ge (processLeftJump N) tau h,
      postStopSampled_eq_of_ge N tau h,
      postStopSampled_eq_of_ge
        (fun s omega => Function.leftLim (N · omega) s) tau h]
    rfl
  · rw [boundaryJumpProcess,
      postStopSampled_eq_zero_of_lt (processLeftJump N) tau
        (lt_of_not_ge h),
      postStopSampled_eq_zero_of_lt N tau (lt_of_not_ge h),
      postStopSampled_eq_zero_of_lt
        (fun s omega => Function.leftLim (N · omega) s) tau
        (lt_of_not_ge h)]
    simp

omit [MeasurableSpace Ω] in
theorem strictPrefixProcess_add_boundaryJumpProcess_eq_stoppedParts
    {N A : Process Ω} (tau : Ω → NNReal)
    (hN : ProcessHasLeftLimits N) (hA : ProcessHasLeftLimits A) :
    ∀ t omega,
      strictPrefixProcess (fun s omega => N s omega + A s omega) tau t omega =
        MeasureTheory.stoppedProcess N
          (fun omega => (tau omega : WithTop NNReal)) t omega +
          strictPrefixProcess A tau t omega -
            boundaryJumpProcess N tau t omega := by
  intro t omega
  have hSum := strictPrefixProcess_add_postStopSampled_processLeftJump
    (fun s omega => N s omega + A s omega) tau t omega
  have hA' := strictPrefixProcess_add_postStopSampled_processLeftJump A tau t omega
  have hJumpFun : processLeftJump (fun s omega => N s omega + A s omega) =
      (fun s omega => processLeftJump N s omega + processLeftJump A s omega) := by
    funext s omega
    exact processLeftJump_add hN hA s omega
  have hStopped : MeasureTheory.stoppedProcess
      (fun s omega => N s omega + A s omega)
      (fun omega => (tau omega : WithTop NNReal)) t omega =
      MeasureTheory.stoppedProcess N
        (fun omega => (tau omega : WithTop NNReal)) t omega +
        MeasureTheory.stoppedProcess A
          (fun omega => (tau omega : WithTop NNReal)) t omega := by
    simp [MeasureTheory.stoppedProcess]
  calc
    strictPrefixProcess (fun s omega => N s omega + A s omega) tau t omega =
        MeasureTheory.stoppedProcess
            (fun s omega => N s omega + A s omega)
            (fun omega => (tau omega : WithTop NNReal)) t omega -
          postStopSampled
            (processLeftJump (fun s omega => N s omega + A s omega)) tau t omega := by
      linarith
    _ = (MeasureTheory.stoppedProcess N
          (fun omega => (tau omega : WithTop NNReal)) t omega +
          MeasureTheory.stoppedProcess A
            (fun omega => (tau omega : WithTop NNReal)) t omega) -
          (boundaryJumpProcess N tau t omega +
            postStopSampled (processLeftJump A) tau t omega) := by
      rw [hStopped, hJumpFun]
      unfold boundaryJumpProcess
      unfold postStopSampled
      by_cases h : tau omega ≤ t
      · simp only [ite_eq_left h]
      · simp only [ite_eq_right h]
        ring
    _ = MeasureTheory.stoppedProcess N
          (fun omega => (tau omega : WithTop NNReal)) t omega +
          strictPrefixProcess A tau t omega -
            boundaryJumpProcess N tau t omega := by
      have hAStopped : strictPrefixProcess A tau t omega =
          MeasureTheory.stoppedProcess A
            (fun omega => (tau omega : WithTop NNReal)) t omega -
            postStopSampled (processLeftJump A) tau t omega := by
        linarith
      linarith

/-! ## Adaptedness and path regularity -/

theorem boundaryJumpProcess_stronglyAdapted
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {N : Process Ω} {tau : Ω → NNReal}
    (hN : StronglyAdapted F N)
    (hNRight : ∀ omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNLeft : ProcessHasLeftLimits N)
    (hTau : IsStoppingTime F
      (fun omega => (tau omega : WithTop NNReal))) :
    StronglyAdapted F (boundaryJumpProcess N tau) := by
  rw [boundaryJumpProcess_eq_sub]
  have hValue : StronglyAdapted F (postStopSampled N tau) :=
    postStopSampled_stronglyAdapted_of_rightContinuous N tau hN hNRight hTau
  have hLeftPred : IsStronglyPredictable F
      (fun t omega => Function.leftLim (N · omega) t) :=
    ProcessHasLeftLimits.stronglyPredictable_leftLim hNLeft hN
  have hLeft : StronglyAdapted F
      (postStopSampled
        (fun t omega => Function.leftLim (N · omega) t) tau) :=
    postStopSampled_stronglyAdapted_of_predictable
      (fun t omega => Function.leftLim (N · omega) t) tau hLeftPred hTau
  exact hValue.sub hLeft

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_rightContinuous
    (N : Process Ω) (tau : Ω → NNReal) :
    ∀ omega t, ContinuousWithinAt
      (boundaryJumpProcess N tau · omega) (Ici t) t := by
  exact postStopSampled_rightContinuous (processLeftJump N) tau

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_hasLeftLimits
    (N : Process Ω) (tau : Ω → NNReal) :
    ProcessHasLeftLimits (boundaryJumpProcess N tau) := by
  exact postStopSampled_hasLeftLimits (processLeftJump N) tau

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_boundedVariation
    (N : Process Ω) (tau : Ω → NNReal) :
    ∀ omega, BoundedVariationOn
      (boundaryJumpProcess N tau · omega) Set.univ := by
  exact postStopSampled_boundedVariation (processLeftJump N) tau

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_zero
    {N : Process Ω} {tau : Ω → NNReal} :
    boundaryJumpProcess N tau 0 = 0 := by
  funext omega
  by_cases h : tau omega ≤ 0
  · have hτ : tau omega = 0 := le_antisymm h bot_le
    rw [boundaryJumpProcess,
      postStopSampled_eq_of_ge (processLeftJump N) tau h]
    change processLeftJump N (tau omega) omega = 0
    rw [hτ]
    unfold processLeftJump
    rw [show Function.leftLim (fun s => N s omega) 0 = N 0 omega from
      leftLim_eq_of_isBot isBot_bot]
    simp
  · rw [boundaryJumpProcess,
      postStopSampled_eq_zero_of_lt (processLeftJump N) tau
        (lt_of_not_ge h)]
    simp

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_constant_after
    {N : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (hTauT : ∀ omega, tau omega ≤ T) :
    ∀ omega t, T ≤ t →
      boundaryJumpProcess N tau t omega = boundaryJumpProcess N tau T omega := by
  intro omega t htt
  by_cases h : tau omega ≤ T
  · rw [boundaryJumpProcess,
      postStopSampled_eq_of_ge (processLeftJump N) tau h,
      postStopSampled_eq_of_ge (processLeftJump N) tau (h.trans htt)]
  · exact False.elim (h (hTauT omega))

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_at_horizon_eq_processLeftJump
    {N : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (hTauT : ∀ omega, tau omega ≤ T) :
    ∀ omega,
      boundaryJumpProcess N tau T omega = processLeftJump N (tau omega) omega := by
  intro omega
  rw [boundaryJumpProcess,
    postStopSampled_eq_of_ge (processLeftJump N) tau (hTauT omega)]

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_abs_le_two_mul_envelope
    {N : Process Ω}
    {tau : Ω → NNReal} {T : NNReal}
    (hNRight : ∀ omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNLeft : ProcessHasLeftLimits N)
    (hTauT : ∀ omega, tau omega ≤ T)
    (hEnvelopeEq : ∀ omega,
      ENNReal.ofReal
          (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            (MeasureTheory.stoppedProcess N
              (fun omega => (tau omega : WithTop NNReal))) T omega) =
        ⨆ t : Set.Iic T, ENNReal.ofReal
          (|MeasureTheory.stoppedProcess N
            (fun omega => (tau omega : WithTop NNReal)) t.1 omega|)) :
    ∀ omega,
      |boundaryJumpProcess N tau T omega| ≤
        2 * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess N
            (fun omega => (tau omega : WithTop NNReal))) T omega := by
  intro omega
  let τ : Ω → WithTop NNReal :=
    fun omega => (tau omega : WithTop NNReal)
  let S : Process Ω := MeasureTheory.stoppedProcess N τ
  have hSRight : ∀ omega t,
      ContinuousWithinAt (S · omega) (Ici t) t := by
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous N hNRight
  have hSLeft : ProcessHasLeftLimits S := hNLeft.stoppedProcess τ
  have hEnvelopeBound : ∀ s : NNReal, s ≤ T →
      |S s omega| ≤
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope S T omega := by
    intro s hs
    have hOf : ENNReal.ofReal |S s omega| ≤
        ENNReal.ofReal
          (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope S T omega) := by
      rw [hEnvelopeEq omega]
      exact le_iSup (fun t : Set.Iic T => ENNReal.ofReal |S t.1 omega|)
        ⟨s, hs⟩
    have hE : 0 ≤
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope S T omega :=
      Real.sqrt_nonneg _
    exact (ENNReal.ofReal_le_ofReal_iff hE).mp hOf
  have hJumpStopped :
      processLeftJump S (tau omega) omega =
        processLeftJump N (tau omega) omega := by
    exact processLeftJump_stoppedProcess_eq_of_le N hNLeft τ
      (tau omega) omega (by rfl)
  have hJumpBound :
      |processLeftJump S (tau omega) omega| ≤
        2 * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope S T omega := by
    exact abs_processLeftJump_le_two_mul_of_bound_upTo S
      (hEnvelopeBound ·) (hTauT omega) (hSLeft omega (tau omega))
  rw [boundaryJumpProcess_at_horizon_eq_processLeftJump hTauT omega,
    ← hJumpStopped]
  exact hJumpBound

theorem boundaryJumpProcess_memLp_one
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    Integrable (fun omega =>
      |boundaryJumpProcess w.N tau T omega|) mu := by
  have hBoundaryStrong : StronglyAdapted F (boundaryJumpProcess w.N tau) :=
    boundaryJumpProcess_stronglyAdapted w.martingale_isStronglyAdapted
      w.martingale_isRightContinuous w.martingale_hasLeftLimits w.stoppingTime
  have hBoundaryMeas : AEStronglyMeasurable
      (boundaryJumpProcess w.N tau T) mu :=
    ((hBoundaryStrong T).mono (F.le T)).aestronglyMeasurable
  have hEnvelopeIntegrable : Integrable
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess w.N
          (fun omega => (tau omega : WithTop NNReal))) T) mu :=
    w.martingale_envelope_memLp_one.integrable (by norm_num)
  have hTwoEnvelopeIntegrable : Integrable
      (fun omega => 2 *
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N
            (fun omega => (tau omega : WithTop NNReal))) T omega) mu :=
    hEnvelopeIntegrable.const_mul 2
  have hJumpIntegrable : Integrable
      (boundaryJumpProcess w.N tau T) mu := by
    apply hTwoEnvelopeIntegrable.mono hBoundaryMeas
    filter_upwards [] with omega
    change |boundaryJumpProcess w.N tau T omega| ≤
      |2 * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess w.N
          (fun omega => (tau omega : WithTop NNReal))) T omega|
    have hE : 0 ≤
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N
            (fun omega => (tau omega : WithTop NNReal))) T omega :=
      Real.sqrt_nonneg _
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hE)]
    exact boundaryJumpProcess_abs_le_two_mul_envelope
      w.martingale_isRightContinuous
      w.martingale_hasLeftLimits w.stoppingTime_le_horizon
      w.martingale_envelope_eq_iSup omega
  simpa only [Real.norm_eq_abs] using hJumpIntegrable.norm

/-! The jump estimate also has a direct integrated form.  This is the
quantitative bridge used by the fixed-source consumer below; it does not
assert any running-supremum control for a terminal-`L¹` residual. -/

theorem boundaryJumpProcess_expected_abs_le_two_martingaleCost
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    (∫⁻ omega, ENNReal.ofReal
      |boundaryJumpProcess w.N tau T omega| ∂mu) ≤
      2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w := by
  let E : Ω → Real := fun omega =>
    FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      (MeasureTheory.stoppedProcess w.N
        (fun omega => (tau omega : WithTop NNReal))) T omega
  have hE_nonnegative : ∀ omega, 0 ≤ E omega := by
    intro omega
    dsimp [E]
    unfold FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
    exact Real.sqrt_nonneg _
  have hBound : ∀ omega,
      ENNReal.ofReal |boundaryJumpProcess w.N tau T omega| ≤
        ENNReal.ofReal (2 * E omega) := by
    intro omega
    apply ENNReal.ofReal_le_ofReal
    exact boundaryJumpProcess_abs_le_two_mul_envelope
      w.martingale_isRightContinuous w.martingale_hasLeftLimits
      w.stoppingTime_le_horizon w.martingale_envelope_eq_iSup omega
  calc
    (∫⁻ omega, ENNReal.ofReal
        |boundaryJumpProcess w.N tau T omega| ∂mu) ≤
        ∫⁻ omega, ENNReal.ofReal (2 * E omega) ∂mu := by
      exact lintegral_mono hBound
    _ = ∫⁻ omega, (2 : ENNReal) * ENNReal.ofReal (E omega) ∂mu := by
      apply lintegral_congr
      intro omega
      rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2),
        ENNReal.ofReal_ofNat]
    _ = 2 * (∫⁻ omega, ENNReal.ofReal (E omega) ∂mu) := by
      have hEmeas : AEMeasurable
          (fun omega => ENNReal.ofReal (E omega)) mu := by
        exact w.martingale_envelope_stronglyMeasurable.aemeasurable.ennreal_ofReal
      rw [← lintegral_const_mul'' (2 : ENNReal) hEmeas]
    _ = 2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w := by
      congr 1
      change (∫⁻ omega, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N
            (fun omega => (tau omega : WithTop NNReal))) T omega) ∂mu) = _
      unfold prelocalH1SupWitnessMartingaleCost
      unfold prelocalH1SupMartingaleRunningSupExpectation
      rw [eLpNorm_one_eq_lintegral_enorm
        w.martingale_envelope_stronglyMeasurable.aestronglyMeasurable]
      apply lintegral_congr
      intro omega
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg]
      exact hE_nonnegative omega

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_eVariationOn_Icc_le
    {N : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (hTauT : ∀ omega, tau omega ≤ T) :
    ∀ omega,
      eVariationOn (boundaryJumpProcess N tau · omega) (Icc 0 T) ≤
        ENNReal.ofReal |boundaryJumpProcess N tau T omega| := by
  intro omega
  let c : Real := boundaryJumpProcess N tau T omega
  have hPath : (boundaryJumpProcess N tau · omega) =
      (fun t => if tau omega ≤ t then c else 0) := by
    funext t
    by_cases ht : tau omega ≤ t
    · have hτT : tau omega ≤ T := hTauT omega
      rw [boundaryJumpProcess]
      rw [postStopSampled_eq_of_ge (processLeftJump N) tau ht]
      simp only [ite_eq_left ht]
      change processLeftJump N (tau omega) omega = c
      dsimp [c]
      rw [boundaryJumpProcess,
        postStopSampled_eq_of_ge (processLeftJump N) tau hτT]
    · rw [boundaryJumpProcess,
        postStopSampled_eq_zero_of_lt (processLeftJump N) tau
          (lt_of_not_ge ht)]
      simp only [ite_eq_right ht]
  rw [hPath]
  have hmono_nonneg : ∀ {d : Real}, 0 ≤ d →
      Monotone (fun t : NNReal => if tau omega ≤ t then d else 0) := by
    intro d hd s t hst
    by_cases hs : tau omega ≤ s
    · have ht : tau omega ≤ t := hs.trans hst
      simp only [hs, ht, ↓reduceIte]
      exact le_rfl
    · by_cases ht : tau omega ≤ t
      · simp only [hs, ht, ↓reduceIte]
        exact hd
      · simp only [hs, ht, ↓reduceIte, le_refl]
  have hmono_nonpos : ∀ {d : Real}, d ≤ 0 →
      Antitone (fun t : NNReal => if tau omega ≤ t then d else 0) := by
    intro d hd s t hst
    by_cases hs : tau omega ≤ s
    · have ht : tau omega ≤ t := hs.trans hst
      simp only [hs, ht, ↓reduceIte]
      exact le_rfl
    · by_cases ht : tau omega ≤ t
      · simp only [hs, ht, ↓reduceIte]
        exact hd
      · simp only [hs, ht, ↓reduceIte, le_refl]
  by_cases hc : 0 ≤ c
  · have hmono := hmono_nonneg hc
    have hEq := (monotoneOn_univ.2 hmono).eVariationOn_eq
      (show (0 : NNReal) ∈ Set.univ from Set.mem_univ _)
      (show T ∈ Set.univ from Set.mem_univ _)
    have hEq' : eVariationOn
        (fun t : NNReal => if tau omega ≤ t then c else 0) (Icc 0 T) =
        ENNReal.ofReal ((if tau omega ≤ T then c else 0) -
          if tau omega ≤ 0 then c else 0) := by
      simpa only [Set.univ_inter] using hEq
    rw [hEq']
    by_cases hτ0 : tau omega = 0
    · have hzero : c = 0 := by
        dsimp [c]
        rw [boundaryJumpProcess_at_horizon_eq_processLeftJump hTauT omega,
          hτ0]
        unfold processLeftJump
        rw [show Function.leftLim (fun s => N s omega) 0 = N 0 omega from
          leftLim_eq_of_isBot isBot_bot]
        simp
      simp [hzero]
    · have hτpos : 0 < tau omega := (pos_iff_ne_zero).2 hτ0
      have hzero : (if tau omega ≤ (0 : NNReal) then c else 0) = 0 := by
        simp [not_le_of_gt hτpos]
      have hterminal : (if tau omega ≤ T then c else 0) = c := by
        simp [hTauT omega]
      rw [hzero, hterminal, sub_zero]
      exact ENNReal.ofReal_le_ofReal (le_abs_self c)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    rw [← pathVariation_neg]
    have hmono := hmono_nonpos hc'
    have hmonoNeg : Monotone (fun t : NNReal =>
        - (if tau omega ≤ t then c else 0)) := by
      intro s t hst
      exact neg_le_neg (hmono hst)
    have hEq := (monotoneOn_univ.2 hmonoNeg).eVariationOn_eq
      (show (0 : NNReal) ∈ Set.univ from Set.mem_univ _)
      (show T ∈ Set.univ from Set.mem_univ _)
    have hEq' : eVariationOn
        (fun t : NNReal => - (if tau omega ≤ t then c else 0)) (Icc 0 T) =
        ENNReal.ofReal ((- (if tau omega ≤ T then c else 0)) -
          - (if tau omega ≤ 0 then c else 0)) := by
      simpa only [Set.univ_inter] using hEq
    rw [hEq']
    by_cases hτ0 : tau omega = 0
    · have hzero : c = 0 := by
        dsimp [c]
        rw [boundaryJumpProcess_at_horizon_eq_processLeftJump hTauT omega,
          hτ0]
        unfold processLeftJump
        rw [show Function.leftLim (fun s => N s omega) 0 = N 0 omega from
          leftLim_eq_of_isBot isBot_bot]
        simp
      simp [hzero]
    · have hτpos : 0 < tau omega := (pos_iff_ne_zero).2 hτ0
      have hzero : - (if tau omega ≤ (0 : NNReal) then c else 0) = 0 := by
        simp [not_le_of_gt hτpos]
      have hterminal : - (if tau omega ≤ T then c else 0) = -c := by
        simp [hTauT omega]
      rw [hzero, hterminal, sub_zero]
      rw [abs_of_nonpos hc']

omit [MeasurableSpace Ω] in
private theorem eVariationOn_const_eq_zero
    {Time : Type*} [LinearOrder Time] (c : Real) (s : Set Time) :
    eVariationOn (fun _ : Time => c) s = 0 := by
  rw [eVariationOn]
  apply le_antisymm
  · apply iSup_le
    intro p
    simp
  · exact bot_le

omit [MeasurableSpace Ω] in
private theorem boundedVariationOn_const_path
    (c : Real) : BoundedVariationOn (fun _ : NNReal => c) Set.univ := by
  change eVariationOn (fun _ : NNReal => c) Set.univ ≠ ∞
  rw [eVariationOn_const_eq_zero]
  exact ENNReal.zero_ne_top

theorem measurable_eVariationOn_Icc_of_stronglyAdapted_rightContinuous
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {D : Process Ω} {T : NNReal}
    (hD : StronglyAdapted F D)
    (hDRight : ∀ omega t,
      ContinuousWithinAt (D · omega) (Ici t) t) :
    Measurable (fun omega => eVariationOn
      (D · omega) (Icc 0 T)) := by
  have hEq : (fun omega => eVariationOn
        (D · omega) (Icc 0 T)) =
      (fun omega => ⨆ r, FiniteVariationFactorialApproximation.eGridVariation
        (D · omega) T r) := by
    funext omega
    exact FiniteVariationFactorialApproximation.eVariationOn_Icc_eq_iSup_eGridVariation
      (D · omega) (hDRight omega) T
  rw [hEq]
  apply Measurable.iSup
  intro r
  unfold FiniteVariationFactorialApproximation.eGridVariation
  apply Finset.measurable_fun_sum
  intro k hk
  apply Measurable.edist
  · exact ((hD
      (FiniteVariationFactorialApproximation.point T r (k + 1))).mono
      (F.le (FiniteVariationFactorialApproximation.point T r (k + 1)))).measurable
  · exact ((hD
      (FiniteVariationFactorialApproximation.point T r k)).mono
      (F.le (FiniteVariationFactorialApproximation.point T r k))).measurable

/-! ## Normalized boundary remainder -/

/-- The zero-normalized finite-variation remainder left after removing the
stopped martingale and its boundary jump. -/
noncomputable def strictPrefixBoundaryRemainder
    (N A : Process Ω) (tau : Ω → NNReal) : Process Ω :=
  fun t omega => strictPrefixProcess A tau t omega -
    boundaryJumpProcess N tau t omega - A 0 omega

omit [MeasurableSpace Ω] in
theorem strictPrefixProcess_zero
    (A : Process Ω) (tau : Ω → NNReal) :
    strictPrefixProcess A tau 0 = A 0 := by
  funext omega
  by_cases h : 0 < tau omega
  · rw [strictPrefixProcess_eq_of_lt A tau h]
  · have hτ : tau omega = 0 := by
      exact le_antisymm (not_lt.mp h) bot_le
    rw [strictPrefixProcess_eq_of_ge A tau (by rw [hτ])]
    simpa only [hτ] using
      (show Function.leftLim (fun s => A s omega) 0 = A 0 omega from
        leftLim_eq_of_isBot isBot_bot)

omit [MeasurableSpace Ω] in
theorem strictPrefixBoundaryRemainder_zero
    (N A : Process Ω) (tau : Ω → NNReal) :
    strictPrefixBoundaryRemainder N A tau 0 = 0 := by
  funext omega
  rw [strictPrefixBoundaryRemainder, strictPrefixProcess_zero,
    boundaryJumpProcess_zero]
  simp

theorem strictPrefixBoundaryRemainder_stronglyAdapted
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {N A : Process Ω} {tau : Ω → NNReal}
    (hN : StronglyAdapted F N)
    (hNRight : ∀ omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNLeft : ProcessHasLeftLimits N)
    (hA : StronglyAdapted F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t)
    (hALeft : ProcessHasLeftLimits A)
    (hTau : IsStoppingTime F
      (fun omega => (tau omega : WithTop NNReal))) :
    StronglyAdapted F (strictPrefixBoundaryRemainder N A tau) := by
  have hC : StronglyAdapted F (strictPrefixProcess A tau) :=
    strictPrefixProcess_stronglyAdapted A tau hA hARight hALeft hTau
  have hJ : StronglyAdapted F (boundaryJumpProcess N tau) :=
    boundaryJumpProcess_stronglyAdapted hN hNRight hNLeft hTau
  have hA0 : StronglyAdapted F (fun _t omega => A 0 omega) := by
    intro t
    exact (hA 0).mono (F.mono bot_le)
  unfold strictPrefixBoundaryRemainder
  exact (hC.sub hJ).sub hA0

omit [MeasurableSpace Ω] in
theorem strictPrefixBoundaryRemainder_rightContinuous
    {N A : Process Ω} {tau : Ω → NNReal}
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t) :
    ∀ omega t,
      ContinuousWithinAt
        (strictPrefixBoundaryRemainder N A tau · omega) (Ici t) t := by
  intro omega t
  exact (strictPrefixProcess_rightContinuous A tau hARight omega t).sub
    (boundaryJumpProcess_rightContinuous N tau omega t) |>.sub
      continuousWithinAt_const

omit [MeasurableSpace Ω] in
theorem strictPrefixBoundaryRemainder_hasLeftLimits
    {N A : Process Ω} {tau : Ω → NNReal}
    (hALeft : ProcessHasLeftLimits A) :
    ProcessHasLeftLimits (strictPrefixBoundaryRemainder N A tau) := by
  have hC := strictPrefixProcess_hasLeftLimits A tau hALeft
  have hJ := boundaryJumpProcess_hasLeftLimits N tau
  have hA0 : ProcessHasLeftLimits (fun _t _omega => A 0 _omega) := by
    intro omega t
    apply tendsto_leftLim_of_tendsto
    exact ⟨A 0 omega, tendsto_const_nhds⟩
  unfold strictPrefixBoundaryRemainder
  exact (hC.sub hJ).sub hA0

omit [MeasurableSpace Ω] in
theorem strictPrefixBoundaryRemainder_boundedVariation
    {N A : Process Ω} {tau : Ω → NNReal}
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ) :
    ∀ omega, BoundedVariationOn
      (strictPrefixBoundaryRemainder N A tau · omega) Set.univ := by
  intro omega
  exact boundedVariationOn_add
    (boundedVariationOn_add
      (strictPrefixProcess_boundedVariation A tau hAVar omega)
      (boundedVariationOn_neg (boundaryJumpProcess_boundedVariation N tau omega)))
    (boundedVariationOn_neg (boundedVariationOn_const_path (A 0 omega)))

omit [MeasurableSpace Ω] in
theorem strictPrefixBoundaryRemainder_constant_after
    {N A : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (hTauT : ∀ omega, tau omega ≤ T)
    (hT : ∀ omega t, T ≤ t →
      strictPrefixProcess A tau t omega = strictPrefixProcess A tau T omega) :
    ∀ omega t, T ≤ t →
      strictPrefixBoundaryRemainder N A tau t omega =
        strictPrefixBoundaryRemainder N A tau T omega := by
  intro omega t htt
  unfold strictPrefixBoundaryRemainder
  rw [hT omega t htt,
    boundaryJumpProcess_constant_after hTauT omega t htt]

omit [MeasurableSpace Ω] in
private theorem strictPrefixBoundaryRemainder_eVariationOn_Icc_le
    {N A : Process Ω} {tau : Ω → NNReal} {T : NNReal} :
    (hTauT : ∀ omega, tau omega ≤ T) →
    ∀ omega,
      eVariationOn
          (strictPrefixBoundaryRemainder N A tau · omega) (Icc 0 T) ≤
        eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 T) +
          ENNReal.ofReal |boundaryJumpProcess N tau T omega| := by
  intro hTauT omega
  let C : NNReal → Real := (strictPrefixProcess A tau · omega)
  let J : NNReal → Real := (boundaryJumpProcess N tau · omega)
  let c : Real := A 0 omega
  have hFirst := eVariationOn_add_le_real C (fun t => -J t) (Icc 0 T)
  have hSecond := eVariationOn_add_le_real
    (fun t => C t - J t) (fun _ : NNReal => -c) (Icc 0 T)
  calc
    eVariationOn
        (strictPrefixBoundaryRemainder N A tau · omega) (Icc 0 T) =
        eVariationOn (fun t => (C t - J t) + (-c)) (Icc 0 T) := by
      congr 1
    _ ≤ eVariationOn (fun t => C t - J t) (Icc 0 T) +
          eVariationOn (fun _ : NNReal => -c) (Icc 0 T) := hSecond
    _ ≤ (eVariationOn C (Icc 0 T) +
          eVariationOn (fun t => -J t) (Icc 0 T)) +
          eVariationOn (fun _ : NNReal => -c) (Icc 0 T) := by
      exact add_le_add hFirst le_rfl
    _ ≤ eVariationOn C (Icc 0 T) +
          eVariationOn J (Icc 0 T) := by
      rw [pathVariation_neg, eVariationOn_const_eq_zero]
      simp
    _ ≤ eVariationOn C (Icc 0 T) +
          ENNReal.ofReal |boundaryJumpProcess N tau T omega| := by
      exact add_le_add le_rfl
        (boundaryJumpProcess_eVariationOn_Icc_le hTauT omega)

omit [MeasurableSpace Ω] in
theorem strictPrefixBoundaryRemainder_cumulativeVariation_le
    {N A : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (hTauT : ∀ omega, tau omega ≤ T)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ) :
    ∀ omega,
      localVariation
          (strictPrefixBoundaryRemainder N A tau) T omega ≤
        (eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 T)).toReal +
          |boundaryJumpProcess N tau T omega| := by
  intro omega
  have hCVar : BoundedVariationOn
      (strictPrefixProcess A tau · omega) Set.univ :=
    strictPrefixProcess_boundedVariation A tau hAVar omega
  have hCNeTop : eVariationOn
      (strictPrefixProcess A tau · omega) (Icc 0 T) ≠ ∞ :=
    ne_top_of_le_ne_top hCVar (eVariationOn.mono _ (Set.subset_univ _))
  have hRNeTop :
      eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 T) +
          ENNReal.ofReal |boundaryJumpProcess N tau T omega| ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hCNeTop, ENNReal.ofReal_ne_top⟩
  have hDVar : eVariationOn
      (strictPrefixBoundaryRemainder N A tau · omega) (Icc 0 T) ≤
      eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 T) +
        ENNReal.ofReal |boundaryJumpProcess N tau T omega| :=
    strictPrefixBoundaryRemainder_eVariationOn_Icc_le (N := N) (A := A)
      (tau := tau) (T := T) hTauT omega
  have hDNeTop : eVariationOn
      (strictPrefixBoundaryRemainder N A tau · omega) (Icc 0 T) ≠ ∞ :=
    ne_top_of_le_ne_top hRNeTop hDVar
  have hToReal := (ENNReal.toReal_le_toReal hDNeTop hRNeTop).2 hDVar
  have hRhsToReal :
      (eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 T) +
        ENNReal.ofReal |boundaryJumpProcess N tau T omega|).toReal =
        (eVariationOn (strictPrefixProcess A tau · omega) (Icc 0 T)).toReal +
          |boundaryJumpProcess N tau T omega| := by
    rw [ENNReal.toReal_add hCNeTop ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (abs_nonneg _)]
  have hCommon : localVariation
        (strictPrefixBoundaryRemainder N A tau) T omega =
      (eVariationOn
        (strictPrefixBoundaryRemainder N A tau · omega) (Icc 0 T)).toReal := by
    rw [commonStopCumulativeVariation_apply,
      variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ T from bot_le),
      Set.univ_inter]
  rw [hCommon]
  rw [hRhsToReal] at hToReal
  exact hToReal

theorem measurable_commonStopCumulativeVariation_of_regularProcess
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {D : Process Ω} {T : NNReal}
    (hD : StronglyAdapted F D)
    (hDRight : ∀ omega t,
      ContinuousWithinAt (D · omega) (Ici t) t) :
    Measurable (localVariation D T) := by
  have hVarMeas := measurable_eVariationOn_Icc_of_stronglyAdapted_rightContinuous
    hD hDRight (T := T)
  have hEq : localVariation D T =
      (fun omega => (eVariationOn (D · omega) (Icc 0 T)).toReal) := by
    funext omega
    rw [commonStopCumulativeVariation_apply,
      variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ T from bot_le),
      Set.univ_inter]
  rw [hEq]
  exact hVarMeas.ennreal_toReal

theorem strictPrefixBoundaryRemainder_expected_cumulativeVariation_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    (∫⁻ omega, ENNReal.ofReal
      (localVariation
        (strictPrefixBoundaryRemainder w.N w.A tau) T omega) ∂mu) ≤
      prelocalH1SupWitnessVariationCost (mu := mu) w +
        2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w := by
  let C : Process Ω := strictPrefixProcess w.A tau
  let D : Process Ω := strictPrefixBoundaryRemainder w.N w.A tau
  have hCVarMeas : Measurable (fun omega =>
      eVariationOn (C · omega) (Set.Icc 0 T)) := by
    simpa only [C] using w.finiteVariation_measurable
  have hCVarTop : ∀ omega,
      eVariationOn (C · omega) (Set.Icc 0 T) ≠ ∞ := by
    intro omega
    have hCBV : BoundedVariationOn
        (strictPrefixProcess w.A tau · omega) Set.univ :=
      strictPrefixProcess_boundedVariation w.A tau
        w.finiteVariation_isBoundedVariation omega
    exact ne_top_of_le_ne_top hCBV
      (eVariationOn.mono _ (Set.subset_univ _))
  have hDAdapted : StronglyAdapted F D := by
    simpa only [D] using strictPrefixBoundaryRemainder_stronglyAdapted
      w.martingale_isStronglyAdapted w.martingale_isRightContinuous
      w.martingale_hasLeftLimits w.finiteVariation_isStronglyAdapted
      w.finiteVariation_isRightContinuous w.finiteVariation_hasLeftLimits
      w.stoppingTime
  have hDRight : ∀ omega t,
      ContinuousWithinAt (D · omega) (Ici t) t := by
    simpa only [D] using strictPrefixBoundaryRemainder_rightContinuous
      w.finiteVariation_isRightContinuous
  have hDVarMeas : Measurable (localVariation D T) :=
    measurable_commonStopCumulativeVariation_of_regularProcess hDAdapted hDRight
  have hJStrong : StronglyAdapted F
      (boundaryJumpProcess w.N tau) :=
    boundaryJumpProcess_stronglyAdapted w.martingale_isStronglyAdapted
      w.martingale_isRightContinuous w.martingale_hasLeftLimits w.stoppingTime
  have hJMeas : Measurable (boundaryJumpProcess w.N tau T) :=
    ((hJStrong T).mono (F.le T)).measurable
  have hJumpMeas : AEMeasurable
      (fun omega => ENNReal.ofReal
        |boundaryJumpProcess w.N tau T omega|) mu :=
    hJMeas.aemeasurable.norm.ennreal_ofReal
  have hPoint : ∀ omega,
      ENNReal.ofReal (localVariation D T omega) ≤
        eVariationOn (C · omega) (Set.Icc 0 T) +
          ENNReal.ofReal |boundaryJumpProcess w.N tau T omega| := by
    intro omega
    have hVar := strictPrefixBoundaryRemainder_cumulativeVariation_le
      (N := w.N) (A := w.A) (tau := tau) (T := T)
      w.stoppingTime_le_horizon
      w.finiteVariation_isBoundedVariation omega
    dsimp only [D, C]
    calc
      ENNReal.ofReal
          (localVariation
            (strictPrefixBoundaryRemainder w.N w.A tau) T omega) ≤
          ENNReal.ofReal
            ((eVariationOn (strictPrefixProcess w.A tau · omega)
              (Set.Icc 0 T)).toReal +
              |boundaryJumpProcess w.N tau T omega|) :=
        ENNReal.ofReal_le_ofReal hVar
      _ = eVariationOn (strictPrefixProcess w.A tau · omega)
            (Set.Icc 0 T) +
          ENNReal.ofReal |boundaryJumpProcess w.N tau T omega| := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _),
          ENNReal.ofReal_toReal (hCVarTop omega)]
  calc
    (∫⁻ omega, ENNReal.ofReal
        (localVariation D T omega) ∂mu) ≤
        ∫⁻ omega, eVariationOn (C · omega) (Set.Icc 0 T) +
          ENNReal.ofReal |boundaryJumpProcess w.N tau T omega| ∂mu :=
      lintegral_mono hPoint
    _ = (∫⁻ omega, eVariationOn (C · omega) (Set.Icc 0 T) ∂mu) +
          ∫⁻ omega, ENNReal.ofReal
            |boundaryJumpProcess w.N tau T omega| ∂mu := by
      rw [lintegral_add_left' hCVarMeas.aemeasurable]
    _ ≤ prelocalH1SupWitnessVariationCost (mu := mu) w +
          2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w := by
      exact add_le_add (by rfl)
        (boundaryJumpProcess_expected_abs_le_two_martingaleCost w)

/-! ## The normalized boundary remainder -/

theorem strictPrefixBoundaryRemainder_l1Data
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu)
      (strictPrefixBoundaryRemainder w.N w.A tau) T := by
  let D : Process Ω := strictPrefixBoundaryRemainder w.N w.A tau
  have hDAdapted : StronglyAdapted F D := by
    simpa only [D] using strictPrefixBoundaryRemainder_stronglyAdapted
      (N := w.N) (A := w.A) (tau := tau)
      w.martingale_isStronglyAdapted
      w.martingale_isRightContinuous w.martingale_hasLeftLimits
      w.finiteVariation_isStronglyAdapted
      w.finiteVariation_isRightContinuous w.finiteVariation_hasLeftLimits
      w.stoppingTime
  have hDRight : ∀ omega t,
      ContinuousWithinAt (D · omega) (Ici t) t := by
    simpa only [D] using strictPrefixBoundaryRemainder_rightContinuous
      (N := w.N) (A := w.A) (tau := tau)
      w.finiteVariation_isRightContinuous
  have hDLeft : ProcessHasLeftLimits D := by
    simpa only [D] using strictPrefixBoundaryRemainder_hasLeftLimits
      (N := w.N) (A := w.A) (tau := tau)
      w.finiteVariation_hasLeftLimits
  have hDBV : ∀ omega, BoundedVariationOn (D · omega) Set.univ := by
    simpa only [D] using strictPrefixBoundaryRemainder_boundedVariation
      (N := w.N) (A := w.A) (tau := tau)
      w.finiteVariation_isBoundedVariation
  have hDZero : D 0 = 0 := by
    simpa only [D] using strictPrefixBoundaryRemainder_zero w.N w.A tau
  have hDConst : ∀ omega t, T ≤ t → D t omega = D T omega := by
    intro omega t htt
    simpa only [D] using
      (strictPrefixBoundaryRemainder_constant_after
        (N := w.N) (A := w.A) (tau := tau) (T := T)
        w.stoppingTime_le_horizon
        (fun omega t htt => strictPrefixProcess_constant_after w.A tau
          (w.stoppingTime_le_horizon omega) htt) omega t htt)
  have hCVarMeas : Measurable (fun omega =>
      eVariationOn (strictPrefixProcess w.A tau · omega) (Icc 0 T)) :=
    measurable_strictPrefixVariation_of_regularProcess
      w.A tau T w.finiteVariation_isStronglyAdapted
      w.finiteVariation_isRightContinuous w.finiteVariation_hasLeftLimits
      w.stoppingTime
  have hCVarIntegrable : Integrable (fun omega =>
      (eVariationOn (strictPrefixProcess w.A tau · omega) (Icc 0 T)).toReal) mu := by
    apply integrable_toReal_of_lintegral_ne_top hCVarMeas.aemeasurable
    simpa only [prelocalH1SupFiniteVariationExpectedVariation] using
      w.finiteVariation_integral_ne_top
  have hJumpIntegrable : Integrable (fun omega =>
      |boundaryJumpProcess w.N tau T omega|) mu := by
    exact boundaryJumpProcess_memLp_one w
  have hRhsIntegrable : Integrable (fun omega =>
      (eVariationOn (strictPrefixProcess w.A tau · omega) (Icc 0 T)).toReal +
        |boundaryJumpProcess w.N tau T omega|) mu :=
    hCVarIntegrable.add hJumpIntegrable
  have hDVarMeas : Measurable (localVariation D T) :=
    measurable_commonStopCumulativeVariation_of_regularProcess hDAdapted hDRight
  have hDVarBound : ∀ omega,
      localVariation D T omega ≤
        (eVariationOn (strictPrefixProcess w.A tau · omega) (Icc 0 T)).toReal +
          |boundaryJumpProcess w.N tau T omega| := by
    simpa only [D] using strictPrefixBoundaryRemainder_cumulativeVariation_le
      w.stoppingTime_le_horizon w.finiteVariation_isBoundedVariation
  refine {
    stronglyAdapted := hDAdapted
    rightContinuous := hDRight
    hasLeftLimits := hDLeft
    boundedVariation := hDBV
    zero := hDZero
    constant_after := hDConst
    terminalVariation_integrable := ?_ }
  apply hRhsIntegrable.mono hDVarMeas.aestronglyMeasurable
  filter_upwards [] with omega
  have hDNonnegative : 0 ≤ localVariation D T omega := by
    rw [commonStopCumulativeVariation_apply]
    exact variationOnFromTo.nonneg_of_le _ _ (show (0 : NNReal) ≤ T from bot_le)
  have hRhsNonnegative : 0 ≤
      (eVariationOn (strictPrefixProcess w.A tau · omega) (Icc 0 T)).toReal +
        |boundaryJumpProcess w.N tau T omega| :=
    add_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hDNonnegative,
    Real.norm_eq_abs, abs_of_nonneg hRhsNonnegative]
  exact hDVarBound omega

/-! ## The global special-decomposition boundary -/

/-- A process-level global special decomposition obtained from a strict-prefix
boundary identity.  The certificate deliberately records indistinguishability
rather than silently turning the value-truncation version into an exact
pointwise carrier witness. -/
structure StrictPrefixBoundaryGlobalSpecialDecomposition
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω}
    (X : Process Ω) (tau : Ω → NNReal) (T : NNReal)
    (source : EmeryPrelocalH1SupWitness
      (F := F) (mu := mu) X tau T) where
  M : Process Ω
  A : Process Ω
  residual : Process Ω
  residual_martingale : Martingale residual F mu
  M_isStronglyAdapted : StronglyAdapted F M
  M_isLocalMartingale : LocalMartingale M F mu
  M_rightContinuous : ∀ omega t,
    ContinuousWithinAt (M · omega) (Ici t) t
  M_leftLimits : ProcessHasLeftLimits M
  A_isStronglyPredictable : IsStronglyPredictable F A
  A_isStronglyAdapted : StronglyAdapted F A
  A_rightContinuous : ∀ omega t,
    ContinuousWithinAt (A · omega) (Ici t) t
  A_leftLimits : ProcessHasLeftLimits A
  A_boundedVariation : ∀ omega,
    BoundedVariationOn (A · omega) Set.univ
  A_variation_measurable : Measurable (fun omega =>
    eVariationOn (A · omega) (Set.Icc 0 T))
  A_variation_integrable : Integrable (fun omega =>
    (eVariationOn (A · omega) (Set.Icc 0 T)).toReal) mu
  A_expected_variation_le :
    (∫⁻ omega, eVariationOn (A · omega) (Set.Icc 0 T) ∂mu) ≤
      prelocalH1SupWitnessVariationCost (mu := mu) source +
        2 * prelocalH1SupWitnessMartingaleCost (mu := mu) source
  decomposition : ProcessIndistinguishable mu
    (strictPrefixProcess X tau)
    (fun t omega => M t omega + A t omega)

/-- Consume the value-truncation finite-variation producer for the boundary
remainder.  The hypothesis `hTarget` is intentionally explicit: the
flattened witness gives exact information on the open prefix, while its
strict-prefix extension at a zero stopping time also depends on the chosen
time-zero convention for the target. -/
theorem exists_strictPrefixBoundaryGlobalSpecialDecomposition
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T)
    (hUsual : Filtration.UsualConditions mu F)
    (hTarget : strictPrefixProcess X tau =
      strictPrefixProcess (fun t omega => w.N t omega + w.A t omega) tau) :
    Nonempty (StrictPrefixBoundaryGlobalSpecialDecomposition
      (F := F) (mu := mu) X tau T w) := by
  let D : Process Ω := strictPrefixBoundaryRemainder w.N w.A tau
  have hDData : NormalizedAdaptedCadlagFiniteVariationL1Data
      (F := F) (mu := mu) D T := by
    simpa only [D] using strictPrefixBoundaryRemainder_l1Data w
  obtain ⟨hFV⟩ := exists_valueTruncationFiniteVariationPredictableLimit
    (F := F) (mu := mu) hDData hUsual
  let τ : Ω → WithTop NNReal := fun omega => (tau omega : WithTop NNReal)
  have hNStoppedAdapted : StronglyAdapted F
      (MeasureTheory.stoppedProcess w.N τ) :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      w.martingale_isStronglyAdapted w.stoppingTime
      w.martingale_isRightContinuous
  have hNStoppedRight : ∀ omega t,
      ContinuousWithinAt
        (MeasureTheory.stoppedProcess w.N τ · omega) (Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous w.N
      w.martingale_isRightContinuous
  have hNStoppedLeft : ProcessHasLeftLimits
      (MeasureTheory.stoppedProcess w.N τ) :=
    w.martingale_hasLeftLimits.stoppedProcess τ
  have hNStoppedLocal : LocalMartingale
      (MeasureTheory.stoppedProcess w.N τ) F mu := by
    simpa only [τ] using LocalMartingale.stoppedProcess_of_rightContinuous
      w.martingale_isLocalMartingale w.martingale_isRightContinuous
      w.stoppingTime
  have hRDefinition : hFV.residual = fun t omega =>
      D t omega - hFV.Ap t omega := by
    simpa only [D] using hFV.residual_definition
  have hRAdapted : StronglyAdapted F hFV.residual :=
    hFV.residual_stronglyAdapted
  have hRRight : ∀ omega t,
      ContinuousWithinAt (hFV.residual · omega) (Ici t) t := by
    rw [hRDefinition]
    intro omega t
    exact (hDData.rightContinuous omega t).sub
      (hFV.Ap_rightContinuous omega t)
  have hRLeft : ProcessHasLeftLimits hFV.residual := by
    rw [hRDefinition]
    exact hDData.hasLeftLimits.sub hFV.Ap_leftLimits
  have hRLocal : LocalMartingale hFV.residual F mu :=
    ProbabilityTheory.Locally.of_prop hFV.residual_martingale
  let M : Process Ω := fun t omega =>
    MeasureTheory.stoppedProcess w.N τ t omega + hFV.residual t omega
  let A : Process Ω := fun t omega => hFV.Ap t omega + w.A 0 omega
  have hA0Adapted : StronglyAdapted F (fun _t omega => w.A 0 omega) := by
    intro t
    exact (w.finiteVariation_isStronglyAdapted 0).mono (F.mono bot_le)
  have hA0Predictable : IsStronglyPredictable F
      (fun _t omega => w.A 0 omega) :=
    LeftContinuousPredictable.stronglyPredictable_of_leftContinuous
      hA0Adapted (fun _ _ => continuousWithinAt_const)
  have hA0Right : ∀ omega t,
      ContinuousWithinAt (fun _t : NNReal => w.A 0 omega) (Ici t) t :=
    fun _ _ => continuousWithinAt_const
  have hA0Left : ProcessHasLeftLimits
      (fun _t omega => w.A 0 omega) := by
    intro omega t
    apply tendsto_leftLim_of_tendsto
    exact ⟨w.A 0 omega, tendsto_const_nhds⟩
  have hMAdapted : StronglyAdapted F M := by
    change StronglyAdapted F (MeasureTheory.stoppedProcess w.N τ + hFV.residual)
    exact hNStoppedAdapted.add hRAdapted
  have hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t := by
    intro omega t
    exact (hNStoppedRight omega t).add (hRRight omega t)
  have hMLeft : ProcessHasLeftLimits M := by
    simpa only [M] using hNStoppedLeft.add hRLeft
  have hMLocal : LocalMartingale M F mu := by
    simpa only [M] using LocalMartingale.add_of_rightContinuous
      hNStoppedLocal hRLocal hNStoppedRight hRRight
  have hAPredictable : IsStronglyPredictable F A := by
    change IsStronglyPredictable F (hFV.Ap + fun _t omega => w.A 0 omega)
    exact hFV.Ap_stronglyPredictable.add hA0Predictable
  have hAAdapted : StronglyAdapted F A := by
    change StronglyAdapted F (hFV.Ap + fun _t omega => w.A 0 omega)
    exact hFV.Ap_stronglyPredictable.stronglyAdapted.add hA0Adapted
  have hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t := by
    intro omega t
    exact (hFV.Ap_rightContinuous omega t).add (hA0Right omega t)
  have hALeft : ProcessHasLeftLimits A := by
    simpa only [A] using hFV.Ap_leftLimits.add hA0Left
  have hABV : ∀ omega, BoundedVariationOn (A · omega) Set.univ := by
    intro omega
    exact boundedVariationOn_add (hFV.Ap_boundedVariation omega)
      (boundedVariationOn_const_path (w.A 0 omega))
  have hAvarEq : ∀ omega,
      eVariationOn (A · omega) (Icc 0 T) =
        eVariationOn (hFV.Ap · omega) (Icc 0 T) := by
    intro omega
    simpa only [A] using
      pathVariation_add_const (w.A 0 omega) (Icc 0 T)
  have hAvarMeas : Measurable (fun omega =>
      eVariationOn (A · omega) (Icc 0 T)) := by
    have hEq : (fun omega => eVariationOn (A · omega) (Icc 0 T)) =
        (fun omega => eVariationOn (hFV.Ap · omega) (Icc 0 T)) := by
      funext omega
      exact hAvarEq omega
    rw [hEq]
    exact hFV.Ap_totalVariation_measurable
  have hAvarIntegrable : Integrable (fun omega =>
      (eVariationOn (A · omega) (Icc 0 T)).toReal) mu := by
    have hEq : (fun omega =>
        (eVariationOn (A · omega) (Icc 0 T)).toReal) =
        (fun omega =>
          (eVariationOn (hFV.Ap · omega) (Icc 0 T)).toReal) := by
      funext omega
      rw [hAvarEq omega]
    rw [hEq]
    exact hFV.Ap_totalVariation_integrable
  have hAvarExpected :
      (∫⁻ omega, eVariationOn (A · omega) (Icc 0 T) ∂mu) ≤
        prelocalH1SupWitnessVariationCost (mu := mu) w +
          2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w := by
    calc
      (∫⁻ omega, eVariationOn (A · omega) (Icc 0 T) ∂mu) =
          ∫⁻ omega, eVariationOn (hFV.Ap · omega) (Icc 0 T) ∂mu := by
        apply lintegral_congr
        intro omega
        exact hAvarEq omega
      _ ≤ ∫⁻ omega, ENNReal.ofReal
          (localVariation D T omega) ∂mu :=
        hFV.Ap_expected_totalVariation_le
      _ ≤ prelocalH1SupWitnessVariationCost (mu := mu) w +
          2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w :=
        strictPrefixBoundaryRemainder_expected_cumulativeVariation_le w
  have hCanonical : ProcessIndistinguishable mu
      (strictPrefixProcess (fun t omega => w.N t omega + w.A t omega) tau)
      (fun t omega => M t omega + A t omega) := by
    filter_upwards [] with omega
    intro t
    have hIdentity := strictPrefixProcess_add_boundaryJumpProcess_eq_stoppedParts
      tau w.martingale_hasLeftLimits w.finiteVariation_hasLeftLimits t omega
    rw [hIdentity]
    dsimp [M, A]
    rw [hRDefinition]
    dsimp [D]
    unfold strictPrefixBoundaryRemainder
    dsimp [τ]
    ring
  have hDecomposition : ProcessIndistinguishable mu
      (strictPrefixProcess X tau)
      (fun t omega => M t omega + A t omega) := by
    rw [hTarget]
    exact hCanonical
  exact ⟨{
    M := M
    A := A
    residual := hFV.residual
    residual_martingale := hFV.residual_martingale
    M_isStronglyAdapted := hMAdapted
    M_isLocalMartingale := hMLocal
    M_rightContinuous := hMRight
    M_leftLimits := hMLeft
    A_isStronglyPredictable := hAPredictable
    A_isStronglyAdapted := hAAdapted
    A_rightContinuous := hARight
    A_leftLimits := hALeft
    A_boundedVariation := hABV
    A_variation_measurable := hAvarMeas
    A_variation_integrable := hAvarIntegrable
    A_expected_variation_le := hAvarExpected
    decomposition := hDecomposition }⟩

end SIntegrableFiniteVariationBridge
end FTAPTheorem42
