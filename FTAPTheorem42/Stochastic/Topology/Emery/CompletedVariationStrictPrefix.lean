/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
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
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppedProcess
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableStrategyAlgebra

/-!
# Strict-prefix finite-variation stopping

For a finite stopping time `rho`, the closed stopped path contains the jump at
`rho`.  This file removes precisely that boundary jump: the path agrees with
the source before `rho` and is held at its left limit from `rho` onwards.
The construction is pointwise, while the measurability of the sampled left
limit is obtained from the predictable left-limit process and the predictable
graph of a stopping time.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

/-! ## The post-stopping constant and the strict-prefix path -/

/-- A process which is zero before a finite random time and takes its sampled
value from that time on. -/
noncomputable def postStopSampled
    (X : Process Omega) (rho : Omega → NNReal) : Process Omega :=
  fun t omega => if rho omega ≤ t then X (rho omega) omega else 0

/-- The strict-prefix version of a process.  The closed stopped process is
corrected by the value at the stopping time and then restored at the sampled
left limit. -/
noncomputable def strictPrefixProcess
    (A : Process Omega) (rho : Omega → NNReal) : Process Omega :=
  fun t omega =>
    MeasureTheory.stoppedProcess A
      (fun omega => (rho omega : WithTop NNReal)) t omega -
      postStopSampled A rho t omega +
      postStopSampled
        (fun s omega => Function.leftLim (A · omega) s) rho t omega

omit [MeasurableSpace Omega] in
@[simp] theorem postStopSampled_eq_zero_of_lt
    (X : Process Omega) (rho : Omega → NNReal)
    {t : NNReal} {omega : Omega} (h : t < rho omega) :
    postStopSampled X rho t omega = 0 := by
  simp only [postStopSampled, ite_eq_right (not_le.mpr h)]

omit [MeasurableSpace Omega] in
@[simp] theorem postStopSampled_eq_of_ge
    (X : Process Omega) (rho : Omega → NNReal)
    {t : NNReal} {omega : Omega} (h : rho omega ≤ t) :
    postStopSampled X rho t omega = X (rho omega) omega := by
  simp only [postStopSampled, ite_eq_left h]

omit [MeasurableSpace Omega] in
theorem stoppedProcess_eq_of_lt
    (A : Process Omega) (rho : Omega → NNReal)
    {t : NNReal} {omega : Omega} (h : t < rho omega) :
    MeasureTheory.stoppedProcess A
        (fun omega => (rho omega : WithTop NNReal)) t omega = A t omega := by
  unfold MeasureTheory.stoppedProcess
  rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
    WithTop.untop_coe, min_eq_left]
  exact h.le

omit [MeasurableSpace Omega] in
theorem stoppedProcess_eq_of_ge
    (A : Process Omega) (rho : Omega → NNReal)
    {t : NNReal} {omega : Omega} (h : rho omega ≤ t) :
    MeasureTheory.stoppedProcess A
        (fun omega => (rho omega : WithTop NNReal)) t omega = A (rho omega) omega := by
  unfold MeasureTheory.stoppedProcess
  rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
    WithTop.untop_coe, min_eq_right]
  exact h

omit [MeasurableSpace Omega] in
theorem strictPrefixProcess_eq_of_lt
    (A : Process Omega) (rho : Omega → NNReal)
    {t : NNReal} {omega : Omega} (h : t < rho omega) :
    strictPrefixProcess A rho t omega = A t omega := by
  rw [strictPrefixProcess, stoppedProcess_eq_of_lt A rho h,
    postStopSampled_eq_zero_of_lt A rho h,
    postStopSampled_eq_zero_of_lt (fun s omega => Function.leftLim (A · omega) s)
      rho h]
  ring

omit [MeasurableSpace Omega] in
theorem strictPrefixProcess_eq_of_ge
    (A : Process Omega) (rho : Omega → NNReal)
    {t : NNReal} {omega : Omega} (h : rho omega ≤ t) :
    strictPrefixProcess A rho t omega =
      Function.leftLim (fun s => A s omega) (rho omega) := by
  rw [strictPrefixProcess, stoppedProcess_eq_of_ge A rho h,
    postStopSampled_eq_of_ge A rho h,
    postStopSampled_eq_of_ge (fun s omega => Function.leftLim (A · omega) s)
      rho h]
  ring

omit [MeasurableSpace Omega] in
theorem strictPrefixProcess_constant_after
    (A : Process Omega) (rho : Omega → NNReal)
    {T t : NNReal} {omega : Omega} (hρT : rho omega ≤ T) (hTt : T ≤ t) :
    strictPrefixProcess A rho t omega = strictPrefixProcess A rho T omega := by
  rw [strictPrefixProcess_eq_of_ge A rho (hρT.trans hTt),
    strictPrefixProcess_eq_of_ge A rho hρT]

/-! ## Path regularity of the one-jump correction -/

omit [MeasurableSpace Omega] in
theorem postStopSampled_rightContinuous
    (X : Process Omega) (rho : Omega → NNReal) :
    ∀ omega t, ContinuousWithinAt
      (postStopSampled X rho · omega) (Set.Ici t) t := by
  intro omega t
  by_cases htr : t < rho omega
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htr)] with u hu hρ
    simp only [postStopSampled,
      ite_eq_right (not_le.mpr htr),
      ite_eq_right (not_le.mpr (show u < rho omega from hρ))]
  · have hrt : rho omega ≤ t := le_of_not_gt htr
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [postStopSampled, ite_eq_left hrt,
      ite_eq_left (hrt.trans (show t ≤ u from hu))]

omit [MeasurableSpace Omega] in
theorem postStopSampled_hasLeftLimits
    (X : Process Omega) (rho : Omega → NNReal) :
    ProcessHasLeftLimits (postStopSampled X rho) := by
  intro omega t
  by_cases hρt : rho omega < t
  · apply tendsto_leftLim_of_tendsto
    refine ⟨X (rho omega) omega, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [Ico_mem_nhdsLT hρt] with s hs
    simp only [postStopSampled,
      ite_eq_left (show rho omega ≤ s from hs.1)]
  · have htρ : t ≤ rho omega := le_of_not_gt hρt
    apply tendsto_leftLim_of_tendsto
    refine ⟨0, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [postStopSampled,
      ite_eq_right (not_le.mpr (show s < rho omega from
        (show s < t from hs).trans_le htρ))]

omit [MeasurableSpace Omega] in
theorem postStopSampled_boundedVariation
    (X : Process Omega) (rho : Omega → NNReal) :
    ∀ omega, BoundedVariationOn
      (postStopSampled X rho · omega) Set.univ := by
  intro omega
  have hAux : ∀ c : Real, 0 ≤ c →
      BoundedVariationOn
        (fun t : NNReal => if rho omega ≤ t then c else 0) Set.univ := by
    intro c hc
    have hmono : MonotoneOn
        (fun t : NNReal => if rho omega ≤ t then c else 0) Set.univ := by
      intro s hs t ht hst
      by_cases hsρ : rho omega ≤ s
      · have htρ : rho omega ≤ t := hsρ.trans hst
        simp only [hsρ, htρ, ↓reduceIte, le_refl]
      · by_cases htρ : rho omega ≤ t
        · simp only [hsρ, htρ, ↓reduceIte]
          exact hc
        · simp only [hsρ, htρ, ↓reduceIte, le_refl]
    apply hmono.boundedVariationOn (C := c)
    intro t ht
    by_cases hρt : rho omega ≤ t
    · simp only [hρt, ↓reduceIte, abs_of_nonneg hc]
      exact le_rfl
    · simp only [hρt, ↓reduceIte, abs_zero]
      exact hc
  by_cases hc : 0 ≤ X (rho omega) omega
  · change BoundedVariationOn
      (fun t : NNReal => if rho omega ≤ t then X (rho omega) omega else 0) Set.univ
    exact hAux _ hc
  · have hc' : X (rho omega) omega ≤ 0 := le_of_not_ge hc
    have hneg := hAux (-X (rho omega) omega) (neg_nonneg.mpr hc')
    change BoundedVariationOn
      (fun t : NNReal => if rho omega ≤ t then X (rho omega) omega else 0) Set.univ
    have hneg' := boundedVariationOn_neg hneg
    simpa only [Pi.neg_apply, neg_ite, neg_neg, neg_zero] using hneg'

/-! ## Adaptedness of the stopped constants -/

theorem postStopSampled_stronglyAdapted_of_rightContinuous
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (X : Process Omega) (rho : Omega → NNReal)
    (hX : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Set.Ici t) t)
    (hρ : IsStoppingTime F
      (fun omega => (rho omega : WithTop NNReal))) :
    StronglyAdapted F (postStopSampled X rho) := by
  let tau : Omega → WithTop NNReal := fun omega => (rho omega : WithTop NNReal)
  have hStopped : StronglyAdapted F (MeasureTheory.stoppedProcess X tau) :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hX hρ hXRight
  intro t
  have hEvent : MeasurableSet[F t] {omega | rho omega ≤ t} := by
    simpa only [tau, WithTop.coe_le_coe] using hρ.measurableSet_le t
  have hInd := (hStopped t).indicator hEvent
  change StronglyMeasurable[F t]
    (fun omega => if rho omega ≤ t then
      MeasureTheory.stoppedProcess X tau t omega else 0) at hInd
  convert hInd using 1
  funext omega
  by_cases h : rho omega ≤ t
  · simp only [h, ↓reduceIte]
    calc
      postStopSampled X rho t omega = X (rho omega) omega :=
        postStopSampled_eq_of_ge X rho h
      _ = MeasureTheory.stoppedProcess X tau t omega := by
        symm
        simpa [tau] using stoppedProcess_eq_of_ge X rho h
  · simp only [h, ↓reduceIte]
    exact postStopSampled_eq_zero_of_lt X rho (lt_of_not_ge h)

theorem postStopSampled_stronglyAdapted_of_predictable
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (X : Process Omega) (rho : Omega → NNReal)
    (hX : IsStronglyPredictable F X)
    (hρ : IsStoppingTime F
      (fun omega => (rho omega : WithTop NNReal))) :
    StronglyAdapted F (postStopSampled X rho) := by
  let tau : Omega → WithTop NNReal := fun omega => (rho omega : WithTop NNReal)
  have hStopped : IsStronglyPredictable F
      (MeasureTheory.stoppedProcess X tau) :=
    IsStronglyPredictable.stoppedProcess_of_stoppingTime hX rho hρ
  have hStrong : StronglyAdapted F
      (MeasureTheory.stoppedProcess X tau) := hStopped.stronglyAdapted
  intro t
  have hEvent : MeasurableSet[F t] {omega | rho omega ≤ t} := by
    simpa only [tau, WithTop.coe_le_coe] using hρ.measurableSet_le t
  have hInd := (hStrong t).indicator hEvent
  change StronglyMeasurable[F t]
    (fun omega => if rho omega ≤ t then
      MeasureTheory.stoppedProcess X tau t omega else 0) at hInd
  convert hInd using 1
  funext omega
  by_cases h : rho omega ≤ t
  · simp only [h, ↓reduceIte]
    calc
      postStopSampled X rho t omega = X (rho omega) omega :=
        postStopSampled_eq_of_ge X rho h
      _ = MeasureTheory.stoppedProcess X tau t omega := by
        symm
        simpa [tau] using stoppedProcess_eq_of_ge X rho h
  · simp only [h, ↓reduceIte]
    exact postStopSampled_eq_zero_of_lt X rho (lt_of_not_ge h)

/-! ## Regularity and the closed-stop jump identity -/

omit [MeasurableSpace Omega] in
theorem strictPrefixProcess_eq_operator
    (A : Process Omega) (rho : Omega → NNReal) :
    strictPrefixProcess A rho =
      MeasureTheory.stoppedProcess A
          (fun omega => (rho omega : WithTop NNReal)) -
        postStopSampled A rho +
        postStopSampled
          (fun s omega => Function.leftLim (A · omega) s) rho := by
  rfl

omit [MeasurableSpace Omega] in
theorem strictPrefixProcess_rightContinuous
    (A : Process Omega) (rho : Omega → NNReal)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t) :
    ∀ omega t, ContinuousWithinAt
      (strictPrefixProcess A rho · omega) (Set.Ici t) t := by
  intro omega t
  rw [strictPrefixProcess_eq_operator]
  exact
    (((RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      A (τ := fun omega => (rho omega : WithTop NNReal)) hARight) omega t).sub
      (postStopSampled_rightContinuous A rho omega t)).add
      (postStopSampled_rightContinuous
        (fun s omega => Function.leftLim (A · omega) s) rho omega t)

omit [MeasurableSpace Omega] in
theorem strictPrefixProcess_hasLeftLimits
    (A : Process Omega) (rho : Omega → NNReal)
    (hALeft : ProcessHasLeftLimits A) :
    ProcessHasLeftLimits (strictPrefixProcess A rho) := by
  have hClosed : ProcessHasLeftLimits
      (MeasureTheory.stoppedProcess A
        (fun omega => (rho omega : WithTop NNReal))) :=
    hALeft.stoppedProcess (fun omega => (rho omega : WithTop NNReal))
  rw [strictPrefixProcess_eq_operator]
  change ProcessHasLeftLimits (fun t omega =>
    MeasureTheory.stoppedProcess A
        (fun omega => (rho omega : WithTop NNReal)) t omega -
      postStopSampled A rho t omega +
      postStopSampled
        (fun s omega => Function.leftLim (A · omega) s) rho t omega)
  intro omega t
  let f : NNReal → Real := fun s =>
    MeasureTheory.stoppedProcess A
        (fun omega => (rho omega : WithTop NNReal)) s omega -
      postStopSampled A rho s omega +
      postStopSampled
        (fun u omega => Function.leftLim (A · omega) u) rho s omega
  let l : Real :=
    Function.leftLim
        (fun s => MeasureTheory.stoppedProcess A
          (fun omega => (rho omega : WithTop NNReal)) s omega) t -
      Function.leftLim (fun s => postStopSampled A rho s omega) t +
      Function.leftLim
        (fun s => postStopSampled
          (fun u omega => Function.leftLim (A · omega) u) rho s omega) t
  have hsum : Tendsto f (𝓝[<] t) (𝓝 l) := by
    dsimp only [f, l]
    simpa using
      ((hClosed omega t).sub (postStopSampled_hasLeftLimits A rho omega t)).add
        (postStopSampled_hasLeftLimits
          (fun s omega => Function.leftLim (A · omega) s) rho omega t)
  change Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t))
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · rw [leftLim_eq_of_eq_bot f hbot]
    simp [hbot]
  · let _ : NeBot (𝓝[<] t) := hne
    have hleft : Function.leftLim f t = l :=
      leftLim_eq_of_tendsto hsum
    rw [hleft]
    exact hsum

omit [MeasurableSpace Omega] in
theorem strictPrefixProcess_boundedVariation
    (A : Process Omega) (rho : Omega → NNReal)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ) :
    ∀ omega, BoundedVariationOn
      (strictPrefixProcess A rho · omega) Set.univ := by
  intro omega
  have hClosed := FiniteVariationStoppedPath.boundedVariationOn_stopAt
    (hAVar omega) (rho omega)
  have hClosedEq :
      (fun t => MeasureTheory.stoppedProcess A
        (fun omega => (rho omega : WithTop NNReal)) t omega) =
      FiniteVariationStoppedPath.stopAt (A · omega) (rho omega) := by
    funext t
    unfold MeasureTheory.stoppedProcess FiniteVariationStoppedPath.stopAt
    rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe]
  have hClosed' : BoundedVariationOn
      (MeasureTheory.stoppedProcess A
        (fun omega => (rho omega : WithTop NNReal)) · omega) Set.univ := by
    rw [hClosedEq]
    exact hClosed
  have hPostA := postStopSampled_boundedVariation A rho omega
  have hPostL := postStopSampled_boundedVariation
    (fun s omega => Function.leftLim (A · omega) s) rho omega
  have hSub := boundedVariationOn_add hClosed'
    (boundedVariationOn_neg hPostA)
  rw [strictPrefixProcess_eq_operator]
  exact boundedVariationOn_add hSub hPostL

theorem strictPrefixProcess_stronglyAdapted
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (A : Process Omega) (rho : Omega → NNReal)
    (hA : StronglyAdapted F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hALeft : ProcessHasLeftLimits A)
    (hρ : IsStoppingTime F
      (fun omega => (rho omega : WithTop NNReal))) :
    StronglyAdapted F (strictPrefixProcess A rho) := by
  have hClosed : StronglyAdapted F
      (MeasureTheory.stoppedProcess A
        (fun omega => (rho omega : WithTop NNReal))) :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hA hρ hARight
  have hPostA : StronglyAdapted F (postStopSampled A rho) :=
    postStopSampled_stronglyAdapted_of_rightContinuous A rho hA hARight hρ
  have hLeftPred : IsStronglyPredictable F
      (fun t omega => Function.leftLim (A · omega) t) :=
    ProcessHasLeftLimits.stronglyPredictable_leftLim hALeft hA
  have hPostL : StronglyAdapted F
      (postStopSampled
        (fun t omega => Function.leftLim (A · omega) t) rho) :=
    postStopSampled_stronglyAdapted_of_predictable
      (fun t omega => Function.leftLim (A · omega) t) rho hLeftPred hρ
  rw [strictPrefixProcess_eq_operator]
  exact (hClosed.sub hPostA).add hPostL

omit [MeasurableSpace Omega] in
theorem strictPrefixProcess_add_postStopSampled_processLeftJump
    (A : Process Omega) (rho : Omega → NNReal) :
    ∀ t omega,
      strictPrefixProcess A rho t omega +
          postStopSampled (processLeftJump A) rho t omega =
        MeasureTheory.stoppedProcess A
          (fun omega => (rho omega : WithTop NNReal)) t omega := by
  intro t omega
  by_cases h : t < rho omega
  · rw [strictPrefixProcess_eq_of_lt A rho h,
      postStopSampled_eq_zero_of_lt (processLeftJump A) rho h,
      stoppedProcess_eq_of_lt A rho h]
    ring
  · have h' : rho omega ≤ t := le_of_not_gt h
    rw [strictPrefixProcess_eq_of_ge A rho h',
      postStopSampled_eq_of_ge (processLeftJump A) rho h',
      stoppedProcess_eq_of_ge A rho h']
    unfold processLeftJump
    ring

/-! ## Strict-prefix variation -/

omit [MeasurableSpace Omega] in
theorem eVariationOn_Icc_le_of_variationOnFromTo
    (f : NNReal → Real) (hVar : BoundedVariationOn f Set.univ)
    {a b : NNReal} (hab : a ≤ b) :
    eVariationOn f (Set.Icc a b) ≤
      ENNReal.ofReal (variationOnFromTo f Set.univ a b) := by
  have hfinite : eVariationOn f (Set.Icc a b) ≠ ∞ := by
    exact ne_top_of_le_ne_top hVar (eVariationOn.mono f (Set.subset_univ _))
  rw [variationOnFromTo.eq_of_le f Set.univ hab, Set.univ_inter,
    ENNReal.ofReal_toReal hfinite]

omit [MeasurableSpace Omega] in
theorem strictPrefixProcess_variation_le_of_before
    (A : Process Omega) (rho : Omega → NNReal) (omega : Omega)
    (hAVar : BoundedVariationOn (A · omega) Set.univ)
    {b : Real}
    (hBefore : ∀ t, t < rho omega →
      variationOnFromTo (A · omega) Set.univ 0 t ≤ b) :
    eVariationOn (strictPrefixProcess A rho · omega) Set.univ ≤
      ENNReal.ofReal b := by
  let r : NNReal := rho omega
  let P : NNReal → Real := (strictPrefixProcess A rho · omega)
  change eVariationOn P Set.univ ≤ ENNReal.ofReal b
  have hVarIio : eVariationOn (A · omega) (Set.Iio r) ≤
      ENNReal.ofReal b := by
    rw [eVariationOn]
    apply iSup_le
    rintro ⟨n, u, hu, humem⟩
    have hPart :
        (∑ i ∈ Finset.range n,
          edist ((A · omega) (u (i + 1))) ((A · omega) (u i))) ≤
        eVariationOn (A · omega) (Set.Icc (u 0) (u n)) := by
      apply eVariationOn.sum_le_of_monotoneOn_Iic
        (f := (A · omega)) (s := Set.Icc (u 0) (u n))
        (hu.monotoneOn (Set.Iic n))
      intro i hi
      exact ⟨hu (Nat.zero_le i), hu hi⟩
    have hIcc := eVariationOn_Icc_le_of_variationOnFromTo
      (A · omega) hAVar (hu (Nat.zero_le n))
    have hVle :
        variationOnFromTo (A · omega) Set.univ (u 0) (u n) ≤
          variationOnFromTo (A · omega) Set.univ 0 (u n) := by
      rw [← variationOnFromTo.add hAVar.locallyBoundedVariationOn
        (Set.mem_univ 0) (Set.mem_univ (u 0)) (Set.mem_univ (u n))]
      exact le_add_of_nonneg_left
        (variationOnFromTo.nonneg_of_le (A · omega) Set.univ
          (show (0 : NNReal) ≤ u 0 from bot_le))
    exact hPart.trans (hIcc.trans
      (ENNReal.ofReal_le_ofReal
        (hVle.trans (hBefore (u n) (show u n < r from humem n)))))
  by_cases hr : r = 0
  · have hrho0 : rho omega = 0 := by simpa [r] using hr
    have hPconst : (P '' Set.univ).Subsingleton := by
      rintro _ ⟨t, -, rfl⟩ _ ⟨s, -, rfl⟩
      dsimp [P]
      rw [strictPrefixProcess_eq_of_ge A rho (by rw [hrho0]; exact bot_le),
        strictPrefixProcess_eq_of_ge A rho (by rw [hrho0]; exact bot_le)]
    simp only [eVariationOn.constant_on hPconst]
    exact bot_le
  · have hrpos : 0 < r := pos_iff_ne_zero.mpr hr
    let _ : NeBot (𝓝[<] r) :=
      nhdsLT_neBot_of_exists_lt ⟨0, hrpos⟩
    have hPleft : Tendsto P (𝓝[<] r) (𝓝 (P r)) := by
      rw [show P r = Function.leftLim (A · omega) r by
        dsimp [P, r]
        exact strictPrefixProcess_eq_of_ge A rho le_rfl]
      apply (hAVar.tendsto_leftLim r).congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      dsimp [P]
      exact (strictPrefixProcess_eq_of_lt A rho
        (show s < rho omega from hs)).symm
    have hPleftIic : ContinuousWithinAt P (Set.Iic r) r :=
      continuousWithinAt_Iio_iff_Iic.1 hPleft
    have hIicEq : eVariationOn P (Set.Iic r) =
        eVariationOn P (Set.Iio r) := by
      symm
      simpa only [Set.univ_inter] using
        (eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
          (f := P) (s := Set.univ) (a := r)
          (by simpa only [Set.univ_inter] using
            (show (𝓝[<] r).NeBot from inferInstance))
          (by simpa only [Set.univ_inter] using hPleftIic))
    have hPIioEq : eVariationOn P (Set.Iio r) =
        eVariationOn (A · omega) (Set.Iio r) := by
      apply eVariationOn.eq_of_eqOn
      intro s hs
      dsimp [P]
      exact strictPrefixProcess_eq_of_lt A rho
        (show s < rho omega from hs)
    have hPIci : eVariationOn P (Set.Ici r) = 0 := by
      apply eVariationOn.constant_on
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      dsimp [P]
      rw [strictPrefixProcess_eq_of_ge A rho hs,
        strictPrefixProcess_eq_of_ge A rho ht]
    have hUnion : Set.Iic r ∪ Set.Ici r = Set.univ := by
      ext t
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ,
        iff_true]
      exact le_total t r
    calc
      eVariationOn P Set.univ = eVariationOn P (Set.Iic r ∪ Set.Ici r) := by
        rw [hUnion]
      _ = eVariationOn P (Set.Iic r) + eVariationOn P (Set.Ici r) :=
        eVariationOn.union P
          ⟨Set.mem_Iic.mpr le_rfl, fun _ h => h⟩
          ⟨Set.mem_Ici.mpr le_rfl, fun _ h => h⟩
      _ = eVariationOn (A · omega) (Set.Iio r) := by
        rw [hIicEq, hPIioEq, hPIci, add_zero]
      _ ≤ ENNReal.ofReal b := hVarIio

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
