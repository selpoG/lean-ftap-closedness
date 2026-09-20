/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.GlobalDecompositionOverlap
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.CompensatorJumpBound

/-!
# One coherent family of finite-horizon large-jump decompositions

Each horizon is constructed from the original local martingale. The same
stored projections and residuals retain their regularity, zero initial
values and coordinate agreements. Horizon overlap and compensator jump
bounds are collected on common full-measure sets over all integer horizons.
-/

namespace FTAPTheorem42.HorizonFactorialGrid

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

open FiniteLargeJumpClosedStopFamily

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {c : Real}

/-- Finite-horizon data and their ordered overlap, for one original source.
The localizing schedules internal to different horizons remain independent. -/
structure FiniteLargeJumpHorizonFamily
    (hX : LocalMartingale X F mu) (c : Real)
    (hUsual : Filtration.UsualConditions mu F) where
  slice : ∀ n, FiniteLargeJumpValueTruncationFamily (F := F) (mu := mu)
    X c (cadlagPassageHorizon n)
  closed : ∀ n, FiniteLargeJumpClosedStopFamily hX (slice n)
  data : ∀ n, GlobalDecompositionData hX (slice n) (closed n) hUsual
  compensator_jump_bound : ∀ᵐ omega ∂mu, ∀ n t, t ≤ cadlagPassageHorizon n →
    |processLeftJump (data n).P t omega| ≤ c
  overlap : ∀ᵐ omega ∂mu, ∀ m n, m ≤ n → ∀ t,
    (data n).P (min t (cadlagPassageHorizon m)) omega =
      (data m).P (min t (cadlagPassageHorizon m)) omega ∧
    (data n).Q (min t (cadlagPassageHorizon m)) omega =
      (data m).Q (min t (cadlagPassageHorizon m)) omega ∧
    X (min t (cadlagPassageHorizon m)) omega -
        (data n).Q (min t (cadlagPassageHorizon m)) omega =
      X (min t (cadlagPassageHorizon m)) omega -
        (data m).Q (min t (cadlagPassageHorizon m)) omega

/-- Construct all horizon coordinates, then apply source consistency and
rigidity to these actual stored coordinates. -/
theorem exists_finiteLargeJumpHorizonFamily
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hc : 0 < c) (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (FiniteLargeJumpHorizonFamily hX c hUsual) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  let slice : ∀ n, FiniteLargeJumpValueTruncationFamily (F := F) (mu := mu)
      X c (cadlagPassageHorizon n) := fun n =>
    Classical.choice (exists_finiteLargeJumpValueTruncationFamily X c (cadlagPassageHorizon n)
      hXAdapted hXRight hXLeft hc hUsual)
  let closed : ∀ n, FiniteLargeJumpClosedStopFamily hX (slice n) := fun n =>
    Classical.choice (exists_finiteLargeJumpClosedStopFamily
      hX hXAdapted hXRight hXLeft hXZero hc (slice n) hUsual)
  let data : ∀ n, GlobalDecompositionData hX (slice n) (closed n) hUsual := fun n =>
    Classical.choice (exists_globalDecompositionData
      hX hXAdapted hXRight hXLeft hc (slice n) (closed n) hUsual)
  have hJump : ∀ᵐ omega ∂mu, ∀ n t, t ≤ cadlagPassageHorizon n →
      |processLeftJump (data n).P t omega| ≤ c := by
    exact ae_all_iff.2 (fun n =>
      (data n).abs_predictableCompensator_leftJump_le hXAdapted hXRight hXLeft hc)
  have hPair : ∀ m n, ∀ᵐ omega ∂mu, m ≤ n → ∀ t,
      (data n).P (min t (cadlagPassageHorizon m)) omega =
        (data m).P (min t (cadlagPassageHorizon m)) omega ∧
      (data n).Q (min t (cadlagPassageHorizon m)) omega =
        (data m).Q (min t (cadlagPassageHorizon m)) omega ∧
      X (min t (cadlagPassageHorizon m)) omega -
          (data n).Q (min t (cadlagPassageHorizon m)) omega =
        X (min t (cadlagPassageHorizon m)) omega -
          (data m).Q (min t (cadlagPassageHorizon m)) omega := by
    intro m n
    by_cases hmn : m ≤ n
    · filter_upwards [(data m).stopped_components_overlap (data n)
        hXRight hXLeft hc (cadlagPassageHorizon_monotone hmn)] with omega hOmega
      exact fun _ => hOmega
    · exact Eventually.of_forall fun _ h => (hmn h).elim
  exact ⟨{
    slice := slice
    closed := closed
    data := data
    compensator_jump_bound := hJump
    overlap := ae_all_iff.2 (fun m => ae_all_iff.2 (hPair m)) }⟩

end FTAPTheorem42.HorizonFactorialGrid

namespace FTAPTheorem42.HorizonFactorialGrid

/-!
## Gluing the predictable projections across horizons

The coherent finite-horizon projections supply the compatibility required
by finite-variation gluing. The resulting predictable process agrees with
every stored projection on its whole horizon, on one common event.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {c : Real} {hX : LocalMartingale X F mu}
  {hUsual : Filtration.UsualConditions mu F}

omit [SigmaFiniteFiltration mu F] in
/-- Glue the stored predictable components at all integer horizons.
The equality is simultaneous in the horizon and in time. -/
theorem FiniteLargeJumpHorizonFamily.exists_predictable_projection
    (family : FiniteLargeJumpHorizonFamily hX c hUsual) :
    ∃ P : Process Ω, IsStronglyPredictable F P ∧
      (∀ omega t, ContinuousWithinAt (P · omega) (Ici t) t) ∧
      (∀ omega, LocallyBoundedVariationOn (P · omega) Set.univ) ∧
      (∀ᵐ omega ∂mu, ∀ n t, P (min t (cadlagPassageHorizon n)) omega =
        (family.data n).P (min t (cadlagPassageHorizon n)) omega) := by
  let tau : Nat → Ω → WithTop NNReal := fun n _ => cadlagPassageHorizon n
  let A : Nat → Process Ω := fun n t omega =>
    (family.data n).P (min t (cadlagPassageHorizon n)) omega
  have hTau : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    refine { isStoppingTime := fun n => isStoppingTime_const F (cadlagPassageHorizon n)
             tendsto_top := ?_, mono := ?_ }
    · apply Eventually.of_forall
      intro omega
      exact WithTop.tendsto_coe_atTop.comp cadlagPassageHorizon_tendsto_atTop
    · exact Eventually.of_forall fun _ _ _ h =>
        WithTop.coe_le_coe.mpr (cadlagPassageHorizon_monotone h)
  have hCompatibility : ∀ n m, ProcessIndistinguishable mu
      (stoppedProcess (A n) (min (tau n) (tau m)))
      (stoppedProcess (A m) (min (tau n) (tau m))) := by
    intro n m
    filter_upwards [family.overlap] with omega hOverlap
    intro t
    have hStop : min (tau n) (tau m) =
        fun _ : Ω => ((min (cadlagPassageHorizon n) (cadlagPassageHorizon m) : NNReal) :
          WithTop NNReal) := by
      funext omega
      simp only [tau, Pi.inf_apply, WithTop.coe_min]
    rw [hStop, stoppedProcess_const_apply, stoppedProcess_const_apply]
    dsimp only [A]
    rcases le_total n m with hnm | hmn
    · have hH := cadlagPassageHorizon_monotone hnm
      simp only [min_eq_left hH, min_assoc, min_self]
      exact (hOverlap n m hnm t).1.symm
    · have hH := cadlagPassageHorizon_monotone hmn
      simp only [min_eq_right hH, min_assoc, min_eq_left hH, min_self]
      exact (hOverlap m n hmn t).1
  obtain ⟨P, hPred, hRight, hVar, hStop⟩ :=
    CompatibleLocalFiniteVariationGluing.exists_predictable_rightContinuous_locallyBoundedVariation
      hUsual hTau
      (fun n => IsStronglyPredictable.deterministicallyStopped_of_pos
        (family.data n).P_isStronglyPredictable (cadlagPassageHorizon n)
        (cadlagPassageHorizon_pos n))
      (fun n omega t => FiniteVariationStoppedPath.rightContinuous_stopAt
        ((family.data n).P · omega) ((family.data n).P_rightContinuous omega)
        (cadlagPassageHorizon n) t)
      (fun n omega =>
        FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
          ((family.data n).P_locallyBoundedVariation omega) (cadlagPassageHorizon n))
      hCompatibility
  refine ⟨P, hPred, hRight, hVar, ?_⟩
  rw [ae_all_iff]
  intro n
  filter_upwards [hStop n] with omega hOmega
  intro t
  simpa only [tau, A, stoppedProcess_const_apply, min_assoc, min_self] using hOmega t

/-- The original local martingale supplies one zero-initial predictable,
locally finite-variation projection with a jump bound at every time.
Its agreement with all the finite-horizon projections is retained. -/
theorem exists_finiteLargeJumpHorizonProjection
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hc : 0 < c) (hUsual : Filtration.UsualConditions mu F) :
    ∃ family : FiniteLargeJumpHorizonFamily hX c hUsual,
      ∃ P : Process Ω, IsStronglyPredictable F P ∧
        (∀ omega t, ContinuousWithinAt (P · omega) (Ici t) t) ∧
        (∀ omega, LocallyBoundedVariationOn (P · omega) Set.univ) ∧ P 0 = 0 ∧
        (∀ᵐ omega ∂mu, ∀ n t, P (min t (cadlagPassageHorizon n)) omega =
          (family.data n).P (min t (cadlagPassageHorizon n)) omega) ∧
        (∀ᵐ omega ∂mu, ∀ t, |processLeftJump P t omega| ≤ c) := by
  obtain ⟨family⟩ := exists_finiteLargeJumpHorizonFamily
    hX hXAdapted hXRight hXLeft hXZero hc hUsual
  obtain ⟨Praw, hPred, hRight, hVar, hAgreement⟩ := family.exists_predictable_projection
  have hZero : ∀ᵐ omega ∂mu, Praw 0 omega = 0 := by
    filter_upwards [hAgreement] with omega hOmega
    simpa only [show min (0 : NNReal) (cadlagPassageHorizon 0) = 0 from
      min_eq_left bot_le, (family.data 0).P_zero, Pi.zero_apply] using hOmega 0 0
  let bad : Set Ω := {omega | Praw 0 omega ≠ 0}
  have hBad : mu bad = 0 := ae_iff.mp hZero
  let P := ProcessNullSetRegularization.zeroOn bad Praw
  have hVersion : ProcessIndistinguishable mu P Praw :=
    ProcessNullSetRegularization.zeroOn_indistinguishable hBad Praw
  have hPVar : ∀ omega, LocallyBoundedVariationOn (P · omega) Set.univ :=
    ProcessNullSetRegularization.zeroOn_isLocallyBoundedVariation (fun omega _ => hVar omega)
  have hPAgreement : ∀ᵐ omega ∂mu, ∀ n t, P (min t (cadlagPassageHorizon n)) omega =
      (family.data n).P (min t (cadlagPassageHorizon n)) omega := by
    filter_upwards [hVersion, hAgreement] with omega hV hA
    exact fun n t => (hV _).trans (hA n t)
  refine ⟨family, P,
    ProcessNullSetRegularization.isStronglyPredictable_zeroOn
      (hUsual.containsNullSetsAtZero bad hBad) hPred,
    ProcessNullSetRegularization.zeroOn_isRightContinuous (fun omega _ => hRight omega),
    hPVar, ?_, hPAgreement, ?_⟩
  · funext omega
    change ProcessNullSetRegularization.zeroOn bad Praw 0 omega = (0 : Real)
    by_cases h : omega ∈ bad
    · exact ProcessNullSetRegularization.zeroOn_apply_of_mem bad Praw h
    · rw [ProcessNullSetRegularization.zeroOn_apply_of_notMem bad Praw h]
      exact not_ne_iff.mp h
  · have hPLeft : ProcessHasLeftLimits P :=
      SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
        hPVar
    filter_upwards [hPAgreement, family.compensator_jump_bound] with omega hA hJump
    intro t
    obtain ⟨n, hn⟩ := (cadlagPassageHorizon_tendsto_atTop.eventually_ge_atTop t).exists
    let rho : Ω → WithTop NNReal := fun _ => cadlagPassageHorizon n
    have ht : (t : WithTop NNReal) ≤ rho omega := WithTop.coe_le_coe.mpr hn
    have hPath : (fun s => stoppedProcess P rho s omega) =
        (fun s => stoppedProcess (family.data n).P rho s omega) := by
      funext s
      simpa only [rho, stoppedProcess_const_apply] using hA n s
    have hFiniteLeft : ProcessHasLeftLimits (family.data n).P :=
      SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
        (family.data n).P_locallyBoundedVariation
    have hJumpEq : processLeftJump P t omega = processLeftJump (family.data n).P t omega := by
      rw [← processLeftJump_stoppedProcess_eq_of_le P hPLeft rho t omega ht,
        ← processLeftJump_stoppedProcess_eq_of_le (family.data n).P hFiniteLeft rho t omega ht]
      change (fun s => stoppedProcess P rho s omega) t -
          Function.leftLim (fun s => stoppedProcess P rho s omega) t = _
      rw [hPath]
      rfl
    rw [hJumpEq]
    exact hJump n t hn

end FTAPTheorem42.HorizonFactorialGrid
