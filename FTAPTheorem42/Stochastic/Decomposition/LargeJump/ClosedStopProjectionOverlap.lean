/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.ClosedStopFamily
import FTAPTheorem42.Stochastic.FiniteVariation.PredictableFiniteVariationLocalMartingale

/-!
# Overlap of closed finite-large-jump predictable projections

The closed finite-large-jump sources form a nested family only up to the
stopping operation.  This module compares the predictable finite-variation
projections on that nested overlap.  The later residual is stopped at the
earlier refined stop, and the two residual martingales identify the
difference of the two predictable coordinates as a source-free predictable
finite-variation local martingale.

Only process indistinguishability is asserted.  In particular, no pointwise
compatibility of the selected representatives is introduced.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open PredictableFiniteVariationLocalMartingale

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

namespace FiniteLargeJumpClosedStopFamily

variable {X : Process Ω} {c : Real} {T : NNReal}
  {hX : LocalMartingale X F mu}
  {family : FiniteLargeJumpValueTruncationFamily
    (F := F) (mu := mu) X c T}

/-! ## Pathwise stopped finite-variation helper -/

omit [MeasurableSpace Ω] in
private theorem stoppedProcess_path_eq_stopAt_finiteTime
    {A : Process Ω} (tau : Ω → NNReal) (omega : Ω) :
    (fun t => MeasureTheory.stoppedProcess A
      (fun omega => (tau omega : WithTop NNReal)) t omega) =
      FiniteVariationStoppedPath.stopAt (A · omega) (tau omega) := by
  funext t
  simp only [FiniteVariationStoppedPath.stopAt,
    MeasureTheory.stoppedProcess]
  have hcoe : (((min t (tau omega) : NNReal) : WithTop NNReal)) =
      min (t : WithTop NNReal) (tau omega : WithTop NNReal) :=
    WithTop.coe_min t (tau omega)
  have hne : ((min t (tau omega) : NNReal) : WithTop NNReal) ≠
      (⊤ : WithTop NNReal) := WithTop.coe_ne_top
  calc
    A (min (t : WithTop NNReal) (tau omega : WithTop NNReal)).untopA omega =
        A (((min t (tau omega) : NNReal) : WithTop NNReal)).untopA omega := by
          rw [hcoe]
    _ = A (min t (tau omega)) omega := by
          rw [WithTop.untopA_eq_untop hne, WithTop.untop_coe]

/-! ## Pairwise projection overlap -/

/-- The predictable projections selected for two nested closed stops agree
after stopping the later projection at the earlier refined stop. -/
theorem projection_overlap_of_le
    {X : Process Ω} {c : Real} {T : NNReal}
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T)
    (closedFamily : FiniteLargeJumpClosedStopFamily
      (F := F) (mu := mu) hX family)
    (hUsual : Filtration.UsualConditions mu F)
    {m n : ℕ} (hmn : m ≤ n) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (closedFamily.data n).projection.Ap
        (fun omega => ((closedFamily.data m).tau omega : WithTop NNReal)))
      (closedFamily.data m).projection.Ap := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  let tauM : Ω → WithTop NNReal := fun omega =>
    ((closedFamily.data m).tau omega : WithTop NNReal)
  let Pn : Process Ω := (closedFamily.data n).projection.Ap
  let Pm : Process Ω := (closedFamily.data m).projection.Ap
  let Rn : Process Ω := (closedFamily.data n).projection.residual
  let Rm : Process Ω := (closedFamily.data m).projection.residual
  let D : Process Ω := fun t omega =>
    MeasureTheory.stoppedProcess Pn tauM t omega - Pm t omega
  have hClosedOverlap : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (closedFamily.data n).closed tauM)
      (closedFamily.data m).closed := by
    dsimp [tauM]
    exact closed_stopped_at_le_eq closedFamily hXAdapted hXRight hXLeft hmn
  have hPnRight : ∀ omega t,
      ContinuousWithinAt (Pn · omega) (Ici t) t := by
    intro omega t
    exact (closedFamily.data n).projection.Ap_rightContinuous omega t
  have hPmRight : ∀ omega t,
      ContinuousWithinAt (Pm · omega) (Ici t) t := by
    intro omega t
    exact (closedFamily.data m).projection.Ap_rightContinuous omega t
  have hRnRight : ∀ omega t,
      ContinuousWithinAt (Rn · omega) (Ici t) t := by
    intro omega t
    dsimp [Rn]
    rw [(closedFamily.data n).projection.residual_definition]
    exact ((closedFamily.data n).source_data.rightContinuous omega t).sub
      ((closedFamily.data n).projection.Ap_rightContinuous omega t)
  have hStoppedRnMartingale : Martingale
      (MeasureTheory.stoppedProcess Rn tauM) F mu := by
    dsimp [Rn, tauM]
    exact RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      (closedFamily.data n).projection.residual_martingale
      (closedFamily.data m).tau_isStoppingTime hRnRight
  have hStoppedPnPredictable : IsStronglyPredictable F
      (MeasureTheory.stoppedProcess Pn tauM) := by
    dsimp [Pn, tauM]
    exact IsStronglyPredictable.stoppedProcess_of_stoppingTime_withTop
      (closedFamily.data n).projection.Ap_stronglyPredictable
      (fun omega => ((closedFamily.data m).tau omega : WithTop NNReal))
      (closedFamily.data m).tau_isStoppingTime
  have hD_predictable : IsStronglyPredictable F D := by
    unfold IsStronglyPredictable
    dsimp [D]
    exact hStoppedPnPredictable.sub
      (closedFamily.data m).projection.Ap_stronglyPredictable
  have hD_rightContinuous : ∀ omega t,
      ContinuousWithinAt (D · omega) (Ici t) t := by
    intro omega t
    dsimp [D]
    exact (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      Pn hPnRight omega t).sub (hPmRight omega t)
  have hStoppedPn_variation : ∀ omega,
      BoundedVariationOn
        (MeasureTheory.stoppedProcess Pn tauM · omega) Set.univ := by
    intro omega
    have hPath := stoppedProcess_path_eq_stopAt_finiteTime
      (A := Pn) (closedFamily.data m).tau omega
    rw [hPath]
    exact FiniteVariationStoppedPath.boundedVariationOn_stopAt
      ((closedFamily.data n).projection.Ap_boundedVariation omega)
      ((closedFamily.data m).tau omega)
  have hD_variation : ∀ omega, BoundedVariationOn (D · omega) Set.univ := by
    intro omega
    dsimp [D]
    exact boundedVariationOn_add (hStoppedPn_variation omega)
      (boundedVariationOn_neg
        ((closedFamily.data m).projection.Ap_boundedVariation omega))
  have hPn_decomposition : (closedFamily.data n).closed =
      (fun t omega => Rn t omega + Pn t omega) := by
    funext t omega
    have h := congrFun
      (congrFun (closedFamily.data n).projection.residual_definition t) omega
    dsimp [Rn, Pn] at h ⊢
    linarith
  have hPm_decomposition : (closedFamily.data m).closed =
      (fun t omega => Rm t omega + Pm t omega) := by
    funext t omega
    have h := congrFun
      (congrFun (closedFamily.data m).projection.residual_definition t) omega
    dsimp [Rm, Pm] at h ⊢
    linarith
  have hStoppedSum :
      MeasureTheory.stoppedProcess
          (fun t omega => Rn t omega + Pn t omega) tauM =
        (fun t omega =>
          MeasureTheory.stoppedProcess Rn tauM t omega +
            MeasureTheory.stoppedProcess Pn tauM t omega) := by
    funext t omega
    simp only [MeasureTheory.stoppedProcess]
  have hExpanded : ProcessIndistinguishable mu
      (fun t omega =>
        MeasureTheory.stoppedProcess Rn tauM t omega +
          MeasureTheory.stoppedProcess Pn tauM t omega)
      (fun t omega => Rm t omega + Pm t omega) := by
    rw [← hStoppedSum, ← hPn_decomposition, ← hPm_decomposition]
    exact hClosedOverlap
  have hOpposite : ProcessIndistinguishable mu D
      (fun t omega => Rm t omega -
        MeasureTheory.stoppedProcess Rn tauM t omega) := by
    filter_upwards [hExpanded] with omega hOmega
    intro t
    dsimp [D] at ⊢
    linarith [hOmega t]
  have hOppositeMartingale : Martingale
      (fun t omega => Rm t omega -
        MeasureTheory.stoppedProcess Rn tauM t omega) F mu :=
    (closedFamily.data m).projection.residual_martingale.sub
      hStoppedRnMartingale
  have hD_martingale : Martingale D F mu := by
    apply hOppositeMartingale.congr hD_predictable.stronglyAdapted
    intro t
    exact (hOpposite.eventuallyEq_at t).symm
  have hD_localMartingale : LocalMartingale D F mu :=
    ProbabilityTheory.Locally.of_prop hD_martingale
  have hD_zero_ae : D 0 =ᵐ[mu] 0 := by
    filter_upwards [(closedFamily.data n).projection.Ap_zero_ae,
      (closedFamily.data m).projection.Ap_zero_ae] with omega hPnZero hPmZero
    have hStoppedPnZero :
        MeasureTheory.stoppedProcess Pn tauM 0 omega = 0 := by
      rw [MeasureTheory.stoppedProcess_eq_of_le bot_le]
      simpa only [Pn, Pi.zero_apply] using hPnZero
    dsimp [D]
    rw [hStoppedPnZero]
    dsimp [Pm]
    rw [hPmZero]
    simp
  have hD_constant :=
    indistinguishable_initial_of_predictableFiniteVariationLocalMartingale
      hUsual D hD_localMartingale hD_predictable hD_rightContinuous hD_variation
  have hD_zero : ProcessIndistinguishable mu D (fun _ _ => 0) := by
    filter_upwards [hD_constant, hD_zero_ae] with omega hConstant hZero
    intro t
    calc
      D t omega = D 0 omega := hConstant t
      _ = 0 := hZero
  filter_upwards [hD_zero] with omega hOmega
  intro t
  have hDt := hOmega t
  dsimp [D] at hDt
  exact sub_eq_zero.mp hDt

end FiniteLargeJumpClosedStopFamily

end HorizonFactorialGrid

end FTAPTheorem42
