/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.ClosedStopResidualGluing
import FTAPTheorem42.Stochastic.Decomposition.Source.RegularizedSpecialSemimartingale

/-!
# The global decomposition of the finite-large-jump process

The two glued components are identified using the exhaustive closed-stop
schedule.  Choosing the residual as the exact difference of the source and
the normalized projection preserves its pathwise finite variation and its
zero initial value, while indistinguishability transfers the local martingale
property from the glued residual.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42.HorizonFactorialGrid.FiniteLargeJumpClosedStopFamily

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {c : Real} {T : NNReal}

/-- A decomposition of the original large-jump process with a single exact
residual representative carrying both local martingale and local BV properties. -/
structure GlobalDecompositionData
    (hX : LocalMartingale X F mu)
    (family : FiniteLargeJumpValueTruncationFamily
      (F := F) (mu := mu) X c T)
    (closedFamily : FiniteLargeJumpClosedStopFamily hX family)
    (hUsual : Filtration.UsualConditions mu F)
    extends ProjectionGluingData hX family closedFamily hUsual where
  Q : Process Ω
  Q_definition : Q = fun t omega => FiniteLargeJumpProcess.process X c T t omega - P t omega
  Q_isStronglyAdapted : StronglyAdapted F Q
  Q_isLocalMartingale : LocalMartingale Q F mu
  Q_rightContinuous : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t
  Q_leftLimits : ProcessHasLeftLimits Q
  Q_locallyBoundedVariation : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ
  Q_zero : Q 0 = 0
  source_identity : ProcessIndistinguishable mu (FiniteLargeJumpProcess.process X c T)
    (fun t omega => Q t omega + P t omega)

/-- Identify the glued components globally and transfer the local martingale
property to the exact source-minus-projection residual. -/
theorem exists_globalDecompositionData
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (hc : 0 < c)
    (family : FiniteLargeJumpValueTruncationFamily (F := F) (mu := mu) X c T)
    (closedFamily : FiniteLargeJumpClosedStopFamily hX family)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (GlobalDecompositionData hX family closedFamily hUsual) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨p⟩ := exists_projectionGluingData
    hX hXAdapted hXRight hXLeft family closedFamily hUsual
  obtain ⟨q⟩ := exists_residualMartingaleGluingData
    hX hXAdapted hXRight hXLeft family closedFamily hUsual
  let J := FiniteLargeJumpProcess.process X c T
  let Q : Process Ω := fun t omega => J t omega - p.P t omega
  have hEq : ProcessIndistinguishable mu Q q.Q := by
    apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence
      closedFamily.isLocalizingSequence
    intro n
    filter_upwards [p.P_stopped n, q.Q_stopped n] with omega hp hq
    intro t
    let s := (min (t : WithTop NNReal)
      ((closedFamily.data n).tau omega : WithTop NNReal)).untopA
    have hClosed : (closedFamily.data n).closed s omega = J s omega := by
      rw [(closedFamily.data n).closed_eq_stopped]
      change MeasureTheory.stoppedProcess J
        (fun omega => ((closedFamily.data n).tau omega : WithTop NNReal)) s omega = _
      apply MeasureTheory.stoppedProcess_eq_of_le
      dsimp [s]
      exact (WithTop.coe_le_coe.mpr
        ((WithTop.untopA_le_iff (ne_top_of_le_ne_top WithTop.coe_ne_top
          (min_le_left _ _))).mpr (min_le_right _ _)))
    have hResidual := congrFun (congrFun
      (closedFamily.data n).projection.residual_definition s) omega
    change J s omega - p.P s omega = q.Q s omega
    have hpAt := hp t
    have hqAt := hq t
    change p.P s omega = (closedFamily.data n).projection.Ap s omega at hpAt
    change q.Q s omega = (closedFamily.data n).projection.residual s omega at hqAt
    rw [hpAt, hqAt, hResidual, hClosed]
  have hQAdapted : StronglyAdapted F Q :=
    (FiniteLargeJumpProcess.stronglyAdapted_process
      hXAdapted hXRight hXLeft hc T).sub p.P_isStronglyPredictable.stronglyAdapted
  have hQRight : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t := by
    intro omega t
    exact (FiniteLargeJumpProcess.process_rightContinuous hXRight hXLeft hc omega t).sub
      (p.P_rightContinuous omega t)
  have hQVariation : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ := by
    intro omega a b ha hb
    simpa only [Q, J, sub_eq_add_neg] using
      boundedVariationOn_add
        (FiniteLargeJumpProcess.process_locallyBoundedVariationOn
          (T := T) hXRight hXLeft hc omega a b ha hb)
        (boundedVariationOn_neg (p.P_locallyBoundedVariation omega a b ha hb))
  refine ⟨{
    toProjectionGluingData := p
    Q := Q
    Q_definition := rfl
    Q_isStronglyAdapted := hQAdapted
    Q_isLocalMartingale := q.Q_isLocalMartingale.congr_indistinguishable
      hQAdapted hQRight hEq.symm
    Q_rightContinuous := hQRight
    Q_leftLimits :=
      SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
        hQVariation
    Q_locallyBoundedVariation := hQVariation
    Q_zero := by
      funext omega
      change J 0 omega - p.P 0 omega = 0
      simp [J, FiniteLargeJumpProcess.process_zero hXRight hXLeft hc, p.P_zero]
    source_identity := by
      exact Filter.Eventually.of_forall (fun omega t => (sub_add_cancel _ _).symm) }⟩

end FTAPTheorem42.HorizonFactorialGrid.FiniteLargeJumpClosedStopFamily
