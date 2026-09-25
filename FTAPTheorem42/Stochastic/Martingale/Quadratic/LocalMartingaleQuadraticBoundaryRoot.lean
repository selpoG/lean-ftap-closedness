/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.J1.StrictPrefix

/-! # The boundary jump cost of a closed-stopped quadratic root -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

theorem LocalMartingaleQuadraticVariation.root_le_leftRoot_add_jump
    (Q : LocalMartingaleQuadraticVariation X F mu) :
    ∀ᵐ w ∂mu, ∀ t, Real.sqrt (Q.variation t w) ≤
      Real.sqrt (Function.leftLim (Q.variation · w) t) + |processLeftJump X t w| := by
  filter_upwards [Q.jump_sq] with w hw
  intro t
  have hLeft : 0 ≤ Function.leftLim (Q.variation · w) t := by
    by_cases ht : t = 0
    · rw [ht, leftLim_eq_of_isBot (f := (Q.variation · w)) (a := (0 : NNReal)) isBot_bot,
        Q.zero]
      exact le_rfl
    · have h := (Q.monotone w).le_leftLim (pos_iff_ne_zero.mpr ht)
      simpa only [Q.zero, Pi.zero_apply] using h
  have hJump := hw t
  change Q.variation t w - Function.leftLim (Q.variation · w) t =
    processLeftJump X t w ^ 2 at hJump
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt hLeft, sq_abs (processLeftJump X t w),
    mul_nonneg (Real.sqrt_nonneg (Function.leftLim (Q.variation · w) t))
      (abs_nonneg (processLeftJump X t w))]

theorem LocalMartingaleQuadraticVariation.stopped_allTimeRoot_eq
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (Q : LocalMartingaleQuadraticVariation X F mu)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hZero : X 0 = 0)
    {tau : Ω → NNReal} (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (w : Ω) :
    (⨆ t : NNReal, ENNReal.ofReal (Real.sqrt
      ((Q.stopped hRight hLeft hZero hTau).variation t w))) =
      ENNReal.ofReal (Real.sqrt (Q.variation (tau w) w)) := by
  have hValue : ∀ t, (Q.stopped hRight hLeft hZero hTau).variation t w =
      Q.variation (min t (tau w)) w := fun t => by
    change stoppedProcess Q.variation (fun w => (tau w : WithTop NNReal)) t w = _
    simp only [stoppedProcess, ← WithTop.coe_min]
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
    rfl
  apply le_antisymm
  · apply iSup_le
    intro t
    rw [hValue]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (Q.monotone w (min_le_right _ _)))
  · apply le_trans _ (le_iSup (fun t : NNReal => ENNReal.ofReal (Real.sqrt
      ((Q.stopped hRight hLeft hZero hTau).variation t w))) (tau w))
    rw [hValue, min_self]

theorem LocalMartingaleQuadraticVariation.lintegral_stopped_root_le_leftRoot_add_jump
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (Q : LocalMartingaleQuadraticVariation X F mu)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hZero : X 0 = 0)
    {tau : Ω → NNReal} (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal))) :
    (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt
      ((Q.stopped hRight hLeft hZero hTau).variation t w)) ∂mu) ≤
    ∫⁻ w, ENNReal.ofReal (Real.sqrt (Function.leftLim (Q.variation · w) (tau w))) +
      ENNReal.ofReal |processLeftJump X (tau w) w| ∂mu := by
  apply lintegral_mono_ae
  filter_upwards [Q.root_le_leftRoot_add_jump] with w hw
  rw [Q.stopped_allTimeRoot_eq hRight hLeft hZero hTau w]
  exact (ENNReal.ofReal_le_ofReal (hw (tau w))).trans_eq
    (ENNReal.ofReal_add (Real.sqrt_nonneg _) (abs_nonneg _))

end FTAPTheorem42
