/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.CorrectedNonnegative

/-! # Closed stopping of the DDY jump correction -/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem tsum_stopped_jump_eq
    (L Q : Process Ω) (hL : ProcessHasLeftLimits L) (hQ : ProcessHasLeftLimits Q)
    (f : Real → Real → Real) (hf : f 0 0 = 0)
    (tau : Ω → NNReal) (t : NNReal) (omega : Ω) :
    (∑' s : Ioc (0 : NNReal) t,
      f (processLeftJump (stoppedProcess L (fun w => (tau w : WithTop NNReal))) s omega)
        (processLeftJump (stoppedProcess Q (fun w => (tau w : WithTop NNReal))) s omega)) =
      ∑' s : Ioc (0 : NNReal) (min t (tau omega)),
        f (processLeftJump L s omega) (processLeftJump Q s omega) := by
  classical
  rw [tsum_subtype (Ioc (0 : NNReal) t) (fun s =>
    f (processLeftJump (stoppedProcess L (fun w => (tau w : WithTop NNReal))) s omega)
      (processLeftJump (stoppedProcess Q (fun w => (tau w : WithTop NNReal))) s omega)),
    tsum_subtype (Ioc (0 : NNReal) (min t (tau omega)))
      (fun s => f (processLeftJump L s omega) (processLeftJump Q s omega))]
  apply tsum_congr
  intro s
  by_cases hs : s ∈ Ioc (0 : NNReal) t
  · by_cases hTau : s ≤ tau omega
    · have hMin : s ∈ Ioc (0 : NNReal) (min t (tau omega)) :=
        ⟨hs.1, le_min hs.2 hTau⟩
      simp only [Set.indicator_apply, hs, hMin, ite_true]
      rw [processLeftJump_stoppedProcess_eq_of_le L hL _ s omega
        (WithTop.coe_le_coe.mpr hTau),
        processLeftJump_stoppedProcess_eq_of_le Q hQ _ s omega
          (WithTop.coe_le_coe.mpr hTau)]
    · have hMin : s ∉ Ioc (0 : NNReal) (min t (tau omega)) :=
        fun h => hTau (h.2.trans (min_le_right _ _))
      simp only [Set.indicator_apply, hs, hMin, ite_true, ite_false]
      rw [processLeftJump_stoppedProcess_eq_zero_of_lt L _ s omega
        (WithTop.coe_lt_coe.mpr (lt_of_not_ge hTau)),
        processLeftJump_stoppedProcess_eq_zero_of_lt Q _ s omega
          (WithTop.coe_lt_coe.mpr (lt_of_not_ge hTau)), hf]
  · have hMin : s ∉ Ioc (0 : NNReal) (min t (tau omega)) :=
      fun h => hs ⟨h.1, h.2.trans (min_le_left _ _)⟩
    simp only [Set.indicator_apply, hs, hMin, ite_false]

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

noncomputable def DoleansDadeYenData.stoppedQuadraticCorrection
    (d : DoleansDadeYenData X F mu c) (tau : Ω → NNReal) : Process Ω := fun t omega =>
      2 * (∑' s : Ioc (0 : NNReal) t,
        processLeftJump (stoppedProcess d.L (fun w => (tau w : WithTop NNReal))) s omega *
          processLeftJump (stoppedProcess d.Q (fun w => (tau w : WithTop NNReal))) s omega) +
      ∑' s : Ioc (0 : NNReal) t,
        (processLeftJump (stoppedProcess d.Q (fun w => (tau w : WithTop NNReal))) s omega) ^ 2

theorem DoleansDadeYenData.quadraticCorrection_stopped
    (d : DoleansDadeYenData X F mu c) (tau : Ω → NNReal) (t : NNReal) (omega : Ω) :
    stoppedProcess d.quadraticCorrection (fun w => (tau w : WithTop NNReal)) t omega =
      d.stoppedQuadraticCorrection tau t omega := by
  unfold stoppedQuadraticCorrection
  rw [BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply]
  have hCross := tsum_stopped_jump_eq d.L d.Q d.L_leftLimits d.Q_leftLimits
    (fun x y => x * y) (mul_zero 0) tau t omega
  have hSquare := tsum_stopped_jump_eq d.Q d.Q d.Q_leftLimits d.Q_leftLimits
    (fun _ y => y ^ 2) (zero_pow (by decide : 2 ≠ 0)) tau t omega
  rw [hCross, hSquare]
  rfl

theorem DoleansDadeYenData.corrected_stoppedCoordinate
    (d : DoleansDadeYenData X F mu c)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C)
    {V : Process Ω} (hV : ProcessIndistinguishable mu V
      (fun t omega => QC.variation t omega + d.quadraticCorrection t omega)) (n : Nat) :
    ProcessIndistinguishable mu
      (stoppedProcess V (fun w => (C.localizer n w : WithTop NNReal)))
      (fun t omega => stoppedProcess (C.coordinate n).quadraticData.variation
        (fun w => (C.localizer n w : WithTop NNReal)) t omega +
          d.stoppedQuadraticCorrection (C.localizer n) t omega) := by
  filter_upwards [hV, QC.variation_stoppedCoordinate n] with omega hPath hCoord
  intro t
  rw [← d.quadraticCorrection_stopped]
  rw [BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
    BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
    BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply]
  have hEq := hCoord t
  simp only [BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply] at hEq
  rw [hPath, hEq]

end FTAPTheorem42
