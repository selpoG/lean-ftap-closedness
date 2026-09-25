/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.StieltjesLimit
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticLocalizingScheduleSemantics

/-! # Identifying stopped quadratic approximations with original-source grids -/

namespace FTAPTheorem42.BoundedMartingaleQuadraticApproximation

open MeasureTheory
open scoped NNReal ENNReal

theorem squaredIncrementPart_stopped_eq
    {Ω : Type*} [MeasurableSpace Ω] (X : Process Ω) (tau : Ω → NNReal)
    (T t : NNReal) (omega : Ω) (htT : t ≤ T) (r : Nat) :
    squaredIncrementPart (stoppedProcess X (fun w => (tau w : WithTop NNReal))) T r t omega =
      (FactorialChronologicalGrid.grid (level T r)).squaredIncrementProcess X
        (min t (tau omega)) omega := by
  have hClamp : ∀ a : NNReal, min (min t (min a T)) T = min t a := by
    intro a
    rw [← min_assoc, min_eq_left ((min_le_left t a).trans htT),
      min_eq_left ((min_le_left t a).trans htT)]
  unfold squaredIncrementPart ChronologicalGrid.squaredIncrementProcess
  apply Finset.sum_congr rfl
  intro k _
  simp only [deterministicallyStoppedProcess_apply,
    BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
    grid, ChronologicalGrid.sampledTime, FactorialChronologicalGrid.stoppedGrid_time, hClamp,
    min_right_comm]
  rfl

end FTAPTheorem42.BoundedMartingaleQuadraticApproximation

namespace FTAPTheorem42

/-! ## Nonnegativity of the DDY-corrected quadratic candidate -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open BoundedMartingaleQuadraticApproximation

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

/-- The pathwise correction uses the same DDY components at all horizons. -/
noncomputable def DoleansDadeYenData.quadraticCorrection
    (d : DoleansDadeYenData X F mu c) : Process Ω := fun t omega =>
  2 * (∑' s : Ioc (0 : NNReal) t, processLeftJump d.L s omega * processLeftJump d.Q s omega) +
    ∑' s : Ioc (0 : NNReal) t, (processLeftJump d.Q s omega) ^ 2

theorem DoleansDadeYenData.stoppedCorrection_tendsto
    (d : DoleansDadeYenData X F mu c) (tau : Ω → NNReal) (T t : NNReal)
    (omega : Ω) (htT : t ≤ T) :
    Tendsto (fun r =>
      squaredIncrementPart (stoppedProcess X (fun w => (tau w : WithTop NNReal))) T r t omega -
        squaredIncrementPart (stoppedProcess d.L (fun w => (tau w : WithTop NNReal))) T r t omega)
      atTop (𝓝 (d.quadraticCorrection (min t (tau omega)) omega)) := by
  have hRaw : Tendsto (fun r =>
      (FactorialChronologicalGrid.grid r).squaredIncrementProcess X (min t (tau omega)) omega -
        (FactorialChronologicalGrid.grid r).squaredIncrementProcess d.L (min t (tau omega)) omega)
      atTop (𝓝 (d.quadraticCorrection (min t (tau omega)) omega)) :=
    (tendsto_add_atTop_iff_nat 1).mp
      (d.finiteGrid_correction_tendsto_jumpSum (min t (tau omega)) omega)
  have hLevel : Tendsto (level T) atTop atTop :=
    tendsto_atTop_mono (self_le_level T) tendsto_id
  simp_rw [squaredIncrementPart_stopped_eq _ tau T t omega htT]
  exact hRaw.comp hLevel

/-- The actual stored convex weights of the finite-horizon quadratic
provider also preserve convergence of the DDY correction. -/
theorem DoleansDadeYenData.coordinate_stopped_corrected_tendsto
    (d : DoleansDadeYenData X F mu c) (tau : Ω → NNReal) (T : NNReal)
    (D : BoundedMartingaleQuadraticKernel.Data F mu
      (stoppedProcess d.L (fun w => (tau w : WithTop NNReal))) T) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      Tendsto (fun k => BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        (stoppedProcess X (fun w => (tau w : WithTop NNReal))) T
          (D.weights (D.cutoff k)) t omega) atTop
        (𝓝 (D.variation t omega + d.quadraticCorrection (min t (tau omega)) omega)) := by
  filter_upwards [D.variation_uniform] with omega hUniform
  intro t htT
  have hCorrection := d.stoppedCorrection_tendsto tau T t omega htT
  have hConv := ((TailConvexWeights.toForward D.weights).tendsto_apply_real hCorrection).comp
    D.cutoff_strictMono.tendsto_atTop
  have hDifference : Tendsto (fun k =>
      BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        (stoppedProcess X (fun w => (tau w : WithTop NNReal))) T (D.weights (D.cutoff k)) t omega -
      BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        (stoppedProcess d.L (fun w => (tau w : WithTop NNReal))) T (D.weights (D.cutoff k)) t omega)
      atTop (𝓝 (d.quadraticCorrection (min t (tau omega)) omega)) := by
    simpa only [TailConvexWeights.toForward, Function.comp_def, mul_sub, Finset.sum_sub_distrib,
      BoundedMartingaleQuadraticConvexification.squaredIncrementPart, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using hConv
  have hSource := (hUniform.tendsto_at t).add hDifference
  simpa only [← add_sub_assoc, add_sub_cancel_left] using hSource

theorem DoleansDadeYenData.coordinate_corrected_tendsto
    (d : DoleansDadeYenData X F mu c) (tau : Ω → NNReal) (T : NNReal)
    (D : BoundedMartingaleQuadraticKernel.Data F mu
      (stoppedProcess d.L (fun w => (tau w : WithTop NNReal))) T) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T → t ≤ tau omega →
      Tendsto (fun k => BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        (stoppedProcess X (fun w => (tau w : WithTop NNReal))) T
          (D.weights (D.cutoff k)) t omega) atTop
        (𝓝 (D.variation t omega + d.quadraticCorrection t omega)) := by
  filter_upwards [d.coordinate_stopped_corrected_tendsto tau T D] with omega h
  intro t htT htTau
  simpa only [min_eq_left htTau] using h t htT

/-- Nonnegative original-source approximations yield a nonnegative
corrected limit with precisely the stored coordinate weights. -/
theorem DoleansDadeYenData.coordinate_corrected_nonnegative
    (d : DoleansDadeYenData X F mu c) (tau : Ω → NNReal) (T : NNReal)
    (D : BoundedMartingaleQuadraticKernel.Data F mu
      (stoppedProcess d.L (fun w => (tau w : WithTop NNReal))) T) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T → t ≤ tau omega →
      0 ≤ D.variation t omega + d.quadraticCorrection t omega := by
  filter_upwards [d.coordinate_corrected_tendsto tau T D] with omega hLimit
  intro t htT htTau
  have hNonneg : ∀ k, 0 ≤
      BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        (stoppedProcess X (fun w => (tau w : WithTop NNReal))) T
          (D.weights (D.cutoff k)) t omega := by
    intro k
    simp only [BoundedMartingaleQuadraticConvexification.squaredIncrementPart, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg (fun i hi => mul_nonneg ((D.weights (D.cutoff k)).nonneg i hi)
      (squaredIncrementPart_nonneg _ T t i omega))
  exact ge_of_tendsto (hLimit t htT htTau) (Eventually.of_forall hNonneg)

/-- Exhaustion transfers the coordinate result to the same glued
quadratic variation on one event, simultaneously for every time. -/
theorem DoleansDadeYenData.corrected_nonnegative
    (d : DoleansDadeYenData X F mu c)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C) :
    ∀ᵐ omega ∂mu, ∀ t, 0 ≤ QC.variation t omega + d.quadraticCorrection t omega := by
  have hCoordinates : ∀ᵐ omega ∂mu, ∀ n t, t ≤ C.horizon n → t ≤ C.localizer n omega →
      0 ≤ (C.coordinate n).quadraticData.variation t omega + d.quadraticCorrection t omega :=
    ae_all_iff.mpr (fun n => d.coordinate_corrected_nonnegative
      (C.localizer n) (C.horizon n) (C.coordinate n).quadraticData)
  have hStopped := ae_all_iff.mpr QC.variation_stoppedCoordinate
  filter_upwards [C.isLocalizingSequence.tendsto_top, hCoordinates, hStopped]
    with omega hTop hNonneg hEq
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  intro t
  obtain ⟨n, hn⟩ := (hTop (t + 1)).exists
  have htTau : t ≤ C.localizer n omega := by
    have hn' : t + 1 < C.localizer n omega := WithTop.coe_lt_coe.mp hn
    linarith
  have htT := htTau.trans (C.localizer_le_horizon n omega)
  have hSame := hEq n t
  simp only [BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
    min_eq_left htTau] at hSame
  rw [hSame]
  exact hNonneg n t htT htTau

end FTAPTheorem42
