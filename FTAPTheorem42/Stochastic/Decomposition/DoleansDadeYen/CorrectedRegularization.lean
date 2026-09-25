/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.JumpCorrection
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.SquareIntegralMartingale

/-! # Jump-square identity for the same DDY-corrected candidate -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

theorem DoleansDadeYenData.quadraticCorrection_leftJump
    (d : DoleansDadeYenData X F mu c) :
    ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump d.quadraticCorrection t omega =
        2 * (processLeftJump d.L t omega * processLeftJump d.Q t omega) +
          (processLeftJump d.Q t omega) ^ 2 := by
  filter_upwards [d.jump_correction_summable] with omega hSum
  let a : NNReal → Real := fun s =>
    2 * (processLeftJump d.L s omega * processLeftJump d.Q s omega) +
      (processLeftJump d.Q s omega) ^ 2
  have ha : ∀ T, Summable (fun s : Ioc (0 : NNReal) T => a s) := fun T =>
    ((hSum T).1.mul_left 2).add (hSum T).2.1
  have hEq : (d.quadraticCorrection · omega) = fun t => ∑' s : Ioc (0 : NNReal) t, a s := by
    funext t
    dsimp only [quadraticCorrection, a]
    rw [((hSum t).1.mul_left 2).tsum_add (hSum t).2.1, tsum_mul_left]
  intro t
  by_cases ht : t = 0
  · subst t
    have hZero (Y : Process Ω) : processLeftJump Y 0 omega = 0 :=
      sub_eq_zero.mpr (leftLim_eq_of_isBot (f := fun s => Y s omega) isBot_bot).symm
    simp only [hZero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  · change d.quadraticCorrection t omega - Function.leftLim (d.quadraticCorrection · omega) t = a t
    rw [congrFun hEq t, hEq]
    exact SummableJumpCumulative.leftJump_Ioc a ha (pos_iff_ne_zero.mpr ht)

theorem DoleansDadeYenData.corrected_leftJump_eq_sq
    (d : DoleansDadeYenData X F mu c)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C) :
    ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump (fun s omega => QC.variation s omega + d.quadraticCorrection s omega)
        t omega = (processLeftJump X t omega) ^ 2 := by
  filter_upwards [d.quadraticCorrection_leftJump, d.quadraticCorrection_regular,
    QC.leftJump_eq_sq] with omega hJ hReg hQC
  let A : Process Unit := fun t _ => d.quadraticCorrection t omega
  let B : Process Unit := fun t _ => QC.variation t omega
  have hA : ProcessHasLeftLimits A :=
    SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      (fun _ => hReg.2)
  have hB : ProcessHasLeftLimits B := fun _ t => QC.variation_hasLeftLimits omega t
  intro t
  have hAdd := processLeftJump_add hB hA t ()
  change processLeftJump (fun s omega => QC.variation s omega + d.quadraticCorrection s omega)
      t omega = processLeftJump QC.variation t omega +
        processLeftJump d.quadraticCorrection t omega at hAdd
  have hXJump : processLeftJump X t omega =
      processLeftJump d.L t omega + processLeftJump d.Q t omega := by
    calc
      _ = processLeftJump (fun s omega => d.L s omega + d.Q s omega) t omega :=
        congrArg (fun Y => processLeftJump Y t omega) d.decomposition
      _ = _ := processLeftJump_add d.L_leftLimits d.Q_leftLimits t omega
  rw [hAdd, hQC t, hJ t, hXJump]
  ring

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Monotonicity of the DDY-corrected quadratic candidate -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticVariation.Approximation

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

/-- Nested grid comparison for the same coordinate weights, right
continuity, and exhaustion give monotonicity on one common event. -/
theorem DoleansDadeYenData.corrected_monotone
    (d : DoleansDadeYenData X F mu c)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C) :
    ∀ᵐ omega ∂mu, Monotone (fun t => QC.variation t omega + d.quadraticCorrection t omega) := by
  have hLimits := ae_all_iff.mpr (fun n => d.coordinate_corrected_tendsto
    (C.localizer n) (C.horizon n) (C.coordinate n).quadraticData)
  have hStopped := ae_all_iff.mpr QC.variation_stoppedCoordinate
  filter_upwards [C.isLocalizingSequence.tendsto_top, hLimits, hStopped,
    (d.corrected_regular C QC).2] with omega hTop hLimit hSame hReg
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  intro s t hst
  obtain ⟨n, hn⟩ := (hTop (t + 1)).exists
  have htTau : t < C.localizer n omega := by
    have hn' : t + 1 < C.localizer n omega := WithTop.coe_lt_coe.mp hn
    linarith
  have htT := htTau.le.trans (C.localizer_le_horizon n omega)
  let T := C.horizon n
  let R : NNReal → Real := fun u => QC.variation u omega + d.quadraticCorrection u omega
  have hsLimit := FiniteVariationFactorialApproximation.tendsto_apply_min_approx R hReg.1
    (hst.trans htT)
  have htLimit := FiniteVariationFactorialApproximation.tendsto_apply_min_approx R hReg.1 htT
  apply le_of_tendsto_of_tendsto hsLimit htLimit
  have hBelow : ∀ᶠ r in atTop, FactorialChronologicalGrid.approx r t < C.localizer n omega :=
    (FactorialChronologicalGrid.tendsto_approx t).eventually (gt_mem_nhds htTau)
  filter_upwards [eventually_ge_atTop (Nat.ceil T), hBelow] with r hr hBelow
  let u := min (FactorialChronologicalGrid.approx r s) T
  let v := min (FactorialChronologicalGrid.approx r t) T
  have huv : u ≤ v := min_le_min (FactorialChronologicalGrid.approx_mono r hst) le_rfl
  have hvTau : v ≤ C.localizer n omega := (min_le_left _ _).trans hBelow.le
  have huTau := huv.trans hvTau
  have huMem : u ∈ range (FactorialChronologicalGrid.stoppedGrid T r).time := by
    refine ⟨FactorialChronologicalGrid.approxIndex s ((Nat.ceil_mono (hst.trans htT)).trans hr), ?_⟩
    simp only [FactorialChronologicalGrid.stoppedGrid_time,
      FactorialChronologicalGrid.grid_time_approxIndex, u]
  have hvMem : v ∈ range (FactorialChronologicalGrid.stoppedGrid T r).time := by
    refine ⟨FactorialChronologicalGrid.approxIndex t ((Nat.ceil_mono htT).trans hr), ?_⟩
    simp only [FactorialChronologicalGrid.stoppedGrid_time,
      FactorialChronologicalGrid.grid_time_approxIndex, v]
  have hAgree : ∀ z, z ≤ C.localizer n omega →
      (C.coordinate n).quadraticData.variation z omega + d.quadraticCorrection z omega = R z := by
    intro z hz
    have h := hSame n z
    simp only [BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
      min_eq_left hz] at h
    exact congrArg (fun a => a + d.quadraticCorrection z omega) h.symm
  have huLimit := hLimit n u (min_le_right _ _) huTau
  have hvLimit := hLimit n v (min_le_right _ _) hvTau
  rw [hAgree u huTau] at huLimit
  rw [hAgree v hvTau] at hvLimit
  apply le_of_tendsto_of_tendsto huLimit hvLimit
  filter_upwards [eventually_ge_atTop r] with k hk
  exact squaredIncrementPart_mono_on_stoppedGrid_range
    (stoppedProcess X (fun w => (C.localizer n w : WithTop NNReal))) T
    ((C.coordinate n).quadraticData.weights ((C.coordinate n).quadraticData.cutoff k))
    ((hk.trans ((C.coordinate n).quadraticData.cutoff_strictMono.id_le k)).trans
      (self_le_level T _)) huMem hvMem huv omega

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## A pathwise regular representative of the same DDY quadratic candidate -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

/-- Regularize precisely the candidate already produced by the original
source and its quadratic schedule. The exceptional set belongs to time zero. -/
theorem DoleansDadeYenData.exists_regularized_corrected
    (d : DoleansDadeYenData X F mu c)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ V : Process Ω,
      ProcessIndistinguishable mu V
        (fun t omega => QC.variation t omega + d.quadraticCorrection t omega) ∧
      StronglyAdapted F V ∧
      (∀ omega t, ContinuousWithinAt (V · omega) (Ici t) t) ∧
      (∀ omega, Monotone (V · omega)) ∧ V 0 = 0 ∧
      (∀ omega, LocallyBoundedVariationOn (V · omega) univ) ∧ ProcessHasLeftLimits V ∧
      (∀ᵐ omega ∂mu, ∀ t, processLeftJump V t omega = (processLeftJump X t omega) ^ 2) ∧
      (∀ n, ProcessIndistinguishable mu
        (stoppedProcess V (fun w => (C.localizer n w : WithTop NNReal)))
        (fun t omega => stoppedProcess (C.coordinate n).quadraticData.variation
          (fun w => (C.localizer n w : WithTop NNReal)) t omega +
            d.stoppedQuadraticCorrection (C.localizer n) t omega)) ∧
      (∀ᵐ omega ∂mu, ∀ t, X t omega ^ 2 - V t omega =
        (d.L t omega ^ 2 - QC.variation t omega) +
          2 * (d.L t omega * d.Q t omega -
            (∑' s : Ioc (0 : NNReal) t,
              processLeftJump d.L s omega * processLeftJump d.Q s omega) +
            d.finiteVariationSquareIntegral t omega)) := by
  let R : Process Ω := fun t omega => QC.variation t omega + d.quadraticCorrection t omega
  have hReg : ∀ᵐ omega ∂mu,
      (∀ t, ContinuousWithinAt (R · omega) (Ici t) t) ∧ Monotone (R · omega) := by
    filter_upwards [(d.corrected_regular C QC).2, d.corrected_monotone C QC] with omega hR hM
    exact ⟨hR.1, hM⟩
  let bad : Set Ω := {omega | ¬((∀ t, ContinuousWithinAt (R · omega) (Ici t) t) ∧
    Monotone (R · omega))}
  have hNull : mu bad = 0 := ae_iff.mp hReg
  have hGood : ∀ omega, omega ∉ bad →
      (∀ t, ContinuousWithinAt (R · omega) (Ici t) t) ∧ Monotone (R · omega) := by
    intro omega h
    exact not_not.mp h
  let V := ProcessNullSetRegularization.zeroOn bad R
  have hVRight : ∀ omega t, ContinuousWithinAt (V · omega) (Ici t) t :=
    ProcessNullSetRegularization.zeroOn_isRightContinuous (fun omega h => (hGood omega h).1)
  have hVMono : ∀ omega, Monotone (V · omega) := by
    intro omega s t hst
    by_cases h : omega ∈ bad
    · simp only [V, ProcessNullSetRegularization.zeroOn_apply_of_mem bad R h, le_refl]
    · simpa only [V, ProcessNullSetRegularization.zeroOn_apply_of_notMem bad R h] using
        (hGood omega h).2 hst
  have hRZero : R 0 = 0 := by
    funext omega
    simp [R, quadraticCorrection, QC.variation_zero]
  have hVZero : V 0 = 0 := by
    funext omega
    by_cases h : omega ∈ bad
    · exact ProcessNullSetRegularization.zeroOn_apply_of_mem bad R h
    · simpa only [V, ProcessNullSetRegularization.zeroOn_apply_of_notMem bad R h] using
        congrFun hRZero omega
  have hVBV : ∀ omega, LocallyBoundedVariationOn (V · omega) univ := fun omega =>
    ((hVMono omega).monotoneOn univ).locallyBoundedVariationOn
  have hInd : ProcessIndistinguishable mu V R :=
    ProcessNullSetRegularization.zeroOn_indistinguishable hNull R
  have hJump : ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump V t omega = (processLeftJump X t omega) ^ 2 := by
    filter_upwards [hInd, d.corrected_leftJump_eq_sq C QC] with omega hV hJ
    have hPath : (V · omega) = (R · omega) := funext hV
    intro t
    change V t omega - Function.leftLim (V · omega) t = _
    rw [hV t, hPath]
    exact hJ t
  exact ⟨V, hInd,
    ProcessNullSetRegularization.stronglyAdapted_zeroOn
      (hUsual.containsNullSetsAtZero bad hNull) (d.corrected_regular C QC).1,
    hVRight, hVMono, hVZero, hVBV,
    SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      hVBV, hJump, d.corrected_stoppedCoordinate C QC hInd,
      d.corrected_squareResidual_eq C QC hInd⟩

end FTAPTheorem42
