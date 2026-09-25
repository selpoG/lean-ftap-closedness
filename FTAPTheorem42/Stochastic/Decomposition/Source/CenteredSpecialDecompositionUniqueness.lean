/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GoodIntegratorLargeJumpResidual
import FTAPTheorem42.Stochastic.Topology.J1.Stopping

/-! # Centering and restopping the bounded-source decomposition

The source theorem need not normalize the initial component values, nor
choose components constant after a source stop. Centering and stopping the
components supplies both properties and global finite variation.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- A normalized special decomposition with global FV coordinates,
as required by the existing predictable-FV uniqueness and gluing lemmas. -/
structure CenteredGlobalSpecialDecomposition (X : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (μ : Measure Ω)
    extends J1Decomposition X F μ where
  predictableA : IsStronglyPredictable F A
  boundedVariationA : ∀ w, BoundedVariationOn (A · w) univ

namespace HorizonFactorialGrid.BoundedSemimartingaleGlobalSpecialDecompositionData

/-- A finite closed stop of centered components has globally bounded
variation, even if the original FV component has only local BV. -/
noncomputable def centeredStopped
    {X : Process Ω} {source : BoundedSemimartingaleSource X F μ}
    (D : HorizonFactorialGrid.BoundedSemimartingaleGlobalSpecialDecompositionData source)
    (hZero : X 0 = 0) (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun w => (τ w : WithTop NNReal))) :
    CenteredGlobalSpecialDecomposition
      (stoppedProcess X (fun w => (τ w : WithTop NNReal))) F μ := by
  let MC : Process Ω := fun t w => D.M t w - D.M 0 w
  let AC : Process Ω := fun t w => D.A t w - D.A 0 w
  have hMR : ∀ w t, ContinuousWithinAt (MC · w) (Ici t) t :=
    fun w t => (D.M_rightContinuous w t).sub continuousWithinAt_const
  have hAR : ∀ w t, ContinuousWithinAt (AC · w) (Ici t) t :=
    fun w t => (D.A_rightContinuous w t).sub continuousWithinAt_const
  have hM0 : MC 0 = 0 := by funext w; exact sub_self _
  have hAP : IsStronglyPredictable F AC :=
    D.A_isStronglyPredictable.sub
      (IsStronglyPredictable.timeConstant_initial D.A_isStronglyPredictable)
  have hMA : StronglyAdapted F MC := D.M_isStronglyAdapted.sub
    (fun t => (D.M_isStronglyAdapted 0).mono (F.mono bot_le))
  have hBV : ∀ w, BoundedVariationOn
      ((stoppedProcess AC (fun w => (τ w : WithTop NNReal))) · w) univ := by
    intro w
    simp only [stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe,
      AC]
    exact FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
        (SpecialSemimartingaleDecomposition.locallyBoundedVariationOn_sub_initial
          (D.A_locallyBoundedVariation w)) (τ w)
  refine {
    N := stoppedProcess MC (fun w => (τ w : WithTop NNReal))
    A := stoppedProcess AC (fun w => (τ w : WithTop NNReal))
    localMartingale := D.M_isLocalMartingale.centered.stoppedProcess_of_zero_of_rightContinuous
      hM0 hMR hτ
    adaptedN := RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hMA hτ hMR
    rightN := RightContinuousStoppedMartingale.stoppedProcess_rightContinuous MC hMR
    leftN := (D.M_leftLimits.sub (.timeConstant (D.M 0))).stoppedProcess _
    zeroN := ?_
    predictableA := IsStronglyPredictable.stoppedProcess_of_stoppingTime hAP τ hτ
    adaptedA := (IsStronglyPredictable.stoppedProcess_of_stoppingTime hAP τ hτ).stronglyAdapted
    rightA := RightContinuousStoppedMartingale.stoppedProcess_rightContinuous AC hAR
    leftA := (D.A_leftLimits.sub (.timeConstant (D.A 0))).stoppedProcess _
    variationA := fun w => (hBV w).locallyBoundedVariationOn
    boundedVariationA := hBV
    zeroA := ?_
    decomposition := ?_ }
  · filter_upwards [D.decomposition] with w hw
    intro t
    have hz := hw 0
    rw [hZero] at hz
    have ht := hw (min t (τ w))
    simp only [stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe, MC, AC]
    change (0 : Real) = D.M 0 w + D.A 0 w at hz
    linarith
  · funext w
    rw [stoppedProcess_eq_of_le (show ((0 : NNReal) : WithTop NNReal) ≤ _ from bot_le)]
    exact sub_self _
  · funext w
    rw [stoppedProcess_eq_of_le (show ((0 : NNReal) : WithTop NNReal) ≤ _ from bot_le)]
    exact sub_self _

end HorizonFactorialGrid.BoundedSemimartingaleGlobalSpecialDecompositionData

end FTAPTheorem42

namespace FTAPTheorem42.CenteredGlobalSpecialDecomposition

/-! ## Canonical uniqueness of centered globally FV decompositions -/

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F] {X Y : Process Ω}

noncomputable def stopped (D : CenteredGlobalSpecialDecomposition X F μ)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun w => (τ w : WithTop NNReal))) :
    CenteredGlobalSpecialDecomposition (stoppedProcess X (fun w => (τ w : WithTop NNReal))) F μ :=
  { D.toJ1Decomposition.stopped hτ with
    predictableA := IsStronglyPredictable.stoppedProcess_of_stoppingTime D.predictableA τ hτ
    boundedVariationA := fun w => by
      simp only [J1Decomposition.stopped, stoppedProcess, ← WithTop.coe_min,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      exact FiniteVariationStoppedPath.boundedVariationOn_stopAt (D.boundedVariationA w) (τ w) }

/-- Rigidity is applied to the FV difference, which is also a local
martingale. The conclusion uses one exceptional null set for all times. -/
theorem indistinguishable (hUsual : Filtration.UsualConditions μ F)
    (D : CenteredGlobalSpecialDecomposition X F μ)
    (E : CenteredGlobalSpecialDecomposition Y F μ)
    (hXY : ProcessIndistinguishable μ X Y) :
    ProcessIndistinguishable μ D.N E.N ∧ ProcessIndistinguishable μ D.A E.A := by
  let := hUsual.rightContinuous
  have hDiff : ProcessIndistinguishable μ (fun t w => E.N t w - D.N t w)
      (fun t w => D.A t w - E.A t w) := by
    filter_upwards [D.decomposition, E.decomposition, hXY] with w hwD hwE hwXY
    intro t
    have hd := hwD t
    have he := hwE t
    have hx := hwXY t
    linarith
  have hAR : ∀ w t, ContinuousWithinAt ((fun s => D.A s w - E.A s w)) (Ici t) t :=
    fun w t => (D.rightA w t).sub (E.rightA w t)
  have hNM : LocalMartingale (fun t w => E.N t w - D.N t w) F μ := by
    simpa only [sub_eq_add_neg] using
      E.localMartingale.add_of_rightContinuous D.localMartingale.neg E.rightN
        (fun w t => (D.rightN w t).neg)
  have hAM : LocalMartingale (fun t w => D.A t w - E.A t w) F μ :=
    hNM.congr_indistinguishable
      (D.adaptedA.sub E.adaptedA) hAR hDiff
  have hAZ : (fun w => D.A 0 w - E.A 0 w) = 0 := by
    rw [D.zeroA, E.zeroA]
    funext w
    exact sub_self _
  have hBV : ∀ w, BoundedVariationOn (fun t => D.A t w - E.A t w) univ := by
    intro w
    simpa only [sub_eq_add_neg] using
      boundedVariationOn_add (D.boundedVariationA w)
        (boundedVariationOn_neg (E.boundedVariationA w))
  have hZero := HorizonFactorialGrid.predictableFiniteVariationLocalMartingale_eq_zero_of_zero
    hUsual hAM (D.predictableA.sub E.predictableA) hAR
    hBV hAZ
  have hA : ProcessIndistinguishable μ D.A E.A := by
    filter_upwards [hZero] with w hw
    intro t
    exact sub_eq_zero.mp (hw t)
  refine ⟨?_, hA⟩
  filter_upwards [hDiff, hA] with w hw hAw
  intro t
  have hh := hw t
  rw [hAw t, sub_self] at hh
  exact (sub_eq_zero.mp hh).symm

/-- Two finite stopped decompositions agree, component by component,
on their common closed stopping interval. -/
theorem overlap (hUsual : Filtration.UsualConditions μ F)
    (τ σ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun w => (τ w : WithTop NNReal)))
    (hσ : IsStoppingTime F (fun w => (σ w : WithTop NNReal)))
    (D : CenteredGlobalSpecialDecomposition
      (stoppedProcess X (fun w => (τ w : WithTop NNReal))) F μ)
    (E : CenteredGlobalSpecialDecomposition
      (stoppedProcess X (fun w => (σ w : WithTop NNReal))) F μ) :
    let ρ : Ω → WithTop NNReal := fun w => min (τ w : WithTop NNReal) (σ w)
    ProcessIndistinguishable μ (stoppedProcess D.N ρ) (stoppedProcess E.N ρ) ∧
      ProcessIndistinguishable μ (stoppedProcess D.A ρ) (stoppedProcess E.A ρ) := by
  let r : Ω → NNReal := fun w => min (τ w) (σ w)
  have hr : IsStoppingTime F (fun w => (r w : WithTop NNReal)) := by
    simpa only [r, WithTop.coe_min] using hτ.min hσ
  have hEq : ProcessIndistinguishable μ
      (stoppedProcess (stoppedProcess X (fun w => (τ w : WithTop NNReal)))
        (fun w => (r w : WithTop NNReal)))
      (stoppedProcess (stoppedProcess X (fun w => (σ w : WithTop NNReal)))
        (fun w => (r w : WithTop NNReal))) := by
    rw [stoppedProcess_stoppedProcess_of_le_right (fun w =>
      WithTop.coe_le_coe.mpr (min_le_left (τ w) (σ w))),
      stoppedProcess_stoppedProcess_of_le_right (fun w =>
      WithTop.coe_le_coe.mpr (min_le_right (τ w) (σ w)))]
    exact .refl μ _
  simpa only [stopped, J1Decomposition.stopped, r, WithTop.coe_min] using
    (D.stopped r hr).indistinguishable hUsual (E.stopped r hr) hEq

end FTAPTheorem42.CenteredGlobalSpecialDecomposition
