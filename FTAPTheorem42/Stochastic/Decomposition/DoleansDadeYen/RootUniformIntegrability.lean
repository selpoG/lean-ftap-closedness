/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.CommonLocalization
import FTAPTheorem42.Stochastic.Martingale.Quadratic.ConvexQuadraticRootDomination

/-! # First-moment Davis estimates for the original DDY source on finite grids -/

namespace FTAPTheorem42

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [F.IsRightContinuous] {X : Process Ω} {c : Real}

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous] in
theorem DoleansDadeYenL1Localization.source_martingale
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d) (n : Nat) :
    Martingale (stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))) F mu := by
  have hEq : stoppedProcess X (fun w => (R.tau n w : WithTop NNReal)) =
      stoppedProcess d.L (fun w => (R.tau n w : WithTop NNReal)) +
      stoppedProcess d.Q (fun w => (R.tau n w : WithTop NNReal)) := by
    funext t w
    exact congrFun (congrFun d.decomposition _) w
  rw [hEq]
  exact (R.L_martingale n).add (R.Q_martingale n)

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Uniform integrability of convex quadratic roots of the original DDY source -/

open Filter MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

open BoundedMartingaleQuadraticApproximation
open SquareIntegrableMartingaleQuadraticConvexification
open SquareIntegrableMartingaleQuadraticUniformIntegrability

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {c : Real}

omit [MeasurableSpace Ω] in
private theorem terminal_energy_eq (Y : Process Ω) (T : NNReal) (k : Nat) (w : Ω) :
    squaredIncrementPart Y T k T w = (grid T k).squaredIncrementProcess Y T w := by
  simp only [squaredIncrementPart, ChronologicalGrid.squaredIncrementProcess,
    deterministicallyStoppedProcess_apply, min_right_comm, min_self]

/-- The actual common DDY stops supply uniform integrability for every
forward convexification of the original source's terminal grid energies. -/
theorem DoleansDadeYenL1Localization.source_convex_root_uniformIntegrable
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (n : Nat) (T : NNReal) (W : ForwardConvexWeights) :
    let Y := stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
    UniformIntegrable (fun k w => Real.sqrt
      (W.apply (fun i => squaredIncrementPart Y T i T) k w)) 1 mu := by
  let tau : Ω → WithTop NNReal := fun w => R.tau n w
  let Y := stoppedProcess X tau
  let L := stoppedProcess d.L tau
  let Q := stoppedProcess d.Q tau
  have hLR : ∀ w t, ContinuousWithinAt (L · w) (Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous d.L d.L_rightContinuous
  have hYR : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous X hXR
  have hLM : Martingale L F mu := R.L_martingale n
  have hYM : Martingale Y F mu := R.source_martingale n
  have hLT : MemLp (L T) 2 mu := by
    apply MemLp.of_bound ((hLM.stronglyAdapted T).mono (F.le T)).aestronglyMeasurable
      (cadlagPassageLevel n + 2 * c)
    filter_upwards [R.L_bound n] with w hw
    simpa only [Real.norm_eq_abs] using hw T
  have hQBV : ∀ w, LocallyBoundedVariationOn (Q · w) univ := by
    intro w
    have hPath : (Q · w) = FiniteVariationStoppedPath.stopAt (d.Q · w) (R.tau n w) := by
      funext t
      exact BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply d.Q (R.tau n) t w
    rw [hPath]
    exact (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
      (d.Q_locallyBoundedVariation w) (R.tau n w)).locallyBoundedVariationOn
  have hDecomp : Y = fun t w => L t w + Q t w := by
    funext t w
    exact congrFun (congrFun d.decomposition _) w
  apply W.uniformIntegrable_sqrt_of_root_bound
    (squaredIncrementPart_terminal_uniformIntegrable hLM hLR T hLT)
    (R.variation_integrable n)
    (fun k => (squaredIncrementPart_terminal_stronglyMeasurable hYM hYR T k).aestronglyMeasurable)
    (fun k w => squaredIncrementPart_nonneg Y T T k w)
    (fun k w => squaredIncrementPart_nonneg L T T k w)
    (fun w => variationOnFromTo.nonneg_of_le _ _ bot_le)
  intro k w
  rw [terminal_energy_eq, terminal_energy_eq]
  have hTriangle := (grid T k).sqrt_squaredIncrementProcess_add_le L Q T w
  rw [← hDecomp] at hTriangle
  have hVar := (grid T k).sqrt_squaredIncrementProcess_le_variation Q w (hQBV w) T
  exact hTriangle.trans (add_le_add le_rfl (hVar.trans (R.variation_bound n w T)))

end FTAPTheorem42
