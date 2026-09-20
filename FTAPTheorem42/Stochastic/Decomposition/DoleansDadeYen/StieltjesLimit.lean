/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.Basic
import FTAPTheorem42.Stochastic.FiniteVariation.FactorialCellStieltjes
import FTAPTheorem42.Stochastic.Process.CadlagJumpStieltjesSeries

/-! # Finite-grid quadratic control for the original DDY source -/

namespace FTAPTheorem42

open MeasureTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

/-- The original source and its bounded-jump component use the same cells.
Their quadratic roots differ by at most the variation of the same residual. -/
theorem DoleansDadeYenData.finiteGrid_control
    (d : DoleansDadeYenData X F mu c) {N : Nat} (G : ChronologicalGrid NNReal N)
    (t : NNReal) (omega : Ω) :
    G.squaredIncrementProcess X t omega =
      G.squaredIncrementProcess d.L t omega + 2 * G.crossIncrementProcess d.L d.Q t omega +
        G.squaredIncrementProcess d.Q t omega ∧
    |Real.sqrt (G.squaredIncrementProcess X t omega) -
      Real.sqrt (G.squaredIncrementProcess d.L t omega)| ≤
        variationOnFromTo (d.Q · omega) univ 0 t := by
  have hEq := congrArg (fun Y => G.squaredIncrementProcess Y t omega) d.decomposition
  rw [G.squaredIncrementProcess_add] at hEq
  refine ⟨hEq, ?_⟩
  have hX := G.sqrt_squaredIncrementProcess_add_le d.L d.Q t omega
  have hXSource := congrArg (fun Y => Real.sqrt (G.squaredIncrementProcess Y t omega))
    d.decomposition
  rw [← hXSource] at hX
  have hL := G.sqrt_squaredIncrementProcess_add_le X (fun s w => -d.Q s w) t omega
  have hRecover : (fun s w => X s w + -d.Q s w) = d.L := by
    funext s w
    have h := congrFun (congrFun d.decomposition s) w
    change X s w + -d.Q s w = d.L s w
    linarith
  have hNeg : G.squaredIncrementProcess (fun s w => -d.Q s w) t omega =
      G.squaredIncrementProcess d.Q t omega := by
    unfold ChronologicalGrid.squaredIncrementProcess
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hRecover, hNeg] at hL
  have hQ := G.sqrt_squaredIncrementProcess_le_variation d.Q omega
    (d.Q_locallyBoundedVariation omega) t
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Partition convergence of the DDY quadratic correction -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

/-- For the same original source and DDY components, the difference of
finite-grid quadratic sums has a pathwise limit. Identifying these two
Stieltjes integrals with jump series is a separate step. -/
theorem DoleansDadeYenData.finiteGrid_correction_tendsto
    (d : DoleansDadeYenData X F mu c) (T : NNReal) (omega : Ω) :
    let η := FiniteVariationPath.signedMeasure
      (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
        (d.Q_locallyBoundedVariation omega) T)
    Tendsto (fun r =>
      (FactorialChronologicalGrid.grid (r + 1)).squaredIncrementProcess X T omega -
        (FactorialChronologicalGrid.grid (r + 1)).squaredIncrementProcess d.L T omega)
      atTop (𝓝 (2 * (∫ᵛ s in Ioc (0 : NNReal) T, processLeftJump d.L s omega ∂•η) +
        ∫ᵛ s in Ioc (0 : NNReal) T, processLeftJump d.Q s omega ∂•η)) := by
  have hL := FactorialChronologicalGrid.tendsto_crossIncrementProcess_stieltjes d.L d.Q omega
    (d.L_rightContinuous omega) (d.L_leftLimits omega) (d.Q_locallyBoundedVariation omega)
    (d.Q_rightContinuous omega) T
  have hQ := FactorialChronologicalGrid.tendsto_crossIncrementProcess_stieltjes d.Q d.Q omega
    (d.Q_rightContinuous omega) (d.Q_leftLimits omega) (d.Q_locallyBoundedVariation omega)
    (d.Q_rightContinuous omega) T
  apply ((hL.const_mul 2).add hQ).congr'
  apply Eventually.of_forall
  intro r
  have hEq := (d.finiteGrid_control (FactorialChronologicalGrid.grid (r + 1)) T omega).1
  have hSquare : (FactorialChronologicalGrid.grid (r + 1)).crossIncrementProcess d.Q d.Q
      T omega = (FactorialChronologicalGrid.grid (r + 1)).squaredIncrementProcess d.Q
        T omega := by
    simp only [ChronologicalGrid.crossIncrementProcess, ChronologicalGrid.squaredIncrementProcess,
      pow_two]
  dsimp only
  rw [hSquare]
  linarith

/-! ## The DDY jump correction is the limit of the original grid correction -/

/-- The same original source, bounded-jump component and finite-variation
residual satisfy the partition-to-jump-series identity on every path. -/
theorem DoleansDadeYenData.finiteGrid_correction_tendsto_jumpSum
    (d : DoleansDadeYenData X F mu c) (T : NNReal) (omega : Ω) :
    Tendsto (fun r =>
      (FactorialChronologicalGrid.grid (r + 1)).squaredIncrementProcess X T omega -
        (FactorialChronologicalGrid.grid (r + 1)).squaredIncrementProcess d.L T omega)
      atTop (𝓝 (2 * (∑' t : Ioc (0 : NNReal) T,
        processLeftJump d.L t omega * processLeftJump d.Q t omega) +
          ∑' t : Ioc (0 : NNReal) T, (processLeftJump d.Q t omega) ^ 2)) := by
  have h := d.finiteGrid_correction_tendsto T omega
  dsimp only at h
  rw [setIntegral_processLeftJump_eq_tsum d.L d.Q d.L_rightContinuous d.L_leftLimits
      d.Q_rightContinuous d.Q_leftLimits d.Q_locallyBoundedVariation,
    setIntegral_processLeftJump_eq_tsum d.Q d.Q d.Q_rightContinuous d.Q_leftLimits
      d.Q_rightContinuous d.Q_leftLimits d.Q_locallyBoundedVariation] at h
  simpa only [pow_two] using h

end FTAPTheorem42
