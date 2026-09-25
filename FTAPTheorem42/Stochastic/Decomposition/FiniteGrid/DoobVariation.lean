/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.BoundedSemimartingaleSource
import Mathlib.Probability.Martingale.Centering
import FTAPTheorem42.Stochastic.Integral.Elementary.DiscretePredictableIntegral

/-!
# Doob decompositions of a bounded source on finite grids

Sampling a bounded adapted source along a chronological grid gives an
integrable discrete process.  Mathlib's Doob decomposition therefore supplies
a martingale part and a predictable part on the sampled filtration.  This
module records that decomposition and the uniform increment bounds inherited
from the source.  These finite-grid components are the input for the
predictable-variation estimate in the special-semimartingale construction.
-/

namespace FTAPTheorem42

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- The sampled bounded source is integrable at every grid index. -/
theorem integrable_natSample_boundedSemimartingaleSource
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) :
    ∀ n, Integrable (G.natSample S n) mu := by
  intro n
  apply Integrable.of_bound
    ((source.stronglyAdapted (G.sampledTime n)).mono
      (F.le (G.sampledTime n))).aestronglyMeasurable
    (max source.bound 0)
  filter_upwards [source.uniformBound] with omega homega
  rw [Real.norm_eq_abs]
  exact (homega (G.sampledTime n)).trans (le_max_left _ _)

/-- The sampled source has uniformly bounded one-step increments. -/
theorem ae_norm_natSample_increment_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) :
    ∀ᵐ omega ∂mu, ∀ n,
      ‖G.natSample S (n + 1) omega - G.natSample S n omega‖ ≤
        2 * max source.bound 0 := by
  filter_upwards [source.uniformBound] with omega homega n
  rw [Real.norm_eq_abs]
  calc
    |G.natSample S (n + 1) omega - G.natSample S n omega| ≤
        |G.natSample S (n + 1) omega| + |G.natSample S n omega| :=
      abs_sub _ _
    _ ≤ max source.bound 0 + max source.bound 0 :=
      add_le_add
        ((homega (G.sampledTime (n + 1))).trans (le_max_left _ _))
        ((homega (G.sampledTime n)).trans (le_max_left _ _))
    _ = 2 * max source.bound 0 := by ring

/-- The Doob martingale part of the sampled bounded source is a martingale. -/
theorem martingale_martingalePart_natSample_boundedSemimartingaleSource
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) :
    Martingale
      (martingalePart (G.natSample S) (G.sampledFiltration F) mu)
      (G.sampledFiltration F) mu := by
  exact martingale_martingalePart
    (fun n => source.stronglyAdapted (G.sampledTime n))
    (G.integrable_natSample_boundedSemimartingaleSource source)

/-- The predictable part inherits the source's uniform increment bound. -/
theorem ae_norm_predictablePart_increment_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) :
    ∀ᵐ omega ∂mu, ∀ n,
      ‖predictablePart (G.natSample S) (G.sampledFiltration F) mu (n + 1) omega -
          predictablePart (G.natSample S) (G.sampledFiltration F) mu n omega‖ ≤
        2 * max source.bound 0 :=
  predictablePart_bdd_difference (G.sampledFiltration F)
    (G.ae_norm_natSample_increment_le source)

end ChronologicalGrid

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Predictable variation of finite-grid Doob decompositions

For the Doob decomposition of a source sampled on a chronological grid, the
sign of the next predictable increment is known at the current grid time.
It is therefore an adapted coefficient for the sampled filtration and has
absolute value one. Its discrete integral against the source splits exactly
into the corresponding martingale transform plus the total variation of the
predictable part along the grid.
-/

open MeasureTheory Set
open scoped BigOperators NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- The predictable component in the Doob decomposition of the sampled
source. -/
noncomputable def doobPredictablePart
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Nat → Omega → Real :=
  predictablePart (G.natSample S) (G.sampledFiltration F) mu

/-- The martingale component in the Doob decomposition of the sampled
source. -/
noncomputable def doobMartingalePart
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Nat → Omega → Real :=
  martingalePart (G.natSample S) (G.sampledFiltration F) mu

/-- One forward increment of the finite-grid predictable component. -/
noncomputable def doobPredictableIncrement
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (n : Nat) : Omega → Real :=
  G.doobPredictablePart S F mu (n + 1) -
    G.doobPredictablePart S F mu n

/-- The sign which turns the next predictable increment into its absolute
value. The zero increment is assigned sign `1`. -/
noncomputable def doobPredictableSign
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Nat → Omega → Real :=
  fun n omega =>
    if 0 ≤ G.doobPredictableIncrement S F mu n omega then 1 else -1

/-- The sign of the next predictable increment is measurable at the current
grid time. -/
theorem stronglyAdapted_doobPredictableSign
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu] :
    StronglyAdapted (G.sampledFiltration F)
      (G.doobPredictableSign S F mu) := by
  classical
  intro n
  have hNext : StronglyMeasurable[G.sampledFiltration F n]
      (G.doobPredictablePart S F mu (n + 1)) :=
    stronglyAdapted_predictablePart (f := G.natSample S)
      (ℱ := G.sampledFiltration F) (μ := mu) n
  have hNow : StronglyMeasurable[G.sampledFiltration F n]
      (G.doobPredictablePart S F mu n) :=
    stronglyAdapted_predictablePart' (f := G.natSample S)
      (ℱ := G.sampledFiltration F) (μ := mu) n
  have hIncrement : StronglyMeasurable[G.sampledFiltration F n]
      (G.doobPredictableIncrement S F mu n) := hNext.sub hNow
  let B : Set Omega :=
    {omega | 0 ≤ G.doobPredictableIncrement S F mu n omega}
  have hB : MeasurableSet[G.sampledFiltration F n] B := by
    change MeasurableSet[G.sampledFiltration F n]
      ((G.doobPredictableIncrement S F mu n) ⁻¹' Ici 0)
    exact hIncrement.measurable measurableSet_Ici
  change StronglyMeasurable[G.sampledFiltration F n]
    (B.piecewise (fun _ => (1 : Real)) (fun _ => -1))
  exact StronglyMeasurable.piecewise hB
    stronglyMeasurable_const stronglyMeasurable_const

/-- Every predictable-increment sign has absolute value one. -/
@[simp]
theorem abs_doobPredictableSign
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (n : Nat) (omega : Omega) :
    |G.doobPredictableSign S F mu n omega| = 1 := by
  by_cases h : 0 ≤ G.doobPredictableIncrement S F mu n omega <;>
    simp [doobPredictableSign, h]

/-- Multiplication by the selected sign gives the absolute predictable
increment. -/
theorem doobPredictableSign_mul_increment
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (n : Nat) (omega : Omega) :
    G.doobPredictableSign S F mu n omega *
        G.doobPredictableIncrement S F mu n omega =
      |G.doobPredictableIncrement S F mu n omega| := by
  by_cases h : 0 ≤ G.doobPredictableIncrement S F mu n omega
  · simp [doobPredictableSign, h, abs_of_nonneg h]
  · have hneg : G.doobPredictableIncrement S F mu n omega < 0 :=
      lt_of_not_ge h
    simp [doobPredictableSign, h, abs_of_neg hneg]

/-- Total variation of the predictable Doob component over the first `n`
grid increments. -/
noncomputable def doobPredictableVariation
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (n : Nat) : Omega → Real :=
  fun omega => ∑ k ∈ Finset.range n,
    |G.doobPredictableIncrement S F mu k omega|

end ChronologicalGrid

end FTAPTheorem42
