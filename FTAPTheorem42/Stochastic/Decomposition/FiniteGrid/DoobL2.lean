/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobVariation

/-!
# Square integrability of finite-grid Doob martingales

On each finite chronological grid, the predictable Doob component grows at
most linearly in the number of grid steps because its increments inherit the
source bound.  The martingale component is therefore bounded at every fixed
grid index and belongs to `L²`.  Consequently the predictable sign transform
used to expose the variation is itself a true martingale.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- A pathwise `L²` envelope gives finite-grid sample membership. -/
theorem sample_memLp_two_of_memLp_two_envelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Q : Measure Omega} [IsProbabilityMeasure Q]
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) Q)
    (hSBound : ∀ᵐ omega ∂Q, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (n : Nat) : MemLp (G.natSample S n) (2 : ENNReal) Q := by
  have hξNorm : MemLp (fun omega => ‖ξ omega‖) (2 : ENNReal) Q := hξ.norm
  have hSampleAdapted :
      StronglyAdapted (G.sampledFiltration F) (G.natSample S) := by
    intro k
    exact hSAdapted (G.sampledTime k)
  apply MemLp.of_le hξNorm
    ((hSampleAdapted n).mono
      ((G.sampledFiltration F).le n)).aestronglyMeasurable
  filter_upwards [hSBound] with omega hBound
  simpa only [ChronologicalGrid.natSample, Real.norm_eq_abs, abs_abs] using
    hBound (G.sampledTime n)

/-- The predictable Doob component is bounded by the number of elapsed grid
steps times the source-increment bound. -/
theorem ae_norm_doobPredictablePart_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) :
    ∀ᵐ omega ∂mu, ∀ n,
      ‖G.doobPredictablePart S F mu n omega‖ ≤
        (n : Real) * (2 * max source.bound 0) := by
  filter_upwards [G.ae_norm_predictablePart_increment_le source] with
      omega hIncrement
  intro n
  induction n with
  | zero =>
      simp [doobPredictablePart, predictablePart_zero]
  | succ n ih =>
      calc
        ‖G.doobPredictablePart S F mu (n + 1) omega‖ =
            ‖G.doobPredictablePart S F mu n omega +
              (G.doobPredictablePart S F mu (n + 1) omega -
                G.doobPredictablePart S F mu n omega)‖ := by
          congr 1
          ring
        _ ≤
            ‖G.doobPredictablePart S F mu n omega‖ +
              ‖G.doobPredictablePart S F mu (n + 1) omega -
                G.doobPredictablePart S F mu n omega‖ := by
          exact norm_add_le
            (G.doobPredictablePart S F mu n omega)
            (G.doobPredictablePart S F mu (n + 1) omega -
              G.doobPredictablePart S F mu n omega)
        _ ≤ (n : Real) * (2 * max source.bound 0) +
            2 * max source.bound 0 :=
          add_le_add ih (hIncrement n)
        _ = ((n + 1 : Nat) : Real) * (2 * max source.bound 0) := by
          push_cast
          ring

/-- The finite-grid Doob martingale component has a deterministic bound at
each grid index. -/
theorem ae_norm_doobMartingalePart_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (n : Nat) :
    ∀ᵐ omega ∂mu,
      ‖G.doobMartingalePart S F mu n omega‖ ≤
        max source.bound 0 + (n : Real) * (2 * max source.bound 0) := by
  filter_upwards [source.uniformBound,
    G.ae_norm_doobPredictablePart_le source] with omega hSource hPredictable
  unfold doobMartingalePart martingalePart
  rw [Pi.sub_apply, Real.norm_eq_abs]
  calc
    |G.natSample S n omega -
        G.doobPredictablePart S F mu n omega| ≤
        |G.natSample S n omega| +
          |G.doobPredictablePart S F mu n omega| := abs_sub _ _
    _ ≤ max source.bound 0 + (n : Real) * (2 * max source.bound 0) :=
      add_le_add
        ((hSource (G.sampledTime n)).trans (le_max_left _ _))
        (by simpa only [Real.norm_eq_abs] using hPredictable n)

/-- Every fixed-time value of the finite-grid Doob martingale belongs to
`L²`. -/
theorem memLp_two_doobMartingalePart
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (n : Nat) :
    MemLp (G.doobMartingalePart S F mu n) (2 : ENNReal) mu := by
  unfold doobMartingalePart
  have hMeasurable : StronglyMeasurable
      (martingalePart (G.natSample S) (G.sampledFiltration F) mu n) :=
    ((G.martingale_martingalePart_natSample_boundedSemimartingaleSource
      source).stronglyMeasurable n).mono ((G.sampledFiltration F).le n)
  refine MemLp.of_bound (p := (2 : ENNReal)) (μ := mu)
    hMeasurable.aestronglyMeasurable
    (max source.bound 0 + (n : Real) * (2 * max source.bound 0)) ?_
  exact G.ae_norm_doobMartingalePart_le source n

end ChronologicalGrid

end FTAPTheorem42
