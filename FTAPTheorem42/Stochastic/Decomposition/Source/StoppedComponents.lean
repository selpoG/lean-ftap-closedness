/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobComponentStopping
import FTAPTheorem42.Stochastic.Decomposition.Source.ConvexDecomposition

/-!
# Variation-stopped factorial-grid Doob components

At a fixed variation level, the factorial-grid Doob components are stopped by
the predictable gate constructed on each grid. Their decomposition remains
exact, the martingale coordinates are uniformly in `L²`, and the predictable
paths have one deterministic total-variation bound. This is the bounded input
for the subsequent Hilbert convexification.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- The variation-stopped source component at the right factorial
approximation of `t`. -/
noncomputable def stoppedSourceApproximation
    (a : Real) (T t : NNReal) (ht : t ≤ T) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Omega → Real :=
  (grid T r).doobVariationStoppedSourcePart S F mu a
    (approxIndex T t ht r)

/-- The variation-stopped predictable component at the right factorial
approximation of `t`. -/
noncomputable def stoppedPredictableApproximation
    (a : Real) (T t : NNReal) (ht : t ≤ T) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Omega → Real :=
  (grid T r).doobVariationStoppedPredictablePart S F mu a
    (approxIndex T t ht r)

/-- The variation-stopped martingale component at the right factorial
approximation of `t`. -/
noncomputable def stoppedMartingaleApproximation
    (a : Real) (T t : NNReal) (ht : t ≤ T) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Omega → Real :=
  (grid T r).doobVariationStoppedMartingalePart S F mu a
    (approxIndex T t ht r)

/-- The stopped source approximation is exactly the sum of the two stopped
Doob components. -/
theorem stoppedSourceApproximation_eq_martingale_add_predictable
    (a : Real) (T t : NNReal) (ht : t ≤ T) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) :
    stoppedSourceApproximation a T t ht r S F mu =
      stoppedMartingaleApproximation a T t ht r S F mu +
        stoppedPredictableApproximation a T t ht r S F mu :=
  (grid T r).doobVariationStoppedSourcePart_eq_add S F mu a
    (approxIndex T t ht r)

/-- Every fixed-time stopped predictable coordinate belongs to `L²`, with
a bound independent of the factorial-grid level. -/
theorem memLp_two_stoppedPredictableApproximation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    MemLp (stoppedPredictableApproximation a T t ht r S F mu)
      (2 : ENNReal) mu :=
  (grid T r).memLp_two_doobVariationStoppedPredictablePart source ha
    (approxIndex T t ht r)

/-- Every fixed-time stopped martingale coordinate belongs to `L²`, with
a bound independent of the factorial-grid level. -/
theorem memLp_two_stoppedMartingaleApproximation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    MemLp (stoppedMartingaleApproximation a T t ht r S F mu)
      (2 : ENNReal) mu :=
  (grid T r).memLp_two_doobVariationStoppedMartingalePart source ha
    (approxIndex T t ht r)

/-- The canonical `L²` representative of one stopped predictable
coordinate. -/
noncomputable def stoppedPredictableApproximationToLp
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    Lp Real 2 mu :=
  (memLp_two_stoppedPredictableApproximation source ha T t ht r).toLp
    (stoppedPredictableApproximation a T t ht r S F mu)

/-- The canonical `L²` representative of one stopped martingale
coordinate. -/
noncomputable def stoppedMartingaleApproximationToLp
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    Lp Real 2 mu :=
  (memLp_two_stoppedMartingaleApproximation source ha T t ht r).toLp
    (stoppedMartingaleApproximation a T t ht r S F mu)

/-- The stopped predictable representatives have one norm bound, independent
of the factorial-grid level and the evaluation time. -/
theorem stoppedPredictableApproximationToLp_norm_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    ‖stoppedPredictableApproximationToLp source ha T t ht r‖ ≤
      a + 2 * max source.bound 0 := by
  rw [stoppedPredictableApproximationToLp, Lp.norm_toLp]
  have hBound : ∀ᵐ omega ∂mu,
      ‖stoppedPredictableApproximation a T t ht r S F mu omega‖ ≤
        a + 2 * max source.bound 0 := by
    filter_upwards [
        (grid T r).ae_abs_doobVariationStoppedPredictablePart_le source ha] with
        omega homega
    simpa only [stoppedPredictableApproximation, Real.norm_eq_abs] using
      homega (approxIndex T t ht r)
  have hC : 0 ≤ a + 2 * max source.bound 0 := by
    linarith [le_max_right source.bound 0]
  have hNorm := eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
    (memLp_two_stoppedPredictableApproximation source ha T t ht r).aestronglyMeasurable hBound
  calc
    (eLpNorm (stoppedPredictableApproximation a T t ht r S F mu)
        (2 : ENNReal) mu).toReal ≤
        (mu Set.univ ^ (ENNReal.toReal 2)⁻¹ *
          ENNReal.ofReal (a + 2 * max source.bound 0)).toReal :=
      ENNReal.toReal_mono (by simp) hNorm
    _ = a + 2 * max source.bound 0 := by
      simp [measure_univ, hC]

/-- The stopped martingale representatives have one norm bound, independent
of the factorial-grid level and the evaluation time. -/
theorem stoppedMartingaleApproximationToLp_norm_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    ‖stoppedMartingaleApproximationToLp source ha T t ht r‖ ≤
      a + 4 * max source.bound 0 := by
  rw [stoppedMartingaleApproximationToLp, Lp.norm_toLp]
  have hBound : ∀ᵐ omega ∂mu,
      ‖stoppedMartingaleApproximation a T t ht r S F mu omega‖ ≤
        a + 4 * max source.bound 0 := by
    filter_upwards [
        (grid T r).ae_abs_doobVariationStoppedMartingalePart_le source ha] with
        omega homega
    simpa only [stoppedMartingaleApproximation, Real.norm_eq_abs] using
      homega (approxIndex T t ht r)
  have hC : 0 ≤ a + 4 * max source.bound 0 := by
    linarith [le_max_right source.bound 0]
  have hNorm := eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
    (memLp_two_stoppedMartingaleApproximation source ha T t ht r).aestronglyMeasurable hBound
  calc
    (eLpNorm (stoppedMartingaleApproximation a T t ht r S F mu)
        (2 : ENNReal) mu).toReal ≤
        (mu Set.univ ^ (ENNReal.toReal 2)⁻¹ *
          ENNReal.ofReal (a + 4 * max source.bound 0)).toReal :=
      ENNReal.toReal_mono (by simp) hNorm
    _ = a + 4 * max source.bound 0 := by
      simp [measure_univ, hC]

/-- Stopped martingale approximations retain the finite-grid conditional
expectation identity. -/
theorem condExp_stoppedMartingaleApproximation_ae_eq
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    (a : Real) (T s t : NNReal) (hs : s ≤ T) (ht : t ≤ T)
    (hst : s ≤ t) (r : Nat) :
    mu[
      stoppedMartingaleApproximation a T t ht r S F mu |
        ((grid T r).sampledFiltration F) (approxIndex T s hs r)] =ᵐ[mu]
      stoppedMartingaleApproximation a T s hs r S F mu := by
  exact ((grid T r).martingale_doobVariationStoppedMartingalePart source a
    |>.condExp_ae_eq (approxIndex_mono T s t hs ht hst r))

/-- The stopped predictable factorial path. -/
noncomputable def stoppedPredictablePath
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Set.Iic T → Omega → Real :=
  fun t => stoppedPredictableApproximation a T t.1 t.2 r S F mu

/-- At a fixed stopping level, every factorial-grid predictable path has
the same a.e. deterministic variation bound. -/
theorem ae_eVariationOn_stoppedPredictablePath_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    ∀ᵐ omega ∂mu,
      eVariationOn
          (fun t => stoppedPredictablePath a T r S F mu t omega) Set.univ ≤
        ENNReal.ofReal (a + 2 * max source.bound 0) := by
  filter_upwards [
      (grid T r).ae_sum_abs_doobVariationStoppedPredictablePart_increment_le
        source ha] with omega hVariation
  let A : Nat → Real := fun n =>
    (grid T r).doobVariationStoppedPredictablePart S F mu a n omega
  let phi : Set.Iic T → Nat := fun t => (approxIndex T t.1 t.2 r).1
  have hPhi : Monotone phi := monotone_approxIndex_val T r
  have hMaps : MapsTo phi Set.univ (Set.Iic (size T r)) := by
    intro t _ht
    exact approxIndex_val_le_size T r t
  calc
    eVariationOn
        (fun t => stoppedPredictablePath a T r S F mu t omega) Set.univ =
        eVariationOn (A ∘ phi) Set.univ := by rfl
    _ ≤ eVariationOn A (Set.Iic (size T r)) :=
      eVariationOn.comp_le_of_monotoneOn A phi
        (hPhi.monotoneOn Set.univ) hMaps
    _ = ∑ k ∈ Finset.range (size T r), edist (A k) (A (k + 1)) := by
      simpa using
        (eVariationOn.image_range_of_monotone A monotone_id (size T r))
    _ = ENNReal.ofReal
        (∑ k ∈ Finset.range (size T r), |A (k + 1) - A k|) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [edist_dist, Real.dist_eq, abs_sub_comm]
    _ ≤ ENNReal.ofReal (a + 2 * max source.bound 0) :=
      ENNReal.ofReal_le_ofReal (hVariation (size T r))

end HorizonFactorialGrid

end FTAPTheorem42
