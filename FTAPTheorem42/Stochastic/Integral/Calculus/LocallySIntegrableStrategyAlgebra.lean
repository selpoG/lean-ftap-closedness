/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.RightContinuousLocalizer
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy

/-!
# Linear algebra for locally finite-variation strategy records

This module constructs componentwise addition and deterministic scalar
multiplication for `LocallySIntegrableStrategy`.  These are raw data-level
operations; closure of a concrete stochastic-integral carrier is proved
separately.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Multiplication of a real-valued path by a constant preserves bounded
variation on an arbitrary linearly ordered set. -/
theorem boundedVariationOn_const_mul
    {Time : Type*} [LinearOrder Time]
    (c : Real) {f : Time -> Real} {s : Set Time}
    (hf : BoundedVariationOn f s) :
    BoundedVariationOn (fun t => c * f t) s := by
  change eVariationOn f s ≠ ∞ at hf
  change eVariationOn (fun t => c * f t) s ≠ ∞
  have hScaled :
      (‖c‖₊ : ENNReal) * eVariationOn f s ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hf
  refine ne_top_of_le_ne_top hScaled ?_
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, us⟩
  calc
    (∑ i ∈ Finset.range n,
        edist (c * f (u (i + 1))) (c * f (u i))) =
        ∑ i ∈ Finset.range n,
          (‖c‖₊ : ENNReal) * edist (f (u (i + 1))) (f (u i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← smul_eq_mul, ← smul_eq_mul, edist_smul₀]
      simp only [ENNReal.smul_def, smul_eq_mul]
    _ = (‖c‖₊ : ENNReal) *
        ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
      rw [Finset.mul_sum]
    _ ≤ (‖c‖₊ : ENNReal) * eVariationOn f s := by
      simpa [mul_comm] using
        (mul_le_mul_left
          (eVariationOn.sum_le (f := f) (s := s) hu us)
          (‖c‖₊ : ENNReal))

namespace LocallySIntegrableStrategy

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsFiniteMeasure mu] [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}

/-- Componentwise addition of local strategy records. -/
noncomputable def add
    (H K : LocallySIntegrableStrategy D) :
    LocallySIntegrableStrategy D where
  integrand := fun t omega => H.integrand t omega + K.integrand t omega
  stochasticIntegral := fun t omega =>
    H.stochasticIntegral t omega + K.stochasticIntegral t omega
  martingalePart := fun t omega =>
    H.martingalePart t omega + K.martingalePart t omega
  finiteVariationPart := fun t omega =>
    H.finiteVariationPart t omega + K.finiteVariationPart t omega
  integrand_isPredictable :=
    H.integrand_isPredictable.add K.integrand_isPredictable
  stochasticIntegral_isStronglyAdapted := fun t =>
    (H.stochasticIntegral_isStronglyAdapted t).add
      (K.stochasticIntegral_isStronglyAdapted t)
  stochasticIntegral_isRightContinuous := fun omega t =>
    (H.stochasticIntegral_isRightContinuous omega t).add
      (K.stochasticIntegral_isRightContinuous omega t)
  martingalePart_isLocalMartingale :=
    LocalMartingale.add_of_rightContinuous
      H.martingalePart_isLocalMartingale K.martingalePart_isLocalMartingale
      H.martingalePart_isRightContinuous K.martingalePart_isRightContinuous
  martingalePart_isStronglyAdapted := fun t =>
    (H.martingalePart_isStronglyAdapted t).add
      (K.martingalePart_isStronglyAdapted t)
  martingalePart_isRightContinuous := fun omega t =>
    (H.martingalePart_isRightContinuous omega t).add
      (K.martingalePart_isRightContinuous omega t)
  finiteVariationPart_isPredictable :=
    H.finiteVariationPart_isPredictable.add K.finiteVariationPart_isPredictable
  finiteVariationPart_isRightContinuous := fun omega t =>
    (H.finiteVariationPart_isRightContinuous omega t).add
      (K.finiteVariationPart_isRightContinuous omega t)
  finiteVariationPart_isLocallyBoundedVariation := fun omega a b ha hb =>
    boundedVariationOn_add
      (H.finiteVariationPart_isLocallyBoundedVariation omega a b ha hb)
      (K.finiteVariationPart_isLocallyBoundedVariation omega a b ha hb)
  integral_decomposition := by
    filter_upwards [H.integral_decomposition, K.integral_decomposition]
      with omega hH hK
    intro t
    rw [hH t, hK t]
    ring
  source_decomposition := H.source_decomposition

/-- Deterministic scalar multiplication of a local strategy record. -/
noncomputable def smul
    (c : Real) (H : LocallySIntegrableStrategy D) :
    LocallySIntegrableStrategy D where
  integrand := c • H.integrand
  stochasticIntegral := c • H.stochasticIntegral
  martingalePart := c • H.martingalePart
  finiteVariationPart := c • H.finiteVariationPart
  integrand_isPredictable := H.integrand_isPredictable.const_smul c
  stochasticIntegral_isStronglyAdapted := fun t =>
    (H.stochasticIntegral_isStronglyAdapted t).const_smul c
  stochasticIntegral_isRightContinuous := fun omega t => by
    change ContinuousWithinAt
      (fun u => c * H.stochasticIntegral u omega) (Set.Ici t) t
    exact (continuousWithinAt_const :
      ContinuousWithinAt (fun _ : NNReal => c) (Set.Ici t) t).mul
        (H.stochasticIntegral_isRightContinuous omega t)
  martingalePart_isLocalMartingale :=
    LocalMartingale.smul c H.martingalePart_isLocalMartingale
  martingalePart_isStronglyAdapted := fun t =>
    (H.martingalePart_isStronglyAdapted t).const_smul c
  martingalePart_isRightContinuous := fun omega t => by
    change ContinuousWithinAt
      (fun u => c * H.martingalePart u omega) (Set.Ici t) t
    exact (continuousWithinAt_const :
      ContinuousWithinAt (fun _ : NNReal => c) (Set.Ici t) t).mul
        (H.martingalePart_isRightContinuous omega t)
  finiteVariationPart_isPredictable :=
    H.finiteVariationPart_isPredictable.const_smul c
  finiteVariationPart_isRightContinuous := fun omega t => by
    change ContinuousWithinAt
      (fun u => c * H.finiteVariationPart u omega) (Set.Ici t) t
    exact (continuousWithinAt_const :
      ContinuousWithinAt (fun _ : NNReal => c) (Set.Ici t) t).mul
        (H.finiteVariationPart_isRightContinuous omega t)
  finiteVariationPart_isLocallyBoundedVariation := fun omega a b ha hb => by
    change BoundedVariationOn
      (fun t => c * H.finiteVariationPart t omega) (Set.univ ∩ Set.Icc a b)
    exact boundedVariationOn_const_mul c
      (H.finiteVariationPart_isLocallyBoundedVariation omega a b ha hb)
  integral_decomposition := by
    filter_upwards [H.integral_decomposition] with omega hOmega
    intro t
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hOmega t]
    ring
  source_decomposition := H.source_decomposition

end LocallySIntegrableStrategy

end FTAPTheorem42
