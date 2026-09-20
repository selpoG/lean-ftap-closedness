/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationFactorialApproximation
import FTAPTheorem42.Stochastic.Stopping.CadlagPassageLocalizer
import FTAPTheorem42.Stochastic.Decomposition.Source.RegularizedSpecialSemimartingale

/-! # Cumulative variation passages with an integrable endpoint overshoot -/

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

theorem localVariation_stronglyAdapted
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {Q : Process Ω}
    (hQ : StronglyAdapted F Q)
    (hRight : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t) :
    StronglyAdapted F (localVariation Q) := by
  intro t
  apply Measurable.stronglyMeasurable
  apply @FiniteVariationFactorialApproximation.measurable_variationOnFromTo_of_le
    Ω Real (F t) inferInstance inferInstance inferInstance inferInstance Q t
  · exact fun s hs => (hQ.stronglyMeasurable_le hs).measurable
  · exact hRight

omit [MeasurableSpace Ω] in
theorem localVariation_rightContinuous {Q : Process Ω}
    (hQ : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ)
    (hRight : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t) :
    ∀ omega t, ContinuousWithinAt (localVariation Q · omega) (Ici t) t := by
  intro omega t
  apply continuousWithinAt_Ioi_iff_Ici.mp
  have h := variationOnFromTo.tendsto_right (a := (0 : NNReal)) (b := t)
    (mem_univ _) (mem_univ _) (hQ omega)
    (by simpa only [univ_inter, ContinuousWithinAt] using
      (hRight omega t).mono Ioi_subset_Ici_self)
  simpa only [univ_inter, dist_self, add_zero, localVariation, ContinuousWithinAt] using h

omit [MeasurableSpace Ω] in
theorem localVariation_leftLimits {Q : Process Ω}
    (hQ : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ) :
    ProcessHasLeftLimits (localVariation Q) := by
  apply
    SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
  intro omega
  have hMono : Monotone (localVariation Q · omega) := fun s t hst =>
    variationOnFromTo.monotoneOn (hQ omega) (mem_univ _) (mem_univ _) (mem_univ _) hst
  exact (hMono.monotoneOn univ).locallyBoundedVariationOn

omit [MeasurableSpace Ω] in
theorem abs_le_localVariation {Q : Process Ω}
    (hQ : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ) (hZero : Q 0 = 0)
    (omega : Ω) (t : NNReal) : |Q t omega| ≤ localVariation Q t omega := by
  have h := variationOnFromTo.abs_sub_le_sub_of_le (hQ omega)
    (a := (0 : NNReal)) (b := 0) (c := t) (mem_univ _) (mem_univ _) (mem_univ _) bot_le
  simpa only [hZero, Pi.zero_apply, sub_zero, variationOnFromTo.self, localVariation] using h

omit [MeasurableSpace Ω] in
/-- Only the pre-stop path is bounded. The terminal value is allowed to
overshoot and enters linearly in the closed variation estimate. -/
theorem localVariation_le_two_mul_add_abs_of_le_passage {Q : Process Ω}
    (hQ : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ)
    (hLeft : ProcessHasLeftLimits Q) (hZero : Q 0 = 0)
    {a : Real} (ha : 0 ≤ a) (omega : Ω) (r : NNReal)
    (hr : (r : WithTop NNReal) ≤ absoluteStrictHittingAfter (localVariation Q) a omega) :
    localVariation Q r omega ≤ 2 * a + |Q r omega| := by
  by_cases hr0 : r = 0
  · subst r
    simp only [localVariation, variationOnFromTo.self]
    positivity
  have hPre : ∀ s < r, localVariation Q s omega ≤ a := by
    intro s hs
    exact (le_abs_self _).trans (abs_le_of_lt_absoluteStrictHittingAfter
      (localVariation Q) a omega s ((WithTop.coe_lt_coe.mpr hs).trans_le hr))
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr hr0⟩
  have hVarLim := variationOnFromTo.tendsto_left (a := (0 : NNReal)) (b := r)
    (mem_univ _) (mem_univ _) (hQ omega)
    (by simpa only [univ_inter] using hLeft omega r)
  have hBefore : localVariation Q r omega -
      |Q r omega - Function.leftLim (Q · omega) r| ≤ a := by
    apply le_of_tendsto (by simpa only [univ_inter, Real.dist_eq, localVariation] using hVarLim)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hPre s hs
  have hLeftBound : |Function.leftLim (Q · omega) r| ≤ a := by
    apply le_of_tendsto (hLeft omega r).abs
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (abs_le_localVariation hQ hZero omega s).trans (hPre s hs)
  linarith [abs_sub (Q r omega) (Function.leftLim (Q · omega) r)]

end FTAPTheorem42
