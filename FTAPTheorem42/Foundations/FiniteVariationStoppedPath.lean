/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.FiniteVariationPathMeasure

/-!
# Deterministically stopped finite-variation paths

Stopping a path at a deterministic nonnegative time preserves right
continuity and bounded variation.  Its variation up to any horizon is exactly
the original variation up to the clamped horizon.  These pathwise facts are
the deterministic core of the variation localization used in Lemma 4.7.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

namespace FiniteVariationStoppedPath

/-- A path stopped at the deterministic time `τ`. -/
def stopAt {E : Type*} (f : ℝ≥0 → E) (τ : ℝ≥0) : ℝ≥0 → E :=
  fun t => f (min t τ)

theorem monotone_clamp (τ : ℝ≥0) : Monotone fun t : ℝ≥0 => min t τ :=
  fun _ _ h => min_le_min_right τ h

theorem range_clamp (τ : ℝ≥0) :
    (fun t : ℝ≥0 => min t τ) '' Set.univ = Set.Iic τ := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    exact min_le_right t τ
  · intro hx
    exact ⟨x, Set.mem_univ x, min_eq_left hx⟩

/-- Right continuity is preserved by deterministic stopping. -/
theorem rightContinuous_stopAt
    {E : Type*} [TopologicalSpace E]
    (f : ℝ≥0 → E)
    (hRight : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (τ t : ℝ≥0) :
    ContinuousWithinAt (stopAt f τ) (Set.Ici t) t := by
  let φ : ℝ≥0 → ℝ≥0 := fun u => min u τ
  have hφ : ContinuousWithinAt φ (Set.Ici t) t :=
    (continuous_id.min continuous_const).continuousWithinAt
  have hMaps : MapsTo φ (Set.Ici t) (Set.Ici (φ t)) := by
    intro u hu
    exact min_le_min_right τ hu
  exact (hRight (φ t)).comp hφ hMaps

/-- Deterministic stopping preserves bounded variation. -/
theorem boundedVariationOn_stopAt
    {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ≥0 → E} (hf : BoundedVariationOn f Set.univ) (τ : ℝ≥0) :
    BoundedVariationOn (stopAt f τ) Set.univ := by
  change eVariationOn (f ∘ fun t : ℝ≥0 => min t τ) Set.univ ≠ ∞
  exact ne_top_of_le_ne_top hf
    (eVariationOn.comp_le_of_monotoneOn f (fun t : ℝ≥0 => min t τ)
      ((monotone_clamp τ).monotoneOn Set.univ) (mapsTo_univ _ _))

/-- Deterministic stopping turns locally bounded variation on `ℝ≥0` into
bounded variation on the whole time axis. -/
theorem boundedVariationOn_stopAt_of_locallyBoundedVariationOn
    {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ≥0 → E} (hf : LocallyBoundedVariationOn f Set.univ) (τ : ℝ≥0) :
    BoundedVariationOn (stopAt f τ) Set.univ := by
  have hfIic : BoundedVariationOn f (Set.Iic τ) := by
    have hLocal := hf 0 τ (Set.mem_univ 0) (Set.mem_univ τ)
    apply hLocal.mono
    intro x hx
    exact ⟨Set.mem_univ x, bot_le, hx⟩
  change eVariationOn (f ∘ fun t : ℝ≥0 => min t τ) Set.univ ≠ ∞
  exact ne_top_of_le_ne_top hfIic
    (eVariationOn.comp_le_of_monotoneOn f (fun t : ℝ≥0 => min t τ)
      ((monotone_clamp τ).monotoneOn Set.univ)
      (fun x _ => show min x τ ≤ τ from min_le_right x τ))

/-- Variation of a stopped path up to `t` equals the original variation up
to `min t τ`. -/
theorem variationOnFromTo_stopAt
    {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ≥0 → E) (τ t : ℝ≥0) :
    variationOnFromTo (stopAt f τ) Set.univ 0 t =
      variationOnFromTo f Set.univ 0 (min t τ) := by
  change variationOnFromTo
      (f ∘ fun u : ℝ≥0 => min u τ) Set.univ 0 t = _
  rw [variationOnFromTo.comp_eq_of_monotoneOn f
    (fun u : ℝ≥0 => min u τ) ((monotone_clamp τ).monotoneOn Set.univ)
    (Set.mem_univ 0) (Set.mem_univ t), range_clamp]
  rw [min_eq_left (show (0 : ℝ≥0) ≤ τ from bot_le)]
  unfold variationOnFromTo
  rw [ite_eq_left (show (0 : ℝ≥0) ≤ min t τ from bot_le),
    ite_eq_left (show (0 : ℝ≥0) ≤ min t τ from bot_le)]
  apply congrArg ENNReal.toReal
  apply congrArg (eVariationOn f)
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_univ,
    true_and]
  constructor
  · rintro ⟨-, hx0, hxmin⟩
    exact ⟨hx0, hxmin⟩
  · rintro ⟨hx0, hxmin⟩
    exact ⟨hxmin.trans (min_le_right t τ), hx0, hxmin⟩

/-- A right-continuous Stieltjes path has no total-variation atom at zero. -/
theorem totalVariation_singleton_zero
    (A : ℝ≥0 → ℝ) (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t) :
    (FiniteVariationPath.signedMeasure hA).totalVariation
      ({0} : Set ℝ≥0) = 0 := by
  rw [signedMeasure_totalVariation_eq_variation,
    FiniteVariationPath.signedMeasure_eq_vectorMeasure]
  apply (VectorMeasure.variation_apply_eq_zero (MeasurableSet.singleton 0)).2
  intro s hs _
  rcases s.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · simp
  · have ht0 : t = 0 := hs ht
    have h0s : (0 : ℝ≥0) ∈ s := ht0 ▸ ht
    have hseq : s = ({0} : Set ℝ≥0) := by
      apply Set.Subset.antisymm hs
      intro x hx
      have hx0 : x = 0 := by simpa using hx
      simpa [hx0] using h0s
    rw [hseq, hA.vectorMeasure_singleton]
    rw [(hRight 0).rightLim_eq]
    have hleft : Function.leftLim A (0 : ℝ≥0) = A 0 :=
      leftLim_eq_of_isBot isBot_bot
    rw [hleft, sub_self]

/-- The total variation of a deterministically stopped path on all of
`ℝ≥0` is exactly the original cumulative variation at the stopping time. -/
theorem totalVariation_univ_stopAt
    (A : ℝ≥0 → ℝ) (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (τ : ℝ≥0) :
    (FiniteVariationPath.signedMeasure
      (boundedVariationOn_stopAt hA τ)).totalVariation Set.univ =
        ENNReal.ofReal (variationOnFromTo A Set.univ 0 τ) := by
  let Aτ := stopAt A τ
  let hAτ := boundedVariationOn_stopAt hA τ
  let ν := (FiniteVariationPath.signedMeasure hAτ).totalVariation
  let : IsFiniteMeasure ν := by
    constructor
    change (FiniteVariationPath.signedMeasure hAτ).totalVariation Set.univ < ∞
    rw [SignedMeasure.totalVariation, Measure.add_apply, ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩
  have hAτRight : ∀ t, ContinuousWithinAt Aτ (Set.Ici t) t :=
    rightContinuous_stopAt A hRight τ
  have hmono : Monotone (fun n : ℕ => Ioc (0 : ℝ≥0) (n : ℝ≥0)) := by
    intro m n hmn
    exact Ioc_subset_Ioc_right (by exact_mod_cast hmn)
  have hunion : (⋃ n : ℕ, Ioc (0 : ℝ≥0) (n : ℝ≥0)) = Ioi 0 := by
    rw [iUnion_Ioc_eq_Ioi_self_iff]
    intro x hx
    exact ⟨⌈(x : ℝ)⌉₊, by exact_mod_cast Nat.le_ceil x⟩
  have hlim : Tendsto (fun n : ℕ => ν (Ioc 0 (n : ℝ≥0))) atTop
      (𝓝 (ν (Ioi 0))) := by
    simpa [Function.comp_def, hunion] using
      (tendsto_measure_iUnion_atTop (μ := ν) hmono)
  have heventually : ∀ᶠ n : ℕ in atTop,
      ν (Ioc 0 (n : ℝ≥0)) =
        ENNReal.ofReal (variationOnFromTo A Set.univ 0 τ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil τ)] with n hn
    have hτn : τ ≤ (n : ℝ≥0) :=
      (Nat.le_ceil τ).trans (by exact_mod_cast hn)
    rw [← ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top ν _) ENNReal.ofReal_ne_top]
    have hOfReal :
        (ENNReal.ofReal (variationOnFromTo A Set.univ 0 τ)).toReal =
          variationOnFromTo A Set.univ 0 τ :=
      ENNReal.toReal_ofReal
        (variationOnFromTo.nonneg_of_le A Set.univ bot_le)
    rw [hOfReal]
    change (FiniteVariationPath.signedMeasure hAτ).totalVariation.real
      (Ioc 0 (n : ℝ≥0)) = _
    calc
      (FiniteVariationPath.signedMeasure hAτ).totalVariation.real
          (Ioc 0 (n : ℝ≥0)) =
          variationOnFromTo Aτ Set.univ 0 n :=
        (FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
          hAτ hAτRight bot_le).symm
      _ = variationOnFromTo A Set.univ 0 τ :=
        (variationOnFromTo_stopAt A τ n).trans (by rw [min_eq_right hτn])
  have hlimConst : Tendsto (fun n : ℕ => ν (Ioc 0 (n : ℝ≥0))) atTop
      (𝓝 (ENNReal.ofReal (variationOnFromTo A Set.univ 0 τ))) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [heventually] with n hn
      exact hn.symm)
  have hIoi : ν (Ioi 0) =
      ENNReal.ofReal (variationOnFromTo A Set.univ 0 τ) :=
    tendsto_nhds_unique hlim hlimConst
  have hdisjoint : Disjoint ({0} : Set ℝ≥0) (Ioi 0) := by
    exact Set.disjoint_left.2 fun x hx0 hxpos => by
      have hx : x = 0 := by simpa using hx0
      subst x
      simp at hxpos
  have huniv : ({0} : Set ℝ≥0) ∪ Ioi 0 = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, mem_Ioi, mem_univ,
      iff_true]
    rcases (bot_le : (0 : ℝ≥0) ≤ x).eq_or_lt with hx | hx
    · exact Or.inl hx.symm
    · exact Or.inr hx
  calc
    ν Set.univ = ν (({0} : Set ℝ≥0) ∪ Ioi 0) := congrArg ν huniv.symm
    _ = ν ({0} : Set ℝ≥0) + ν (Ioi 0) :=
      measure_union hdisjoint measurableSet_Ioi
    _ = 0 + ν (Ioi 0) := by
      rw [totalVariation_singleton_zero Aτ hAτ hAτRight]
    _ = ENNReal.ofReal (variationOnFromTo A Set.univ 0 τ) := by
      rw [zero_add, hIoi]

/-- The signed Stieltjes mass of a deterministically stopped path on the
whole nonnegative time axis is its endpoint increment. -/
theorem signedMeasure_univ_stopAt
    (A : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hAT : BoundedVariationOn (stopAt A T) Set.univ) :
    FiniteVariationPath.signedMeasure hAT Set.univ = A T - A 0 := by
  let AT := stopAt A T
  have hTop : Tendsto AT atTop (𝓝 (A T)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop T] with t ht
    simp only [AT, stopAt, min_eq_right ht]
  have hBot : limUnder atBot AT = A 0 := by
    rw [atBot_eq_pure_of_isBot isBot_bot]
    rw [(tendsto_pure_nhds AT (⊥ : ℝ≥0)).limUnder_eq]
    rw [bot_eq_zero]
    change A (min 0 T) = A 0
    have h0T : (0 : ℝ≥0) ≤ T := by positivity
    rw [min_eq_left h0T]
  rw [FiniteVariationPath.signedMeasure_univ hAT, hTop.limUnder_eq, hBot]

end FiniteVariationStoppedPath

end FTAPTheorem42
