/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.ProcessEnvelope
import Mathlib.Topology.Compactness.Compact

/-!
# Càdlàg maximal envelopes

A real càdlàg path is bounded on every compact time interval.  Consequently
the finite-horizon factorial-grid envelope is exactly the supremum of the
path on that interval.  Taking the countable supremum over integer horizons
then recovers the genuine all-time maximal function.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FactorialChronologicalGrid

omit [MeasurableSpace Ω] in
/-- A real path which is right-continuous and has left limits is bounded on
every compact interval `[0, T]`. -/
theorem exists_abs_le_on_Icc_of_rightContinuous_leftLimits
    (f : ℝ≥0 → ℝ)
    (hRight : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t)
      (𝓝 (Function.leftLim f t)))
    (T : ℝ≥0) :
    ∃ G : ℝ, ∀ t, t ≤ T → |f t| ≤ G := by
  have hLocallyBounded : ∀ x : ℝ≥0,
      ∃ U ∈ 𝓝 x, Bornology.IsBounded (f '' U) := by
    intro x
    obtain ⟨a, ha⟩ :=
      ((hLeft x).norm.isBoundedUnder_le).eventually_le
    obtain ⟨b, hb⟩ :=
      ((hRight x).norm.isBoundedUnder_le).eventually_le
    refine ⟨{y | ‖f y‖ ≤ max a b}, ?_, ?_⟩
    · rw [← nhdsLT_sup_nhdsGE x]
      change ∀ᶠ y in 𝓝[<] x ⊔ 𝓝[≥] x, ‖f y‖ ≤ max a b
      rw [Filter.eventually_sup]
      constructor
      · filter_upwards [ha] with y hy
        exact hy.trans (le_max_left _ _)
      · filter_upwards [hb] with y hy
        exact hy.trans (le_max_right _ _)
    · apply isBounded_iff_forall_norm_le.mpr
      refine ⟨max a b, ?_⟩
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hx
  have hBounded : Bornology.IsBounded (f '' Set.Icc 0 T) :=
    Bornology.isBounded_image_of_isLocallyBounded_of_isCompact
      isCompact_Icc hLocallyBounded
  obtain ⟨G, hG⟩ := hBounded.exists_norm_le
  refine ⟨G, fun t ht => ?_⟩
  simpa only [Real.norm_eq_abs] using
    hG (f t) ⟨t, ⟨bot_le, ht⟩, rfl⟩

omit [MeasurableSpace Ω] in
/-- On a càdlàg path, the factorial-grid envelope dominates every value on
the finite horizon without requiring an externally supplied path bound. -/
theorem abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
    {X : Process Ω} (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hLeft : ∀ ω t, Tendsto (X · ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (X · ω) t)))
    (T : ℝ≥0) :
    ∀ t, t ≤ T → |X t ω| ≤ finiteHorizonAbsoluteEnvelope X T ω := by
  obtain ⟨G, hG⟩ :=
    exists_abs_le_on_Icc_of_rightContinuous_leftLimits
      (X · ω) (hRight ω) (hLeft ω) T
  exact abs_le_finiteHorizonAbsoluteEnvelope_of_bound hRight T hG

omit [MeasurableSpace Ω] in
/-- The extended-real finite-horizon factorial envelope equals the genuine
supremum of the absolute value of a càdlàg path on `[0, T]`. -/
theorem ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup
    {X : Process Ω} (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hLeft : ∀ ω t, Tendsto (X · ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (X · ω) t)))
    (T : ℝ≥0) :
    ENNReal.ofReal (finiteHorizonAbsoluteEnvelope X T ω) =
      ⨆ t : Set.Iic T, ENNReal.ofReal |X t.1 ω| := by
  let Z : ℝ≥0∞ := ⨆ t : Set.Iic T, ENNReal.ofReal |X t.1 ω|
  obtain ⟨G, hG⟩ :=
    exists_abs_le_on_Icc_of_rightContinuous_leftLimits
      (X · ω) (hRight ω) (hLeft ω) T
  have hZLe : Z ≤ ENNReal.ofReal G := by
    apply iSup_le
    intro t
    exact ENNReal.ofReal_le_ofReal (hG t.1 t.2)
  have hZNeTop : Z ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZLe
  have hValueLeZ : ∀ t, t ≤ T → |X t ω| ≤ Z.toReal := by
    intro t ht
    have hOfReal : ENNReal.ofReal |X t ω| ≤ Z :=
      le_iSup (fun s : Set.Iic T => ENNReal.ofReal |X s.1 ω|) ⟨t, ht⟩
    have hToReal :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hZNeTop).2 hOfReal
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using hToReal
  apply le_antisymm
  · calc
      ENNReal.ofReal (finiteHorizonAbsoluteEnvelope X T ω) ≤
          ENNReal.ofReal Z.toReal :=
        ENNReal.ofReal_le_ofReal
          (finiteHorizonAbsoluteEnvelope_le_of_bound X T hValueLeZ)
      _ = Z := ENNReal.ofReal_toReal hZNeTop
  · apply iSup_le
    intro t
    exact ENNReal.ofReal_le_ofReal
      (abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
        hRight hLeft T t.1 t.2)

omit [MeasurableSpace Ω] in
/-- Finite-horizon càdlàg envelopes are monotone in the horizon. -/
theorem finiteHorizonAbsoluteEnvelope_mono
    {X : Process Ω} (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hLeft : ∀ ω t, Tendsto (X · ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (X · ω) t)))
    {T U : ℝ≥0} (hTU : T ≤ U) :
    finiteHorizonAbsoluteEnvelope X T ω ≤
      finiteHorizonAbsoluteEnvelope X U ω := by
  apply finiteHorizonAbsoluteEnvelope_le_of_bound
  intro t ht
  exact abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
    hRight hLeft U t (ht.trans hTU)

/-- The measurable extended-real envelope obtained from all positive integer
horizons. -/
noncomputable def allTimeAbsoluteEnvelope (X : Process Ω) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ n : ℕ, ENNReal.ofReal
    (finiteHorizonAbsoluteEnvelope X ((n + 1 : ℕ) : ℝ≥0) ω)

/-- The all-time factorial envelope is measurable. -/
theorem measurable_allTimeAbsoluteEnvelope
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X) :
    Measurable (allTimeAbsoluteEnvelope X) := by
  apply Measurable.iSup
  intro n
  exact ((stronglyMeasurable_finiteHorizonAbsoluteEnvelope hX
    ((n + 1 : ℕ) : ℝ≥0)).mono
      (ℱ.le ((n + 1 : ℕ) : ℝ≥0))).measurable.ennreal_ofReal

omit [MeasurableSpace Ω] in
/-- For a càdlàg path, the countable integer-horizon envelope is exactly the
genuine supremum over all nonnegative times. -/
theorem allTimeAbsoluteEnvelope_eq_iSup
    {X : Process Ω} (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hLeft : ∀ ω t, Tendsto (X · ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (X · ω) t))) :
    allTimeAbsoluteEnvelope X ω =
      ⨆ t : ℝ≥0, ENNReal.ofReal |X t ω| := by
  apply le_antisymm
  · apply iSup_le
    intro n
    rw [ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup hRight hLeft]
    apply iSup_le
    intro t
    exact le_iSup (fun s : ℝ≥0 => ENNReal.ofReal |X s ω|) t.1
  · apply iSup_le
    intro t
    let n := Nat.ceil t
    have ht : t ≤ ((n + 1 : ℕ) : ℝ≥0) := by
      apply (Nat.le_ceil t).trans
      dsimp [n]
      exact_mod_cast Nat.le_add_right (Nat.ceil t) 1
    calc
      ENNReal.ofReal |X t ω| ≤ ENNReal.ofReal
          (finiteHorizonAbsoluteEnvelope X ((n + 1 : ℕ) : ℝ≥0) ω) :=
        ENNReal.ofReal_le_ofReal
          (abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
            hRight hLeft _ t ht)
      _ ≤ allTimeAbsoluteEnvelope X ω :=
        le_iSup (fun k : ℕ => ENNReal.ofReal
          (finiteHorizonAbsoluteEnvelope X ((k + 1 : ℕ) : ℝ≥0) ω)) n

/-- The genuine extended-real all-time supremum of a strongly adapted
càdlàg process is measurable. -/
theorem measurable_iSup_ofReal_abs_of_cadlag
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hLeft : ∀ ω t, Tendsto (X · ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (X · ω) t))) :
    Measurable (fun ω =>
      ⨆ t : ℝ≥0, ENNReal.ofReal |X t ω|) := by
  have hEq : (fun ω =>
      ⨆ t : ℝ≥0, ENNReal.ofReal |X t ω|) =
        allTimeAbsoluteEnvelope X := by
    funext ω
    exact (allTimeAbsoluteEnvelope_eq_iSup hRight hLeft).symm
  rw [hEq]
  exact measurable_allTimeAbsoluteEnvelope hX

end FactorialChronologicalGrid

end FTAPTheorem42
