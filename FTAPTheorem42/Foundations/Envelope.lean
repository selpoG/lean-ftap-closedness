/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.FactorialChronologicalGrid

/-! # Envelope shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace ChronologicalGrid

variable {Time : Type*} [LinearOrder Time]
variable {N : ℕ} (G : ChronologicalGrid Time N)

/-- Clamp a natural index to the last point of a finite grid. -/
def natIndex (_G : ChronologicalGrid Time N) (k : ℕ) : Fin (N + 1) :=
  ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩

theorem natIndex_mono : Monotone G.natIndex := by
  intro i j hij
  exact min_le_min hij le_rfl

@[simp]
theorem natIndex_last : G.natIndex N = ⟨N, Nat.lt_succ_self N⟩ := by
  ext
  simp [natIndex]

/-- Time selected by the constantly extended grid. -/
def sampledTime (k : ℕ) : Time := G.time (G.natIndex k)

@[simp]
theorem sampledTime_fin_eq (k : Fin (N + 1)) :
    G.sampledTime k = G.time k := by
  unfold sampledTime natIndex
  congr 1
  ext
  exact min_eq_left (Nat.le_of_lt_succ k.isLt)

theorem sampledTime_mono : Monotone G.sampledTime :=
  fun _ _ hij => G.monotone_time (G.natIndex_mono hij)

/-- Reindex a filtration along a finite chronological grid. -/
def sampledFiltration
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq k := ℱ (G.sampledTime k)
  mono' := fun _ _ hij => ℱ.mono (G.sampledTime_mono hij)
  le' := fun k => ℱ.le (G.sampledTime k)

@[simp]
theorem sampledFiltration_apply
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)) (k : ℕ) :
    G.sampledFiltration ℱ k = ℱ (G.sampledTime k) :=
  rfl

/-- Sample a process on the constantly extended grid. -/
def natSample (f : Time → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun k => f (G.sampledTime k)

omit [MeasurableSpace Ω] in
theorem natSample_nonneg {f : Time → Ω → ℝ} (hf : 0 ≤ f) :
    0 ≤ G.natSample f := by
  intro k ω
  exact hf (G.sampledTime k) ω

end ChronologicalGrid

/-- The running maximum of a real process over `0, ..., n`. -/
noncomputable def finiteRunningMax (f : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => f k ω

theorem measurable_finiteRunningMax
    (f : ℕ → Ω → ℝ) (n : ℕ)
    (hf : ∀ k, k ≤ n → Measurable (f k)) :
    Measurable (finiteRunningMax f n) := by
  exact Finset.measurable_range_sup'' fun k hk =>
    hf k hk

omit [MeasurableSpace Ω] in
theorem finiteRunningMax_nonneg
    (f : ℕ → Ω → ℝ) (n : ℕ) (hf : 0 ≤ f) :
    0 ≤ finiteRunningMax f n := by
  intro ω
  exact (hf 0 ω).trans
    (Finset.le_sup' (fun k => f k ω)
      (Finset.mem_range.2 (Nat.zero_lt_succ n)))

namespace FactorialChronologicalGrid

/-- Factorial grid clamped at a deterministic terminal time. -/
noncomputable def stoppedGrid (T : ℝ≥0) (r : ℕ) :
    ChronologicalGrid ℝ≥0 (r * r.factorial) where
  time k := min ((grid r).time k) T
  monotone_time := fun _ _ hkl =>
    min_le_min ((grid r).monotone_time hkl) le_rfl

@[simp]
theorem stoppedGrid_time (T : ℝ≥0) (r : ℕ)
    (k : Fin (r * r.factorial + 1)) :
    (stoppedGrid T r).time k = min ((grid r).time k) T :=
  rfl

/-- Running maximum on the level-`r` factorial grid clamped at `T`. -/
noncomputable def factorialRunningMax
    (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (r : ℕ) : Ω → ℝ :=
  finiteRunningMax ((stoppedGrid T r).natSample f) (r * r.factorial)

/-- Extended nonnegative envelope of all stopped factorial-grid maxima. -/
noncomputable def eFactorialRunningMaxEnvelope
    (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ r, ENNReal.ofReal (factorialRunningMax f T r ω)

/-- The extended factorial-grid absolute envelope, capped at one and then
viewed as a real random variable.  Unlike the uncapped real square-root
envelope, it records an infinite extended envelope by the value one. -/
noncomputable def cappedFiniteHorizonAbsoluteEnvelope
    (X : Process Ω) (T : ℝ≥0) : Ω → ℝ :=
  fun ω => (min
    (eFactorialRunningMaxEnvelope (fun t ω => |X t ω|) T ω) 1).toReal

theorem stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X) (T : ℝ≥0) :
    StronglyMeasurable[ℱ T]
      (cappedFiniteHorizonAbsoluteEnvelope X T) := by
  let : MeasurableSpace Ω := ℱ T
  have hEnvelope : Measurable
      (eFactorialRunningMaxEnvelope (fun t ω => |X t ω|) T) := by
    apply Measurable.iSup
    intro r
    apply Measurable.ennreal_ofReal
    unfold factorialRunningMax
    apply measurable_finiteRunningMax
    intro k _
    have htime : (stoppedGrid T r).sampledTime k ≤ T := by
      simp only [ChronologicalGrid.sampledTime, stoppedGrid_time]
      exact min_le_right _ _
    exact (((hX ((stoppedGrid T r).sampledTime k)).mono
      (ℱ.mono htime)).norm).measurable
  exact (hEnvelope.min measurable_const).ennreal_toReal.stronglyMeasurable

omit [MeasurableSpace Ω] in
theorem cappedFiniteHorizonAbsoluteEnvelope_nonneg
    (X : Process Ω) (T : ℝ≥0) (ω : Ω) :
    0 ≤ cappedFiniteHorizonAbsoluteEnvelope X T ω :=
  ENNReal.toReal_nonneg

omit [MeasurableSpace Ω] in
theorem cappedFiniteHorizonAbsoluteEnvelope_le_one
    (X : Process Ω) (T : ℝ≥0) (ω : Ω) :
    cappedFiniteHorizonAbsoluteEnvelope X T ω ≤ 1 := by
  unfold cappedFiniteHorizonAbsoluteEnvelope
  have hMinNeTop : min
      (eFactorialRunningMaxEnvelope (fun t ω => |X t ω|) T ω) 1 ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_right _ _)
  have h := ENNReal.toReal_mono (by finiteness : (1 : ℝ≥0∞) ≠ ∞)
    (min_le_right
      (eFactorialRunningMaxEnvelope (fun t ω => |X t ω|) T ω) 1)
  simpa only [ENNReal.toReal_one] using h

end FactorialChronologicalGrid

end FTAPTheorem42
