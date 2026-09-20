/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.CadlagEnvelope
import FTAPTheorem42.Trading.Basic

/-! # From finite-horizon to all-time maximal bounds

Increasing finite horizons identify the all-time maximal event. The module
also records preservation of left limits under deterministic stopping.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableMartingaleRestrictionL2Calculus

variable {μ : Measure Ω}

/-- Uniform control of all finite-horizon factorial envelopes implies the
uniform tail estimate for the genuine all-time maximal functions of the
càdlàg martingale parts. -/
theorem processClass_allTimeMaximal_boundedInProbability_of_finiteHorizon
    (𝓧 : Set (Process Ω))
    (hRight : ∀ X ∈ 𝓧, ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hMartingaleLeft : ∀ H ∈ 𝓧,
      ProcessHasLeftLimits H)
    (hFinite : ClaimSetBoundedInProbability μ
      {f | ∃ X ∈ 𝓧, ∃ T : ℝ≥0, 0 < T ∧
        f = FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T}) :
    ∀ ε : ℝ, 0 < ε →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ H ∈ 𝓧,
        μ {ω | ENNReal.ofReal R <
          ⨆ t : ℝ≥0, ENNReal.ofReal |H t ω|} ≤
            ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨R, hR, hTail⟩ := hFinite ε hε
  refine ⟨R, hR, ?_⟩
  intro H hH
  let A : ℕ → Set Ω := fun n => {ω | R <
    FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      H ((n + 1 : ℕ) : ℝ≥0) ω}
  have hAMono : Monotone A := by
    intro n m hnm ω hω
    exact hω.trans_le
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_mono
        (hRight H hH) (hMartingaleLeft H hH)
        (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hATail : ∀ n, μ (A n) ≤ ENNReal.ofReal ε := by
    intro n
    have hClassMember :
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          H ((n + 1 : ℕ) : ℝ≥0) ∈
            {f | ∃ X ∈ 𝓧, ∃ T : ℝ≥0, 0 < T ∧
              f = FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T} :=
      ⟨H, hH, ((n + 1 : ℕ) : ℝ≥0), by positivity, rfl⟩
    have h := hTail _ hClassMember
    have hAbsEvent :
        {ω | R < |FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          H ((n + 1 : ℕ) : ℝ≥0) ω|} = A n := by
      ext ω
      change (R < |FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        H ((n + 1 : ℕ) : ℝ≥0) ω|) ↔
          R < FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            H ((n + 1 : ℕ) : ℝ≥0) ω
      have hNonnegative : 0 ≤
          FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            H ((n + 1 : ℕ) : ℝ≥0) ω := by
        unfold FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        positivity
      rw [abs_of_nonneg hNonnegative]
    rwa [hAbsEvent] at h
  have hUnion :
      {ω | ENNReal.ofReal R <
        FactorialChronologicalGrid.allTimeAbsoluteEnvelope
          H ω} = ⋃ n, A n := by
    ext ω
    simp only [FactorialChronologicalGrid.allTimeAbsoluteEnvelope,
      Set.mem_ofPred_eq, Set.mem_iUnion, lt_iSup_iff,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hR, A]
  have hActualEvent :
      {ω | ENNReal.ofReal R <
        ⨆ t : ℝ≥0, ENNReal.ofReal |H t ω|} =
        {ω | ENNReal.ofReal R <
          FactorialChronologicalGrid.allTimeAbsoluteEnvelope
            H ω} := by
    ext ω
    change (ENNReal.ofReal R <
      ⨆ t : ℝ≥0, ENNReal.ofReal |H t ω|) ↔
        ENNReal.ofReal R <
          FactorialChronologicalGrid.allTimeAbsoluteEnvelope
            H ω
    rw [FactorialChronologicalGrid.allTimeAbsoluteEnvelope_eq_iSup
      (hRight H hH) (hMartingaleLeft H hH)]
  rw [hActualEvent, hUnion, hAMono.measure_iUnion]
  exact iSup_le hATail

end SIntegrableMartingaleRestrictionL2Calculus

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Lemma 4.7 for locally finite-variation strategies

The finite-horizon Lemma 4.7 calculus consumes globally bounded-variation
paths.  A general special-semimartingale decomposition only has locally
bounded variation.  This section applies the indexed class theorem
simultaneously to every deterministic integer horizon and then exhausts the
whole time axis.  Thus no global pathwise variation hypothesis and no finite
predictable signed measure for the original strategy appear in the public
conclusion.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Deterministic stopping preserves pathwise left limits. -/
theorem ProcessHasLeftLimits.deterministicallyStopped
    {X : Process Ω} (hX : ProcessHasLeftLimits X) (T : ℝ≥0) :
    ProcessHasLeftLimits (fun t ω => X (min t T) ω) := by
  rw [show (fun t ω => X (min t T) ω) =
      MeasureTheory.stoppedProcess X
        (fun _ : Ω => (T : WithTop ℝ≥0)) by
    funext t ω
    rw [MeasureTheory.stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]]
  exact hX.stoppedProcess _

end FTAPTheorem42
