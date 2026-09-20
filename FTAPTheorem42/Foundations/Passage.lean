/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.HahnStopping
import FTAPTheorem42.Foundations.HilbertConvexification

/-! # Passage prefixes and convex tail events -/

namespace FTAPTheorem42

open Filter MeasureTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- First strict passage of the absolute value of `X` above `r`. -/
noncomputable def absoluteStrictHittingAfter
    (X : Process Ω) (r : ℝ) : Ω → WithTop ℝ≥0 :=
  RightContinuousHittingTime.strictHittingAfter
    (fun t ω => |X t ω|) r

/-- The increment of `X` strictly after a possibly infinite stopping time.
It is zero up to and including `τ`, and equals `X t - X τ` afterwards. -/
noncomputable def postStoppingTailProcess
    (X : Process Ω) (τ : Ω → WithTop ℝ≥0) : Process Ω :=
  fun t ω => X t ω - MeasureTheory.stoppedProcess X τ t ω

/-- The martingale tail after its own strict absolute passage. -/
noncomputable def absolutePassageTail (M : Process Ω) (c : Real) : Process Ω :=
  postStoppingTailProcess M (absoluteStrictHittingAfter M c)

/-- A component stopped at its own absolute passage and a finite horizon. -/
noncomputable def absolutePassagePrefix (M : Process Ω) (c : Real) (T : NNReal) : Process Ω :=
  stoppedProcess M (fun ω => min (absoluteStrictHittingAfter M c ω) (T : WithTop NNReal))

omit [MeasurableSpace Ω] in
theorem sub_absolutePassagePrefix_eq_tail (M : Process Ω) (c : Real)
    (T t : NNReal) (ht : t ≤ T) (ω : Ω) :
    M t ω - absolutePassagePrefix M c T t ω = absolutePassageTail M c t ω := by
  have hComp : absolutePassagePrefix M c T =
      stoppedProcess (stoppedProcess M (absoluteStrictHittingAfter M c))
        (fun _ => (T : WithTop NNReal)) := by
    rw [stoppedProcess_stoppedProcess']
    unfold absolutePassagePrefix
    congr 1
    funext ω
    exact min_comm _ _
  rw [hComp, stoppedProcess_eq_of_le (τ := fun _ : Ω => (T : WithTop NNReal))
    (ω := ω) (WithTop.coe_le_coe.mpr ht)]
  rfl

omit [MeasurableSpace Ω] in
/-- Clamping the passage of a deterministically stopped process at the same
horizon gives the same time as clamping the original passage. -/
theorem min_absoluteStrictHittingAfter_deterministicallyStopped
    (X : Process Ω) (r : Real) (T : NNReal) (omega : Ω) :
    min
        (absoluteStrictHittingAfter
          (fun t omega => X (min t T) omega) r omega)
        (T : WithTop NNReal) =
      min (absoluteStrictHittingAfter X r omega) (T : WithTop NNReal) := by
  let stoppedHit := absoluteStrictHittingAfter
    (fun t omega => X (min t T) omega) r omega
  let originalHit := absoluteStrictHittingAfter X r omega
  have hlt : forall i : NNReal,
      min stoppedHit (T : WithTop NNReal) < (i : WithTop NNReal) <->
        min originalHit (T : WithTop NNReal) < (i : WithTop NNReal) := by
    intro i
    simp only [min_lt_iff, WithTop.coe_lt_coe]
    by_cases hTi : T < i
    · simp only [hTi, or_true]
    · have hiT : i <= T := le_of_not_gt hTi
      have hHit : stoppedHit < (i : WithTop NNReal) <->
          originalHit < (i : WithTop NNReal) := by
        dsimp only [stoppedHit, originalHit]
        unfold absoluteStrictHittingAfter
          RightContinuousHittingTime.strictHittingAfter
        rw [MeasureTheory.hittingAfter_lt_iff,
          MeasureTheory.hittingAfter_lt_iff]
        constructor
        · rintro ⟨t, ht, htLevel⟩
          refine ⟨t, ht, ?_⟩
          have htT : t <= T := ht.2.le.trans hiT
          simpa only [min_eq_left htT] using htLevel
        · rintro ⟨t, ht, htLevel⟩
          refine ⟨t, ht, ?_⟩
          have htT : t <= T := ht.2.le.trans hiT
          simpa only [min_eq_left htT] using htLevel
      simp only [hTi, or_false, hHit]
  apply le_antisymm
  · by_contra hnot
    have hlt' : min originalHit (T : WithTop NNReal) <
        min stoppedHit (T : WithTop NNReal) := lt_of_not_ge hnot
    obtain ⟨c, hOriginal, hStopped⟩ := exists_between hlt'
    have hcTop : c ≠ (⊤ : WithTop NNReal) := ne_top_of_lt hStopped
    lift c to NNReal using hcTop with i hi
    have hContradiction := (hlt i).mpr (by simpa only [hi] using hOriginal)
    exact (not_lt_of_ge hStopped.le) (by simpa only [hi] using hContradiction)
  · by_contra hnot
    have hlt' : min stoppedHit (T : WithTop NNReal) <
        min originalHit (T : WithTop NNReal) := lt_of_not_ge hnot
    obtain ⟨c, hStopped, hOriginal⟩ := exists_between hlt'
    have hcTop : c ≠ (⊤ : WithTop NNReal) := ne_top_of_lt hOriginal
    lift c to NNReal using hcTop with i hi
    have hContradiction := (hlt i).mp (by simpa only [hi] using hStopped)
    exact (not_lt_of_ge hOriginal.le) (by simpa only [hi] using hContradiction)

omit [MeasurableSpace Ω] in
/-- A deterministic horizon commutes with the individual passage tail,
including the value at the horizon and the passage jump. -/
theorem absolutePassageTail_deterministicallyStopped
    (M : Process Ω) (c : Real) (T : NNReal) :
    absolutePassageTail (fun t ω => M (min t T) ω) c =
      fun t ω => absolutePassageTail M c (min t T) ω := by
  have hStop : (fun t ω => M (min t T) ω) =
      stoppedProcess M (fun _ => (T : WithTop NNReal)) := by
    funext t ω
    simp only [stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hComp : stoppedProcess (fun t ω => M (min t T) ω)
      (absoluteStrictHittingAfter (fun t ω => M (min t T) ω) c) =
      stoppedProcess (stoppedProcess M (absoluteStrictHittingAfter M c))
        (fun _ => (T : WithTop NNReal)) := by
    rw [hStop, stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']
    congr 1
    funext ω
    rw [← hStop, min_absoluteStrictHittingAfter_deterministicallyStopped, min_comm]
  funext t ω
  change M (min t T) ω -
    stoppedProcess (fun t ω => M (min t T) ω)
      (absoluteStrictHittingAfter (fun t ω => M (min t T) ω) c) t ω = _
  rw [hComp]
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rfl

/-- The event that a finite convex martingale tail passes the given level. -/
def convexTailPassageEvent (M : Nat → Process Ω) (w : TailConvexWeights 0)
    (c ε : Real) : Set Ω :=
  {ω | absoluteStrictHittingAfter
    (w.applyVector (fun i => absolutePassageTail (M i) c)) ε ω ≠ ⊤}

end FTAPTheorem42
