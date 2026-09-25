/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.Process
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# The bounded-jump residual after removing finite large jumps

For a càdlàg source `X`, subtracting the finite large-jump process removes
exactly the jumps larger than `c` on `(0,T]`.  This file records the
source-level residual and its pathwise jump bound.  It does not identify any
predictable projection of the removed process, nor does it assert a
closed-stop compatibility statement.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FiniteLargeJumpProcess

/-! ## The residual process -/

/-- The source with all left jumps larger than `c` on `(0,T]` removed. -/
noncomputable def smallJumpResidual
    (X : Process Ω) (c : Real) (T : NNReal) : Process Ω :=
  fun t omega => X t omega - process X c T t omega

theorem smallJumpResidual_stronglyAdapted
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    [F.IsRightContinuous]
    {X : Process Ω} {c : Real} {T : NNReal}
    (hX : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    StronglyAdapted F (smallJumpResidual X c T) := by
  change StronglyAdapted F (X - process X c T)
  exact hX.sub (stronglyAdapted_process hX hXRight hXLeft hc T)

omit [MeasurableSpace Ω] in
theorem smallJumpResidual_rightContinuous
    {X : Process Ω} {c : Real} {T : NNReal}
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ∀ omega t,
      ContinuousWithinAt (smallJumpResidual X c T · omega) (Ici t) t := by
  intro omega t
  change ContinuousWithinAt
    (fun s => X s omega - process X c T s omega) (Ici t) t
  exact (hXRight omega t).sub
    (process_rightContinuous hXRight hXLeft hc omega t)

omit [MeasurableSpace Ω] in
theorem smallJumpResidual_hasLeftLimits
    {X : Process Ω} {c : Real} {T : NNReal}
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ProcessHasLeftLimits (smallJumpResidual X c T) := by
  change ProcessHasLeftLimits
    (fun t omega => X t omega - process X c T t omega)
  exact hXLeft.sub (process_hasLeftLimits hXRight hXLeft hc)

/-! ## Exact left-jump identities -/

omit [MeasurableSpace Ω] in
theorem smallJumpResidual_processLeftJump_eq_sub
    {X : Process Ω} {c : Real} {T : NNReal}
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    (t : NNReal) (omega : Ω) :
    processLeftJump (smallJumpResidual X c T) t omega =
      processLeftJump X t omega -
        processLeftJump (process X c T) t omega := by
  change processLeftJump
    (fun s omega => X s omega - process X c T s omega) t omega = _
  exact processLeftJump_sub hXLeft
    (process_hasLeftLimits hXRight hXLeft hc) t omega

omit [MeasurableSpace Ω] in
theorem smallJumpResidual_processLeftJump_eq_dichotomy
    {X : Process Ω} {c : Real} {T : NNReal}
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    (t : NNReal) (omega : Ω) :
    (t ∈ largeJumpTimeSet (fun s => X s omega) c T →
      processLeftJump (smallJumpResidual X c T) t omega = 0) ∧
    (t ∉ largeJumpTimeSet (fun s => X s omega) c T →
      processLeftJump (smallJumpResidual X c T) t omega =
        processLeftJump X t omega) := by
  constructor
  · intro ht
    rw [smallJumpResidual_processLeftJump_eq_sub
      hXRight hXLeft hc t omega,
      process_leftJump_eq_of_large hXRight hXLeft hc ht]
    ring
  · intro ht
    rw [smallJumpResidual_processLeftJump_eq_sub
      hXRight hXLeft hc t omega,
      process_leftJump_eq_of_not_large hXRight hXLeft hc ht]
    simp

omit [MeasurableSpace Ω] in
theorem smallJumpResidual_processLeftJump_eq_zero_of_large
    {X : Process Ω} {c : Real} {T : NNReal}
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    {t : NNReal} {omega : Ω}
    (ht : t ∈ largeJumpTimeSet (fun s => X s omega) c T) :
    processLeftJump (smallJumpResidual X c T) t omega = 0 := by
  exact (smallJumpResidual_processLeftJump_eq_dichotomy
    hXRight hXLeft hc t omega).1 ht

omit [MeasurableSpace Ω] in
theorem smallJumpResidual_processLeftJump_eq_source_of_not_large
    {X : Process Ω} {c : Real} {T : NNReal}
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    {t : NNReal} {omega : Ω}
    (ht : t ∉ largeJumpTimeSet (fun s => X s omega) c T) :
    processLeftJump (smallJumpResidual X c T) t omega =
      processLeftJump X t omega := by
  exact (smallJumpResidual_processLeftJump_eq_dichotomy
    hXRight hXLeft hc t omega).2 ht

omit [MeasurableSpace Ω] in
theorem smallJumpResidual_processLeftJump_eq_zero_of_large_jump
    {X : Process Ω} {c : Real} {T : NNReal}
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    {t : NNReal} {omega : Ω} (ht : t ∈ Ioc (0 : NNReal) T)
    (hlarge : c < |processLeftJump X t omega|) :
    processLeftJump (smallJumpResidual X c T) t omega = 0 := by
  apply smallJumpResidual_processLeftJump_eq_zero_of_large
    hXRight hXLeft hc
  refine ⟨ht, ?_⟩
  simpa [processLeftJump, cadlagLeftJump] using hlarge

omit [MeasurableSpace Ω] in
theorem smallJumpResidual_processLeftJump_eq_source_of_small_jump
    {X : Process Ω} {c : Real} {T : NNReal}
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    {t : NNReal} {omega : Ω} (ht : t ∈ Ioc (0 : NNReal) T)
    (hsmall : ¬ c < |processLeftJump X t omega|) :
    processLeftJump (smallJumpResidual X c T) t omega =
      processLeftJump X t omega := by
  apply smallJumpResidual_processLeftJump_eq_source_of_not_large
    hXRight hXLeft hc
  intro hlarge
  apply hsmall
  have hlarge' : t ∈ largeJumpTimeSet (fun s => X s omega) c T :=
    ⟨ht, hlarge.2⟩
  simpa [processLeftJump, cadlagLeftJump] using hlarge'.2

/-! The residual has no large left jump on the source horizon. -/

omit [MeasurableSpace Ω] in
theorem abs_smallJumpResidual_processLeftJump_le
    {X : Process Ω} {c : Real} {T : NNReal}
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    {t : NNReal} {omega : Ω} (ht : t ∈ Ioc (0 : NNReal) T) :
    |processLeftJump (smallJumpResidual X c T) t omega| ≤ c := by
  classical
  by_cases hlarge : c < |processLeftJump X t omega|
  · have hzero := smallJumpResidual_processLeftJump_eq_zero_of_large_jump
      hXRight hXLeft hc ht hlarge
    rw [hzero]
    simpa using hc.le
  · have hsource := smallJumpResidual_processLeftJump_eq_source_of_small_jump
      hXRight hXLeft hc ht hlarge
    rw [hsource]
    exact le_of_not_gt hlarge

end FiniteLargeJumpProcess

end FTAPTheorem42
