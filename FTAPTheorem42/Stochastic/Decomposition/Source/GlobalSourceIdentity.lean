/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRows
import FTAPTheorem42.Foundations.ProcessIndistinguishable

/-!
# Global source identity from a common stopped schedule

This module contains the source-independent composition used after component
gluing.  It only sees stopped component agreements, the re-stopping identities
for the local coordinates, and the stopped source identity supplied by a
fixed-stop consumer.  In particular, it does not select a decomposition or
assert any source-specific regularity.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω}

/-- A coordinate already defined as a stopped process is unchanged when it is
stopped once more at the same stopping time. -/
theorem stoppedProcess_self_of_eq_stopped
    {X Y : Process Ω} {tau : Ω → WithTop NNReal}
    (hY : Y = MeasureTheory.stoppedProcess X tau) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess Y tau) Y := by
  rw [hY, MeasureTheory.stoppedProcess_stoppedProcess']
  simp only [min_self]
  exact ProcessIndistinguishable.refl mu _

/-- A common stopped source identity and compatible glued components imply the
global source identity.  The localizer and both component coordinates are
shared throughout the statement. -/
theorem source_indistinguishable_of_stopped_components_localizingSequence
    {S M A : Process Ω}
    {Mρ Aρ : Nat → Process Ω}
    {tau : Nat → Ω → WithTop NNReal}
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    (hMStopped : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess M (tau n))
      (MeasureTheory.stoppedProcess (Mρ n) (tau n)))
    (hAStopped : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess A (tau n))
      (MeasureTheory.stoppedProcess (Aρ n) (tau n)))
    (hMRestarted : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (Mρ n) (tau n))
      (Mρ n))
    (hARestarted : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (Aρ n) (tau n))
      (Aρ n))
    (hSource : ∀ n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess S (tau n))
      (fun t omega => Mρ n t omega + Aρ n t omega)) :
    ProcessIndistinguishable mu S
      (fun t omega => M t omega + A t omega) := by
  apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence hTau
  intro n
  have hComponents := (hMStopped n).add (hAStopped n)
  have hComponents' : ProcessIndistinguishable mu
      (fun t omega =>
        MeasureTheory.stoppedProcess M (tau n) t omega +
          MeasureTheory.stoppedProcess A (tau n) t omega)
      (fun t omega =>
        MeasureTheory.stoppedProcess (Mρ n) (tau n) t omega +
          MeasureTheory.stoppedProcess (Aρ n) (tau n) t omega) := by
    simpa only using hComponents
  have hSelf : ProcessIndistinguishable mu
      (fun t omega =>
        MeasureTheory.stoppedProcess (Mρ n) (tau n) t omega +
          MeasureTheory.stoppedProcess (Aρ n) (tau n) t omega)
      (fun t omega => Mρ n t omega + Aρ n t omega) := by
    exact (hMRestarted n).add (hARestarted n)
  have hSum : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (fun t omega => M t omega + A t omega) (tau n))
      (fun t omega =>
        MeasureTheory.stoppedProcess M (tau n) t omega +
          MeasureTheory.stoppedProcess A (tau n) t omega) := by
    change ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (M + A) (tau n))
      (fun t omega =>
        MeasureTheory.stoppedProcess M (tau n) t omega +
          MeasureTheory.stoppedProcess A (tau n) t omega)
    rw [HorizonFactorialGrid.stoppedProcess_add]
    exact ProcessIndistinguishable.refl mu _
  exact (hSum.trans (hComponents'.trans (hSelf.trans (hSource n).symm))).symm

end HorizonFactorialGrid

end FTAPTheorem42
