/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Stopping.MonotoneCadlagRationalPassage
import FTAPTheorem42.Foundations.ProcessIndistinguishable

/-!
# Source-independent process bridge

The countable clamped positive-rational passage argument is independent of
the construction of the predictable limsup and of the source process.  This
module consumes only the path properties of the càdlàg monotone version, the
corresponding continuity-point and post-horizon facts for the predictable
version, and equality at every bounded stopping time.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open FTAPTheorem42.MonotoneCadlagRationalPassage

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {T : NNReal}

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem processIndistinguishable_of_boundedStoppingTime_ae_eq_core
    (hRightContinuous : F.IsRightContinuous)
    {Preg Ppred : Process Ω}
    (hPregStronglyAdapted : StronglyAdapted F Preg)
    (hPregRightContinuous : ∀ omega t,
      ContinuousWithinAt (Preg · omega) (Ici t) t)
    (hPregLeftLimits : ProcessHasLeftLimits Preg)
    (hPregNonnegative : ∀ omega t, 0 ≤ Preg t omega)
    (hPregMonotone : ∀ omega, Monotone (Preg · omega))
    (hPregZero : Preg 0 = 0)
    (hPregConstantAfter : ∀ omega t, T ≤ t →
      Preg t omega = Preg T omega)
    (hPpredZero : Ppred 0 = 0)
    (hPpredConstantAfter : ∀ᵐ omega ∂mu, ∀ t, T ≤ t →
      Ppred t omega = Ppred T omega)
    (hPpredEqPregAtContinuity : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      ContinuousAt (Preg · omega) t → Ppred t omega = Preg t omega)
    (hStopping : ∀ (τ : Ω → NNReal),
      IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)) →
      (∀ omega, τ omega ≤ T) →
      (fun omega => Ppred (τ omega) omega) =ᵐ[mu]
        (fun omega => Preg (τ omega) omega)) :
    ProcessIndistinguishable mu Ppred Preg := by
  let passage : Nat → Ω → NNReal := fun n omega =>
    clampedStrictPassage Preg T (positiveRationalLevel n) omega
  have hPassageStopping (n : Nat) :
      IsStoppingTime F (fun omega =>
        (passage n omega : WithTop NNReal)) := by
    dsimp [passage]
    exact @clampedStrictPassage_isStoppingTime
      Ω _ F hRightContinuous Preg hPregStronglyAdapted
      hPregRightContinuous T (positiveRationalLevel n)
  have hPassageLe (n : Nat) (omega : Ω) : passage n omega ≤ T := by
    exact clampedStrictPassage_le Preg T (positiveRationalLevel n) omega
  have hPassageEq (n : Nat) :
      (fun omega => Ppred (passage n omega) omega) =ᵐ[mu]
        (fun omega => Preg (passage n omega) omega) :=
    hStopping (passage n) (hPassageStopping n) (hPassageLe n)
  have hPassageEqAll : ∀ᵐ omega ∂mu, ∀ n,
      Ppred (passage n omega) omega = Preg (passage n omega) omega := by
    rw [ae_all_iff]
    intro n
    exact hPassageEq n
  have hGood : ∀ᵐ omega ∂mu, ∀ t, Ppred t omega = Preg t omega := by
    filter_upwards [hPassageEqAll, hPpredEqPregAtContinuity,
      hPpredConstantAfter] with omega hPassage hContinuity hAfter
    have hEqLe : ∀ t, t ≤ T → Ppred t omega = Preg t omega := by
      intro t ht
      by_cases ht0 : t = 0
      · subst t
        calc
          Ppred 0 omega = 0 := by
            simpa using congrFun hPpredZero omega
          _ = Preg 0 omega := by
            symm
            simpa using congrFun hPregZero omega
      · by_cases hjump : processLeftJump Preg t omega = 0
        · exact hContinuity t ht
            (continuousAt_of_rightContinuous_of_leftLimit_of_processLeftJump_eq_zero
              (Preg · omega) t
              (fun s => hPregRightContinuous omega s)
              (fun s => hPregLeftLimits omega s)
              hjump)
        · obtain ⟨n, hn⟩ :=
            exists_clampedStrictPassage_eq_of_processLeftJump_ne_zero
              Preg hPregNonnegative hPregMonotone ht hjump
          have hEq := hPassage n
          dsimp [passage] at hEq
          rw [hn] at hEq
          exact hEq
    intro t
    by_cases htT : t ≤ T
    · exact hEqLe t htT
    · have hTt : T ≤ t := le_of_not_ge htT
      calc
        Ppred t omega = Ppred T omega := hAfter t hTt
        _ = Preg T omega := hEqLe T le_rfl
        _ = Preg t omega := (hPregConstantAfter omega t hTt).symm
  exact hGood

end HorizonFactorialGrid

end FTAPTheorem42
