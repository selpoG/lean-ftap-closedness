/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalExhaustion
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopSquareIntegrableFullLevel

/-!
# The square-integrable common-stop family

The one-horizon envelope producer is run once at each scheduled horizon.  This
module keeps those dependent level certificates together, and only then takes
the tail infimum of their stopping times.  Re-stopping at a localizing time is
performed on the stored level through the source-independent component
consumer; no rows, coefficients, or fixed-stop package are selected again.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The level-indexed producer output -/

/-- A family of complete square-integrable one-horizon producer outputs.

The `level` field is dependent in the horizon and error schedule.  In
particular, each level contains the common gate, its rows and coefficients,
the regularized raw/Jordan data, and the uncentered fixed-stop package that
was produced from those same witnesses.
-/
structure SquareIntegrableCommonStopUncenteredFixedStopFamily
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) where
  level : ∀ m, SquareIntegrableCommonStopUncenteredFixedStopLevelData
    (F := F) (mu := mu) (T m) (eta m) ξ hξ hUsual hSAdapted hSRight hSLeft hSBound

theorem exists_squareIntegrableCommonStopUncenteredFixedStopFamily
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (heta : ∀ m, 0 < eta m) :
    Nonempty (SquareIntegrableCommonStopUncenteredFixedStopFamily
      (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound) := by
  let level : ∀ m, SquareIntegrableCommonStopUncenteredFixedStopLevelData
      (F := F) (mu := mu) (T m) (eta m) ξ hξ hUsual hSAdapted hSRight hSLeft hSBound :=
    fun m => Classical.choice
      (exists_squareIntegrableCommonStopUncenteredFixedStopLevelData
        (F := F) (mu := mu) (T m) (heta m) hUsual hS hSAdapted hSRight hSLeft
        ξ hξ hSBound)
  exact ⟨{ level := level }⟩

/-! ## The tail-infimum exhaustion certificate -/

/-- The localizing sequence and the re-stopped component certificates
attached to a stored square-integrable fixed-stop family. -/
structure SquareIntegrableCommonStopUncenteredFixedStopExhaustionData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (family : SquareIntegrableCommonStopUncenteredFixedStopFamily
      (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound)
    (tau : Nat → Ω → WithTop NNReal) where
  isLocalizingSequence : ProbabilityTheory.IsLocalizingSequence F tau mu
  tau_eq_tailInf : ∀ n omega,
    tau n omega = ⨅ m ≥ n, (family.level m).analytic.alpha omega
  alpha_stopping : ∀ n, IsStoppingTime F ((family.level n).analytic.alpha)
  alpha_le_horizon : ∀ n omega,
    (family.level n).analytic.alpha omega ≤ (T n : WithTop NNReal)
  alpha_bad_event_measure : ∀ n,
    mu {omega | (family.level n).analytic.alpha omega < (T n : WithTop NNReal)} ≤
      ENNReal.ofReal (4 * eta n)
  tau_le_alpha : ∀ n omega,
    tau n omega ≤ (family.level n).analytic.alpha omega
  tau_le_horizon : ∀ n omega,
    tau n omega ≤ (T n : WithTop NNReal)
  tau_le_all_alpha : ∀ n m omega, n ≤ m →
    tau n omega ≤ (family.level m).analytic.alpha omega
  Mρ : ∀ _n, Process Ω
  Aρ : ∀ _n, Process Ω
  restopped : ∀ n,
    CommonStopUncenteredRestoppedComponentData
      (family.level n).alpha_stopping
      ((family.level n).toComponentView)
      (tau n)
      (isLocalizingSequence.isStoppingTime n)
      (tau_le_alpha n)
      (Mρ n) (Aρ n)
  restopped_decomposition : ∀ n,
    Nonempty (SpecialSemimartingaleDecomposition
      (MeasureTheory.stoppedProcess S (tau n)) F mu)

theorem exists_squareIntegrableCommonStopUncenteredFixedStopExhaustion
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hT : Tendsto (fun n => (T n : WithTop NNReal)) atTop (𝓝 ⊤))
    (heta : ∀ m, 0 < eta m)
    (hEta : (∑' m, ENNReal.ofReal (4 * eta m)) ≠ ⊤)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) :
    ∃ family : SquareIntegrableCommonStopUncenteredFixedStopFamily
        (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound,
      ∃ tau : Nat → Ω → WithTop NNReal,
        Nonempty (SquareIntegrableCommonStopUncenteredFixedStopExhaustionData
          (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound
          family tau) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨family⟩ :=
    exists_squareIntegrableCommonStopUncenteredFixedStopFamily
      (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound heta
  let alpha : Nat → Ω → WithTop NNReal := fun m omega =>
    (family.level m).analytic.alpha omega
  let boundedFamily : BoundedStoppingTimeFamily (F := F) (mu := mu) T alpha := {
    horizon_tendsto := hT
    isStoppingTime := fun m => (family.level m).alpha_stopping
    le_horizon := fun m omega => (family.level m).alpha_le_horizon omega
    bad_measure_sum := by
      apply ne_top_of_le_ne_top hEta
      exact ENNReal.tsum_le_tsum (fun m => by
        simpa only [alpha] using
          (family.level m).alpha_bad_event_measure) }
  have hAlphaStopping : ∀ n, IsStoppingTime F ((family.level n).analytic.alpha) := by
    intro n
    exact (family.level n).alpha_stopping
  have hAlphaLeHorizon : ∀ n omega,
      (family.level n).analytic.alpha omega ≤ (T n : WithTop NNReal) := by
    intro n omega
    exact (family.level n).alpha_le_horizon omega
  have hAlphaMeasure : ∀ n,
      mu {omega | (family.level n).analytic.alpha omega < (T n : WithTop NNReal)} ≤
        ENNReal.ofReal (4 * eta n) := by
    intro n
    exact (family.level n).alpha_bad_event_measure
  let hPre := boundedFamily.isPreLocalizingSequence
  let hLocal := hPre.isLocalizingSequence_biInf
  let tau : Nat → Ω → WithTop NNReal := fun n omega =>
    ⨅ m ≥ n, alpha m omega
  have hTau : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    simpa only [tau] using hLocal
  have hTauEq : ∀ n omega,
      tau n omega = ⨅ m ≥ n, (family.level m).analytic.alpha omega := by
    intro n omega
    rfl
  have hTauAlpha : ∀ n omega, tau n omega ≤ alpha n omega := by
    intro n omega
    dsimp only [tau]
    exact iInf_le_of_le n (iInf_le_of_le (le_rfl) (le_refl _))
  have hTauHorizon : ∀ n omega, tau n omega ≤ (T n : WithTop NNReal) := by
    intro n omega
    exact (hTauAlpha n omega).trans (boundedFamily.le_horizon n omega)
  have hTauAll : ∀ n m omega, n ≤ m → tau n omega ≤ alpha m omega := by
    intro n m omega hnm
    dsimp only [tau]
    exact iInf_le_of_le m (iInf_le_of_le hnm (le_refl _))
  have hTauAlpha' : ∀ n omega,
      tau n omega ≤ (family.level n).analytic.alpha omega := by
    simpa only [alpha] using hTauAlpha
  have hTauAll' : ∀ n m omega, n ≤ m →
      tau n omega ≤ (family.level m).analytic.alpha omega := by
    simpa only [alpha] using hTauAll
  let hStop : ∀ n, IsStoppingTime F (tau n) :=
    fun n => hTau.isStoppingTime n
  choose Mρ Aρ hRestopped hRestoppedDecomposition using fun n =>
    exists_squareIntegrableCommonStopUncenteredRestoppedComponentData
      (F := F) (mu := mu) (family.level n) (tau n) (hStop n) (hTauAlpha' n)
  let data : SquareIntegrableCommonStopUncenteredFixedStopExhaustionData
      (F := F) (mu := mu) T eta ξ hξ hUsual hS hSAdapted hSRight hSLeft hSBound
      family tau := {
    isLocalizingSequence := hTau
    tau_eq_tailInf := hTauEq
    alpha_stopping := hAlphaStopping
    alpha_le_horizon := hAlphaLeHorizon
    alpha_bad_event_measure := hAlphaMeasure
    tau_le_alpha := hTauAlpha'
    tau_le_horizon := hTauHorizon
    tau_le_all_alpha := hTauAll'
    Mρ := Mρ
    Aρ := Aρ
    restopped := hRestopped
    restopped_decomposition := hRestoppedDecomposition }
  exact ⟨family, tau, ⟨data⟩⟩

end HorizonFactorialGrid

end FTAPTheorem42
