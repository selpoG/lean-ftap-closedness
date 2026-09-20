/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRows

/-!
# Exhaustion of the common-stop localizers

The finite-horizon common-stop producer gives a stopping time `alpha m` which
is bounded by a deterministic horizon `T m`, except on an event whose
probabilities are summable.  This file turns such a family into one genuine
localizing sequence.  The tail infimum is taken only after the
Borel--Cantelli step has shown that the original family tends to infinity
almost surely.

The construction uses mathlib's `IsPreLocalizingSequence.isLocalizingSequence_biInf`.
Thus the stopping-time and monotonicity assertions for the tail infimum are
not obtained from an uncountable intersection of events, and no monotonicity
of the original family of common stops is assumed.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The generic tail-infimum construction -/

/-- A family of bounded stopping times whose failures to reach their
deterministic horizons have summable probabilities. -/
structure BoundedStoppingTimeFamily
    (T : Nat → NNReal)
    (alpha : Nat → Ω → WithTop NNReal) : Prop where
  horizon_tendsto : Tendsto (fun n => (T n : WithTop NNReal)) atTop (𝓝 ⊤)
  isStoppingTime : ∀ n, IsStoppingTime F (alpha n)
  le_horizon : ∀ n ω, alpha n ω ≤ (T n : WithTop NNReal)
  bad_measure_sum :
    (∑' n, mu {ω | alpha n ω < (T n : WithTop NNReal)}) ≠ ⊤

namespace BoundedStoppingTimeFamily

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- The original bounded stopping times eventually coincide with their
 horizons almost surely. -/
theorem ae_eventually_eq_horizon
    {T : Nat → NNReal}
    {alpha : Nat → Ω → WithTop NNReal}
    (h : BoundedStoppingTimeFamily (F := F) (mu := mu) T alpha) :
    ∀ᵐ ω ∂mu, ∀ᶠ n in atTop,
      alpha n ω = (T n : WithTop NNReal) := by
  let bad : Nat → Set Ω := fun n =>
    {ω | alpha n ω < (T n : WithTop NNReal)}
  have hae_bad : ∀ᵐ ω ∂mu, ∀ᶠ n in atTop, ω ∉ bad n :=
    MeasureTheory.ae_eventually_notMem (μ := mu) (s := bad) (by
      simpa only [bad] using h.bad_measure_sum)
  filter_upwards [hae_bad] with ω hω
  filter_upwards [hω] with n hn
  have hnot : ¬ alpha n ω < (T n : WithTop NNReal) := by
    simpa only [bad, Set.mem_ofPred_eq] using hn
  exact le_antisymm (h.le_horizon n ω) (le_of_not_gt hnot)

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- The family of common-stop times is a pre-localizing sequence. -/
theorem isPreLocalizingSequence
    {T : Nat → NNReal}
    {alpha : Nat → Ω → WithTop NNReal}
    (h : BoundedStoppingTimeFamily (F := F) (mu := mu) T alpha) :
    ProbabilityTheory.IsPreLocalizingSequence F alpha mu := by
  refine { isStoppingTime := h.isStoppingTime, tendsto_top := ?_ }
  filter_upwards [h.ae_eventually_eq_horizon] with ω hω
  rw [WithTop.tendsto_nhds_top_iff]
  intro t
  have hT := h.horizon_tendsto
  rw [WithTop.tendsto_nhds_top_iff] at hT
  filter_upwards [hω, hT t] with n hn hTn
  rw [hn]
  exact hTn

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- Tail infima of the bounded stopping-time family form an exhaustive
localizing sequence.  The result also records the order bounds needed to
reuse the corresponding fixed-stop decompositions. -/
theorem exists_tailInf_localizingSequence
    {T : Nat → NNReal}
    {alpha : Nat → Ω → WithTop NNReal}
    (h : BoundedStoppingTimeFamily (F := F) (mu := mu) T alpha)
    [F.IsRightContinuous] :
    ∃ tau : Nat → Ω → WithTop NNReal,
      ProbabilityTheory.IsLocalizingSequence F tau mu ∧
        (∀ n ω, tau n ω ≤ alpha n ω) ∧
        (∀ n ω, tau n ω ≤ (T n : WithTop NNReal)) ∧
        (∀ n m ω, n ≤ m → tau n ω ≤ alpha m ω) := by
  let hPre := h.isPreLocalizingSequence
  let hLocal := hPre.isLocalizingSequence_biInf
  let tau : Nat → Ω → WithTop NNReal := fun n ω =>
    ⨅ m ≥ n, alpha m ω
  have hLocal' : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    simpa only [tau] using hLocal
  have hTauLe (n m : Nat) (hnm : n ≤ m) (ω : Ω) :
      tau n ω ≤ alpha m ω := by
    dsimp only [tau]
    exact iInf_le_of_le m (iInf_le_of_le hnm (le_refl _))
  refine ⟨tau, hLocal', ?_, ?_, ?_⟩
  · intro n ω
    exact hTauLe n n (le_rfl) ω
  · intro n ω
    exact (hTauLe n n (le_rfl) ω).trans (h.le_horizon n ω)
  · intro n m ω hnm
    exact hTauLe n m hnm ω

end BoundedStoppingTimeFamily

end HorizonFactorialGrid

end FTAPTheorem42
