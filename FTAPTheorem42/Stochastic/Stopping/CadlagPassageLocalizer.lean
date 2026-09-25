/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.CadlagEnvelope
import FTAPTheorem42.Stochastic.DS.Lemma47.FirstPassage

/-!
# Càdlàg absolute-passage localizers

The first strict passages of a càdlàg process through the increasing levels
`n + 1`, clamped at the increasing deterministic horizons `n + 1`, form a
genuine localizing sequence.  Cofinality uses only pathwise boundedness on
compact time intervals; it does not require a global path bound.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Positive integral passage thresholds, chosen independently of value-truncation caps. -/
def cadlagPassageLevel (n : Nat) : Real :=
  (n + 1 : Nat)

/-- The positive integral horizons used by the canonical càdlàg localizer. -/
def cadlagPassageHorizon (n : Nat) : NNReal :=
  (n + 1 : Nat)

theorem cadlagPassageLevel_nonnegative (n : Nat) :
    0 ≤ cadlagPassageLevel n := by
  unfold cadlagPassageLevel
  positivity

theorem cadlagPassageHorizon_pos (n : Nat) :
    0 < cadlagPassageHorizon n := by
  unfold cadlagPassageHorizon
  positivity

/-- Stop either at the strict absolute-value passage through `n + 1` or at
the deterministic horizon `n + 1`, whichever comes first. -/
noncomputable def cadlagAbsolutePassageLocalizer
    (X : Process Omega) (n : Nat) : Omega -> WithTop NNReal :=
  fun omega => min
    (absoluteStrictHittingAfter X (cadlagPassageLevel n) omega)
    (cadlagPassageHorizon n : WithTop NNReal)

omit [MeasurableSpace Omega] in
/-- Every clamped càdlàg passage is finite. -/
theorem cadlagAbsolutePassageLocalizer_ne_top
    (X : Process Omega) (n : Nat) (omega : Omega) :
    cadlagAbsolutePassageLocalizer X n omega ≠ ⊤ := by
  apply ne_top_of_le_ne_top (WithTop.coe_ne_top :
    (cadlagPassageHorizon n : WithTop NNReal) ≠ ⊤)
  exact min_le_right _ _

/-- The finite-valued representative of the clamped càdlàg passage. -/
noncomputable def cadlagAbsolutePassageLocalizerFinite
    (X : Process Omega) (n : Nat) : Omega → NNReal :=
  fun omega => (cadlagAbsolutePassageLocalizer X n omega).untop
    (cadlagAbsolutePassageLocalizer_ne_top X n omega)

omit [MeasurableSpace Omega] in
@[simp]
theorem coe_cadlagAbsolutePassageLocalizerFinite
    (X : Process Omega) (n : Nat) (omega : Omega) :
    (cadlagAbsolutePassageLocalizerFinite X n omega : WithTop NNReal) =
      cadlagAbsolutePassageLocalizer X n omega :=
  WithTop.coe_untop _ (cadlagAbsolutePassageLocalizer_ne_top X n omega)

omit [MeasurableSpace Omega] in
/-- The finite passage representative stays below its deterministic
horizon. -/
theorem cadlagAbsolutePassageLocalizerFinite_le_horizon
    (X : Process Omega) (n : Nat) (omega : Omega) :
    cadlagAbsolutePassageLocalizerFinite X n omega ≤
      cadlagPassageHorizon n := by
  apply WithTop.coe_le_coe.mp
  rw [coe_cadlagAbsolutePassageLocalizerFinite]
  exact min_le_right _ _

theorem cadlagPassageLevel_monotone : Monotone cadlagPassageLevel := by
  intro n m hnm
  unfold cadlagPassageLevel
  exact_mod_cast Nat.add_le_add_right hnm 1

theorem cadlagPassageHorizon_monotone : Monotone cadlagPassageHorizon := by
  intro n m hnm
  unfold cadlagPassageHorizon
  exact_mod_cast Nat.add_le_add_right hnm 1

theorem cadlagPassageLevel_tendsto_atTop :
    Tendsto cadlagPassageLevel atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

theorem cadlagPassageHorizon_tendsto_atTop :
    Tendsto cadlagPassageHorizon atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

omit [MeasurableSpace Omega] in
/-- The canonical càdlàg passage localizer is increasing pathwise. -/
theorem cadlagAbsolutePassageLocalizer_monotone
    (X : Process Omega) (omega : Omega) :
    Monotone (fun n => cadlagAbsolutePassageLocalizer X n omega) := by
  intro n m hnm
  apply min_le_min
  · unfold absoluteStrictHittingAfter
      RightContinuousHittingTime.strictHittingAfter
    apply MeasureTheory.hittingAfter_anti
    intro x hx
    exact (cadlagPassageLevel_monotone hnm).trans_lt hx
  · exact WithTop.coe_le_coe.mpr (cadlagPassageHorizon_monotone hnm)

omit [MeasurableSpace Omega] in
/-- On every càdlàg path, the canonical absolute-passage localizer tends to
infinity.  The proof uses a compact bound on `[0, t + 1]` for each fixed
test time `t`. -/
theorem cadlagAbsolutePassageLocalizer_tendsto_top
    {X : Process Omega}
    (hRight : forall omega t,
      ContinuousWithinAt (X · omega) (Set.Ici t) t)
    (hLeft : ProcessHasLeftLimits X)
    (omega : Omega) :
    Tendsto (fun n => cadlagAbsolutePassageLocalizer X n omega)
      atTop (nhds ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro t
  let U : NNReal := t + 1
  obtain ⟨G, hG⟩ :=
    FactorialChronologicalGrid.exists_abs_le_on_Icc_of_rightContinuous_leftLimits
      (X · omega) (hRight omega) (hLeft omega) U
  have hLevel : ∀ᶠ n in atTop,
      G < cadlagPassageLevel n :=
    cadlagPassageLevel_tendsto_atTop.eventually_gt_atTop G
  have hHorizon : ∀ᶠ n in atTop,
      t < cadlagPassageHorizon n :=
    cadlagPassageHorizon_tendsto_atTop.eventually_gt_atTop t
  filter_upwards [hLevel, hHorizon] with n hnLevel hnHorizon
  unfold cadlagAbsolutePassageLocalizer
  rw [lt_min_iff]
  refine ⟨?_, by exact_mod_cast hnHorizon⟩
  by_contra hnot
  have hHitLe :
      absoluteStrictHittingAfter X (cadlagPassageLevel n) omega <=
        (t : WithTop NNReal) := le_of_not_gt hnot
  have htU : (t : WithTop NNReal) < (U : WithTop NNReal) := by
    exact_mod_cast (lt_add_one t)
  have hHitU :
      absoluteStrictHittingAfter X (cadlagPassageLevel n) omega <
        (U : WithTop NNReal) := hHitLe.trans_lt htU
  unfold absoluteStrictHittingAfter
    RightContinuousHittingTime.strictHittingAfter at hHitU
  rw [MeasureTheory.hittingAfter_lt_iff] at hHitU
  obtain ⟨u, hu, huLevel⟩ := hHitU
  have huU : u <= U := hu.2.le
  have huBound : abs (X u omega) <= G := hG u huU
  exact (not_lt_of_ge huBound) (hnLevel.trans huLevel)

/-- Strong adaptation and càdlàg paths turn the canonical absolute passages
into a genuine localizing sequence. -/
theorem cadlagAbsolutePassageLocalizer_isLocalizingSequence
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [F.IsRightContinuous]
    {mu : Measure Omega}
    {X : Process Omega}
    (hAdapted : StronglyAdapted F X)
    (hRight : forall omega t,
      ContinuousWithinAt (X · omega) (Set.Ici t) t)
    (hLeft : ProcessHasLeftLimits X) :
    ProbabilityTheory.IsLocalizingSequence F
      (cadlagAbsolutePassageLocalizer X) mu where
  isStoppingTime n :=
    (absoluteStrictHittingAfter_isStoppingTime
      hAdapted hRight (cadlagPassageLevel n)).min
        (isStoppingTime_const F (cadlagPassageHorizon n))
  mono := Filter.Eventually.of_forall fun omega =>
    cadlagAbsolutePassageLocalizer_monotone X omega
  tendsto_top := Filter.Eventually.of_forall fun omega =>
    cadlagAbsolutePassageLocalizer_tendsto_top hRight hLeft omega

end FTAPTheorem42
