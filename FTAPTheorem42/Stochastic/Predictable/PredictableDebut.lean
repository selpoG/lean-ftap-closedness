/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Predictable.SetAlgebraInnerApproximation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Predictable debuts and graph announcements

This module proves the predictable-section machinery needed to turn a
predictable stopping-time graph into an actual announcing sequence.  The
first step constructs a countable essential upper envelope of all foretold
times lying below a prescribed random time.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableDebut

/-- A bounded, order-reflecting coordinate on extended nonnegative time. -/
noncomputable def compactENNCoordinate (t : WithTop ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (StoppingTimeForetelling.compactCoordinate t)

omit [MeasurableSpace Ω] in
theorem compactCoordinate_nonneg (t : WithTop ℝ≥0) :
    0 ≤ StoppingTimeForetelling.compactCoordinate t :=
  (StoppingTimeForetelling.timeOrderIsoUnitInterval t).property.1

omit [MeasurableSpace Ω] in
theorem compactCoordinate_le_one (t : WithTop ℝ≥0) :
    StoppingTimeForetelling.compactCoordinate t ≤ 1 :=
  (StoppingTimeForetelling.timeOrderIsoUnitInterval t).property.2

omit [MeasurableSpace Ω] in
theorem compactENNCoordinate_le_one (t : WithTop ℝ≥0) :
    compactENNCoordinate t ≤ 1 := by
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
  exact ENNReal.ofReal_le_ofReal (compactCoordinate_le_one t)

omit [MeasurableSpace Ω] in
theorem compactENNCoordinate_mono : Monotone compactENNCoordinate := by
  intro s t hst
  apply ENNReal.ofReal_le_ofReal
  exact StoppingTimeForetelling.timeOrderIsoUnitInterval.monotone hst

omit [MeasurableSpace Ω] in
theorem compactENNCoordinate_injective :
    Function.Injective compactENNCoordinate := by
  intro s t hst
  have hcoord : StoppingTimeForetelling.compactCoordinate s =
      StoppingTimeForetelling.compactCoordinate t :=
    (ENNReal.ofReal_eq_ofReal_iff
      (compactCoordinate_nonneg s) (compactCoordinate_nonneg t)).1 hst
  apply StoppingTimeForetelling.timeOrderIsoUnitInterval.injective
  apply Subtype.ext
  exact hcoord

omit [MeasurableSpace Ω] in
theorem measurable_compactENNCoordinate : Measurable compactENNCoordinate :=
  ENNReal.continuous_ofReal.measurable.comp
    StoppingTimeForetelling.continuous_compactCoordinate.measurable

/-- A foretold random time lying below a target almost surely. -/
structure ForetoldBelow
    (μ : Measure Ω)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (D : Ω → WithTop ℝ≥0) where
  time : Ω → WithTop ℝ≥0
  foretelling : StoppingTimeForetelling ℱ time
  le_target : time ≤ᵐ[μ] D

namespace ForetoldBelow

/-- Zero is always a foretold lower bound. -/
noncomputable def zero
    (μ : Measure Ω)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (D : Ω → WithTop ℝ≥0) : ForetoldBelow μ ℱ D where
  time := fun _ => 0
  foretelling := StoppingTimeForetelling.const ℱ 0
  le_target := Eventually.of_forall fun _ => bot_le

/-- Foretold lower bounds are closed under pointwise maximum. -/
noncomputable def max
    {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D : Ω → WithTop ℝ≥0}
    (a b : ForetoldBelow μ ℱ D) : ForetoldBelow μ ℱ D where
  time := fun ω => a.time ω ⊔ b.time ω
  foretelling := a.foretelling.max b.foretelling
  le_target := by
    filter_upwards [a.le_target, b.le_target] with ω ha hb
    exact sup_le ha hb

end ForetoldBelow

/-- The bounded score used to select a countable essential envelope. -/
noncomputable def score (μ : Measure Ω) (T : Ω → WithTop ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, compactENNCoordinate (T ω) ∂μ

theorem score_mono
    {μ : Measure Ω} {S T : Ω → WithTop ℝ≥0}
    (hST : ∀ ω, S ω ≤ T ω) : score μ S ≤ score μ T :=
  lintegral_mono fun ω => compactENNCoordinate_mono (hST ω)

theorem score_le_measure_univ
    (μ : Measure Ω) (T : Ω → WithTop ℝ≥0) :
    score μ T ≤ μ Set.univ := by
  calc
    score μ T ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ :=
      lintegral_mono fun ω => compactENNCoordinate_le_one (T ω)
    _ = μ Set.univ := by simp

/-- A foretold essential upper envelope for all foretold lower bounds of
`D`. -/
structure EssentialForetellingEnvelope
    (μ : Measure Ω)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (D : Ω → WithTop ℝ≥0) where
  time : Ω → WithTop ℝ≥0
  foretelling : StoppingTimeForetelling ℱ time
  le_target : time ≤ᵐ[μ] D
  upper : ∀ a : ForetoldBelow μ ℱ D, a.time ≤ᵐ[μ] time

/-- Every random time admits a countably generated essential envelope of
its foretold lower bounds. -/
noncomputable def essentialForetellingEnvelope
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (D : Ω → WithTop ℝ≥0) : EssentialForetellingEnvelope μ ℱ D := by
  classical
  let Candidate := ForetoldBelow μ ℱ D
  let base : Candidate := ForetoldBelow.zero μ ℱ D
  let supremumScore : ℝ≥0∞ := ⨆ a : Candidate, score μ a.time
  have hsupFinite : supremumScore ≠ ∞ := by
    have hle : supremumScore ≤ μ Set.univ :=
      iSup_le fun a => score_le_measure_univ μ a.time
    exact (hle.trans_lt IsFiniteMeasure.measure_univ_lt_top).ne
  let ε : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0)
    convert ENNReal.tendsto_inv_nat_nhds_zero.comp
      (tendsto_add_atTop_nat 1) using 1
    funext n
    simp
  have hεne : ∀ n, ε n ≠ 0 := by
    intro n
    exact ENNReal.inv_ne_zero.mpr (by finiteness)
  let selected : ℕ → Candidate := fun n =>
    if h : supremumScore - ε n < supremumScore then
      Classical.choose ((lt_iSup_iff).1 h)
    else base
  have hselectedLower : ∀ n,
      supremumScore - ε n ≤ score μ (selected n).time := by
    intro n
    by_cases h : supremumScore - ε n < supremumScore
    · have hspec := Classical.choose_spec ((lt_iSup_iff).1 h)
      simpa only [selected, dite_eq_left h] using hspec.le
    · have hsupZero : supremumScore = 0 := by
        by_contra hzero
        exact h (ENNReal.sub_lt_self hsupFinite hzero (hεne n))
      simp [hsupZero]
  let T : Ω → WithTop ℝ≥0 := fun ω => ⨆ n, (selected n).time ω
  let aT : StoppingTimeForetelling ℱ T :=
    StoppingTimeForetelling.iSup fun n => (selected n).foretelling
  have hTle : T ≤ᵐ[μ] D := by
    have hall : ∀ᵐ ω ∂μ, ∀ n, (selected n).time ω ≤ D ω :=
      ae_all_iff.2 fun n => (selected n).le_target
    filter_upwards [hall] with ω hω
    exact iSup_le hω
  let topCandidate : Candidate :=
    { time := T
      foretelling := aT
      le_target := hTle }
  have hsubTendsto : Tendsto (fun n => supremumScore - ε n)
      atTop (𝓝 supremumScore) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hεzero
      (Or.inl hsupFinite)
  have hsupLeT : supremumScore ≤ score μ T := by
    apply le_of_tendsto hsubTendsto
    exact Eventually.of_forall fun n =>
      (hselectedLower n).trans (score_mono fun ω =>
        le_iSup (fun k => (selected k).time ω) n)
  have hTScore : score μ T = supremumScore := by
    apply le_antisymm
    · exact le_iSup (fun a : Candidate => score μ a.time) topCandidate
    · exact hsupLeT
  refine
    { time := T
      foretelling := aT
      le_target := hTle
      upper := ?_ }
  intro a
  let joined : Candidate := topCandidate.max a
  have hjoinedScore : score μ joined.time ≤ score μ T := by
    calc
      score μ joined.time ≤ supremumScore :=
        le_iSup (fun b : Candidate => score μ b.time) joined
      _ = score μ T := hTScore.symm
  have hcoordLe : (fun ω => compactENNCoordinate (T ω)) ≤ᵐ[μ]
      fun ω => compactENNCoordinate (joined.time ω) :=
    Eventually.of_forall fun ω => by
      apply compactENNCoordinate_mono
      change T ω ≤ T ω ⊔ a.time ω
      exact le_sup_left
  have hTIntegralFinite : score μ T ≠ ∞ :=
    (score_le_measure_univ μ T).trans_lt
      IsFiniteMeasure.measure_univ_lt_top |>.ne
  have hjoinedMeas : AEMeasurable
      (fun ω => compactENNCoordinate (joined.time ω)) μ :=
    (measurable_compactENNCoordinate.comp
      joined.foretelling.target_isStoppingTime.measurable').aemeasurable
  have hcoordEq : (fun ω => compactENNCoordinate (T ω)) =ᵐ[μ]
      fun ω => compactENNCoordinate (joined.time ω) :=
    ae_eq_of_ae_le_of_lintegral_le hcoordLe hTIntegralFinite
      hjoinedMeas hjoinedScore
  filter_upwards [hcoordEq] with ω hω
  have htime : T ω = joined.time ω := compactENNCoordinate_injective hω
  change T ω = T ω ⊔ a.time ω at htime
  change a.time ω ≤ T ω
  exact sup_eq_left.mp htime.symm

/-! ## Debuts of countable intersections -/

/-- The upper interval anchored at a foretold random time. -/
noncomputable def upperInterval
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {T : Ω → WithTop ℝ≥0} (a : StoppingTimeForetelling ℱ T) :
    PredictableIntervalAlgebra.Interval ℱ where
  left := T
  right := fun _ => ⊤
  left_foretelling := a
  right_foretelling := StoppingTimeForetelling.const ℱ ⊤

theorem carrier_upperInterval
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {T : Ω → WithTop ℝ≥0} (a : StoppingTimeForetelling ℱ T) :
    (upperInterval a).carrier =
      PredictableIntervalAlgebra.foretoldUpperSet T := by
  ext p
  rcases p with ⟨t, ω⟩
  rw [PredictableIntervalAlgebra.Interval.mem_carrier_iff]
  change (T ω ≤ (t : WithTop ℝ≥0) ∧
      (t : WithTop ℝ≥0) < ⊤) ↔ T ω ≤ (t : WithTop ℝ≥0)
  simp only [WithTop.coe_lt_top, and_true]

omit [MeasurableSpace Ω] in
theorem debut_mono_section
    {A B : Set (ℝ≥0 × Ω)} {ω : Ω}
    (hAB : ∀ t : ℝ≥0, (t, ω) ∈ A → (t, ω) ∈ B) :
    PredictableIntervalAlgebra.debut B ω ≤
      PredictableIntervalAlgebra.debut A ω := by
  classical
  unfold PredictableIntervalAlgebra.debut
  apply le_iInf
  intro t
  by_cases ht : (t, ω) ∈ A
  · rw [ite_eq_left ht]
    exact iInf_le_of_le t (by rw [ite_eq_left (hAB t ht)])
  · rw [ite_eq_right ht]
    exact le_top

omit [MeasurableSpace Ω] in
theorem le_debut_of_forall_mem
    {A : Set (ℝ≥0 × Ω)} {ω : Ω} {s : WithTop ℝ≥0}
    (hs : ∀ t : ℝ≥0, (t, ω) ∈ A → s ≤ (t : WithTop ℝ≥0)) :
    s ≤ PredictableIntervalAlgebra.debut A ω := by
  classical
  unfold PredictableIntervalAlgebra.debut
  apply le_iInf
  intro t
  by_cases ht : (t, ω) ∈ A
  · rw [ite_eq_left ht]
    exact hs t ht
  · rw [ite_eq_right ht]
    exact le_top

/-- The debut of a countable intersection of interval-algebra carriers is
foretold and is attained almost surely whenever it is finite. -/
structure CountableIntersectionDebutData
    (μ : Measure Ω)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (L : ℕ → List (PredictableIntervalAlgebra.Interval ℱ)) where
  foretelling : StoppingTimeForetelling ℱ
    (PredictableIntervalAlgebra.debut
      (⋂ n, PredictableIntervalAlgebra.carrier (L n)))
  attained : ∀ᵐ ω ∂μ,
    ∀ hfinite : PredictableIntervalAlgebra.debut
        (⋂ n, PredictableIntervalAlgebra.carrier (L n)) ω ≠ ⊤,
      ((PredictableIntervalAlgebra.debut
          (⋂ n, PredictableIntervalAlgebra.carrier (L n)) ω).untop hfinite,
        ω) ∈ ⋂ n, PredictableIntervalAlgebra.carrier (L n)

/-- Countable interval intersections inherit the finite-union debut theorem
by anchoring every finite approximation at the essential foretold lower
envelope. -/
noncomputable def countableIntersectionDebutData
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hUsual : Filtration.UsualConditions μ ℱ)
    (L : ℕ → List (PredictableIntervalAlgebra.Interval ℱ)) :
    CountableIntersectionDebutData μ ℱ L := by
  classical
  let A : Set (ℝ≥0 × Ω) :=
    ⋂ n, PredictableIntervalAlgebra.carrier (L n)
  let D : Ω → WithTop ℝ≥0 := PredictableIntervalAlgebra.debut A
  let E : EssentialForetellingEnvelope μ ℱ D :=
    essentialForetellingEnvelope D
  let anchor : PredictableIntervalAlgebra.Interval ℱ :=
    upperInterval E.foretelling
  let K : ℕ → List (PredictableIntervalAlgebra.Interval ℱ) := fun n =>
    PredictableIntervalAlgebra.inter (L n) [anchor]
  have hcarrierK : ∀ n, PredictableIntervalAlgebra.carrier (K n) =
      PredictableIntervalAlgebra.carrier (L n) ∩
        PredictableIntervalAlgebra.foretoldUpperSet E.time := by
    intro n
    rw [PredictableIntervalAlgebra.carrier_inter]
    simp only [PredictableIntervalAlgebra.carrier_cons,
      PredictableIntervalAlgebra.carrier.eq_1, union_empty]
    exact congrArg (PredictableIntervalAlgebra.carrier (L n) ∩ ·)
      (carrier_upperInterval E.foretelling)
  let dK : ∀ n, ForetoldBelow μ ℱ D := fun n =>
    { time := PredictableIntervalAlgebra.debut
        (PredictableIntervalAlgebra.carrier (K n))
      foretelling := PredictableIntervalAlgebra.debut_foretelling hUsual (K n)
      le_target := by
        filter_upwards [E.le_target] with ω hTD
        apply debut_mono_section
        intro t ht
        rw [hcarrierK n]
        refine ⟨?_, ?_⟩
        · exact Set.mem_iInter.mp ht n
        · exact hTD.trans
            (PredictableIntervalAlgebra.debut_le_of_mem ht) }
  have hKLe : ∀ n,
      PredictableIntervalAlgebra.debut
          (PredictableIntervalAlgebra.carrier (K n)) ≤ᵐ[μ] E.time :=
    fun n => E.upper (dK n)
  have hLeK : ∀ n ω, E.time ω ≤
      PredictableIntervalAlgebra.debut
        (PredictableIntervalAlgebra.carrier (K n)) ω := by
    intro n ω
    apply le_debut_of_forall_mem
    intro t ht
    rw [hcarrierK n] at ht
    exact ht.2
  have hKEq : ∀ n,
      PredictableIntervalAlgebra.debut
          (PredictableIntervalAlgebra.carrier (K n)) =ᵐ[μ] E.time := by
    intro n
    exact Filter.EventuallyLE.antisymm (hKLe n)
      (Eventually.of_forall (hLeK n))
  have hAllKEq : ∀ᵐ ω ∂μ, ∀ n,
      PredictableIntervalAlgebra.debut
          (PredictableIntervalAlgebra.carrier (K n)) ω = E.time ω :=
    ae_all_iff.2 hKEq
  have hDEq : D =ᵐ[μ] E.time := by
    filter_upwards [E.le_target, hAllKEq] with ω hTD hEq
    by_cases hfinite : E.time ω ≠ ⊤
    · have hmemA : ((E.time ω).untop hfinite, ω) ∈ A := by
        apply Set.mem_iInter.2
        intro n
        have hKnFinite : PredictableIntervalAlgebra.debut
            (PredictableIntervalAlgebra.carrier (K n)) ω ≠ ⊤ := by
          rw [hEq n]
          exact hfinite
        have hmemK :=
          PredictableIntervalAlgebra.debut_carrier_mem_of_ne_top
            (K n) ω hKnFinite
        have hcoord :
            (PredictableIntervalAlgebra.debut
                (PredictableIntervalAlgebra.carrier (K n)) ω).untop
                hKnFinite = (E.time ω).untop hfinite := by
          apply WithTop.coe_injective
          rw [WithTop.coe_untop _ hKnFinite,
            WithTop.coe_untop _ hfinite, hEq n]
        rw [hcoord] at hmemK
        rw [hcarrierK n] at hmemK
        exact hmemK.1
      apply le_antisymm
      · calc
          D ω ≤ ((E.time ω).untop hfinite : WithTop ℝ≥0) :=
            PredictableIntervalAlgebra.debut_le_of_mem hmemA
          _ = E.time ω := WithTop.coe_untop _ hfinite
      · exact hTD
    · have htop : E.time ω = ⊤ := not_ne_iff.mp hfinite
      rw [htop]
      apply top_unique
      simpa only [htop] using hTD
  have hforetelling : StoppingTimeForetelling ℱ D := by
    apply StoppingTimeForetelling.of_ae hUsual E.foretelling.time
      E.foretelling.isStoppingTime
    filter_upwards [hDEq] with ω hEq
    refine ⟨E.foretelling.monotone ω, ?_, ?_, ?_⟩
    · intro n
      exact (E.foretelling.le n ω).trans_eq hEq.symm
    · intro n hD
      rw [hEq]
      apply E.foretelling.lt_of_ne_zero n ω
      simpa only [← hEq] using hD
    · simpa only [hEq] using E.foretelling.tendsto ω
  refine
    { foretelling := ?_
      attained := ?_ }
  · simpa only [A, D] using hforetelling
  · filter_upwards [hDEq, hAllKEq] with ω hDE hEq
    intro hfinite
    change D ω ≠ ⊤ at hfinite
    have hEFinite : E.time ω ≠ ⊤ := by
      intro htop
      apply hfinite
      rw [hDE, htop]
    have hmemA : ((E.time ω).untop hEFinite, ω) ∈ A := by
      apply Set.mem_iInter.2
      intro n
      have hKnFinite : PredictableIntervalAlgebra.debut
          (PredictableIntervalAlgebra.carrier (K n)) ω ≠ ⊤ := by
        rw [hEq n]
        exact hEFinite
      have hmemK :=
        PredictableIntervalAlgebra.debut_carrier_mem_of_ne_top
          (K n) ω hKnFinite
      have hcoord :
          (PredictableIntervalAlgebra.debut
              (PredictableIntervalAlgebra.carrier (K n)) ω).untop
              hKnFinite = (E.time ω).untop hEFinite := by
        apply WithTop.coe_injective
        rw [WithTop.coe_untop _ hKnFinite,
          WithTop.coe_untop _ hEFinite, hEq n]
      rw [hcoord] at hmemK
      rw [hcarrierK n] at hmemK
      exact hmemK.1
    have hcoord :
        (PredictableIntervalAlgebra.debut A ω).untop hfinite =
          (E.time ω).untop hEFinite := by
      apply WithTop.coe_injective
      rw [WithTop.coe_untop _ hfinite,
        WithTop.coe_untop _ hEFinite]
      exact hDE
    simpa only [A, hcoord] using hmemA

end PredictableDebut

end FTAPTheorem42
