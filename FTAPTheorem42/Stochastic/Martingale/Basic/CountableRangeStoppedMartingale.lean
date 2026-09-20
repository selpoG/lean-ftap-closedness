/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Stopping

/-!
# Countable-range stopped martingales

Mathlib's continuous-index optional-sampling API handles stopping times with
countable range.  This module records the corresponding stopped-process
martingale theorem on `ℝ≥0`, with an explicit countable-range hypothesis.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
private theorem countable_range_min_const
    {τ : Ω → WithTop ℝ≥0} (hτ : (Set.range τ).Countable) (c : ℝ≥0) :
    (Set.range (fun ω => min (c : WithTop ℝ≥0) (τ ω))).Countable := by
  apply Set.Countable.mono ?_ (hτ.image (fun x => min (c : WithTop ℝ≥0) x))
  rintro _ ⟨ω, rfl⟩
  exact ⟨τ ω, ⟨ω, rfl⟩, rfl⟩

/-- A countable-range stopping time preserves strong adaptedness.  Unlike the
general continuous-time result, this needs no progressive-measurability
hypothesis: below each deterministic time the stopped process is assembled
from countably many measurable stopping-time fibers. -/
theorem StronglyAdapted.stoppedProcess_of_countableRange
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {f : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hf : StronglyAdapted ℱ f)
    (hτ : IsStoppingTime ℱ τ)
    (hτ_countable : (Set.range τ).Countable) :
    StronglyAdapted ℱ (MeasureTheory.stoppedProcess f τ) := by
  intro i
  apply Measurable.stronglyMeasurable
  intro s hs
  let R : Set (WithTop ℝ≥0) := Set.range τ ∩ Iio (i : WithTop ℝ≥0)
  have hR : R.Countable := hτ_countable.mono inter_subset_left
  have hpreimage :
      MeasureTheory.stoppedProcess f τ i ⁻¹' s =
        ({ω | (i : WithTop ℝ≥0) ≤ τ ω} ∩ f i ⁻¹' s) ∪
          ⋃ r ∈ R, ({ω | τ ω = r} ∩ f r.untopA ⁻¹' s) := by
    ext ω
    change MeasureTheory.stoppedProcess f τ i ω ∈ s ↔ _
    constructor
    · intro hfs
      by_cases hω : (i : WithTop ℝ≥0) ≤ τ ω
      · left
        rw [MeasureTheory.stoppedProcess_eq_of_le hω] at hfs
        exact ⟨hω, hfs⟩
      · have hωlt : τ ω < (i : WithTop ℝ≥0) := lt_of_not_ge hω
        right
        apply Set.mem_iUnion.2
        refine ⟨τ ω, ?_⟩
        apply Set.mem_iUnion.2
        refine ⟨⟨⟨ω, rfl⟩, hωlt⟩, ?_⟩
        rw [MeasureTheory.stoppedProcess_eq_of_ge hωlt.le] at hfs
        exact ⟨rfl, hfs⟩
    · rintro (⟨hω, hfi⟩ | hlow)
      · rw [MeasureTheory.stoppedProcess_eq_of_le hω]
        exact hfi
      · rcases Set.mem_iUnion.1 hlow with ⟨r, hlow⟩
        rcases Set.mem_iUnion.1 hlow with ⟨hrR, hτr, hfr⟩
        have hτle : τ ω ≤ (i : WithTop ℝ≥0) := by
          rw [hτr]
          exact hrR.2.le
        rw [MeasureTheory.stoppedProcess_eq_of_ge hτle, hτr]
        exact hfr
  rw [hpreimage]
  apply MeasurableSet.union
  · exact (hτ.measurableSet_ge i).inter ((hf i).measurable hs)
  · apply MeasurableSet.biUnion hR
    intro r hr
    have hrlt : r < (i : WithTop ℝ≥0) := hr.2
    have hrtop : r ≠ ⊤ := ne_top_of_lt hrlt
    lift r to ℝ≥0 using hrtop with t ht
    have hti : t ≤ i := by
      exact_mod_cast hrlt.le
    exact ((ℱ.mono hti) _
      (by simpa [ht] using
        hτ.measurableSet_eq_of_countable_range hτ_countable t)).inter
      (((hf t).mono (ℱ.mono hti)).measurable hs)

/-- Sampling a strongly adapted process at a bounded countable-range
stopping time gives a random variable strongly measurable at the
deterministic upper-bound sigma algebra. -/
theorem StronglyAdapted.stronglyMeasurable_stoppedValue_of_countableRange_filtration
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {f : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hf : StronglyAdapted ℱ f)
    (hτ : IsStoppingTime ℱ τ)
    (hτ_countable : (Set.range τ).Countable)
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) :
    StronglyMeasurable[ℱ T] (MeasureTheory.stoppedValue f τ) := by
  have hsample := FTAPTheorem42.StronglyAdapted.stoppedProcess_of_countableRange
    hf hτ hτ_countable T
  have heq : MeasureTheory.stoppedProcess f τ T =
      MeasureTheory.stoppedValue f τ := by
    ext ω
    rw [MeasureTheory.stoppedProcess_eq_of_ge (hτT ω)]
    rfl
  rw [heq] at hsample
  exact hsample

theorem martingale_stoppedProcess_of_countableRange
    {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {f : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hf : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ)
    (hτ_countable : (Set.range τ).Countable) :
    Martingale (MeasureTheory.stoppedProcess f τ) ℱ μ := by
  refine ⟨FTAPTheorem42.StronglyAdapted.stoppedProcess_of_countableRange
    hf.stronglyAdapted hτ hτ_countable, ?_⟩
  intro i j hij
  let τj : Ω → WithTop ℝ≥0 := fun ω => min (j : WithTop ℝ≥0) (τ ω)
  let σij : Ω → WithTop ℝ≥0 :=
    fun ω => min (i : WithTop ℝ≥0) (τj ω)
  have hτj : IsStoppingTime ℱ τj := by
    simpa [τj] using (isStoppingTime_const ℱ j).min hτ
  have hσij : IsStoppingTime ℱ σij := by
    simpa [σij] using (isStoppingTime_const ℱ i).min hτj
  have hτj_le : ∀ ω, τj ω ≤ (j : ℝ≥0) := by
    intro ω
    exact min_le_left _ _
  have hσij_le_τj : σij ≤ τj := by
    intro ω
    exact min_le_right _ _
  have hτj_countable : (Set.range τj).Countable := by
    exact countable_range_min_const hτ_countable j
  have hσij_countable : (Set.range σij).Countable := by
    exact countable_range_min_const hτj_countable i
  have hconst : IsStoppingTime ℱ (fun _ : Ω => (i : WithTop ℝ≥0)) :=
    isStoppingTime_const ℱ i
  have hconst_space : hconst.measurableSpace = ℱ i :=
    IsStoppingTime.measurableSpace_const ℱ i
  have hstop :=
    MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le_of_countable_range
      (ι := ℝ≥0) (f := f) (ℱ := ℱ) (μ := μ) (τ := τj) (σ := σij)
      hf hτj hσij hσij_le_τj hτj_le hτj_countable hσij_countable
  have hτj_eq : MeasureTheory.stoppedValue f τj =ᵐ[μ]
      μ[f j | hτj.measurableSpace] :=
    hf.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      hτj hτj_le hτj_countable
  have hτj_integrable : Integrable (MeasureTheory.stoppedValue f τj) μ := by
    have hcond : Integrable (μ[f j | hτj.measurableSpace]) μ := integrable_condExp
    exact hcond.congr hτj_eq.symm
  let : SigmaFinite (μ.trim hτj.measurableSpace_le) := by
    infer_instance
  have hτj_condExp_eq :
      μ[MeasureTheory.stoppedValue f τj | hτj.measurableSpace] =ᵐ[μ]
        MeasureTheory.stoppedValue f τj := by
    apply condExp_of_aestronglyMeasurable' hτj.measurableSpace_le
    · exact stronglyMeasurable_condExp.aestronglyMeasurable.congr hτj_eq.symm
    · exact hτj_integrable
  have hfirst :
      μ[MeasureTheory.stoppedValue f τj | hσij.measurableSpace] =ᵐ[
        μ.restrict {x | (i : WithTop ℝ≥0) ≤ τj x}]
        μ[MeasureTheory.stoppedValue f τj | hconst.measurableSpace] := by
    simpa [σij, IsStoppingTime.measurableSpace_min, inf_comm] using
      (condExp_min_stopping_time_ae_eq_restrict_le
        (f := MeasureTheory.stoppedValue f τj) hconst hτj)
  let A : Set Ω := {x | τj x ≤ (i : WithTop ℝ≥0)}
  have hA_meas : MeasurableSet[ℱ i] A := by
    dsimp [A]
    exact hτj.measurableSet_le i
  have hA_meas_ambient : MeasurableSet A := ℱ.le i A hA_meas
  have hσij_process :
      MeasureTheory.stoppedValue f σij =
        MeasureTheory.stoppedProcess f τ i := by
    ext ω
    change f ((σij ω).untopA) ω =
      f ((min (i : WithTop ℝ≥0) (τ ω)).untopA) ω
    congr 2
    dsimp [σij, τj]
    have hminij :
        min (i : WithTop ℝ≥0) (j : WithTop ℝ≥0) =
          (i : WithTop ℝ≥0) :=
      min_eq_left (by exact_mod_cast hij)
    calc
      min (i : WithTop ℝ≥0) (min (j : WithTop ℝ≥0) (τ ω)) =
          min (min (i : WithTop ℝ≥0) (j : WithTop ℝ≥0)) (τ ω) :=
        (min_assoc _ _ _).symm
      _ = min (i : WithTop ℝ≥0) (τ ω) := by rw [hminij]
  have hσij_stronglyMeasurable :
      StronglyMeasurable[ℱ i] (MeasureTheory.stoppedValue f σij) := by
    rw [hσij_process]
    exact FTAPTheorem42.StronglyAdapted.stoppedProcess_of_countableRange
      hf.stronglyAdapted hτ hτ_countable i
  have hA_indicator_eq :
      A.indicator (MeasureTheory.stoppedValue f τj) =
        A.indicator (MeasureTheory.stoppedValue f σij) := by
    ext x
    by_cases hx : x ∈ A
    · have hle : τj x ≤ (i : WithTop ℝ≥0) := hx
      simp only [Set.indicator_of_mem hx]
      have hσij_eq : σij x = τj x := by
        dsimp [σij]
        exact min_eq_right hle
      change f ((τj x).untopA) x = f ((σij x).untopA) x
      rw [hσij_eq]
    · simp only [Set.indicator_of_notMem hx]
  have hA_indicator_stronglyMeasurable :
      StronglyMeasurable[ℱ i]
        (A.indicator (MeasureTheory.stoppedValue f τj)) := by
    rw [hA_indicator_eq]
    exact hσij_stronglyMeasurable.indicator hA_meas
  have hA_indicator_integrable :
      Integrable (A.indicator (MeasureTheory.stoppedValue f τj)) μ := by
    exact hτj_integrable.indicator hA_meas_ambient
  have hA_condExp_indicator :
      μ[A.indicator (MeasureTheory.stoppedValue f τj) | ℱ i] =ᵐ[μ]
        A.indicator (μ[MeasureTheory.stoppedValue f τj | ℱ i]) :=
    condExp_indicator hτj_integrable hA_meas
  have hA_condExp_eq :
      μ[A.indicator (MeasureTheory.stoppedValue f τj) | ℱ i] =
        A.indicator (MeasureTheory.stoppedValue f τj) := by
    have hEq := condExp_of_stronglyMeasurable (ℱ.le i)
      hA_indicator_stronglyMeasurable hA_indicator_integrable
    exact hEq
  have hA_condExp :
      μ[MeasureTheory.stoppedValue f τj | ℱ i] =ᵐ[
        μ.restrict A] MeasureTheory.stoppedValue f τj := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hA_meas_ambient]
    have hEq :
        A.indicator (μ[MeasureTheory.stoppedValue f τj | ℱ i]) =ᵐ[μ]
          A.indicator (MeasureTheory.stoppedValue f τj) :=
      hA_condExp_indicator.symm.trans
        (Filter.Eventually.of_forall (fun x => congrFun hA_condExp_eq x))
    filter_upwards [hEq] with x hx hxA
    simpa only [Set.indicator_of_mem hxA] using hx
  have hA_condExp' :
      μ[MeasureTheory.stoppedValue f τj | hconst.measurableSpace] =ᵐ[
        μ.restrict A] MeasureTheory.stoppedValue f τj := by
    simpa only [hconst_space] using hA_condExp
  have hsecond :
      μ[MeasureTheory.stoppedValue f τj | hσij.measurableSpace] =ᵐ[
        μ.restrict {x | τj x ≤ (i : WithTop ℝ≥0)}]
        μ[MeasureTheory.stoppedValue f τj | hconst.measurableSpace] := by
    have hmin := condExp_min_stopping_time_ae_eq_restrict_le
      (μ := μ) (ℱ := ℱ) (τ := τj)
      (σ := fun _ : Ω => (i : WithTop ℝ≥0))
      (f := MeasureTheory.stoppedValue f τj) hτj hconst
    have hmin' :
        μ[MeasureTheory.stoppedValue f τj | hσij.measurableSpace] =ᵐ[
          μ.restrict {x | τj x ≤ (i : WithTop ℝ≥0)}]
          μ[MeasureTheory.stoppedValue f τj | hτj.measurableSpace] := by
      simpa only [σij, IsStoppingTime.measurableSpace_min, inf_comm] using hmin
    have hτj_condExp_ae :
        μ[MeasureTheory.stoppedValue f τj | hτj.measurableSpace] =ᵐ[μ]
          MeasureTheory.stoppedValue f τj := hτj_condExp_eq
    exact hmin'.trans ((Filter.EventuallyEq.restrict hτj_condExp_ae).trans hA_condExp'.symm)
  have hstop_target :
      MeasureTheory.stoppedValue f σij =ᵐ[μ]
        μ[MeasureTheory.stoppedValue f τj | hconst.measurableSpace] := by
    refine hstop.trans ?_
    refine ae_of_ae_restrict_of_ae_restrict_compl
      {x | (i : WithTop ℝ≥0) ≤ τj x} hfirst ?_
    apply ae_restrict_of_ae_restrict_of_subset
      (s := {x | (i : WithTop ℝ≥0) ≤ τj x}ᶜ)
      (t := {x | τj x ≤ (i : WithTop ℝ≥0)}) ?_ hsecond
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
    exact le_of_lt hx
  have hτj_process :
      MeasureTheory.stoppedValue f τj =
        MeasureTheory.stoppedProcess f τ j := by
    ext ω
    change f ((τj ω).untopA) ω =
      f ((min (j : WithTop ℝ≥0) (τ ω)).untopA) ω
    rfl
  calc
    μ[MeasureTheory.stoppedProcess f τ j | ℱ i] =ᵐ[μ]
        μ[MeasureTheory.stoppedValue f τj | hconst.measurableSpace] := by
          rw [hτj_process, hconst_space]
    _ =ᵐ[μ] MeasureTheory.stoppedValue f σij := hstop_target.symm
    _ =ᵐ[μ] MeasureTheory.stoppedProcess f τ i :=
      Filter.Eventually.of_forall (fun ω => congrFun hσij_process ω)

end FTAPTheorem42
