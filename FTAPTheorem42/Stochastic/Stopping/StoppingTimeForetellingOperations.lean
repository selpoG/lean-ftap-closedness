/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeAnnouncementRepair
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.MetricSpace.Polish

/-!
# Closure operations for foretold stopping times

This module supplies the two closure operations needed by the predictable
section argument.  First, an eventually constant sequence of foretold target
times has a foretold limit.  The proof selects one approximant from each
announcement in measure, extracts an almost-surely convergent subsequence,
and takes increasing tail infima.  Second, a foretold stopping time can be
restricted to the strict event that it precedes another foretold stopping
time.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace StoppingTimeForetelling

/-- The identity order isomorphism between mathlib's generic extended
nonnegative time and `ENNReal`.  The two types have distinct topology
instances, so this bridge must be explicit when continuity is used. -/
def timeOrderIsoENNReal : WithTop ℝ≥0 ≃o ℝ≥0∞ where
  toFun := fun t => t
  invFun := fun t => t
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_rel_iff' := Iff.rfl

/-- The order isomorphism from extended nonnegative time to the compact unit
interval. -/
noncomputable def timeOrderIsoUnitInterval : WithTop ℝ≥0 ≃o Set.Icc (0 : ℝ) 1 :=
  timeOrderIsoENNReal.trans ENNReal.orderIsoUnitIntervalBirational

/-- The compact order coordinate on extended nonnegative time. -/
noncomputable def compactCoordinate (t : WithTop ℝ≥0) : ℝ :=
  timeOrderIsoUnitInterval t

omit [MeasurableSpace Ω] in
theorem continuous_compactCoordinate : Continuous compactCoordinate :=
  continuous_subtype_val.comp
    timeOrderIsoUnitInterval.toHomeomorph.continuous

/-- The target of a foretelling sequence is itself a stopping time. -/
theorem target_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : Ω → WithTop ℝ≥0} (a : StoppingTimeForetelling ℱ τ) :
    IsStoppingTime ℱ τ := by
  have hSup : IsStoppingTime ℱ (fun ω => ⨆ n, a.time n ω) := by
    intro t
    have heq : {ω | (⨆ n, a.time n ω) ≤ (t : WithTop ℝ≥0)} =
        ⋂ n, {ω | a.time n ω ≤ (t : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, iSup_le_iff]
    rw [heq]
    exact MeasurableSet.iInter fun n => a.isStoppingTime n t
  convert hSup using 1
  funext ω
  apply le_antisymm
  · exact le_of_tendsto (a.tendsto ω)
      (Eventually.of_forall fun n => le_iSup (fun k => a.time k ω) n)
  · exact iSup_le fun n => a.le n ω

/-- Restrict a random time to an event, sending the complement to infinity. -/
noncomputable def restrictEvent
    (τ : Ω → WithTop ℝ≥0) (B : Set Ω) : Ω → WithTop ℝ≥0 :=
  by
    classical
    exact fun ω => if ω ∈ B then τ ω else ⊤

/-- A foretelling sequence remains a foretelling sequence after restriction
to an event known at time zero. -/
noncomputable def on_event
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : Ω → WithTop ℝ≥0} (a : StoppingTimeForetelling ℱ τ)
    (B : Set Ω) (hB : MeasurableSet[ℱ 0] B) :
    StoppingTimeForetelling ℱ (restrictEvent τ B) := by
  classical
  let u : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
    if ω ∈ B then a.time n ω else ⊤
  refine
    { time := fun n ω => Min.min (constApprox n ⊤) (u n ω)
      isStoppingTime := fun n t => ?_
      monotone := ?_
      le := ?_
      lt_of_ne_zero := ?_
      tendsto := ?_ }
  · have heq : {ω | Min.min (constApprox n ⊤)
          (u n ω) ≤ (t : WithTop ℝ≥0)} =
        (if constApprox n ⊤ ≤ (t : WithTop ℝ≥0) then Set.univ
          else B ∩ {ω | a.time n ω ≤ (t : WithTop ℝ≥0)}) := by
      ext ω
      by_cases hcap : constApprox n ⊤ ≤ (t : WithTop ℝ≥0)
      · rw [ite_eq_left hcap]
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, min_le_iff]
        exact Or.inl hcap
      · rw [ite_eq_right hcap]
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, min_le_iff,
          or_iff_right hcap]
        by_cases hω : ω ∈ B
        · change (if ω ∈ B then a.time n ω else ⊤) ≤
            (t : WithTop ℝ≥0) ↔ ω ∈ B ∧ a.time n ω ≤ t
          rw [ite_eq_left hω]
          simp only [hω, true_and]
        · change (if ω ∈ B then a.time n ω else ⊤) ≤
            (t : WithTop ℝ≥0) ↔ ω ∈ B ∧ a.time n ω ≤ t
          rw [ite_eq_right hω]
          simp only [WithTop.top_le_iff, WithTop.coe_ne_top, hω,
            false_and]
    rw [heq]
    split_ifs
    · exact MeasurableSet.univ
    · exact (ℱ.mono bot_le _ hB).inter (a.isStoppingTime n t)
  · intro ω n k hnk
    by_cases hω : ω ∈ B
    · simp only [u, ite_eq_left hω]
      exact min_le_min (constApprox_mono ⊤ hnk) (a.monotone ω hnk)
    · simp only [u, ite_eq_right hω, min_eq_left le_top]
      exact constApprox_mono ⊤ hnk
  · intro n ω
    by_cases hω : ω ∈ B
    · rw [restrictEvent, ite_eq_left hω]
      simp only [u, ite_eq_left hω]
      exact (min_le_right _ _).trans (a.le n ω)
    · rw [restrictEvent, ite_eq_right hω]
      exact le_top
  · intro n ω htarget
    by_cases hω : ω ∈ B
    · rw [restrictEvent, ite_eq_left hω] at htarget ⊢
      simp only [u, ite_eq_left hω]
      exact (min_le_right _ _).trans_lt (a.lt_of_ne_zero n ω htarget)
    · rw [restrictEvent, ite_eq_right hω]
      exact (min_le_left _ _).trans_lt
        (constApprox_lt_of_ne_zero n (by simp))
  · intro ω
    by_cases hω : ω ∈ B
    · rw [restrictEvent, ite_eq_left hω]
      simp only [u, ite_eq_left hω]
      simpa only [min_eq_right le_top] using
        (tendsto_constApprox ⊤).min (a.tendsto ω)
    · rw [restrictEvent, ite_eq_right hω]
      simp only [u, ite_eq_right hω, min_eq_left le_top]
      exact
        tendsto_constApprox ⊤

/-- If the target times of a sequence of foretellings are eventually equal
pointwise, their common eventual value is foretold.  A deterministic
diagonal need not converge pointwise, so the construction first chooses a
diagonal in measure and then repairs its single exceptional null set. -/
noncomputable def of_eventuallyEq
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hUsual : Filtration.UsualConditions μ ℱ)
    {τ : Ω → WithTop ℝ≥0} {τn : ℕ → Ω → WithTop ℝ≥0}
    (a : ∀ n, StoppingTimeForetelling ℱ (τn n))
    (hstable : ∀ ω, ∃ N, ∀ n ≥ N, τn n ω = τ ω) :
    StoppingTimeForetelling ℱ τ := by
  classical
  let ρ : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hρpos : ∀ n, 0 < ρ n := by
    intro n
    exact ENNReal.inv_pos.mpr (by finiteness)
  have hρzero : Tendsto ρ atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0)
    convert ENNReal.tendsto_inv_nat_nhds_zero.comp
      (tendsto_add_atTop_nat 1) using 1
    funext n
    simp
  have hinner : ∀ n, TendstoInMeasure μ
      (fun k ω => compactCoordinate ((a n).time k ω)) atTop
      (fun ω => compactCoordinate (τn n ω)) := by
    intro n
    apply tendstoInMeasure_of_tendsto_ae
    · intro k
      exact (continuous_compactCoordinate.measurable.comp
        ((a n).isStoppingTime k).measurable').aestronglyMeasurable
    · exact ae_of_all _ fun ω =>
        continuous_compactCoordinate.continuousAt.tendsto.comp
          ((a n).tendsto ω)
  have hselect : ∀ n, ∃ k,
      μ {ω | ρ n ≤ edist
        (compactCoordinate ((a n).time k ω))
        (compactCoordinate (τn n ω))} ≤ ρ n := by
    intro n
    have hconv := hinner n (ρ n) (hρpos n)
    rw [ENNReal.tendsto_atTop_zero] at hconv
    obtain ⟨k, hk⟩ := hconv (ρ n) (hρpos n)
    exact ⟨k, hk k le_rfl⟩
  choose κ hκ using hselect
  let selected : ℕ → Ω → WithTop ℝ≥0 :=
    fun n => (a n).time (κ n)
  let error : ℕ → Ω → ℝ := fun n ω =>
    compactCoordinate (selected n ω) - compactCoordinate (τn n ω)
  have herror : TendstoInMeasure μ error atTop (fun _ => 0) := by
    intro ε hε
    rw [ENNReal.tendsto_atTop_zero]
    intro δ hδ
    obtain ⟨Nε, hNε⟩ :=
      ENNReal.tendsto_atTop_zero.mp hρzero ε hε
    obtain ⟨Nδ, hNδ⟩ :=
      ENNReal.tendsto_atTop_zero.mp hρzero δ hδ
    refine ⟨Max.max Nε Nδ, ?_⟩
    intro n hn
    have hnε : Nε ≤ n := (le_max_left _ _).trans hn
    have hnδ : Nδ ≤ n := (le_max_right _ _).trans hn
    calc
      μ {ω | ε ≤ edist (error n ω) 0} ≤
          μ {ω | ρ n ≤ edist
            (compactCoordinate (selected n ω))
            (compactCoordinate (τn n ω))} := by
        apply measure_mono
        intro ω hω
        have hdist : edist (error n ω) 0 = edist
            (compactCoordinate (selected n ω))
            (compactCoordinate (τn n ω)) := by
          simp only [error, edist_dist, Real.dist_eq, sub_zero,
            abs_sub_comm]
        change ε ≤ edist (error n ω) 0 at hω
        change ρ n ≤ edist (compactCoordinate (selected n ω))
          (compactCoordinate (τn n ω))
        rw [← hdist]
        exact (hNε n hnε).trans hω
      _ ≤ ρ n := hκ n
      _ ≤ δ := hNδ n hnδ
  let ns := Classical.choose herror.exists_seq_tendsto_ae
  have hnsSpec := Classical.choose_spec herror.exists_seq_tendsto_ae
  have hnsMono : StrictMono ns := hnsSpec.1
  have herrorAE : ∀ᵐ x ∂μ,
      Tendsto (fun i => error (ns i) x) atTop (𝓝 0) := hnsSpec.2
  let chosen : ℕ → Ω → WithTop ℝ≥0 := fun n => selected (ns n)
  have hchosenStopping : ∀ n, IsStoppingTime ℱ (chosen n) :=
    fun n => (a (ns n)).isStoppingTime (κ (ns n))
  have hchosenTendsto : ∀ᵐ ω ∂μ,
      Tendsto (fun n => chosen n ω) atTop (𝓝 (τ ω)) := by
    filter_upwards [herrorAE] with ω herrorω
    obtain ⟨N, hN⟩ := hstable ω
    have hnsTop : Tendsto ns atTop atTop := hnsMono.tendsto_atTop
    have htargetEventually : (fun n => compactCoordinate (τn (ns n) ω)) =ᶠ[atTop]
        fun _ => compactCoordinate (τ ω) := by
      filter_upwards [hnsTop.eventually (eventually_ge_atTop N)] with n hn
      rw [hN (ns n) hn]
    have hcompact : Tendsto (fun n => compactCoordinate (chosen n ω))
        atTop (𝓝 (compactCoordinate (τ ω))) := by
      have hsum := herrorω.add
        (tendsto_const_nhds.congr' htargetEventually.symm)
      simpa only [error, chosen, selected, sub_add_cancel, zero_add] using hsum
    have hsubtype : Tendsto
        (fun n => timeOrderIsoUnitInterval (chosen n ω))
        atTop (𝓝 (timeOrderIsoUnitInterval (τ ω))) := by
      exact tendsto_subtype_rng.mpr hcompact
    have hinverse :=
      timeOrderIsoUnitInterval.toHomeomorph.symm.continuous.continuousAt.tendsto.comp
        hsubtype
    simpa [Function.comp_def] using hinverse
  let raw : ℕ → Ω → WithTop ℝ≥0 :=
    fun n ω => ⨅ i, chosen (i + n) ω
  have hrawStopping : ∀ n, IsStoppingTime ℱ (raw n) := by
    let : ℱ.IsRightContinuous := hUsual.rightContinuous
    intro n
    exact IsStoppingTime.iInf fun i => hchosenStopping (i + n)
  have hrawMono : ∀ ω, Monotone fun n => raw n ω := by
    intro ω
    apply monotone_nat_of_le_succ
    intro n
    apply le_iInf
    intro i
    have hle := iInf_le (fun j => chosen (j + n) ω) (i + 1)
    calc
      (⨅ j, chosen (j + n) ω) ≤ chosen ((i + 1) + n) ω := hle
      _ = chosen (i + (n + 1)) ω := by rw [Nat.add_assoc, Nat.one_add]
  have hrawLe : ∀ n ω, raw n ω ≤ τ ω := by
    intro n ω
    obtain ⟨N, hN⟩ := hstable ω
    let j := Max.max n N
    have hnsN : N ≤ ns j := (le_max_right n N).trans
      (StrictMono.id_le hnsMono j)
    have hterm : chosen j ω ≤ τ ω := by
      rw [← hN (ns j) hnsN]
      exact (a (ns j)).le (κ (ns j)) ω
    calc
      raw n ω ≤ chosen ((j - n) + n) ω :=
        iInf_le (fun i => chosen (i + n) ω) (j - n)
      _ = chosen j ω := by rw [Nat.sub_add_cancel (le_max_left n N)]
      _ ≤ τ ω := hterm
  have hrawLt : ∀ n ω, τ ω ≠ 0 → raw n ω < τ ω := by
    intro n ω hτ
    obtain ⟨N, hN⟩ := hstable ω
    let j := Max.max n N
    have hnsN : N ≤ ns j := (le_max_right n N).trans
      (StrictMono.id_le hnsMono j)
    have hterm : chosen j ω < τ ω := by
      rw [← hN (ns j) hnsN] at hτ ⊢
      exact (a (ns j)).lt_of_ne_zero (κ (ns j)) ω hτ
    calc
      raw n ω ≤ chosen ((j - n) + n) ω :=
        iInf_le (fun i => chosen (i + n) ω) (j - n)
      _ = chosen j ω := by rw [Nat.sub_add_cancel (le_max_left n N)]
      _ < τ ω := hterm
  apply StoppingTimeForetelling.of_ae hUsual raw hrawStopping
  filter_upwards [hchosenTendsto] with ω hconv
  refine ⟨hrawMono ω, (fun n => hrawLe n ω),
    (fun n => hrawLt n ω), ?_⟩
  have hlimit : (⨆ n, raw n ω) = τ ω := by
    rw [← hconv.liminf_eq, liminf_eq_iSup_iInf_of_nat']
  rw [← hlimit]
  exact tendsto_atTop_iSup (hrawMono ω)

/-- Keep `σ` on the strict event `{σ < τ}` and send its complement to
infinity. -/
noncomputable def restrictLT
    (σ τ : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => if σ ω < τ ω then σ ω else ⊤

/-- Strict restriction preserves foretelling under the usual conditions.
This is the stopping-time form of the standard closure
`S ↦ S_{\{S<T\}}` used in the predictable-section theorem. -/
noncomputable def on_lt
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hUsual : Filtration.UsualConditions μ ℱ)
    {σ τ : Ω → WithTop ℝ≥0}
    (a : StoppingTimeForetelling ℱ σ)
    (b : StoppingTimeForetelling ℱ τ) :
    StoppingTimeForetelling ℱ (restrictLT σ τ) := by
  let nonzero : Set Ω :=
    {ω | τ ω ≠ ((0 : ℝ≥0) : WithTop ℝ≥0)}
  have hnonzero : MeasurableSet[ℱ 0] nonzero := by
    have hzero := b.target_isStoppingTime.measurableSet_eq 0
    exact hzero.compl
  let c : ∀ n, StoppingTimeForetelling ℱ
      (restrictEvent (restrictLE σ (b.time n)) nonzero) :=
    fun n => (a.on_le (b.isStoppingTime n)).on_event nonzero hnonzero
  apply of_eventuallyEq hUsual c
  intro ω
  by_cases hστ : σ ω < τ ω
  · have hτ : τ ω ≠ 0 := ne_of_gt (bot_le.trans_lt hστ)
    have hevent : ∀ᶠ n in atTop, σ ω < b.time n ω :=
      (b.tendsto ω).eventually (Ioi_mem_nhds hστ)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    refine ⟨N, fun n hn => ?_⟩
    rw [restrictEvent, ite_eq_left (show ω ∈ nonzero by simpa [nonzero] using hτ),
      restrictLE, ite_eq_left (hN n hn).le, restrictLT, ite_eq_left hστ]
  · refine ⟨0, fun n _ => ?_⟩
    by_cases hτ : τ ω = 0
    · rw [restrictEvent, ite_eq_right (show ω ∉ nonzero by simpa [nonzero]),
        restrictLT, ite_eq_right hστ]
    · have hnot : ¬σ ω ≤ b.time n ω := by
        exact not_le_of_gt ((b.lt_of_ne_zero n ω hτ).trans_le
          (le_of_not_gt hστ))
      rw [restrictEvent,
        ite_eq_left (show ω ∈ nonzero by simpa [nonzero] using hτ),
        restrictLE, ite_eq_right hnot, restrictLT, ite_eq_right hστ]

end StoppingTimeForetelling

end FTAPTheorem42
