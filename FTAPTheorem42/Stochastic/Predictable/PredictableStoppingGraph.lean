/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import FTAPTheorem42.Stochastic.Predictable.PredictableJumpEnvelope

/-!
# Conditional-expectation control of predictable jumps

This module proves the local conditional-expectation calculation used on
each predictable stopping-time graph in Delbaen--Schachermayer Theorem 2.3.
It is independent of the construction of those graphs.
-/

namespace FTAPTheorem42

open Filter MeasureTheory

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- If `X = M + A`, the martingale term has conditional mean zero, and `A`
is measurable at the conditioning σ-algebra, then `A` is the conditional
expectation of `X`. -/
theorem condExp_ae_eq_of_add_decomposition
    {μ : Measure Ω} (m : MeasurableSpace Ω)
    (hm : m ≤ m0)
    [SigmaFinite (μ.trim (m := m) hm)]
    {X M A : Ω → ℝ}
    (hM : Integrable M μ) (hA : Integrable A μ)
    (hAmeas : StronglyMeasurable[m] A)
    (hdecomp : X =ᵐ[μ] fun ω => M ω + A ω)
    (hcondM : μ[M | m] =ᵐ[μ] fun _ => 0) :
    μ[X | m] =ᵐ[μ] A := by
  have hX : Integrable X μ := (hM.add hA).congr hdecomp.symm
  have hcondA : μ[A | m] = A :=
    condExp_of_stronglyMeasurable (μ := μ) hm hAmeas hA
  refine (condExp_congr_ae hdecomp).trans ?_
  refine (condExp_add hM hA m).trans ?_
  filter_upwards [hcondM] with ω hzero
  change μ[M | m] ω + μ[A | m] ω = A ω
  rw [hzero, congrFun hcondA ω, zero_add]

/-- Conditional Jensen bounds a predictable component by the conditional
expectation of the absolute total increment. -/
theorem abs_le_condExp_abs_of_add_decomposition
    {μ : Measure Ω} (m : MeasurableSpace Ω)
    (hm : m ≤ m0)
    [SigmaFinite (μ.trim (m := m) hm)]
    {X M A : Ω → ℝ}
    (hM : Integrable M μ) (hA : Integrable A μ)
    (hAmeas : StronglyMeasurable[m] A)
    (hdecomp : X =ᵐ[μ] fun ω => M ω + A ω)
    (hcondM : μ[M | m] =ᵐ[μ] fun _ => 0) :
    (fun ω => |A ω|) ≤ᵐ[μ] μ[(fun ω => |X ω|) | m] := by
  have hX : Integrable X μ := (hM.add hA).congr hdecomp.symm
  have hcondX := condExp_ae_eq_of_add_decomposition
    (m0 := m0) (μ := μ) (X := X) (M := M) (A := A)
    m hm hM hA hAmeas hdecomp hcondM
  have habs := abs_condExp_ae_le_condExp_abs (μ := μ) (m := m) X
  filter_upwards [hcondX, habs] with ω hcond habs
  rw [← hcond]
  exact habs

/-- A dominating integrable envelope can replace the absolute increment in
the conditional-expectation bound. -/
theorem abs_le_condExp_of_add_decomposition_of_abs_le
    {μ : Measure Ω} (m : MeasurableSpace Ω)
    (hm : m ≤ m0)
    [SigmaFinite (μ.trim (m := m) hm)]
    {X M A J : Ω → ℝ}
    (hM : Integrable M μ) (hA : Integrable A μ)
    (hJ : Integrable J μ)
    (hAmeas : StronglyMeasurable[m] A)
    (hdecomp : X =ᵐ[μ] fun ω => M ω + A ω)
    (hcondM : μ[M | m] =ᵐ[μ] fun _ => 0)
    (hXJ : (fun ω => |X ω|) ≤ᵐ[μ] J) :
    (fun ω => |A ω|) ≤ᵐ[μ] μ[J | m] := by
  have hX : Integrable X μ := (hM.add hA).congr hdecomp.symm
  exact (abs_le_condExp_abs_of_add_decomposition
      (m0 := m0) (μ := μ) (X := X) (M := M) (A := A)
      m hm hM hA hAmeas hdecomp hcondM).trans
    (condExp_mono hX.abs hJ hXJ)

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Predictable stopping graphs and sampled processes

The measurable space immediately before a predictable graph is represented
as the pullback of the predictable σ-algebra along `ω ↦ (τ ω, ω)`.  A graph
is predictable when this pullback is below the ambient measurable space.  A
predictable process sampled on such a graph is then strongly measurable with
respect to the pullback space by composition.
-/

open Filter MeasureTheory
open scoped ENNReal MeasureTheory NNReal Topology

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- Map whose image is the graph of a finite random time. -/
def stoppingGraphMap (τ : Ω → ℝ≥0) : Ω → ℝ≥0 × Ω :=
  fun ω => (τ ω, ω)

/-- Pullback of the predictable σ-algebra to a finite random-time graph. -/
@[reducible] def predictableGraphMeasurableSpace
    (ℱ : Filtration ℝ≥0 m0) (τ : Ω → ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (stoppingGraphMap τ) ℱ.predictable

/-- The graph of a finite random time as a subset of time–sample space. -/
def finiteStoppingTimeGraph (τ : Ω → ℝ≥0) : Set (ℝ≥0 × Ω) :=
  {p | p.1 = τ p.2}

/-- A genuinely predictable finite stopping time: it is a stopping time and
its graph belongs to the predictable σ-algebra. -/
def IsPredictableStoppingTime
    (ℱ : Filtration ℝ≥0 m0) (τ : Ω → ℝ≥0) : Prop :=
  IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    MeasurableSet[ℱ.predictable] (finiteStoppingTimeGraph τ)

theorem IsPredictableStoppingTime.isStoppingTime
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → ℝ≥0}
    (hτ : IsPredictableStoppingTime ℱ τ) :
    IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) :=
  hτ.1

theorem IsPredictableStoppingTime.measurableSet_graph
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → ℝ≥0}
    (hτ : IsPredictableStoppingTime ℱ τ) :
    MeasurableSet[ℱ.predictable] (finiteStoppingTimeGraph τ) :=
  hτ.2

/-- The graph map is measurable by definition when the domain carries the
pullback measurable space. -/
theorem measurable_stoppingGraphMap
    (ℱ : Filtration ℝ≥0 m0) (τ : Ω → ℝ≥0) :
    @Measurable Ω (ℝ≥0 × Ω) (predictableGraphMeasurableSpace ℱ τ)
      ℱ.predictable (stoppingGraphMap τ) :=
  comap_measurable _

/-- A finite stopping time is measurable from the ambient σ-algebra to the
predictable σ-algebra along its graph map.  On the predictable generators,
the preimages are `{τ = 0} ∩ A` and `{i < τ} ∩ A`. -/
theorem IsStoppingTime.measurable_stoppingGraphMap_predictable
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    @Measurable Ω (ℝ≥0 × Ω) m0 ℱ.predictable (stoppingGraphMap τ) := by
  apply measurable_generateFrom
  rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · have hτ0 : MeasurableSet[ℱ 0] {ω | τ ω = 0} := by
      simpa only [WithTop.coe_eq_coe] using hτ.measurableSet_eq 0
    have hpre : stoppingGraphMap τ ⁻¹' ({(0 : ℝ≥0)} ×ˢ A) =
        {ω | τ ω = 0} ∩ A := by
      ext ω
      simp [stoppingGraphMap]
    change MeasurableSet (stoppingGraphMap τ ⁻¹' ({(0 : ℝ≥0)} ×ˢ A))
    rw [hpre]
    exact ℱ.le 0 _ (hτ0.inter hA)
  · have hτi : MeasurableSet[ℱ i] {ω | i < τ ω} := by
      simpa only [Set.compl_ofPred, Set.mem_ofPred_eq, not_le,
        WithTop.coe_lt_coe] using (hτ.measurableSet_le i).compl
    have hpre : stoppingGraphMap τ ⁻¹' (Set.Ioi i ×ˢ A) =
        {ω | i < τ ω} ∩ A := by
      ext ω
      simp [stoppingGraphMap]
    rw [hpre]
    exact ℱ.le i _ (hτi.inter hA)

/-- The predictable graph pullback of every finite stopping time is below
the ambient measurable space. -/
theorem IsStoppingTime.predictableGraphMeasurableSpace_le
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    predictableGraphMeasurableSpace ℱ τ ≤ m0 := by
  change MeasurableSpace.comap (stoppingGraphMap τ) ℱ.predictable ≤ m0
  rw [← measurable_iff_comap_le]
  exact IsStoppingTime.measurable_stoppingGraphMap_predictable hτ

/-- The predictable set whose section at a later graph recovers an event
measurable at an earlier stopping time. -/
def stoppingTimeEventPredictableLift
    (σ : Ω → ℝ≥0) (B : Set Ω) : Set (ℝ≥0 × Ω) :=
  ⋃ q : ℚ, Set.Ioi (Real.toNNReal q) ×ˢ
    (B ∩ {ω | σ ω ≤ Real.toNNReal q})

/-- If finite stopping times satisfy `σ < τ` pointwise, then the stopping-time
sigma algebra at `σ` is contained in the predictable graph pullback at `τ`.
The proof inserts a rational time between the two graph times. -/
theorem IsStoppingTime.measurableSpace_le_predictableGraphMeasurableSpace_of_lt
    {ℱ : Filtration ℝ≥0 m0} {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω < τ ω) :
    hσ.measurableSpace ≤ predictableGraphMeasurableSpace ℱ τ := by
  intro B hB
  apply MeasurableSpace.measurableSet_comap.2
  refine ⟨stoppingTimeEventPredictableLift σ B, ?_, ?_⟩
  · unfold stoppingTimeEventPredictableLift
    apply MeasurableSet.iUnion
    intro q
    apply measurableSet_predictable_Ioi_prod
    have hBq := (hσ.measurableSet B).1 hB |>.2 (Real.toNNReal q)
    simpa only [WithTop.coe_le_coe] using hBq
  · ext ω
    simp only [stoppingGraphMap, stoppingTimeEventPredictableLift,
      Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_Ioi,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, hqτ, hBω, -⟩
      exact hBω
    · intro hBω
      obtain ⟨q, -, hσq, hqτ⟩ :=
        (NNReal.lt_iff_exists_rat_btwn (σ ω) (τ ω)).1 (hστ ω)
      exact ⟨q, hqτ, hBω, hσq.le⟩

/-- An event known at time `i`, restricted to `{i < σ}`, is measurable at
the stopping time `σ`. -/
theorem IsStoppingTime.measurableSet_inter_lt
    {ℱ : Filtration ℝ≥0 m0} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    {i : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ i] A) :
    MeasurableSet[hσ.measurableSpace] (A ∩ {ω | i < σ ω}) := by
  rw [hσ.measurableSet]
  constructor
  · exact ((le_iSup ℱ i) A hA).inter
      ((le_iSup ℱ i) _ (by simpa only [Set.compl_ofPred, Set.mem_ofPred_eq,
        not_le, WithTop.coe_lt_coe] using (hσ.measurableSet_le i).compl))
  · intro j
    by_cases hij : i < j
    · have hAj : MeasurableSet[ℱ j] A := ℱ.mono hij.le _ hA
      have hσgt : MeasurableSet[ℱ j] {ω | i < σ ω} :=
        ℱ.mono hij.le _ (by simpa only [Set.compl_ofPred, Set.mem_ofPred_eq,
          not_le, WithTop.coe_lt_coe] using (hσ.measurableSet_le i).compl)
      exact (hAj.inter hσgt).inter (hσ.measurableSet_le j)
    · have hempty :
          (A ∩ {ω | i < σ ω}) ∩ {ω | (σ ω : WithTop ℝ≥0) ≤ j} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        intro hleft
        exact (not_lt_of_ge (le_of_not_gt hij))
          (hleft.1.2.trans_le (WithTop.coe_le_coe.mp hleft.2))
      rw [hempty]
      exact @MeasurableSet.empty Ω (ℱ j)

/-- Predictable sets sampled at a finite stopping time are measurable in the
stopping-time σ-algebra. -/
theorem IsStoppingTime.predictableGraphMeasurableSpace_le_measurableSpace
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    predictableGraphMeasurableSpace ℱ τ ≤ hτ.measurableSpace := by
  change MeasurableSpace.comap (stoppingGraphMap τ) ℱ.predictable ≤
    hτ.measurableSpace
  rw [← measurable_iff_comap_le]
  refine @measurable_generateFrom Ω (ℝ≥0 × Ω) hτ.measurableSpace _
    (stoppingGraphMap τ) ?_
  rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · have hpre : stoppingGraphMap τ ⁻¹' (({⊥} : Set ℝ≥0) ×ˢ A) =
        A ∩ {ω | (τ ω : WithTop ℝ≥0) =
          ((0 : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [stoppingGraphMap, Set.mem_preimage, Set.mem_prod,
        Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
        WithTop.coe_eq_coe]
      tauto
    rw [hpre]
    apply (hτ.measurableSet_inter_eq_iff A 0).2
    exact hA.inter (hτ.measurableSet_eq 0)
  · have hpre : stoppingGraphMap τ ⁻¹' (Set.Ioi i ×ˢ A) =
        A ∩ {ω | i < τ ω} := by
      ext ω
      simp [stoppingGraphMap, and_comm]
    rw [hpre]
    exact IsStoppingTime.measurableSet_inter_lt hτ hA

/-- A sequence of finite stopping times strictly below `τ` and converging
pointwise to it generates the whole predictable graph pullback at `τ`. -/
theorem predictableGraphMeasurableSpace_eq_iSup_measurableSpace
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → ℝ≥0}
    {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime ℱ
      (fun ω => (σ n ω : WithTop ℝ≥0)))
    (hστ : ∀ n ω, σ n ω < τ ω)
    (htend : ∀ ω, Tendsto (fun n => σ n ω) Filter.atTop (𝓝 (τ ω))) :
    predictableGraphMeasurableSpace ℱ τ =
      ⨆ n, (hσ n).measurableSpace := by
  apply le_antisymm
  · change MeasurableSpace.comap (stoppingGraphMap τ) ℱ.predictable ≤
      ⨆ n, (hσ n).measurableSpace
    apply measurable_iff_comap_le.mp
    unfold Filtration.predictable
    refine @measurable_generateFrom Ω (ℝ≥0 × Ω)
      (⨆ n, (hσ n).measurableSpace) _ (stoppingGraphMap τ) ?_
    rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
    · have hpre : stoppingGraphMap τ ⁻¹' (({⊥} : Set ℝ≥0) ×ˢ A) = ∅ := by
        ext ω
        simp only [stoppingGraphMap, Set.mem_preimage, Set.mem_prod,
          Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hτ0, -⟩
        have hlt := hστ 0 ω
        rw [hτ0] at hlt
        exact (not_lt_of_ge bot_le) hlt
      rw [hpre]
      exact @MeasurableSet.empty Ω (⨆ n, (hσ n).measurableSpace)
    · have hpre : stoppingGraphMap τ ⁻¹' (Set.Ioi i ×ˢ A) =
          ⋃ n, A ∩ {ω | i < σ n ω} := by
        ext ω
        simp only [stoppingGraphMap, Set.mem_preimage, Set.mem_prod,
          Set.mem_Ioi, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hiτ, hAω⟩
          have hevent : ∀ᶠ n in Filter.atTop, i < σ n ω :=
            (htend ω).eventually (Ioi_mem_nhds hiτ)
          obtain ⟨n, hin⟩ := hevent.exists
          exact ⟨n, hAω, hin⟩
        · rintro ⟨n, hAω, hiσ⟩
          exact ⟨hiσ.trans (hστ n ω), hAω⟩
      rw [hpre]
      apply MeasurableSet.iUnion
      intro n
      exact (le_iSup (fun k => (hσ k).measurableSpace) n) _
        (IsStoppingTime.measurableSet_inter_lt (hσ n) hA)
  · apply iSup_le
    intro n
    exact IsStoppingTime.measurableSpace_le_predictableGraphMeasurableSpace_of_lt
      (hσ n) (hστ n)

/-- Sampling a strongly predictable process on a predictable graph is
strongly measurable at the graph pullback σ-algebra. -/
theorem IsStronglyPredictable.stronglyMeasurable_sampledGraph
    {ℱ : Filtration ℝ≥0 m0} {u : Process Ω}
    (hu : IsStronglyPredictable ℱ u) (τ : Ω → ℝ≥0) :
    StronglyMeasurable[predictableGraphMeasurableSpace ℱ τ]
      (fun ω => u (τ ω) ω) := by
  exact hu.comp_measurable (measurable_stoppingGraphMap ℱ τ)

/-- A predictable left-jump process supplies the measurability input used by
the graphwise conditional-expectation theorem. -/
theorem IsStronglyPredictable.stronglyMeasurable_sampledLeftJump
    {ℱ : Filtration ℝ≥0 m0} {A : Process Ω}
    (hjump : IsStronglyPredictable ℱ (processLeftJump A))
    (τ : Ω → ℝ≥0) :
    StronglyMeasurable[predictableGraphMeasurableSpace ℱ τ]
      (fun ω => processLeftJump A (τ ω) ω) :=
  IsStronglyPredictable.stronglyMeasurable_sampledGraph hjump τ

end FTAPTheorem42
