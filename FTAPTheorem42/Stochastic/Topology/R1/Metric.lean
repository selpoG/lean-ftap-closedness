/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.R1.LocalMaximal
import FTAPTheorem42.Stochastic.Topology.R1.Triangle
import FTAPTheorem42.Stochastic.Topology.R1.Separation

/-! # Vanishing r1 cost implies uniform convergence in probability on compact horizons -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

theorem J1Decomposition.aemeasurable_maximal (D : J1Decomposition X F mu) (T : NNReal) :
    AEMeasurable (fun w => ⨆ t : Iic T, ENNReal.ofReal |X t.1 w|) mu := by
  let Y : Process Ω := fun t w => D.N t w + D.A t w
  have hMeas : Measurable (fun w => ENNReal.ofReal
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope Y T w)) :=
    (((FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      (D.adaptedN.add D.adaptedA) T).mono (F.le T)).measurable).ennreal_ofReal
  apply hMeas.aemeasurable.congr
  filter_upwards [D.decomposition] with w hw
  rw [FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup (X := Y)
    (fun w t => (D.rightN w t).add (D.rightA w t)) (D.leftN.add D.leftA)]
  apply iSup_congr
  intro t
  rw [hw t.1]

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]

theorem tendsto_maximal_tail_zero_of_summable_r1
    (hUsual : Filtration.UsualConditions mu F) {Z : Nat → Process Ω}
    (hSum : (∑' k, semimartingaleR1 (Z k) F mu) ≠ ∞)
    (T : NNReal) {e : ENNReal} (he : 0 < e) :
    Tendsto (fun k => mu {w | e ≤ ⨆ t : Iic T, ENNReal.ofReal |Z k t.1 w|}) atTop (𝓝 0) := by
  let M : Nat → Ω → ENNReal := fun k w => ⨆ t : Iic T, ENNReal.ofReal |Z k t.1 w|
  have hMeas : ∀ k, AEStronglyMeasurable (fun w => (M k w).toReal) mu := by
    intro k
    have hSmall : semimartingaleR1 (Z k) F mu < ∞ :=
      lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hSum
        (ENNReal.le_tsum (f := fun k => semimartingaleR1 (Z k) F mu) k))
    obtain ⟨D, _⟩ := iInf_lt_iff.mp hSmall
    exact (D.aemeasurable_maximal T).ennreal_toReal.aestronglyMeasurable
  have hPath : ∀ᵐ w ∂mu, Tendsto (fun k => (M k w).toReal) atTop (𝓝 (0 : Real)) := by
    filter_upwards [ae_tendsto_maximal_zero_of_summable_r1 hUsual hSum] with w hw
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hw T)
  have hConv := (tendstoInMeasure_of_tendsto_ae hMeas hPath) e he
  apply hConv.congr'
  apply Eventually.of_forall
  intro k
  apply measure_congr
  filter_upwards [ae_tsum_maximal_ne_top_of_summable_r1 hUsual hSum] with w hw
  have hFinite : M k w ≠ ∞ := ne_top_of_le_ne_top (hw T) (ENNReal.le_tsum (f := fun k => M k w) k)
  change (e ≤ edist (M k w).toReal (0 : Real)) = (e ≤ M k w)
  simp only [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hFinite]

theorem tendsto_maximal_tail_zero_of_tendsto_r1_zero
    (hUsual : Filtration.UsualConditions mu F) {Z : Nat → Process Ω}
    (hZero : Tendsto (fun k => semimartingaleR1 (Z k) F mu) atTop (𝓝 0))
    (T : NNReal) {e : ENNReal} (he : 0 < e) :
    Tendsto (fun k => mu {w | e ≤ ⨆ t : Iic T, ENNReal.ofReal |Z k t.1 w|}) atTop (𝓝 0) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨f, _, hSum⟩ := exists_strictMono_summable_r1_of_tendsto_zero (hZero.comp hns)
  exact ⟨f, tendsto_maximal_tail_zero_of_summable_r1 hUsual
    (ne_top_of_le_ne_top (by norm_num) hSum) T he⟩

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## The r1 metric on decomposable processes modulo indistinguishability -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- All targets admitting a regular zero-initial local-martingale/FV decomposition. -/
structure R1Process
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (mu : Measure Ω) where
  val : Process Ω
  property : Nonempty (J1Decomposition val F mu)

namespace R1Process

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [hUsual : Fact (Filtration.UsualConditions mu F)]

theorem sub_cost_ne_top (X Y : R1Process F mu) : semimartingaleR1 (X.val - Y.val) F mu ≠ ∞ := by
  obtain ⟨D⟩ := X.property
  obtain ⟨E⟩ := Y.property
  apply (semimartingaleR1_ne_top_iff_decomposition hUsual.out).mpr
  simpa only [sub_eq_add_neg] using (show Nonempty (J1Decomposition (X.val + -Y.val) F mu) from
    ⟨D.add E.neg⟩)

noncomputable instance : PseudoMetricSpace (R1Process F mu) where
  dist X Y := (semimartingaleR1 (X.val - Y.val) F mu).toReal
  dist_self X := by simp only [sub_self, semimartingaleR1_zero, ENNReal.toReal_zero]
  dist_comm X Y := by
    have hEq : X.val - Y.val = -(Y.val - X.val) := by abel
    rw [hEq, semimartingaleR1_neg]
  dist_triangle X Y Z := by
    have hEq : X.val - Z.val = (X.val - Y.val) + (Y.val - Z.val) := by abel
    have hLe : semimartingaleR1 (X.val - Z.val) F mu ≤
        semimartingaleR1 (X.val - Y.val) F mu + semimartingaleR1 (Y.val - Z.val) F mu := by
      rw [hEq]
      exact semimartingaleR1_add_le hUsual.out
    exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨sub_cost_ne_top X Y,
      sub_cost_ne_top Y Z⟩) hLe).trans_eq
        (ENNReal.toReal_add (sub_cost_ne_top X Y) (sub_cost_ne_top Y Z))
  edist X Y := semimartingaleR1 (X.val - Y.val) F mu
  edist_dist X Y := (ENNReal.ofReal_toReal (sub_cost_ne_top X Y)).symm

theorem edist_eq (X Y : R1Process F mu) :
    edist X Y = semimartingaleR1 (X.val - Y.val) F mu := rfl

theorem quotient_eq_iff (X Y : R1Process F mu) :
    SeparationQuotient.mk X = SeparationQuotient.mk Y ↔
      ProcessIndistinguishable mu X.val Y.val := by
  let : F.IsRightContinuous := hUsual.out.rightContinuous
  rw [SeparationQuotient.mk_eq_mk, EMetric.inseparable_iff, edist_eq]
  exact semimartingaleR1_sub_eq_zero_iff hUsual.out

theorem quotient_edist_eq (X Y : R1Process F mu) :
    edist (SeparationQuotient.mk X) (SeparationQuotient.mk Y) =
      semimartingaleR1 (X.val - Y.val) F mu := by
  rw [SeparationQuotient.edist_mk, edist_eq]

theorem quotient_tendsto_iff {Z : Nat → R1Process F mu} {X : R1Process F mu} :
    Tendsto (fun k => SeparationQuotient.mk (Z k)) atTop (𝓝 (SeparationQuotient.mk X)) ↔
      Tendsto (fun k => semimartingaleR1 ((Z k).val - X.val) F mu) atTop (𝓝 0) := by
  rw [tendsto_iff_edist_tendsto_0]
  simp only [quotient_edist_eq]

end R1Process

end FTAPTheorem42

namespace FTAPTheorem42.R1Process

/-! ## Common summable component witnesses for Cauchy sequences in the r1 quotient -/

open Filter MeasureTheory Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [hUsual : Fact (Filtration.UsualConditions mu F)] {Z : Nat → R1Process F mu}

theorem exists_strictMono_summable_differences_of_cauchy
    (h : CauchySeq (fun k => SeparationQuotient.mk (Z k))) :
    ∃ f : Nat → Nat, StrictMono f ∧
      (∑' k, semimartingaleR1 ((Z (f (k + 1))).val - (Z (f k)).val) F mu) ≤ 1 := by
  obtain ⟨b, hBound, hZero⟩ := EMetric.cauchySeq_iff_le_tendsto_0.mp h
  have hEventually (k : Nat) : ∀ᶠ n in atTop, b n < (2 : ENNReal)⁻¹ ^ (k + 1) :=
    hZero.eventually (gt_mem_nhds
      (ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _))
  obtain ⟨f, hf, hSmall⟩ := extraction_forall_of_eventually hEventually
  refine ⟨f, hf, ?_⟩
  calc
    _ ≤ ∑' k : Nat, (2 : ENNReal)⁻¹ ^ (k + 1) := by
      apply ENNReal.tsum_le_tsum
      intro k
      have hLe := hBound (f (k + 1)) (f k) (f k) (hf.monotone (Nat.le_succ k)) le_rfl
      rw [quotient_edist_eq] at hLe
      exact hLe.trans (hSmall k).le
    _ = 1 := by
      rw [ENNReal.tsum_geometric_add_one]
      norm_num
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

open SIntegrableFiniteVariationBridge

end FTAPTheorem42.R1Process
