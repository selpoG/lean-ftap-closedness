import FTAPTheorem42.Stochastic.Topology.R1.ElementaryAddTopology
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessFastSubsequence
import FTAPTheorem42.Stochastic.Topology.R1.Metric
import FTAPTheorem42.Stochastic.Process.UniformProcessLimitUniqueness

/-! # From elementary metric convergence to raw tests and ucp -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.ElementaryMetricProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [Fact (Filtration.UsualConditions μ F)]

/-- The quotient map with its codomain fixed to the elementary metric type.
This prevents inference from selecting the original R1 quotient topology. -/
noncomputable def ofR1 (X : R1Process F μ) : ElementaryMetricProcess F μ := SeparationQuotient.mk X

theorem gauge_of_tendsto (X : Nat → ElementaryMetricProcess F μ)
    (Y : ElementaryMetricProcess F μ) (hX : Tendsto X atTop (𝓝 Y)) :
    ∀ T : NNReal, ∀ ε > (0 : Real), ∀ᶠ n in atTop,
      R1Process.elementaryGauge T (X n) Y ≤ ENNReal.ofReal ε := by
  intro T ε hε
  let k := Nat.ceil T
  let w : ENNReal := (2⁻¹) ^ (k + 1)
  have hw : w ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num))
  have hRadius : 0 < w * ENNReal.ofReal ε :=
    pos_iff_ne_zero.mpr (mul_ne_zero hw (ne_of_gt (ENNReal.ofReal_pos.mpr hε)))
  filter_upwards [EMetric.tendsto_nhds.mp hX _ hRadius] with n hn
  have hT : T ≤ (k : NNReal) + 1 :=
    (Nat.le_ceil T).trans (by simp [k])
  have hTerm : w * R1Process.elementaryGauge T (X n) Y ≤ edist (X n) Y :=
    (mul_le_mul' le_rfl (R1Process.elementaryGauge_mono hT _ _)).trans
      (ENNReal.le_tsum (f := fun k : Nat => (2 : ENNReal)⁻¹ ^ (k + 1) *
      R1Process.elementaryGauge (k + 1) (X n) Y) k)
  by_contra h
  exact (not_le_of_gt hn)
    ((mul_le_mul' (le_rfl : w ≤ w) (le_of_not_ge h)).trans hTerm)

/-- The same metric recognizes elementary convergence of arbitrary raw
decomposable representatives; no pointwise regularity is imposed here. -/
theorem tendsto_mk_iff (X : Nat → R1Process F μ) (Y : R1Process F μ) :
    Tendsto (fun n => ofR1 (X n)) atTop (𝓝 (ofR1 Y)) ↔
      ElementaryEmeryConverges μ F (fun n => (X n).val) Y.val := by
  constructor
  · intro h T ε hε
    filter_upwards [gauge_of_tendsto _ _ h T ε hε] with n hn
    exact (R1Process.elementaryGauge_mk_le_iff T (X n) Y hε.le).mp hn
  · intro h
    apply tendsto_of_gauge
    intro T ε hε
    filter_upwards [h T ε hε] with n hn
    exact (R1Process.elementaryGauge_mk_le_iff T (X n) Y hε.le).mpr hn

end FTAPTheorem42.ElementaryMetricProcess

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F] [F.IsRightContinuous]

/-- The R1 maximal-tail estimate supplies the same capped ucp criterion as
the elementary metric, including for nonregular raw representatives. -/
theorem capped_ucp_of_tendsto_r1 (hUsual : Filtration.UsualConditions μ F)
    {Z : Nat → Process Ω} {X : Process Ω}
    (h : Tendsto (fun n => semimartingaleR1 (Z n - X) F μ) atTop (𝓝 0))
    (T : NNReal) :
    TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (Z n - X) T) atTop (fun _ => (0 : Real)) := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_maximal_tail_zero_of_tendsto_r1_zero hUsual h T hε)
    (fun _ => bot_le)
  intro n
  apply measure_mono
  intro w hw
  change ε ≤ edist _ (0 : Real) at hw
  rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg
    (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _)] at hw
  unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope at hw
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
    (min_le_right _ _))] at hw
  apply hw.trans ((min_le_left _ _).trans ?_)
  apply iSup_le
  intro r
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (r * r.factorial + 1)) Finset.nonempty_range_add_one
    (fun j => (FactorialChronologicalGrid.stoppedGrid T r).natSample
      (fun t w => |(Z n - X) t w|) j w)
  rw [show FactorialChronologicalGrid.factorialRunningMax
      (fun t w => |(Z n - X) t w|) T r w = _ from hk]
  have ht : (FactorialChronologicalGrid.stoppedGrid T r).sampledTime k ≤ T := by
    simp only [ChronologicalGrid.sampledTime, FactorialChronologicalGrid.stoppedGrid_time]
    exact min_le_right _ _
  exact le_iSup (fun t : Iic T => ENNReal.ofReal |(Z n - X) t.1 w|) ⟨_, ht⟩

end FTAPTheorem42

namespace FTAPTheorem42.R1Process

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [hUsual : Fact (Filtration.UsualConditions μ F)]

/-- Limits in the two topologies coincide. Regularity is supplied internally
by decomposition representatives, rather than assumed of raw process values. -/
theorem elementary_r1_limit_unique (X : Nat → R1Process F μ) (Y Z : R1Process F μ)
    (hY : ElementaryEmeryConverges μ F (fun n => (X n).val) Y.val)
    (hZ : Tendsto (fun n => semimartingaleR1 ((X n).val - Z.val) F μ)
      atTop (𝓝 0)) : ProcessIndistinguishable μ Y.val Z.val := by
  let : F.IsRightContinuous := hUsual.out.rightContinuous
  choose R hXR hRP hRR hRL hR0 using fun n => (X n).exists_regular_representative
  obtain ⟨Y', hYY', hYP, hYR, _, hY0⟩ := Y.exists_regular_representative
  obtain ⟨Z', hZZ', _, hZR, _, _⟩ := Z.exists_regular_representative
  have hY' := (hY.congr_sequence hXR).congr_limit hYY'
  have hZ' : Tendsto (fun n => semimartingaleR1 ((R n).val - Z'.val) F μ)
      atTop (𝓝 0) := by
    apply quotient_tendsto_iff.mp
    have h := quotient_tendsto_iff.mpr hZ
    have heq : (fun n => SeparationQuotient.mk (X n)) =
        (fun n => SeparationQuotient.mk (R n)) :=
      funext fun n => (quotient_eq_iff _ _).mpr (hXR n)
    rw [heq, (quotient_eq_iff _ _).mpr hZZ'] at h
    exact h
  apply hYY'.trans
  apply ProcessIndistinguishable.trans _ hZZ'.symm
  apply FactorialChronologicalGrid.processIndistinguishable_of_common_cappedFiniteHorizon_limit
    (fun n => (R n).val) Y'.val Z'.val hYR hZR
  · intro r
    exact hY'.ucp hRP hYP (fun n => Eventually.of_forall fun w => by rw [hR0, hY0]) _
  · intro r
    exact capped_ucp_of_tendsto_r1 hUsual.out hZ' _

end FTAPTheorem42.R1Process

namespace FTAPTheorem42.ElementaryMetricProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [Fact (Filtration.UsualConditions μ F)]

/-- Identity of the underlying process classes, with the R1 topology in the codomain. -/
def toR1 (X : ElementaryMetricProcess F μ) : SeparationQuotient (R1Process F μ) := X

theorem limit_unique {X : Nat → ElementaryMetricProcess F μ}
    {Y : ElementaryMetricProcess F μ} {Z : SeparationQuotient (R1Process F μ)}
    (hY : Tendsto X atTop (𝓝 Y))
    (hZ : Tendsto (fun n => toR1 (X n)) atTop (𝓝 Z)) : toR1 Y = Z := by
  choose R hR using fun n => SeparationQuotient.surjective_mk (X n)
  obtain ⟨Y', hY'⟩ := SeparationQuotient.surjective_mk Y
  obtain ⟨Z', hZ'⟩ := SeparationQuotient.surjective_mk Z
  have hE : Tendsto (fun n => ofR1 (R n)) atTop (𝓝 (ofR1 Y')) := by
    simpa only [ofR1, hR, hY'] using hY
  have hC : Tendsto (fun n => SeparationQuotient.mk (R n))
      atTop (𝓝 (SeparationQuotient.mk Z')) := by
    simpa only [hR, hZ', toR1] using hZ
  have h := (R1Process.quotient_eq_iff Y' Z').mpr
    (R1Process.elementary_r1_limit_unique R Y' Z'
      ((tendsto_mk_iff R Y').mp hE) (R1Process.quotient_tendsto_iff.mp hC))
  simpa only [hY', hZ', toR1] using h

/-- The graph is closed before invoking any open-mapping or closed-graph theorem. -/
theorem isClosed_graph_toR1 :
    IsClosed {p : ElementaryMetricProcess F μ × SeparationQuotient (R1Process F μ) |
      toR1 p.1 = p.2} := by
  apply isSeqClosed_iff_isClosed.mp
  intro u p hu hp
  have hEq : (fun n => toR1 (u n).1) = (fun n => (u n).2) := funext hu
  exact limit_unique (continuous_fst.tendsto p |>.comp hp)
    (hEq ▸ (continuous_snd.tendsto p |>.comp hp))

end FTAPTheorem42.ElementaryMetricProcess
