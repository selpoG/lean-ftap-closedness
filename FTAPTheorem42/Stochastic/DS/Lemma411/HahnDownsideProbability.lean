import FTAPTheorem42.Stochastic.DS.Lemma411.FiniteHahnImprovement
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessFastSubsequence

/-! # Finite-horizon downside probabilities from capped martingale bounds -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*}

/-- A strict margin on a closed horizon, together with right continuity at
its endpoint, puts the first lower passage strictly after the horizon. -/
theorem lt_lowerStrictHittingAfter_of_margin
    {X : Process Ω} (ω : Ω) (T : NNReal) {a δ : Real} (ha : a < δ)
    (hXR : ContinuousWithinAt (X · ω) (Ici T) T)
    (hBound : ∀ t, t ≤ T → -a ≤ X t ω) :
    (T : WithTop NNReal) < lowerStrictHittingAfter X δ ω := by
  have hXT : -δ < X T ω := by linarith [hBound T le_rfl]
  have hNhds := hXR.tendsto.eventually (Ioi_mem_nhds hXT)
  obtain ⟨u, hTu, hu⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hNhds
  apply lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hTu)
  apply le_of_not_gt
  intro hHit
  change hittingAfter (fun t ω => -X t ω) (Ioi δ) 0 ω < (u : WithTop NNReal) at hHit
  rw [hittingAfter_lt_iff] at hHit
  obtain ⟨t, ht, hx⟩ := hHit
  change δ < -X t ω at hx
  by_cases htT : t ≤ T
  · linarith [hBound t htT]
  · have := hu ⟨le_of_not_ge htT, ht.2⟩
    change -δ < X t ω at this
    linarith

private theorem abs_lt_of_capped_lt {X : Process Ω}
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (T : NNReal) (ω : Ω) {a : Real} (ha : 0 < a) (ha1 : a < 1)
    (hCap : FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω < a)
    {t : NNReal} (ht : t ≤ T) : |X t ω| < a := by
  have hEnv := FactorialChronologicalGrid.eFactorialRunningMaxEnvelope_abs_lt_of_capped_lt
    X T ω ha.le ha1 hCap
  have hValue := FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
    (fun t ω => |X t ω|) T (fun ω t => (hXR ω t).abs) ω ht
  exact (ENNReal.ofReal_lt_ofReal_iff ha).mp (hValue.trans_lt hEnv)

/-- Failure by `T`, including a first passage exactly at `T`, forces one
of the two capped martingale maxima to be at least `δ / 4`. -/
theorem hahnDownside_event_subset
    {N M : Process Ω}
    (hNR : ∀ ω t, ContinuousWithinAt (N · ω) (Ici t) t)
    (hMR : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t)
    (T : NNReal) {δ : Real} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    {ω | lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ ω ≤ (T : WithTop NNReal)} ⊆
      {ω | δ / 4 ≤ FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope N T ω} ∪
      {ω | δ / 4 ≤ FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope M T ω} := by
  intro ω hHit
  by_contra hUnion
  have hn : FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope N T ω < δ / 4 :=
    lt_of_not_ge fun h => hUnion (Or.inl h)
  have hm : FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope M T ω < δ / 4 :=
    lt_of_not_ge fun h => hUnion (Or.inr h)
  have hMargin : ∀ t, t ≤ T → -(δ / 2) ≤ hahnMartingaleAdvantage N M t ω := by
    intro t ht
    have hn' := abs_lt_of_capped_lt hNR T ω (by linarith : 0 < δ / 4)
      (by linarith : δ / 4 < 1) hn ht
    have hm' := abs_lt_of_capped_lt hMR T ω (by linarith : 0 < δ / 4)
      (by linarith : δ / 4 < 1) hm ht
    have hMax : max (M t ω) 0 ≤ δ / 4 := max_le (abs_lt.mp hm').2.le (by linarith)
    change -(δ / 2) ≤ N t ω - max (M t ω) 0
    linarith [(abs_lt.mp hn').1]
  exact (not_lt_of_ge hHit) (lt_lowerStrictHittingAfter_of_margin ω T (by linarith)
    ((hNR ω T).sub ((hMR ω T).max continuousWithinAt_const)) hMargin)

/-- Uniform capped expectations control the finite downside failure
probability. The estimate is independent of the later terminal horizon. -/
theorem hahnDownside_probability_le
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {N M : Process Ω}
    (hN : StronglyAdapted F N) (hM : StronglyAdapted F M)
    (hNR : ∀ ω t, ContinuousWithinAt (N · ω) (Ici t) t)
    (hMR : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t)
    (T : NNReal) {δ : Real} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {bN bM : Real}
    (hBN : (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope N T ω ∂μ) ≤ bN)
    (hBM : (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope M T ω ∂μ) ≤ bM) :
    μ.real {ω | lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ ω ≤
      (T : WithTop NNReal)} ≤ (bN + bM) / (δ / 4) := by
  let EN := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope N T
  let EM := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope M T
  have hInt (X : Process Ω) (hX : StronglyAdapted F X) :
      Integrable (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T) μ :=
    (integrable_const (1 : Real)).mono'
      ((FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
        hX T).mono (F.le T)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg X T ω)]
        exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one X T ω)
  have hMarkovN := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Eventually.of_forall fun ω =>
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg N T ω)
    (hInt N hN) (δ / 4)
  have hMarkovM := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Eventually.of_forall fun ω =>
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg M T ω)
    (hInt M hM) (δ / 4)
  have hMass : μ.real {ω | lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ ω ≤
      (T : WithTop NNReal)} ≤ μ.real {ω | δ / 4 ≤ EN ω} + μ.real {ω | δ / 4 ≤ EM ω} :=
    (measureReal_mono (hahnDownside_event_subset hNR hMR T hδ hδ1)).trans
      (measureReal_union_le _ _)
  apply (le_div_iff₀ (by linarith : 0 < δ / 4)).mpr
  have hn := hMarkovN.trans hBN
  have hm := hMarkovM.trans hBM
  have h := mul_le_mul_of_nonneg_right hMass (by linarith : 0 ≤ δ / 4)
  dsimp only [EN, EM] at h
  nlinarith only [hn, hm, h]

end FTAPTheorem42
