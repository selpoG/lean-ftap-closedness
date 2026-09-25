/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Emery.DirectTriangle

/-!
# Semimartingale inheritance for a realized Emery gain

This file is the direct fixed-time diagonal consumer for the realized Emery
carrier.  The reference row is allowed to move, but it moves slowly: the
uniformly small test is made small relative to the coefficient bound of that
row.  This is the point at which the two-sided Emery tail, rather than a
false tail against an arbitrary fixed row, is used.

Only deterministic-time convergence is proved here.  No component
`M² ⊕ A¹` convergence is inferred from Emery convergence.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

private theorem transformedDifference_rightContinuous
    (S : Process Ω)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (J : PredictableElementaryStrategy ℱ)
    (H : PredictableElementaryStrategy ℱ)
    (X : Process Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t) :
    ∀ ω t, ContinuousWithinAt
      ((fun s ω' => elementaryGain S (J.mul H) s ω' -
        elementaryGain X J s ω') · ω) (Set.Ici t) t := by
  intro ω t
  exact
    (PredictableElementaryStrategy.rightContinuous_gain S hSRight
      (J.mul H) ω t).sub
      (PredictableElementaryStrategy.rightContinuous_gain X hXRight
        J ω t)

private theorem transformedDifference_hasLeftLimits
    (S : Process Ω) (hSLeft : ProcessHasLeftLimits S)
    (J : PredictableElementaryStrategy ℱ)
    (H : PredictableElementaryStrategy ℱ)
    (X : Process Ω) (hXLeft : ProcessHasLeftLimits X) :
    ProcessHasLeftLimits
      (fun s ω => elementaryGain S (J.mul H) s ω -
        elementaryGain X J s ω) := by
  unfold ProcessHasLeftLimits
  exact
    (ElementaryStrategy.gain_hasLeftLimits S hSLeft
      (J.mul H).toElementary).sub
      (ElementaryStrategy.gain_hasLeftLimits X hXLeft J.toElementary)

theorem RealizedStrategy.transformed_gain_error_at_time_tendstoInMeasure_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (J : PredictableElementaryStrategy ℱ) (ε : ℝ) (hε : 0 ≤ ε)
    (hJ : ∀ t ω, |J.integrand t ω| ≤ ε) (T : ℝ≥0) :
    TendstoInMeasure μ
      (fun n => elementaryGain S (J.mul (H.representative n)) T -
        elementaryGain H.gain J T)
      atTop (fun _ => (0 : ℝ)) := by
  have hCapped := H.transformed_gain_error_convergence_at_horizon
    S hSRight J ε hε hJ T
  have hEnvelope : TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S (J.mul (H.representative n)) t ω -
          elementaryGain H.gain J t ω) T)
      atTop (fun _ => (0 : ℝ)) := by
    exact FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_tendstoInMeasure_zero_of_capped
      T hCapped
  have hFixed : TendstoInMeasure μ
      (fun n ω => |elementaryGain S (J.mul (H.representative n)) T ω -
        elementaryGain H.gain J T ω|)
      atTop (fun _ => (0 : ℝ)) := by
    apply tendstoInMeasure_of_nonneg_le
    · intro n ω
      refine ⟨abs_nonneg _, ?_⟩
      exact FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
        (transformedDifference_rightContinuous S hSRight J
          (H.representative n) H.gain H.gain_rightContinuous)
        (transformedDifference_hasLeftLimits S hSLeft J
          (H.representative n) H.gain H.gain_hasLeftLimits) T T le_rfl
    exact hEnvelope
  rw [MeasureTheory.tendstoInMeasure_iff_norm] at hFixed ⊢
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero, Real.norm_eq_abs,
    abs_abs] using hFixed

private theorem exists_selected_index_tendstoInMeasure_zero
    {μ : Measure Ω}
    {f : ℕ → ℕ → Ω → ℝ} (N : ℕ → ℕ)
    (h : ∀ n, TendstoInMeasure μ (fun k => f n k) atTop
      (fun _ => (0 : ℝ))) :
    ∃ k : ℕ → ℕ, (∀ n, N n ≤ k n) ∧
      TendstoInMeasure μ (fun n ω => f n (k n) ω) atTop
        (fun _ => (0 : ℝ)) := by
  classical
  let k : ℕ → ℕ := fun n =>
    max (N n) (ExistsSeqTendstoAe.seqTendstoAeSeq (h n) n)
  have hkN : ∀ n, N n ≤ k n := by
    intro n
    exact le_max_left _ _
  have hkMeasure : ∀ n,
      μ {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤
        edist (f n (k n) ω) (0 : ℝ)} ≤
        (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    exact ExistsSeqTendstoAe.seqTendstoAeSeq_spec
      (h n) n (k n) (le_max_right _ _)
  refine ⟨k, hkN, ?_⟩
  rw [MeasureTheory.tendstoInMeasure_iff_enorm]
  intro ε hε hεtop
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hPow : Tendsto
      (fun n : ℕ => (2 : ℝ≥0∞)⁻¹ ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  obtain ⟨n₀, hn₀⟩ :=
    (eventually_atTop.1
      ((tendsto_order.1 hPow).2 (min ε δ) (lt_min hε hδ)))
  refine ⟨n₀, ?_⟩
  intro n hn
  calc
    μ {x | ε ≤ ‖f n (k n) x - 0‖ₑ} ≤
        μ {x | (2 : ℝ≥0∞)⁻¹ ^ n ≤
          edist (f n (k n) x) (0 : ℝ)} := by
      apply measure_mono
      intro ω hω
      exact (hn₀ n hn).le.trans
        (min_le_left ε δ) |>.trans hω
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n := hkMeasure n
    _ ≤ δ := (hn₀ n hn).le.trans (min_le_right ε δ)

private theorem exists_slow_reference_index
    {μ : Measure Ω} {S : Process Ω}
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (J : ℕ → PredictableElementaryStrategy ℱ)
    (hJ : ElementaryIntegrandsTendstoUniformlyZero J) :
    ∃ N : ℕ → ℕ,
      Tendsto N atTop atTop ∧
        ElementaryIntegrandsTendstoUniformlyZero
          (fun n => (J n).mul (H.representative (N n))) := by
  classical
  let C : ℕ → ℝ := fun m => max (H.representativeBound m : ℝ) 1
  let η : ℕ → ℝ := fun m =>
    1 / (((m + 1 : ℕ) : ℝ) * C m)
  have hη : ∀ m, 0 < η m := by
    intro m
    dsimp [η, C]
    positivity
  choose threshold hthreshold using fun m =>
    (eventually_atTop.1 (hJ (η m) (hη m)))
  let cutoff : ℕ → ℕ := fun m =>
    Nat.rec 0 (fun j c => max c (max (threshold (j + 1)) (j + 1))) m
  have hcutoff_zero : cutoff 0 = 0 := by
    rfl
  have hcutoff_succ (m : ℕ) :
      cutoff (m + 1) =
        max (cutoff m) (max (threshold (m + 1)) (m + 1)) := by
    rfl
  have hcutoff_ge : ∀ m, m ≤ cutoff m := by
    intro m
    induction m with
    | zero => simp [cutoff]
    | succ m ih =>
        rw [hcutoff_succ]
        exact (le_max_right _ _).trans (le_max_right _ _)
  have hthreshold_cutoff : ∀ {m : ℕ}, 0 < m →
      threshold m ≤ cutoff m := by
    intro m hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [hcutoff_succ]
    exact (le_max_left _ _).trans (le_max_right _ _)
  let N : ℕ → ℕ := fun n =>
    @Nat.findGreatest (fun m => cutoff m ≤ n)
      (Classical.decPred (fun m => cutoff m ≤ n)) n
  have hN_le : ∀ n, N n ≤ n := by
    intro n
    dsimp [N]
    exact @Nat.findGreatest_le (fun m => cutoff m ≤ n)
      (Classical.decPred (fun m => cutoff m ≤ n)) n
  have hcutoff_N : ∀ n, cutoff (N n) ≤ n := by
    intro n
    dsimp [N]
    exact @Nat.findGreatest_spec 0 (fun m => cutoff m ≤ n)
      (Classical.decPred (fun m => cutoff m ≤ n)) n
      (by simp) (by simp [hcutoff_zero])
  have hN_atTop : Tendsto N atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro m
    filter_upwards [eventually_ge_atTop (cutoff m)] with n hn
    have h := @Nat.le_findGreatest m (fun j => cutoff j ≤ n)
      (Classical.decPred (fun j => cutoff j ≤ n)) n
      (hcutoff_ge m |>.trans hn) hn
    simpa [N] using h
  have hN_pos : ∀ᶠ n in atTop, 0 < N n := by
    exact hN_atTop.eventually (eventually_ge_atTop 1)
  have hthreshold_N : ∀ᶠ n in atTop,
      threshold (N n) ≤ n := by
    filter_upwards [hN_pos] with n hn
    exact (hthreshold_cutoff hn).trans (hcutoff_N n)
  have hJ_small : ∀ᶠ n in atTop,
      ∀ t ω, |(J n).integrand t ω| ≤ η (N n) := by
    filter_upwards [hthreshold_N] with n hn
    exact hthreshold (N n) n hn
  have hProduct_bound : ∀ᶠ n in atTop, ∀ t ω,
      |((J n).mul (H.representative (N n))).integrand t ω| ≤
        1 / (((N n + 1 : ℕ) : ℝ)) := by
    filter_upwards [hJ_small] with n hn
    intro t ω
    rw [PredictableElementaryStrategy.mul_integrand]
    change |(J n).integrand t ω *
      (H.representative (N n)).integrand t ω| ≤
        1 / (((N n + 1 : ℕ) : ℝ))
    rw [abs_mul]
    have hRep :
        |(H.representative (N n)).integrand t ω| ≤
          (H.representativeBound (N n) : ℝ) := by
      exact (PredictableElementaryStrategy.abs_integrand_le_coefficientAbsSum
        (H.representative (N n)) t ω).trans
        (H.representative_coefficientAbsSum_le (N n) ω)
    have hRepC :
        |(H.representative (N n)).integrand t ω| ≤ C (N n) := by
      exact hRep.trans (le_max_left _ _)
    have hηRep :
        η (N n) * |(H.representative (N n)).integrand t ω| ≤
          η (N n) * C (N n) := by
      exact mul_le_mul_of_nonneg_left hRepC (le_of_lt (hη (N n)))
    calc
      |(J n).integrand t ω| *
          |(H.representative (N n)).integrand t ω| ≤
          η (N n) *
            |(H.representative (N n)).integrand t ω| := by
        exact mul_le_mul_of_nonneg_right (hn t ω) (abs_nonneg _)
      _ ≤ η (N n) * C (N n) := hηRep
      _ = 1 / (((N n + 1 : ℕ) : ℝ)) := by
        dsimp [η]
        field_simp [show C (N n) ≠ 0 by
          dsimp [C]
          positivity]
  have hReciprocal : Tendsto
      (fun n => 1 / (((N n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hBase : Tendsto
        (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    convert hBase.comp (hN_atTop) using 1
    funext n
    rfl
  refine ⟨N, hN_atTop, ?_⟩
  intro ε hε
  filter_upwards [hProduct_bound,
    (tendsto_order.1 hReciprocal).2 ε hε] with n hn hsmall
  intro t ω
  exact (hn t ω).trans hsmall.le

theorem RealizedStrategy.gain_isSemimartingale
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω)
    (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSource : IsSemimartingale S ℱ μ)
    (H : RealizedStrategy (ℱ := ℱ) μ S) :
    IsSemimartingale H.gain ℱ μ := by
  have hGainProgressive : IsStronglyProgressive ℱ H.gain :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      H.gain_stronglyAdapted H.gain_rightContinuous
  refine ⟨?_, ?_⟩
  · intro J T
    exact ((PredictableElementaryStrategy.stronglyAdapted_gain
      H.gain hGainProgressive J T).mono (ℱ.le T)).aestronglyMeasurable
  · intro J hJ T
    have hJUnit : ∀ᶠ n in atTop,
        ∀ t ω, |(J n).integrand t ω| ≤ 1 := by
      exact hJ 1 zero_lt_one
    let Jb : ℕ → BoundedPredictableElementaryMultiplier
        (Ω := Ω) ℱ :=
      eventuallyUnitBoundedMultiplier J T
    have hJbEq : ∀ᶠ n in atTop, (Jb n).strategy = J n := by
      exact eventuallyUnitBoundedMultiplier_strategy_eq J hJUnit T
    obtain ⟨N, hN_atTop, hProduct⟩ :=
      exists_slow_reference_index H J hJ
    have hError : ∀ n, TendstoInMeasure μ
        (fun k ω =>
          elementaryGain S ((Jb n).strategy.mul
            (H.representative k)) T ω -
            elementaryGain H.gain (Jb n).strategy T ω)
        atTop (fun _ => (0 : ℝ)) := by
      intro n
      exact H.transformed_gain_error_at_time_tendstoInMeasure_zero
        S hSRight hSLeft (Jb n).strategy 1 (by norm_num)
          (Jb n).abs_integrand_le_one T
    obtain ⟨K, hKN, hErrorSelected⟩ :=
      exists_selected_index_tendstoInMeasure_zero N hError
    have hK_atTop : Tendsto K atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro m
      have hNge : ∀ᶠ n in atTop, m ≤ N n :=
        hN_atTop.eventually (eventually_ge_atTop m)
      filter_upwards [hNge] with n hn
      exact hn.trans (hKN n)
    have hPair : Tendsto (fun n => (K n, N n)) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro p
      have hKge : ∀ᶠ n in atTop, p.1 ≤ K n :=
        hK_atTop.eventually (eventually_ge_atTop p.1)
      have hNge : ∀ᶠ n in atTop, p.2 ≤ N n :=
        hN_atTop.eventually (eventually_ge_atTop p.2)
      filter_upwards [hKge, hNge] with n hk hn
      exact ⟨hk, hn⟩
    have hGauge : Tendsto
        (fun n => gauge μ S (H.representative (K n))
          (H.representative (N n)) T)
        atTop (𝓝 0) := by
      convert (H.isCauchy T).comp hPair using 1
      rfl
    have hMiddle :=
      fixedTime_testedDifference_tendstoInMeasure_zero_of_eventuallyUnitBounded_gauge_tendsto
        (μ := μ) S hS hSRight hSLeft J hJUnit
        (fun n => H.representative (K n))
        (fun n => H.representative (N n)) T hGauge
    have hErrorRaw : TendstoInMeasure μ
        (fun n ω =>
          elementaryGain S ((J n).mul (H.representative (K n))) T ω -
            elementaryGain H.gain (J n) T ω)
        atTop (fun _ => (0 : ℝ)) := by
      apply hErrorSelected.congr'
      · filter_upwards [hJbEq] with n hn
        filter_upwards [] with ω
        rw [hn]
      · exact EventuallyEq.rfl
    have hFirst : TendstoInMeasure μ
        (fun n ω =>
          elementaryGain H.gain (J n) T ω -
            elementaryGain S ((J n).mul (H.representative (K n))) T ω)
        atTop (fun _ => (0 : ℝ)) := by
      have hNeg := FTAPTheorem42.tendstoInMeasure_smul_const
        (-1 : ℝ) hErrorRaw
      simpa only [Pi.zero_apply, neg_one_mul, neg_sub, neg_zero] using hNeg
    have hSourceTerm : TendstoInMeasure μ
        (fun n ω => elementaryGain S
          ((J n).mul (H.representative (N n))) T ω)
        atTop (fun _ => (0 : ℝ)) := by
      exact hSource.2
        (fun n => (J n).mul (H.representative (N n))) hProduct T
    have hSum := tendstoInMeasure_add
      (tendstoInMeasure_add hFirst hMiddle) hSourceTerm
    have hSum' : TendstoInMeasure μ
        (fun n ω =>
          ((elementaryGain H.gain (J n) T ω -
              elementaryGain S ((J n).mul (H.representative (K n))) T ω) +
            (elementaryGain S ((J n).mul (H.representative (K n))) T ω -
              elementaryGain S ((J n).mul (H.representative (N n))) T ω)) +
            elementaryGain S ((J n).mul (H.representative (N n))) T ω)
        atTop (fun _ => (0 : ℝ)) := by
      simpa only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, add_zero] using hSum
    change TendstoInMeasure μ
      (fun n ω => elementaryGain H.gain (J n) T ω)
      atTop (fun _ => (0 : ℝ))
    refine TendstoInMeasure.congr_left ?_ hSum'
    intro n
    filter_upwards [] with ω
    ring

end PredictableElementaryEmery

end FTAPTheorem42
