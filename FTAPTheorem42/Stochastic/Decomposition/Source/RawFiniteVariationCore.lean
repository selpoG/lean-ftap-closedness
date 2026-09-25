/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.ResidualGridVariationCore
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationFactorialApproximation

/-!
# Source-independent core for raw finite-variation residuals

This module contains the algebraic residual and the purely pathwise bridges
used by both the bounded-source and envelope-specific raw finite-variation
constructions.  Source-specific adaptedness and estimates remain in their
respective modules.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

open _root_.FTAPTheorem42.FactorialChronologicalGrid

/-! ## The raw residual -/

noncomputable def commonStopRawFiniteVariation
    {S : Process Omega} (alpha : Omega → WithTop NNReal)
    (M : Process Omega) : Process Omega :=
  fun t omega => MeasureTheory.stoppedProcess S alpha t omega - S 0 omega - M t omega

/-! ## Algebraic and null-set bridges -/

omit [MeasurableSpace Omega] in
theorem commonStopRawFiniteVariation_source_decomposition
    {S : Process Omega} {alpha : Omega → WithTop NNReal}
    (M A : Process Omega)
    (hA : A = commonStopRawFiniteVariation (S := S) alpha M) :
    ∀ t omega,
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
        M t omega + A t omega := by
  intro t omega
  rw [hA]
  unfold commonStopRawFiniteVariation
  ring

theorem commonStopRawFiniteVariation_zero_ae
    {S : Process Omega}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {alpha : Omega → WithTop NNReal}
    {M : Process Omega} (hMZero : M 0 =ᵐ[mu] 0) :
    commonStopRawFiniteVariation (S := S) alpha M 0 =ᵐ[mu] 0 := by
  filter_upwards [hMZero] with omega hM
  unfold commonStopRawFiniteVariation
  rw [MeasureTheory.stoppedProcess_eq_of_le (by exact bot_le)]
  simp [hM]

/-! ## A single full-measure set on which M is constant after T -/

theorem commonStopRawFiniteVariation_martingale_constant_after_ae
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {M : Process Omega}
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMConstant : ∀ t, T ≤ t → M t =ᵐ[mu] M T) :
    ∀ᵐ omega ∂mu, ∀ t, T ≤ t → M t omega = M T omega := by
  let Mstop : Process Omega :=
    MeasureTheory.stoppedProcess M (fun _ : Omega => (T : WithTop NNReal))
  have hMstopRight : ∀ omega t, ContinuousWithinAt (Mstop · omega) (Ici t) t := by
    intro omega t
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous M hMRight omega t
  have hEqSkeleton : ∀ k, M (NNRealRightDenseSkeleton.skeleton k) =ᵐ[mu]
      Mstop (NNRealRightDenseSkeleton.skeleton k) := by
    intro k
    let s := NNRealRightDenseSkeleton.skeleton k
    by_cases hs : s ≤ T
    · filter_upwards [] with omega
      change M s omega = MeasureTheory.stoppedProcess M
        (fun _ : Omega => (T : WithTop NNReal)) s omega
      change M s omega = M (min s T) omega
      rw [min_eq_left hs]
    · have hTs : T ≤ s := le_of_not_ge hs
      filter_upwards [hMConstant s hTs] with omega hω
      change M s omega = MeasureTheory.stoppedProcess M
        (fun _ : Omega => (T : WithTop NNReal)) s omega
      change M s omega = M (min s T) omega
      rw [min_eq_right hTs]
      exact hω
  have hIndist : ProcessIndistinguishable mu M Mstop :=
    ProcessIndistinguishable.of_ae_eq_on_rightDense M Mstop
      NNRealRightDenseSkeleton.skeleton
      NNRealRightDenseSkeleton.skeleton_rightDense
      (Filter.Eventually.of_forall hMRight)
      (Filter.Eventually.of_forall hMstopRight)
      hEqSkeleton
  filter_upwards [hIndist] with omega hω
  intro t ht
  have hStop := hω t
  change M t omega = M (min t T) omega at hStop
  rw [min_eq_right ht] at hStop
  exact hStop

theorem commonStopRawFiniteVariation_constant_after_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal} {M : Process Omega}
    (hAlphaLeT : ∀ omega, alpha omega ≤ (T : WithTop NNReal))
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMConstant : ∀ t, T ≤ t → M t =ᵐ[mu] M T) :
    ∀ᵐ omega ∂mu, ∀ t, T ≤ t →
      commonStopRawFiniteVariation (S := S) alpha M t omega =
        commonStopRawFiniteVariation (S := S) alpha M T omega := by
  have hMAll := commonStopRawFiniteVariation_martingale_constant_after_ae
    (F := F) (mu := mu) (T := T) (M := M) hMRight hMConstant
  filter_upwards [hMAll] with omega hM
  intro t ht
  unfold commonStopRawFiniteVariation
  have hαt : alpha omega ≤ (t : WithTop NNReal) :=
    (hAlphaLeT omega).trans (WithTop.coe_le_coe.mpr ht)
  rw [MeasureTheory.stoppedProcess_eq_of_ge hαt,
    MeasureTheory.stoppedProcess_eq_of_ge (hAlphaLeT omega), hM t ht,
    hM T le_rfl]

/-! ## Pure finite-grid bridges -/

omit [MeasurableSpace Omega] in
theorem commonStopRawFiniteVariation_grid_sum_tendsto
    {A : Process Omega} {Bbar : Nat → Process Omega} {cutoff : Nat → Nat}
    {T : NNReal}
    {omega : Omega}
    (hUniform : TendstoUniformlyOn
      (fun q t => Bbar (cutoff q) t omega) (fun t => A t omega)
      atTop (Iic T))
    (r : Nat) :
    Tendsto
      (fun q => commonStoppedRowsResidualGridVariation (Bbar (cutoff q)) T r omega)
      atTop (𝓝 (commonStoppedRowsResidualGridVariation A T r omega)) := by
  unfold commonStoppedRowsResidualGridVariation
  apply tendsto_finsetSum
  intro i hi
  have hiN : i < size T r := Finset.mem_range.mp hi
  have hi0 : (grid T r).sampledTime i ≤ T := by
    exact ((grid T r).sampledTime_mono hiN.le).trans_eq
      (sampledTime_size T r)
  have hi1 : (grid T r).sampledTime (i + 1) ≤ T := by
    exact ((grid T r).sampledTime_mono (Nat.succ_le_iff.mpr hiN)).trans_eq
      (sampledTime_size T r)
  have h0 := hUniform.tendsto_at (show (grid T r).sampledTime i ∈ Iic T from hi0)
  have h1 := hUniform.tendsto_at (show (grid T r).sampledTime (i + 1) ∈ Iic T from hi1)
  have hsub := (h1.sub h0).abs
  simpa only [Pi.sub_apply] using hsub

omit [MeasurableSpace Omega] in
theorem commonStopRawFiniteVariation_eGridVariation_le_grid
    {A : Process Omega} (T : NNReal) (r : Nat) (omega : Omega) :
    FiniteVariationFactorialApproximation.eGridVariation (A · omega) T r ≤
      ENNReal.ofReal
        (commonStoppedRowsResidualGridVariation A T (max r (Nat.ceil T)) omega) := by
  let q := max r (Nat.ceil T)
  let m := HorizonFactorialGrid.factorialRatio r q
  let N := r * r.factorial
  let j : Nat → Nat := fun i => m * min i (size T r)
  have hrq : r ≤ q := Nat.le_max_left _ _
  have hj : MonotoneOn j (Set.Iic N) := by
    intro i hi k hk hik
    dsimp [j]
    exact Nat.mul_le_mul_left m (min_le_min_right _ hik)
  have hjN : j N ≤ size T q := by
    dsimp [j]
    calc
      m * min N (size T r) ≤ m * size T r :=
        Nat.mul_le_mul_left m (Nat.min_le_right _ _)
      _ = size T q := HorizonFactorialGrid.factorialRatio_mul_size T r q hrq
  let f : Nat → Real := fun k =>
    A ((HorizonFactorialGrid.grid T q).sampledTime k) omega
  have hpoint : ∀ i, FiniteVariationFactorialApproximation.point T r i =
      (HorizonFactorialGrid.grid T q).sampledTime (j i) := by
    intro i
    by_cases hi : i ≤ size T r
    · have he := HorizonFactorialGrid.factorialGridEmbedding_sampledTime
          T r q hrq i hi
      have hpr := (show (HorizonFactorialGrid.grid T r).sampledTime i =
          FiniteVariationFactorialApproximation.point T r i by
        simp [HorizonFactorialGrid.grid, ChronologicalGrid.sampledTime,
          ChronologicalGrid.natIndex, hi,
          FiniteVariationFactorialApproximation.point])
      calc
        FiniteVariationFactorialApproximation.point T r i =
            (HorizonFactorialGrid.grid T r).sampledTime i := hpr.symm
        _ = (HorizonFactorialGrid.grid T q).sampledTime
            (HorizonFactorialGrid.factorialGridEmbedding T r q hrq
              ⟨i, Nat.lt_succ_of_le hi⟩) := he.symm
        _ = (HorizonFactorialGrid.grid T q).sampledTime (j i) := by
          congr 1
          dsimp [j, m, HorizonFactorialGrid.factorialGridEmbedding]
          simp [hi]
    · have hi' : size T r < i := Nat.lt_of_not_ge hi
      have hsize := (show
          FiniteVariationFactorialApproximation.point T r (size T r) = T by
        unfold FiniteVariationFactorialApproximation.point
          HorizonFactorialGrid.size
        rw [min_eq_right]
        apply (le_div_iff₀ (by positivity)).2
        calc
          T * (r.factorial : NNReal) ≤
              (Nat.ceil T : NNReal) * (r.factorial : NNReal) :=
            mul_le_mul_of_nonneg_right (Nat.le_ceil T) (by positivity)
          _ = (size T r : NNReal) := by simp [HorizonFactorialGrid.size])
      have hmono := FiniteVariationFactorialApproximation.point_monotone T r
        (Nat.le_of_lt hi')
      have hpi : FiniteVariationFactorialApproximation.point T r i = T := by
        apply le_antisymm
        · exact (FiniteVariationFactorialApproximation.point_mem_Icc T r i).2
        · simpa [hsize] using hmono
      have he := HorizonFactorialGrid.factorialGridEmbedding_sampledTime
          T r q hrq (size T r) (Nat.le_refl _)
      calc
        FiniteVariationFactorialApproximation.point T r i = T := hpi
        _ = (HorizonFactorialGrid.grid T r).sampledTime (size T r) :=
          (by symm; exact HorizonFactorialGrid.sampledTime_size T r)
        _ = (HorizonFactorialGrid.grid T q).sampledTime
            (HorizonFactorialGrid.factorialGridEmbedding T r q hrq
              ⟨size T r, Nat.lt_succ_of_le (Nat.le_refl _)⟩) := he.symm
        _ = (HorizonFactorialGrid.grid T q).sampledTime (j i) := by
          congr 1
          dsimp [j, m, HorizonFactorialGrid.factorialGridEmbedding]
          simp [Nat.le_of_lt hi']
  have hsum := FiniteVariationFactorialApproximation.sum_edist_comp_le_range_sum_edist
    f hj hjN
  calc
    FiniteVariationFactorialApproximation.eGridVariation (A · omega) T r =
        ∑ i ∈ Finset.range N,
          edist (A (FiniteVariationFactorialApproximation.point T r (i + 1)) omega)
            (A (FiniteVariationFactorialApproximation.point T r i) omega) := by
      rfl
    _ = ∑ i ∈ Finset.range N, edist (f (j (i + 1))) (f (j i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hpoint (i + 1), hpoint i]
    _ ≤ ∑ k ∈ Finset.range (size T q), edist (f (k + 1)) (f k) := hsum
    _ = ENNReal.ofReal
        (commonStoppedRowsResidualGridVariation A T q omega) := by
      change (∑ k ∈ Finset.range (size T q), edist (f (k + 1)) (f k)) =
        ENNReal.ofReal
          (∑ k ∈ Finset.range (size T q),
            |A ((HorizonFactorialGrid.grid T q).sampledTime (k + 1)) omega -
              A ((HorizonFactorialGrid.grid T q).sampledTime k) omega|)
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      apply Finset.sum_congr rfl
      intro k _
      simp [f, edist_dist, Real.dist_eq, abs_sub_comm]

/-- Uniform convergence of one coordinate identifies the complementary residual. -/
theorem commonStopRawFiniteVariation_residual_tendstoUniformlyOn_ae
    {mu : Measure Omega} {S M A : Process Omega}
    {alpha : Omega → WithTop NNReal} {T : NNReal}
    {Nbar Bbar : Nat → Process Omega} {cutoff : Nat → Nat}
    (hRows : ∀ᵐ omega ∂mu,
      TendstoUniformlyOn (fun q t => Nbar (cutoff q) t omega)
        (fun t => M t omega) atTop (Iic T))
    (hDecomp : ∀ q t omega,
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
        Nbar q t omega + Bbar q t omega)
    (hA : A = commonStopRawFiniteVariation (S := S) alpha M) :
    ∀ᵐ omega ∂mu,
      TendstoUniformlyOn (fun q t => Bbar (cutoff q) t omega)
        (fun t => A t omega) atTop (Iic T) := by
  filter_upwards [hRows] with omega hω
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  have hK := (Metric.tendstoUniformlyOn_iff.mp hω) epsilon hepsilon
  filter_upwards [hK] with q hq
  intro t ht
  have hq' := hq t ht
  have hDec := hDecomp (cutoff q) t omega
  rw [Real.dist_eq] at hq' ⊢
  rw [hA]
  change |MeasureTheory.stoppedProcess S alpha t omega - S 0 omega -
    M t omega - Bbar (cutoff q) t omega| < epsilon
  have hEq :
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega -
        M t omega - Bbar (cutoff q) t omega =
      Nbar (cutoff q) t omega - M t omega := by
    rw [hDec]
    ring
  rw [hEq]
  simpa [abs_sub_comm] using hq'

/-- Nested-grid variation bounds pass to a compact-uniform limit. -/
theorem commonStopRawFiniteVariation_grid_variation_bound_ae
    {mu : Measure Omega} {T : NNReal} {A : Process Omega}
    {Bbar : Nat → Process Omega} {cutoff : Nat → Nat} {V : Omega → Real}
    (hBound : ∀ q, ∀ᵐ omega ∂mu,
      commonStoppedRowsResidualGridVariation (Bbar (cutoff q)) T q omega ≤ V omega)
    (hUniform : ∀ᵐ omega ∂mu,
      TendstoUniformlyOn (fun q t => Bbar (cutoff q) t omega)
        (fun t => A t omega) atTop (Iic T)) :
    ∀ᵐ omega ∂mu, ∀ r,
      commonStoppedRowsResidualGridVariation A T r omega ≤ V omega := by
  have hGridFixed : ∀ r, ∀ᵐ omega ∂mu, ∀ᶠ q in atTop,
      commonStoppedRowsResidualGridVariation (Bbar (cutoff q)) T r omega ≤
        V omega := by
    intro r
    have hAll : ∀ᵐ omega ∂mu, ∀ q, r ≤ q →
        commonStoppedRowsResidualGridVariation (Bbar (cutoff q)) T r omega ≤
          V omega := by
      rw [ae_all_iff]
      intro q
      by_cases hRq : r ≤ q
      · filter_upwards [hBound q] with omega hBound
        intro _
        exact commonStoppedRowsResidualGridVariation_transport T r q hRq omega hBound
      · exact Filter.Eventually.of_forall (fun omega h => (hRq h).elim)
    filter_upwards [hAll] with omega hOmega
    filter_upwards [eventually_ge_atTop r] with q hq
    exact hOmega q hq
  rw [ae_all_iff]
  intro r
  filter_upwards [hUniform, hGridFixed r] with omega hω hRows
  have hlim := commonStopRawFiniteVariation_grid_sum_tendsto hω r
  exact le_of_tendsto hlim hRows

end HorizonFactorialGrid

end FTAPTheorem42
