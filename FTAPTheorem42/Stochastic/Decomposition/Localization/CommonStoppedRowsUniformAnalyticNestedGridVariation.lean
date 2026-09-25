/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsUniformAnalyticLimit
import FTAPTheorem42.Stochastic.Decomposition.Source.ResidualGridVariationCore

/-!
# Nested-grid variation for the source-independent residual rows

The residual control in the common analytic interface is transported from a
row's own factorial grid to every coarser grid.  The same tail weights are
then used to control the convex residual rows.  This module records only
finite-grid variation; it does not assert continuous-time total variation.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

open _root_.FTAPTheorem42.FactorialChronologicalGrid

structure CommonStoppedRowsUniformAnalyticNestedGridVariationData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    (data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop
      selection N B V L hUsual)
    (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
    (Nbar Bbar Xbar : Nat → Process Omega)
    (M : Process Omega) (cutoff : Nat → Nat) : Prop where
  cadlag :
    CommonStoppedRowsUniformAnalyticCadlagMartingaleLimitData data v Z Nbar Bbar Xbar
      M cutoff
  variation_bound : ∀ n, ∀ᵐ omega ∂mu,
    commonStoppedRowsResidualGridVariation (Bbar n) T (selection n) omega ≤ V omega
  variation_bound_fixed_grid : ∀ r n, r ≤ n → ∀ᵐ omega ∂mu,
    commonStoppedRowsResidualGridVariation (Bbar n) T r omega ≤ V omega
  variation_bound_fixed_grid_eventually : ∀ r, ∀ᶠ n in atTop, ∀ᵐ omega ∂mu,
    commonStoppedRowsResidualGridVariation (Bbar n) T r omega ≤ V omega
  variation_bound_cutoff_grid : ∀ q, ∀ᵐ omega ∂mu,
    commonStoppedRowsResidualGridVariation (Bbar (cutoff q)) T q omega ≤ V omega

private theorem uniformAnalyticResidualConvexRow_gridVariation_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    (data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop
      selection N B V L hUsual)
    (v : ∀ n, TailConvexWeights n) (Bbar : Nat → Process Omega)
    (n : Nat) (hBbar : Bbar n = commonStoppedRowsUniformAnalyticResidualConvexRow data v n)
    (omega : Omega)
    (hRows : ∀ k ∈ (v n).support,
      commonStoppedRowsResidualGridVariation (B k) T (selection n) omega ≤
        V omega) :
    commonStoppedRowsResidualGridVariation (Bbar n) T (selection n) omega ≤
      V omega := by
  have hPoint : ∀ i ∈ Finset.range (size T (selection n)),
      |Bbar n ((grid T (selection n)).sampledTime (i + 1)) omega -
        Bbar n ((grid T (selection n)).sampledTime i) omega| ≤
      ∑ k ∈ (v n).support, (v n).weight k *
        |B k ((grid T (selection n)).sampledTime (i + 1)) omega -
          B k ((grid T (selection n)).sampledTime i) omega| := by
    intro i hi
    rw [hBbar]
    change |(v n).apply (fun k => fun omega =>
        B k ((grid T (selection n)).sampledTime (i + 1)) omega) omega -
      (v n).apply (fun k => fun omega =>
        B k ((grid T (selection n)).sampledTime i) omega) omega| ≤ _
    unfold TailConvexWeights.apply
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k ∈ (v n).support,
          ((v n).weight k * B k ((grid T (selection n)).sampledTime (i + 1)) omega -
            (v n).weight k * B k ((grid T (selection n)).sampledTime i) omega)| =
          |∑ k ∈ (v n).support, (v n).weight k *
            (B k ((grid T (selection n)).sampledTime (i + 1)) omega -
              B k ((grid T (selection n)).sampledTime i) omega)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ ∑ k ∈ (v n).support, |(v n).weight k *
            (B k ((grid T (selection n)).sampledTime (i + 1)) omega -
              B k ((grid T (selection n)).sampledTime i) omega)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ (v n).support, (v n).weight k *
            |B k ((grid T (selection n)).sampledTime (i + 1)) omega -
              B k ((grid T (selection n)).sampledTime i) omega| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [abs_mul, abs_of_nonneg ((v n).nonneg k hk)]
  calc
    commonStoppedRowsResidualGridVariation (Bbar n) T (selection n) omega ≤
        ∑ i ∈ Finset.range (size T (selection n)),
          ∑ k ∈ (v n).support, (v n).weight k *
            |B k ((grid T (selection n)).sampledTime (i + 1)) omega -
              B k ((grid T (selection n)).sampledTime i) omega| := by
      unfold commonStoppedRowsResidualGridVariation
      apply Finset.sum_le_sum
      intro i hi
      exact hPoint i hi
    _ = ∑ k ∈ (v n).support, (v n).weight k *
        commonStoppedRowsResidualGridVariation (B k) T (selection n) omega := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.mul_sum]
      rfl
    _ ≤ ∑ k ∈ (v n).support, (v n).weight k * V omega := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hRows k hk) ((v n).nonneg k hk)
    _ = V omega := by
      rw [← Finset.sum_mul, (v n).sum_eq_one, one_mul]

theorem commonStoppedRowsUniformAnalytic_nestedGridVariation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    (data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop
      selection N B V L hUsual)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Omega} {M : Process Omega}
    {cutoff : Nat → Nat}
    (hCadlag : CommonStoppedRowsUniformAnalyticCadlagMartingaleLimitData
      data v Z Nbar Bbar Xbar M cutoff) :
    CommonStoppedRowsUniformAnalyticNestedGridVariationData
      data v Z Nbar Bbar Xbar M cutoff := by
  have hRow : ∀ n, ∀ᵐ omega ∂mu, ∀ k ∈ (v n).support,
      commonStoppedRowsResidualGridVariation (B k) T (selection n) omega ≤
        V omega := by
    intro n
    apply (v n).support.eventually_all.mpr
    intro k hk
    have htail : n ≤ k := (v n).tail k hk
    have hsel : selection n ≤ selection k :=
      data.selection_strictMono.monotone htail
    have hNative := data.residual_baseGridVariation k
    filter_upwards [hNative] with omega hNativeOmega
    apply commonStoppedRowsResidualGridVariation_transport T
      (selection n) (selection k) hsel omega
    simpa [commonStoppedRowsResidualGridVariation] using hNativeOmega
  have hSelected : ∀ n, ∀ᵐ omega ∂mu,
      commonStoppedRowsResidualGridVariation (Bbar n) T (selection n) omega ≤
        V omega := by
    intro n
    filter_upwards [hRow n] with omega hRows
    exact uniformAnalyticResidualConvexRow_gridVariation_le data v Bbar n
      (hCadlag.convexification.residual_row_eq n) omega hRows
  have hFixed : ∀ r n, r ≤ n → ∀ᵐ omega ∂mu,
      commonStoppedRowsResidualGridVariation (Bbar n) T r omega ≤ V omega := by
    intro r n hrn
    have hsel : r ≤ selection n := hrn.trans (StrictMono.id_le data.selection_strictMono n)
    filter_upwards [hSelected n] with omega hOmega
    exact commonStoppedRowsResidualGridVariation_transport T r (selection n)
      hsel omega hOmega
  have hFixedEventually : ∀ r, ∀ᶠ n in atTop, ∀ᵐ omega ∂mu,
      commonStoppedRowsResidualGridVariation (Bbar n) T r omega ≤ V omega := by
    intro r
    filter_upwards [eventually_ge_atTop r] with n hn
    exact hFixed r n hn
  have hCutoff : ∀ q, ∀ᵐ omega ∂mu,
      commonStoppedRowsResidualGridVariation (Bbar (cutoff q)) T q omega ≤
        V omega := by
    intro q
    exact hFixed q (cutoff q) (StrictMono.id_le hCadlag.cutoff_strictMono q)
  exact
    { cadlag := hCadlag
      variation_bound := hSelected
      variation_bound_fixed_grid := hFixed
      variation_bound_fixed_grid_eventually := hFixedEventually
      variation_bound_cutoff_grid := hCutoff }

end HorizonFactorialGrid

end FTAPTheorem42
