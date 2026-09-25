/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopCadlagMartingaleLimit
import FTAPTheorem42.Stochastic.Decomposition.Source.ResidualGridVariationCore

/-!
# Nested-grid variation of the common-stop residual rows

The terminal convexification in the preceding modules uses one family of
weights for the martingale and residual rows.  A residual row indexed by `k`
has a variation bound on its own grid `grid T (selection k)`.  The support of
the row `v n` is contained in `{k | n ≤ k}`, so strict monotonicity of
`selection` embeds the grid at `selection n` into every grid occurring in the
convex combination.  This module transports those bounds by a finite
telescoping estimate and then applies the triangle inequality to the same
convex row.

No new weights, finite-variation version, or predictability assertion is
introduced here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

open _root_.FTAPTheorem42.FactorialChronologicalGrid

/-! ## The common package and its deterministic bound -/

def commonStoppedRowsResidualVariationBound (a J : Real) : Real :=
  (6 * (a + 4 * max J 0) + 2 * (a + 2 * max J 0)) +
    2 * (16 * (a + 4 * max J 0) + 2 * (a + 2 * max J 0))

structure CommonStoppedResidualConvexRowsNestedGridVariationData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
    (Nbar Bbar Xbar : Nat → Process Omega)
    (M : Process Omega) (cutoff : Nat → Nat) : Prop where
  cadlag : CommonStoppedRowsCadlagMartingaleLimitData endpoint v Z Nbar Bbar Xbar M cutoff
  variation_bound : ∀ n, ∀ᵐ omega ∂mu,
    commonStoppedRowsResidualGridVariation (Bbar n) T (selection n) omega ≤
      commonStoppedRowsResidualVariationBound a source.bound
  variation_bound_fixed_grid : ∀ r n, r ≤ n → ∀ᵐ omega ∂mu,
    commonStoppedRowsResidualGridVariation (Bbar n) T r omega ≤
      commonStoppedRowsResidualVariationBound a source.bound
  variation_bound_fixed_grid_eventually : ∀ r, ∀ᶠ n in atTop, ∀ᵐ omega ∂mu,
    commonStoppedRowsResidualGridVariation (Bbar n) T r omega ≤
      commonStoppedRowsResidualVariationBound a source.bound
  variation_bound_cutoff_grid : ∀ q, ∀ᵐ omega ∂mu,
    commonStoppedRowsResidualGridVariation (Bbar (cutoff q)) T q omega ≤
      commonStoppedRowsResidualVariationBound a source.bound

/-! ## Transport of one convex row -/

private theorem commonStoppedResidualConvexRow_gridVariation_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (v : ∀ n, TailConvexWeights n) (Bbar : Nat → Process Omega)
    (n : Nat) (hBbar : Bbar n = commonStoppedRowsResidualConvexRow endpoint v n)
    (omega : Omega)
    (hRows : ∀ k ∈ (v n).support,
      commonStoppedRowsResidualGridVariation
        (commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
          endpoint.alphaSeq_stopping hUsual source k) T (selection n) omega ≤
        commonStoppedRowsResidualVariationBound a source.bound) :
    commonStoppedRowsResidualGridVariation (Bbar n) T (selection n) omega ≤
      commonStoppedRowsResidualVariationBound a source.bound := by
  have hPoint : ∀ i ∈ Finset.range (size T (selection n)),
      |Bbar n ((grid T (selection n)).sampledTime (i + 1)) omega -
        Bbar n ((grid T (selection n)).sampledTime i) omega| ≤
      ∑ k ∈ (v n).support, (v n).weight k *
        |commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
            endpoint.alphaSeq_stopping hUsual source k
            ((grid T (selection n)).sampledTime (i + 1)) omega -
          commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
            endpoint.alphaSeq_stopping hUsual source k
            ((grid T (selection n)).sampledTime i) omega| := by
    intro i hi
    rw [hBbar]
    change |(v n).apply (fun k => fun omega =>
        commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
          endpoint.alphaSeq_stopping hUsual source k
          ((grid T (selection n)).sampledTime (i + 1)) omega) omega -
      (v n).apply (fun k => fun omega =>
        commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
          endpoint.alphaSeq_stopping hUsual source k
          ((grid T (selection n)).sampledTime i) omega) omega| ≤ _
    unfold TailConvexWeights.apply
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k ∈ (v n).support,
          ((v n).weight k *
              commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime (i + 1)) omega -
            (v n).weight k *
              commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime i) omega)| =
          |∑ k ∈ (v n).support, (v n).weight k *
            (commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime (i + 1)) omega -
              commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime i) omega)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ ∑ k ∈ (v n).support, |(v n).weight k *
            (commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime (i + 1)) omega -
              commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime i) omega)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ (v n).support, (v n).weight k *
            |commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime (i + 1)) omega -
              commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime i) omega| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [abs_mul, abs_of_nonneg ((v n).nonneg k hk)]
  calc
    commonStoppedRowsResidualGridVariation (Bbar n) T (selection n) omega ≤
        ∑ i ∈ Finset.range (size T (selection n)),
          ∑ k ∈ (v n).support, (v n).weight k *
            |commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime (i + 1)) omega -
              commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
                endpoint.alphaSeq_stopping hUsual source k
                ((grid T (selection n)).sampledTime i) omega| := by
      unfold commonStoppedRowsResidualGridVariation
      apply Finset.sum_le_sum
      intro i hi
      exact hPoint i hi
    _ = ∑ k ∈ (v n).support, (v n).weight k *
        commonStoppedRowsResidualGridVariation
          (commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
            endpoint.alphaSeq_stopping hUsual source k) T (selection n) omega := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.mul_sum]
      rfl
    _ ≤ ∑ k ∈ (v n).support, (v n).weight k *
        commonStoppedRowsResidualVariationBound a source.bound := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hRows k hk) ((v n).nonneg k hk)
    _ = commonStoppedRowsResidualVariationBound a source.bound := by
      rw [← Finset.sum_mul, (v n).sum_eq_one, one_mul]

/-! ## Public endpoint -/

theorem commonStoppedResidualConvexRows_nestedGridVariation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Omega} {M : Process Omega}
    {cutoff : Nat → Nat}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (hCadlag : CommonStoppedRowsCadlagMartingaleLimitData endpoint v Z Nbar Bbar Xbar M cutoff) :
    CommonStoppedResidualConvexRowsNestedGridVariationData
      endpoint
      v Z Nbar Bbar Xbar M cutoff := by
  let V := commonStoppedRowsResidualVariationBound a source.bound
  have hRow : ∀ n, ∀ᵐ omega ∂mu, ∀ k ∈ (v n).support,
      commonStoppedRowsResidualGridVariation
          (commonStoppedRowResidual u selection a endpoint.a_pos.le T alphaSeq alpha
            endpoint.alphaSeq_stopping hUsual source k) T (selection n) omega ≤ V := by
    intro n
    apply (v n).support.eventually_all.mpr
    intro k hk
    have htail : n ≤ k := (v n).tail k hk
    have hsel : selection n ≤ selection k :=
      endpoint.selection_strictMono.monotone htail
    have hNative := endpoint.data.residual_baseGridVariation k
    filter_upwards [hNative] with omega hNativeOmega
    apply commonStoppedRowsResidualGridVariation_transport T
      (selection n) (selection k) hsel omega
    simpa [commonStoppedRowsResidualGridVariation, V,
      commonStoppedRowsResidualVariationBound] using hNativeOmega
  have hSelected : ∀ n, ∀ᵐ omega ∂mu,
      commonStoppedRowsResidualGridVariation (Bbar n) T (selection n) omega ≤ V := by
    intro n
    filter_upwards [hRow n] with omega hRows
    simpa [V] using commonStoppedResidualConvexRow_gridVariation_le endpoint v Bbar
      n (hCadlag.convexification.residual_row_eq n) omega hRows
  have hFixed : ∀ r n, r ≤ n → ∀ᵐ omega ∂mu,
      commonStoppedRowsResidualGridVariation (Bbar n) T r omega ≤ V := by
    intro r n hrn
    have hsel : r ≤ selection n :=
      hrn.trans (StrictMono.id_le endpoint.selection_strictMono n)
    filter_upwards [hSelected n] with omega hOmega
    exact commonStoppedRowsResidualGridVariation_transport T r (selection n)
      hsel omega hOmega
  have hFixedEventually : ∀ r, ∀ᶠ n in atTop, ∀ᵐ omega ∂mu,
      commonStoppedRowsResidualGridVariation (Bbar n) T r omega ≤ V := by
    intro r
    filter_upwards [eventually_ge_atTop r] with n hn
    exact hFixed r n hn
  have hCutoff : ∀ q, ∀ᵐ omega ∂mu,
      commonStoppedRowsResidualGridVariation (Bbar (cutoff q)) T q omega ≤ V := by
    intro q
    exact hFixed q (cutoff q) (StrictMono.id_le hCadlag.cutoff_strictMono q)
  exact
    { cadlag := hCadlag
      variation_bound := by simpa [V] using hSelected
      variation_bound_fixed_grid := by simpa [V] using hFixed
      variation_bound_fixed_grid_eventually := by simpa [V] using hFixedEventually
      variation_bound_cutoff_grid := by simpa [V] using hCutoff }

theorem exists_commonStoppedResidualConvexRows_nestedGridVariation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (source : BoundedSemimartingaleSource S F mu)
    (T : NNReal) {eta : Real} (heta : 0 < eta) :
    ∃ (a : Real) (u : ∀ n, TailConvexWeights n)
      (selection : Nat → Nat)
      (alphaSeq : Nat → Omega → WithTop NNReal)
      (alpha : Omega → WithTop NNReal) (R : Omega → Real),
      ∃ endpoint : CommonStoppedRowsEndpoint
        (eta := eta) u selection a T alphaSeq alpha R hUsual source,
        ∃ (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
          (Nbar Bbar Xbar : Nat → Process Omega) (M : Process Omega)
          (cutoff : Nat → Nat),
          CommonStoppedResidualConvexRowsNestedGridVariationData endpoint v Z Nbar Bbar
            Xbar M cutoff := by
  obtain ⟨a, u, selection, alphaSeq, alpha, R, endpoint, v, Z,
      Nbar, Bbar, Xbar, M, cutoff, hCadlag⟩ :=
    exists_commonStoppedRows_cadlagMartingaleLimit hUsual hS source T heta
  exact ⟨a, u, selection, alphaSeq, alpha, R, endpoint, v, Z,
    Nbar, Bbar, Xbar, M, cutoff,
    commonStoppedResidualConvexRows_nestedGridVariation endpoint hCadlag⟩

end HorizonFactorialGrid

end FTAPTheorem42
