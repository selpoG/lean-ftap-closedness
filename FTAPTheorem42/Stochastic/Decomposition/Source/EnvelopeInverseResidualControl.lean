/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.EnvelopeNativeResidualControl

/-!
# Inverse residual control under an `L²` envelope

This module consumes the native residual and inverse martingale certificates
on the same dependent data.  It records only finite-grid variation and
horizon running-supremum estimates, both before and after the already chosen
common stop.  No new coefficients, rows, or stopping times are selected.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

noncomputable def envelopeInverseResidualRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (r : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal)
    (alphaSeq : Omega → WithTop NNReal)
    (hAlphaSeqStop : IsStoppingTime F alphaSeq) : Process Omega :=
  envelopeRowInverseResidualGain (S := S) (F := F) (mu := mu)
    u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop

theorem envelopeRowInverseResidualGain_baseGrid_increment_eq_block
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (k : Nat) (hk : k < size T n) (omega : Omega) :
    envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
        ((grid T n).sampledTime (k + 1)) omega -
      envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
        ((grid T n).sampledTime k) omega =
      ∑ j ∈ Finset.range (factorialRatio n (rowCommonLevel u n)),
        rowInverseCoefficient u n a T S F mu alpha
            (factorialRatio n (rowCommonLevel u n) * k + j) omega *
          (envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
              ((grid T (rowCommonLevel u n)).sampledTime
                (factorialRatio n (rowCommonLevel u n) * k + j + 1)) omega -
            envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
              ((grid T (rowCommonLevel u n)).sampledTime
                (factorialRatio n (rowCommonLevel u n) * k + j)) omega) := by
  let q := rowCommonLevel u n
  let m := factorialRatio n q
  let N := size T n
  let L := size T q
  let G := grid T q
  let H := grid T n
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
  have hnq : n ≤ q := by
    dsimp [q]
    exact rowCommonLevel_ge_self u n
  have hmpos : 0 < m := by
    dsimp [m]
    exact factorialRatio_pos n q hnq
  have hsize : m * N = L := by
    dsimp [m, N, L, q]
    exact factorialRatio_mul_size T n (rowCommonLevel u n) hnq
  have hkN : k ≤ N := hk.le
  have hk1N : k + 1 ≤ N := Nat.succ_le_iff.mpr hk
  have hmk : m * k ≤ L := by
    rw [← hsize]
    exact Nat.mul_le_mul_left m hkN
  have hmk1 : m * (k + 1) ≤ L := by
    rw [← hsize]
    exact Nat.mul_le_mul_left m hk1N
  have htime0 : G.sampledTime (m * k) = H.sampledTime k := by
    dsimp [G, H, m, q]
    simpa [factorialGridEmbedding] using
      (factorialGridEmbedding_sampledTime T n (rowCommonLevel u n)
        hnq k hkN)
  have htime1 : G.sampledTime (m * (k + 1)) = H.sampledTime (k + 1) := by
    dsimp [G, H, m, q]
    simpa [factorialGridEmbedding] using
      (factorialGridEmbedding_sampledTime T n (rowCommonLevel u n)
        hnq (k + 1) hk1N)
  have hleft : G.sampledTime (m * k) ≤ H.sampledTime (k + 1) := by
    rw [htime0]
    exact H.sampledTime_mono (Nat.le_succ k)
  have hright : H.sampledTime (k + 1) ≤ G.sampledTime (m * k + m) := by
    rw [show m * k + m = m * (k + 1) by rw [Nat.mul_succ], htime1]
  have hBlock := martingaleIntegralProcess_diff_eq_block G K M
    (H.sampledTime (k + 1)) (m * k) m hmk1 hleft hright omega
  change G.martingaleIntegralProcess K M (H.sampledTime (k + 1)) omega -
      G.martingaleIntegralProcess K M (H.sampledTime k) omega = _
  rw [← htime0, hBlock]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j < m := Finset.mem_range.mp hj
  have hjL : m * k + j < L := by
    calc
      m * k + j < m * k + m := Nat.add_lt_add_left hjm _
      _ = m * (k + 1) := by rw [Nat.mul_succ]
      _ ≤ L := hmk1
  have hK := rowInverseCoefficientProcess_at_sampledTime
    (S := S) (F := F) (mu := mu) u n a T alpha (m * k + j) hjL omega
  have htime_j : G.sampledTime (m * k + j) ≤ H.sampledTime (k + 1) := by
    exact (G.sampledTime_mono
      (Nat.add_le_add_left (Nat.le_of_lt hjm) (m * k))).trans_eq htime1
  have htime_j1 : G.sampledTime (m * k + j + 1) ≤ H.sampledTime (k + 1) := by
    exact (G.sampledTime_mono
      (Nat.add_le_add_left (Nat.succ_le_iff.mpr hjm) (m * k))).trans_eq htime1
  dsimp [K, M]
  rw [hK, min_eq_right htime_j1, min_eq_right htime_j]

theorem envelopeRowInverseResidualGain_baseGridVariation_le_of_bounds
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    {a : Real} (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    {VT CT : Real} (CB VB : Omega → Real) (hCT : 0 ≤ CT)
    (hCB : ∀ omega, 0 ≤ CB omega)
    (hCoeffVar : ∀ omega,
      (∑ i ∈ Finset.range (size T (rowCommonLevel u n)),
        |rowInverseCoefficient u n a T S F mu alpha (i + 1) omega -
          rowInverseCoefficient u n a T S F mu alpha i omega|) ≤ VT)
    (hCoeffBound : ∀ i omega,
      |rowInverseCoefficient u n a T S F mu alpha i omega| ≤ CT)
    (hResidualSup : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T t omega| ≤ CB omega)
    (hResidualVar : ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
            ((grid T n).sampledTime k) omega|) ≤ VB omega) :
    ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
            ((grid T n).sampledTime k) omega|) ≤
        2 * CB omega * VT + CT * VB omega := by
  have hInc : ∀ k, k < size T n → ∀ omega,
      envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
          ((grid T n).sampledTime (k + 1)) omega -
        envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
          ((grid T n).sampledTime k) omega =
      ∑ j ∈ Finset.range (factorialRatio n (rowCommonLevel u n)),
        rowInverseCoefficient u n a T S F mu alpha
            (factorialRatio n (rowCommonLevel u n) * k + j) omega *
          (envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
              ((grid T (rowCommonLevel u n)).sampledTime
                (factorialRatio n (rowCommonLevel u n) * k + j + 1)) omega -
            envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
              ((grid T (rowCommonLevel u n)).sampledTime
                (factorialRatio n (rowCommonLevel u n) * k + j)) omega) := by
    intro k hk omega
    exact envelopeRowInverseResidualGain_baseGrid_increment_eq_block
      u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop k hk omega
  have hIncAll : ∀ᵐ omega ∂mu, ∀ k ∈ Finset.range (size T n),
      envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
          ((grid T n).sampledTime (k + 1)) omega -
        envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
          ((grid T n).sampledTime k) omega =
      ∑ j ∈ Finset.range (factorialRatio n (rowCommonLevel u n)),
        rowInverseCoefficient u n a T S F mu alpha
            (factorialRatio n (rowCommonLevel u n) * k + j) omega *
          (envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
              ((grid T (rowCommonLevel u n)).sampledTime
                (factorialRatio n (rowCommonLevel u n) * k + j + 1)) omega -
            envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
              ((grid T (rowCommonLevel u n)).sampledTime
                (factorialRatio n (rowCommonLevel u n) * k + j)) omega) := by
    apply ae_all_iff.2
    intro k
    by_cases hk : k < size T n
    · filter_upwards [] with omega
      intro _hk
      exact hInc k hk omega
    · exact Filter.Eventually.of_forall (fun _omega hk' => (hk (Finset.mem_range.mp hk')).elim)
  filter_upwards [hResidualSup, hResidualVar, hIncAll] with omega hSup hVar hIncOmega
  let q := rowCommonLevel u n
  let m := factorialRatio n q
  let N := size T n
  let L := size T q
  let f : Nat → Real := fun i => rowInverseCoefficient u n a T S F mu alpha i omega
  let g : Nat → Real := fun i =>
    envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
      ((grid T q).sampledTime i) omega
  have hnq : n ≤ q := by
    dsimp [q]
    exact rowCommonLevel_ge_self u n
  have hmpos : 0 < m := by
    dsimp [m]
    exact factorialRatio_pos n q hnq
  have hsize : m * N = L := by
    dsimp [m, N, L, q]
    exact factorialRatio_mul_size T n (rowCommonLevel u n) hnq
  have hF : (∑ i ∈ Finset.range (m * N), |f (i + 1) - f i|) ≤ VT := by
    simpa [f, L, q, hsize] using hCoeffVar omega
  have hG : (∑ k ∈ Finset.range N,
      |g (m * (k + 1)) - g (m * k)|) ≤ VB omega := by
    calc
      (∑ k ∈ Finset.range N, |g (m * (k + 1)) - g (m * k)|) =
          ∑ k ∈ Finset.range N,
            |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
                ((grid T n).sampledTime (k + 1)) omega -
              envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
                ((grid T n).sampledTime k) omega| := by
        apply Finset.sum_congr rfl
        intro k hk
        have htime0 : (grid T q).sampledTime (m * k) =
            (grid T n).sampledTime k := by
          dsimp [q, m]
          simpa [factorialGridEmbedding] using
            (factorialGridEmbedding_sampledTime T n (rowCommonLevel u n)
              hnq k (Finset.mem_range.mp hk).le)
        have htime1 : (grid T q).sampledTime (m * (k + 1)) =
            (grid T n).sampledTime (k + 1) := by
          dsimp [q, m]
          simpa [factorialGridEmbedding] using
            (factorialGridEmbedding_sampledTime T n (rowCommonLevel u n)
              hnq (k + 1) (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)))
        dsimp [g]
        rw [htime1, htime0]
      _ ≤ VB omega := hVar
  have hmk1 : ∀ k, k < N → m * (k + 1) ≤ L := by
    intro k hk
    rw [← hsize]
    exact Nat.mul_le_mul_left m (Nat.succ_le_iff.mpr hk)
  have hfs : ∀ k, k < N → |f (m * k)| ≤ CT := by
    intro k hk
    exact hCoeffBound (m * k) omega
  have hgc : ∀ k, k < N → ∀ j, j ≤ m → |g (m * k + j)| ≤ CB omega := by
    intro k hk j hj
    apply hSup
    have hidx : m * k + j ≤ L := by
      calc
        m * k + j ≤ m * k + m := Nat.add_le_add_left hj _
        _ = m * (k + 1) := by rw [Nat.mul_succ]
        _ ≤ L := hmk1 k hk
    have htime : (grid T q).sampledTime (m * k + j) ≤ T := by
      exact ((grid T q).sampledTime_mono
        hidx).trans_eq
          (sampledTime_size T q)
    simpa [g] using htime
  have hBound := finite_partition_transform_variation_le m N f g (CB omega) VT (VB omega) CT
    (hCB omega) hCT hF hG hfs hgc
  calc
    (∑ k ∈ Finset.range N,
        |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
            ((grid T n).sampledTime k) omega|) =
      ∑ k ∈ Finset.range N,
        |∑ j ∈ Finset.range m,
          f (m * k + j) * (g (m * k + j + 1) - g (m * k + j))| := by
        apply Finset.sum_congr rfl
        intro k hk
        simpa [f, g, N, m, q] using congrArg abs (hIncOmega k hk)
    _ ≤ 2 * CB omega * VT + CT * VB omega := hBound

theorem envelopeRowInverseResidualGain_horizon_sup_le_of_bounds
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    {a : Real} (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    {VT CT : Real} (CB VB VD : Omega → Real) (hCT : 0 ≤ CT)
    (hCB : ∀ omega, 0 ≤ CB omega) (hVD : ∀ omega, 0 ≤ VD omega)
    (hCoeffVar : ∀ omega,
      (∑ i ∈ Finset.range (size T (rowCommonLevel u n)),
        |rowInverseCoefficient u n a T S F mu alpha (i + 1) omega -
          rowInverseCoefficient u n a T S F mu alpha i omega|) ≤ VT)
    (hCoeffBound : ∀ i omega,
      |rowInverseCoefficient u n a T S F mu alpha i omega| ≤ CT)
    (hResidualSup : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T t omega| ≤ CB omega)
    (hGainVar : ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
            ((grid T n).sampledTime k) omega|) ≤ VB omega)
    (hCellIncrement : ∀ᵐ omega ∂mu, ∀ k, k < size T n → ∀ t,
      (grid T n).sampledTime k ≤ t →
        t ≤ (grid T n).sampledTime (k + 1) →
      |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T t omega -
        envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
          ((grid T n).sampledTime k) omega| ≤ VD omega) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
          t omega| ≤ VB omega + CT * VD omega + 2 * CB omega * VT := by
  filter_upwards [hResidualSup, hGainVar, hCellIncrement] with omega hSup hVar hCell
  intro t ht
  by_cases hT0 : T = 0
  · have ht0 : t = 0 := by
      have ht_le_zero : t ≤ 0 := by simpa [hT0] using ht
      exact le_antisymm ht_le_zero (by positivity)
    subst t
    subst T
    unfold envelopeInverseResidualRow envelopeRowInverseResidualGain
    rw [martingaleIntegralProcess_at_zero
      (grid 0 (rowCommonLevel u n))
      (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
        u n a 0 alpha)
      (envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a 0) omega]
    have hVT : 0 ≤ VT := by
      have hNonneg : 0 ≤
          (∑ i ∈ Finset.range (size 0 (rowCommonLevel u n)),
            |rowInverseCoefficient u n a 0 S F mu alpha (i + 1) omega -
              rowInverseCoefficient u n a 0 S F mu alpha i omega|) := by
        positivity
      linarith [hCoeffVar omega]
    have hVB : 0 ≤ VB omega := by
      have hNonneg : 0 ≤
          (∑ k ∈ Finset.range (size 0 n),
            |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound
                a 0 alpha hAlphaStop ((grid 0 n).sampledTime (k + 1)) omega -
              envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound
                a 0 alpha hAlphaStop ((grid 0 n).sampledTime k) omega|) := by
        positivity
      linarith [hVar]
    simp only [abs_zero]
    nlinarith [hCT, hCB omega, hVD omega, hVT, hVB]
  · have hTpos : 0 < T := pos_of_ne_zero hT0
    obtain ⟨k, hk, hleft, hright⟩ :=
      grid_exists_cell_of_pos T n t ht hTpos
    let q := rowCommonLevel u n
    let m := factorialRatio n q
    let N := size T n
    let L := size T q
    let G := grid T q
    let H := grid T n
    have hnq : n ≤ q := by
      dsimp [q]
      exact rowCommonLevel_ge_self u n
    have hmpos : 0 < m := by
      dsimp [m]
      exact factorialRatio_pos n q hnq
    have hsize : m * N = L := by
      dsimp [m, N, L, q]
      exact factorialRatio_mul_size T n (rowCommonLevel u n) hnq
    have hkN : k ≤ N := hk.le
    have hk1N : k + 1 ≤ N := Nat.succ_le_iff.mpr hk
    have hmk : m * k ≤ L := by
      rw [← hsize]
      exact Nat.mul_le_mul_left m hkN
    have hmk1 : m * (k + 1) ≤ L := by
      rw [← hsize]
      exact Nat.mul_le_mul_left m hk1N
    have htime0 : G.sampledTime (m * k) = H.sampledTime k := by
      dsimp [G, H, m, q]
      simpa [factorialGridEmbedding] using
        (factorialGridEmbedding_sampledTime T n (rowCommonLevel u n)
          hnq k hkN)
    have htime1 : G.sampledTime (m * (k + 1)) = H.sampledTime (k + 1) := by
      dsimp [G, H, m, q]
      simpa [factorialGridEmbedding] using
        (factorialGridEmbedding_sampledTime T n (rowCommonLevel u n)
          hnq (k + 1) hk1N)
    have hPrefix :
        |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
            (H.sampledTime k) omega| ≤ VB omega := by
      have hPrefixEq :
          envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
              (H.sampledTime k) omega =
            ∑ i ∈ Finset.range k,
              (envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                  (H.sampledTime (i + 1)) omega -
                envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                  (H.sampledTime i) omega) := by
        have hzero :
            envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha
              hAlphaStop (H.sampledTime 0) omega = 0 := by
          dsimp [H]
          unfold envelopeInverseResidualRow envelopeRowInverseResidualGain
          have hH0 : (grid T n).sampledTime 0 = 0 := by
            simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex, grid_time]
          rw [hH0]
          exact martingaleIntegralProcess_at_zero
            (grid T (rowCommonLevel u n))
            (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
              u n a T alpha)
            (envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T) omega
        calc
          envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
              (H.sampledTime k) omega =
              envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                (H.sampledTime k) omega - 0 := by simp
          _ = envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                (H.sampledTime k) omega -
              envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                (H.sampledTime 0) omega := by rw [hzero]
          _ = ∑ i ∈ Finset.range k,
              (envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                  (H.sampledTime (i + 1)) omega -
                envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                  (H.sampledTime i) omega) := by
            exact (Finset.sum_range_sub
              (fun i => envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha
                hAlphaStop (H.sampledTime i) omega) k).symm
      rw [hPrefixEq]
      calc
        |∑ i ∈ Finset.range k,
            (envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                (H.sampledTime (i + 1)) omega -
              envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                (H.sampledTime i) omega)| ≤
            ∑ i ∈ Finset.range k,
              |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                  (H.sampledTime (i + 1)) omega -
                envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                  (H.sampledTime i) omega| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range N,
              |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                  (H.sampledTime (i + 1)) omega -
                envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                  (H.sampledTime i) omega| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            exact Finset.mem_range.mpr
              ((Finset.mem_range.mp hi).trans_le hk.le)
          · intro i hi hnot
            exact abs_nonneg _
        _ ≤ VB omega := hVar
    have hleftG : G.sampledTime (m * k) ≤ t := by
      rw [htime0]
      exact hleft
    have hrightG : t ≤ G.sampledTime (m * k + m) := by
      rw [show m * k + m = m * (k + 1) by rw [Nat.mul_succ], htime1]
      exact hright
    let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
      u n a T alpha
    let M := envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
    have hBlockRaw := martingaleIntegralProcess_diff_eq_block G K M t
      (m * k) m hmk1 hleftG hrightG omega
    let fω : Nat → Real := fun i => rowInverseCoefficient u n a T S F mu alpha i omega
    let gω : Nat → Real := fun i => M (min t (G.sampledTime i)) omega
    have hBlock :
        envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop t omega -
            envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
              (H.sampledTime k) omega =
          ∑ j ∈ Finset.range m,
            fω (m * k + j) * (gω (m * k + j + 1) - gω (m * k + j)) := by
      change G.martingaleIntegralProcess K M t omega -
          G.martingaleIntegralProcess K M (H.sampledTime k) omega = _
      rw [← htime0, hBlockRaw]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hjL : m * k + j < L := by
        calc
          m * k + j < m * k + m := Nat.add_lt_add_left hjm _
          _ = m * (k + 1) := by rw [Nat.mul_succ]
          _ ≤ L := hmk1
      have hK := rowInverseCoefficientProcess_at_sampledTime
        (S := S) (F := F) (mu := mu) u n a T alpha (m * k + j) hjL omega
      dsimp [fω, gω, M]
      change rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
        u n a T alpha (G.sampledTime (m * k + j)) omega * _ = _
      rw [hK]
    have hFblock :
        (∑ j ∈ Finset.range m,
          |fω (m * k + j + 1) - fω (m * k + j)|) ≤ VT := by
      have hshift := sum_shifted_range_le_of_nonneg
        (fun i => |fω (i + 1) - fω i|) (m * k) m L
        (by simpa [Nat.mul_succ] using hmk1)
        (fun _ => abs_nonneg _)
      calc
        (∑ j ∈ Finset.range m,
            |fω (m * k + j + 1) - fω (m * k + j)|) ≤
            ∑ i ∈ Finset.range L, |fω (i + 1) - fω i| := by
          simpa [Nat.add_assoc] using hshift
        _ ≤ VT := by
          simpa [fω, L, q, hsize] using hCoeffVar omega
    have hgc : ∀ j, j ≤ m → |gω (m * k + j)| ≤ CB omega := by
      intro j hj
      dsimp [gω]
      apply hSup
      exact (min_le_left _ _).trans ht
    have hEndpoint : |gω (m * k + m) - gω (m * k)| ≤ VD omega := by
      have h := hCell k hk t hleft hright
      have hmin0 : min t (G.sampledTime (m * k)) = H.sampledTime k := by
        rw [min_eq_right hleftG, htime0]
      have hmin1 : min t (G.sampledTime (m * k + m)) = t := by
        rw [min_eq_left hrightG]
      dsimp [gω, M]
      rw [hmin1, hmin0]
      exact h
    have hfs : |fω (m * k)| ≤ CT := by
      dsimp [fω]
      exact hCoeffBound (m * k) omega
    have hTransform := finite_block_transform_abs_le fω gω
      (m * k) m (CB omega) hgc
    have hCurrent :
        |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop t omega -
            envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
            (H.sampledTime k) omega| ≤ CT * VD omega + 2 * CB omega * VT := by
      rw [hBlock]
      calc
        |∑ j ∈ Finset.range m,
            fω (m * k + j) * (gω (m * k + j + 1) - gω (m * k + j))| ≤
            |fω (m * k)| * |gω (m * k + m) - gω (m * k)| +
            2 * CB omega * ∑ j ∈ Finset.range m,
                |fω (m * k + j + 1) - fω (m * k + j)| := hTransform
        _ ≤ CT * VD omega + 2 * CB omega * VT := by
          apply add_le_add
          · exact mul_le_mul hfs hEndpoint (abs_nonneg _) hCT
          · exact mul_le_mul_of_nonneg_left hFblock
              (mul_nonneg (by norm_num) (hCB omega))
    calc
      |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop t omega| =
          |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
              (H.sampledTime k) omega +
            (envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha
                hAlphaStop t omega -
              envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                (H.sampledTime k) omega)| := by
        congr 1
        ring
      _ ≤
          |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
              (H.sampledTime k) omega| +
            |envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha
                hAlphaStop t omega -
              envelopeInverseResidualRow u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
                (H.sampledTime k) omega| := abs_add_le _ _
      _ ≤ VB omega + (CT * VD omega + 2 * CB omega * VT) := add_le_add hPrefix hCurrent
      _ = VB omega + CT * VD omega + 2 * CB omega * VT := by ring

noncomputable def envelopeStoppedInverseResidualRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (r : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal)
    (alphaSeq : Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaSeqStop : IsStoppingTime F alphaSeq) : Process Omega :=
  MeasureTheory.stoppedProcess
    (envelopeInverseResidualRow u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop)
    alpha

def envelopeInverseResidualControl (C Γ : Omega → Real) : Omega → Real :=
  fun omega => 38 * (C omega + 2 * Γ omega) + 6 * C omega

/-! ## The strengthened envelope-specific certificate -/

structure EnvelopeStoppedRowsInverseResidualControlData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (T : NNReal) (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    (eta : Real) (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal) (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real) : Prop where
  nativeResidualControl :
    EnvelopeStoppedRowsNativeResidualControlData ξ hξ T Z Γ hEnvelope eta u selection a
      alphaSeq alpha R hUsual hSAdapted hSRight hSBound C
  inverseMartingaleControl :
    EnvelopeStoppedRowsInverseMartingaleControlData ξ hξ T Z Γ hEnvelope eta u selection a
      alphaSeq alpha R hUsual hSAdapted hSBound C
  control_memLp : MemLp (envelopeInverseResidualControl C Γ) (2 : ENNReal) mu
  control_integrable : Integrable (envelopeInverseResidualControl C Γ) mu
  control_nonneg : ∀ omega, 0 ≤ envelopeInverseResidualControl C Γ omega
  inverseResidual_baseGridVariation : ∀ k, ∀ᵐ omega ∂mu,
    (∑ j ∈ Finset.range (size T (selection k)),
      |envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound a T
          (alphaSeq k)
          (nativeResidualControl.nativeControl.feasibility.commonGate.alphaSeq_stopping k)
          ((grid T (selection k)).sampledTime (j + 1)) omega -
        envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound a T
          (alphaSeq k)
          (nativeResidualControl.nativeControl.feasibility.commonGate.alphaSeq_stopping k)
          ((grid T (selection k)).sampledTime j) omega|) ≤
      envelopeInverseResidualControl C Γ omega
  inverseResidual_horizon_bound : ∀ k, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
    |envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound a T
        (alphaSeq k)
        (nativeResidualControl.nativeControl.feasibility.commonGate.alphaSeq_stopping k)
        t omega| ≤ envelopeInverseResidualControl C Γ omega
  stoppedInverseResidual_baseGridVariation : ∀ k, ∀ᵐ omega ∂mu,
    (∑ j ∈ Finset.range (size T (selection k)),
      |envelopeStoppedInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound
          a T (alphaSeq k) alpha
          (nativeResidualControl.nativeControl.feasibility.commonGate.alphaSeq_stopping k)
          ((grid T (selection k)).sampledTime (j + 1)) omega -
        envelopeStoppedInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound
          a T (alphaSeq k) alpha
          (nativeResidualControl.nativeControl.feasibility.commonGate.alphaSeq_stopping k)
          ((grid T (selection k)).sampledTime j) omega|) ≤
      envelopeInverseResidualControl C Γ omega
  stoppedInverseResidual_horizon_bound : ∀ k, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
    |envelopeStoppedInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound
        a T (alphaSeq k) alpha
        (nativeResidualControl.nativeControl.feasibility.commonGate.alphaSeq_stopping k)
        t omega| ≤ envelopeInverseResidualControl C Γ omega

/-! The producer below keeps the row data and both preceding certificates in
one dependent witness.  The only new estimate is the finite-partition
transform bound, followed by the already available one-crossing estimate for
the common stop. -/

theorem exists_envelopeStoppedRowsInverseResidualControlData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (T : NNReal) (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    {eta : Real} (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal) (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real)
    (nativeResidualControl :
      EnvelopeStoppedRowsNativeResidualControlData ξ hξ T Z Γ hEnvelope eta u selection a
        alphaSeq alpha R hUsual hSAdapted hSRight hSBound C)
    (inverseMartingaleControl :
      EnvelopeStoppedRowsInverseMartingaleControlData ξ hξ T Z Γ hEnvelope eta u selection a
        alphaSeq alpha R hUsual hSAdapted hSBound C) :
    EnvelopeStoppedRowsInverseResidualControlData ξ hξ T Z Γ hEnvelope eta u selection a
      alphaSeq alpha R hUsual hSAdapted hSRight hSBound C := by
  let B : Omega → Real := fun omega => C omega + 2 * Γ omega
  let D : Omega → Real := envelopeInverseResidualControl C Γ
  have hBMem : MemLp B (2 : ENNReal) mu := by
    simpa [B] using nativeResidualControl.residualControl_memLp
  have hDmem : MemLp D (2 : ENNReal) mu := by
    have hsum := (hBMem.const_mul (38 : Real)).add
      (nativeResidualControl.nativeControl.control_memLp.const_mul (6 : Real))
    convert hsum using 1
    funext omega
    simp [D, envelopeInverseResidualControl, B]
  have hDint : Integrable D mu := hDmem.integrable (by norm_num)
  have hBnonneg : ∀ omega, 0 ≤ B omega := by
    intro omega
    exact nativeResidualControl.residualControl_nonneg omega
  have hCnonneg : ∀ omega, 0 ≤ C omega :=
    nativeResidualControl.nativeControl.control_nonneg
  have hDnonneg : ∀ omega, 0 ≤ D omega := by
    intro omega
    dsimp [D, envelopeInverseResidualControl]
    nlinarith [hBnonneg omega, hCnonneg omega]
  let hGate := nativeResidualControl.nativeControl.feasibility.commonGate
  have hHit : ∀ k omega, alphaSeq k omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u (selection k) a T S F mu t omega)
        (-1 / 2) omega) := by
    intro k omega
    exact le_of_eq (hGate.alphaSeq_eq k omega)
  have hCoeffVar : ∀ k omega,
      (∑ i ∈ Finset.range (size T (rowCommonLevel u (selection k))),
        |rowInverseCoefficient u (selection k) a T S F mu (alphaSeq k) (i + 1) omega -
          rowInverseCoefficient u (selection k) a T S F mu (alphaSeq k) i omega|) ≤ 3 := by
    intro k omega
    exact rowInverseCoefficient_variation_le_three u (selection k) a hGate.a_pos T
      (alphaSeq k) (hHit k) omega
  have hCoeffBound : ∀ k i omega,
      |rowInverseCoefficient u (selection k) a T S F mu (alphaSeq k) i omega| ≤ 2 := by
    intro k i omega
    exact rowInverseCoefficient_uniform_abs_le_two_of_le_hitting u (selection k) a T S F mu
      (alphaSeq k) (hHit k) i omega
  have hNativeSup : ∀ k, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |envelopeNativeResidualConvexRow u (selection k) hUsual hSAdapted ξ hξ hSBound a T
          t omega| ≤ B omega := by
    intro k
    filter_upwards [nativeResidualControl.convexResidual_horizon_bound] with omega hOmega
    simpa [B] using hOmega (selection k)
  have hNativeVar : ∀ k, ∀ᵐ omega ∂mu,
      (∑ j ∈ Finset.range (size T (selection k)),
        |envelopeNativeResidualConvexRow u (selection k) hUsual hSAdapted ξ hξ hSBound a T
            ((grid T (selection k)).sampledTime (j + 1)) omega -
          envelopeNativeResidualConvexRow u (selection k) hUsual hSAdapted ξ hξ hSBound a T
            ((grid T (selection k)).sampledTime j) omega|) ≤ C omega := by
    intro k
    filter_upwards [nativeResidualControl.convexResidual_baseGridVariation] with omega hOmega
    exact hOmega (selection k)
  have hInverseVar : ∀ k, ∀ᵐ omega ∂mu,
      (∑ j ∈ Finset.range (size T (selection k)),
        |envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound a T
            (alphaSeq k) (hGate.alphaSeq_stopping k)
            ((grid T (selection k)).sampledTime (j + 1)) omega -
          envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound a T
            (alphaSeq k) (hGate.alphaSeq_stopping k)
            ((grid T (selection k)).sampledTime j) omega|) ≤
        6 * B omega + 2 * C omega := by
    intro k
    have h := envelopeRowInverseResidualGain_baseGridVariation_le_of_bounds
      (u := u) (n := selection k) hUsual hSAdapted ξ hξ hSBound (a := a) T
      (alphaSeq k) (hGate.alphaSeq_stopping k) B C (by norm_num)
      hBnonneg (hCoeffVar k) (hCoeffBound k) (hNativeSup k) (hNativeVar k)
    filter_upwards [h] with omega hOmega
    convert hOmega using 1
    ring
  have hCell : ∀ k, ∀ᵐ omega ∂mu, ∀ i, i < size T (selection k) → ∀ t,
      (grid T (selection k)).sampledTime i ≤ t →
        t ≤ (grid T (selection k)).sampledTime (i + 1) →
      |envelopeNativeResidualConvexRow u (selection k) hUsual hSAdapted ξ hξ hSBound a T
          t omega -
        envelopeNativeResidualConvexRow u (selection k) hUsual hSAdapted ξ hξ hSBound a T
          ((grid T (selection k)).sampledTime i) omega| ≤ 2 * B omega := by
    intro k
    filter_upwards [hNativeSup k] with omega hSup
    intro i hi t _hleft hright
    have hNextT : (grid T (selection k)).sampledTime (i + 1) ≤ T := by
      exact ((grid T (selection k)).sampledTime_mono
        (Nat.succ_le_iff.mpr hi)).trans_eq (sampledTime_size T (selection k))
    have htT : t ≤ T := hright.trans hNextT
    have hiT : (grid T (selection k)).sampledTime i ≤ T := by
      exact ((grid T (selection k)).sampledTime_mono hi.le).trans_eq
        (sampledTime_size T (selection k))
    calc
      |envelopeNativeResidualConvexRow u (selection k) hUsual hSAdapted ξ hξ hSBound a T
            t omega -
          envelopeNativeResidualConvexRow u (selection k) hUsual hSAdapted ξ hξ hSBound a T
            ((grid T (selection k)).sampledTime i) omega| ≤
          |envelopeNativeResidualConvexRow u (selection k) hUsual hSAdapted ξ hξ hSBound a T
              t omega| +
            |envelopeNativeResidualConvexRow u (selection k) hUsual hSAdapted ξ hξ hSBound a T
              ((grid T (selection k)).sampledTime i) omega| := abs_sub _ _
      _ ≤ B omega + B omega := add_le_add (hSup t htT) (hSup _ hiT)
      _ = 2 * B omega := by ring
  have hInverseSup : ∀ k, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound a T
          (alphaSeq k) (hGate.alphaSeq_stopping k) t omega| ≤
        16 * B omega + 2 * C omega := by
    intro k
    have h := envelopeRowInverseResidualGain_horizon_sup_le_of_bounds
      (u := u) (n := selection k) hUsual hSAdapted ξ hξ hSBound (a := a) T
      (alphaSeq k) (hGate.alphaSeq_stopping k) B (fun omega => 6 * B omega + 2 * C omega)
      (fun omega => 2 * B omega) (by norm_num) hBnonneg
      (fun omega => mul_nonneg (by norm_num) (hBnonneg omega)) (hCoeffVar k)
      (hCoeffBound k) (hNativeSup k) (hInverseVar k) (hCell k)
    filter_upwards [h] with omega hOmega
    intro t ht
    convert hOmega t ht using 1
    ring
  have hStoppedVar : ∀ k, ∀ᵐ omega ∂mu,
      (∑ j ∈ Finset.range (size T (selection k)),
        |envelopeStoppedInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ
            hSBound a T (alphaSeq k) alpha (hGate.alphaSeq_stopping k)
            ((grid T (selection k)).sampledTime (j + 1)) omega -
          envelopeStoppedInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ
            hSBound a T (alphaSeq k) alpha (hGate.alphaSeq_stopping k)
            ((grid T (selection k)).sampledTime j) omega|) ≤
        38 * B omega + 6 * C omega := by
    intro k
    filter_upwards [hInverseVar k, hInverseSup k] with omega hVar hSup
    have hAlphaT : alpha omega ≤ (T : WithTop NNReal) :=
      (hGate.alpha_le_alphaSeq k omega).trans (hGate.alphaSeq_le_T k omega)
    have hSupNonneg : 0 ≤ 16 * B omega + 2 * C omega := by
      nlinarith [hBnonneg omega, hCnonneg omega]
    have h := stoppedProcess_gridVariation_le_add_two_of_sup_at
      T (selection k) alpha omega hAlphaT hSupNonneg hVar hSup
    calc
      _ ≤ 6 * B omega + 2 * C omega + 2 * (16 * B omega + 2 * C omega) := by
        simpa only [envelopeStoppedInverseResidualRow] using h
      _ = 38 * B omega + 6 * C omega := by ring
  have hStoppedSup : ∀ k, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |envelopeStoppedInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ
          hSBound a T (alphaSeq k) alpha (hGate.alphaSeq_stopping k) t omega| ≤
        16 * B omega + 2 * C omega := by
    intro k
    filter_upwards [hInverseSup k] with omega hSup
    intro t ht
    change |envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound
        a T (alphaSeq k) (hGate.alphaSeq_stopping k)
        (min (t : WithTop NNReal) (alpha omega)).untopA omega| ≤ _
    have hminT : (min (t : WithTop NNReal) (alpha omega)).untopA ≤ T := by
      exact WithTop.untopA_le
        ((min_le_left _ _).trans (WithTop.coe_le_coe.mpr ht))
    exact hSup _ hminT
  refine
    { nativeResidualControl := nativeResidualControl
      inverseMartingaleControl := inverseMartingaleControl
      control_memLp := hDmem
      control_integrable := hDint
      control_nonneg := hDnonneg
      inverseResidual_baseGridVariation := ?_
      inverseResidual_horizon_bound := ?_
      stoppedInverseResidual_baseGridVariation := ?_
      stoppedInverseResidual_horizon_bound := ?_ }
  · intro k
    filter_upwards [hInverseVar k] with omega hOmega
    calc
      (∑ j ∈ Finset.range (size T (selection k)),
        |envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound a T
            (alphaSeq k) (hGate.alphaSeq_stopping k)
            ((grid T (selection k)).sampledTime (j + 1)) omega -
          envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound a T
            (alphaSeq k) (hGate.alphaSeq_stopping k)
            ((grid T (selection k)).sampledTime j) omega|) ≤
          6 * B omega + 2 * C omega := hOmega
      _ ≤ 38 * B omega + 6 * C omega := by
        nlinarith [hBnonneg omega, hCnonneg omega]
      _ = D omega := by
        simp [D, envelopeInverseResidualControl, B]
  · intro k
    filter_upwards [hInverseSup k] with omega hOmega t ht
    calc
      |envelopeInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ hSBound
          a T (alphaSeq k) (hGate.alphaSeq_stopping k) t omega| ≤
          16 * B omega + 2 * C omega := hOmega t ht
      _ ≤ 38 * B omega + 6 * C omega := by
        nlinarith [hBnonneg omega, hCnonneg omega]
      _ = D omega := by
        simp [D, envelopeInverseResidualControl, B]
  · intro k
    filter_upwards [hStoppedVar k] with omega hOmega
    calc
      (∑ j ∈ Finset.range (size T (selection k)),
        |envelopeStoppedInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ
            hSBound a T (alphaSeq k) alpha (hGate.alphaSeq_stopping k)
            ((grid T (selection k)).sampledTime (j + 1)) omega -
          envelopeStoppedInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ
            hSBound a T (alphaSeq k) alpha (hGate.alphaSeq_stopping k)
            ((grid T (selection k)).sampledTime j) omega|) ≤
          38 * B omega + 6 * C omega := hOmega
      _ = D omega := by
        simp [D, envelopeInverseResidualControl, B]
  · intro k
    filter_upwards [hStoppedSup k] with omega hOmega t ht
    calc
      |envelopeStoppedInverseResidualRow (u := u) (selection k) hUsual hSAdapted ξ hξ
          hSBound a T (alphaSeq k) alpha (hGate.alphaSeq_stopping k) t omega| ≤
          16 * B omega + 2 * C omega := hOmega t ht
      _ ≤ 38 * B omega + 6 * C omega := by
        nlinarith [hBnonneg omega, hCnonneg omega]
      _ = D omega := by
        simp [D, envelopeInverseResidualControl, B]

end HorizonFactorialGrid

end FTAPTheorem42
