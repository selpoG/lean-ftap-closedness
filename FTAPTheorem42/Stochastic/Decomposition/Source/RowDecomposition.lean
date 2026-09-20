/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.RowInverse

/-!
# Concrete decompositions of the inverse rows

The inverse coefficient is first represented by a process whose values at the
left endpoints of the common grid are the actual row coefficients.  The
finite-grid martingale integral is then used for the martingale part.  All
identities below are finite-sum identities; no stochastic-integral callback is
introduced.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## A common-grid coefficient process -/

noncomputable def rowInverseCoefficientProcess
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal) : Process Omega :=
  let q := rowCommonLevel u n
  let G := grid T q
  fun t omega =>
    if h : ∃ k ∈ Finset.range (size T q), t = G.sampledTime k then
      rowInverseCoefficient u n a T S F mu alpha (Classical.choose h) omega
    else 0

theorem rowInverseCoefficientProcess_stronglyAdapted
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha) :
    StronglyAdapted F
      (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
        u n a T alpha) := by
  intro t
  let q := rowCommonLevel u n
  let G := grid T q
  by_cases ht : T < t
  · have hgrid : ¬ ∃ k ∈ Finset.range (size T q), t = G.sampledTime k := by
      intro h
      obtain ⟨k, hk, htk⟩ := h
      have hle : G.sampledTime k ≤ T := by
        exact (G.sampledTime_mono (Finset.mem_range.mp hk).le).trans_eq
          (sampledTime_size T q)
      linarith
    change StronglyMeasurable[F t]
      (fun omega =>
        if h : ∃ k ∈ Finset.range (size T q), t = G.sampledTime k then
          rowInverseCoefficient u n a T S F mu alpha (Classical.choose h) omega
        else 0)
    simp only [hgrid]
    exact stronglyMeasurable_const
  · have htT : t ≤ T := le_of_not_gt ht
    by_cases hgrid : ∃ k ∈ Finset.range (size T q), t = G.sampledTime k
    · have hj : Classical.choose hgrid ∈ Finset.range (size T q) :=
        (Classical.choose_spec hgrid).1
      have htime : t = G.sampledTime (Classical.choose hgrid) :=
        (Classical.choose_spec hgrid).2
      have hCoeff := rowInverseCoefficient_stronglyAdapted
        (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop
        (Classical.choose hgrid)
      have hCoeff' : StronglyMeasurable[F (G.sampledTime
          (Classical.choose hgrid))]
          (rowInverseCoefficient u n a T S F mu alpha
            (Classical.choose hgrid)) := hCoeff
      rw [← htime] at hCoeff'
      change StronglyMeasurable[F t]
        (fun omega =>
          if h : ∃ k ∈ Finset.range (size T q), t = G.sampledTime k then
            rowInverseCoefficient u n a T S F mu alpha (Classical.choose h) omega
          else 0)
      simp only [hgrid]
      simpa using hCoeff'
    · change StronglyMeasurable[F t]
        (fun omega =>
          if h : ∃ k ∈ Finset.range (size T q), t = G.sampledTime k then
            rowInverseCoefficient u n a T S F mu alpha (Classical.choose h) omega
          else 0)
      simp only [hgrid]
      exact stronglyMeasurable_const

theorem rowInverseCoefficientProcess_abs_le_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    ∀ t omega, |rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
        u n a T alpha t omega| ≤ 2 := by
  intro t omega
  let q := rowCommonLevel u n
  let G := grid T q
  by_cases ht : T < t
  · have hgrid : ¬ ∃ k ∈ Finset.range (size T q), t = G.sampledTime k := by
      intro h
      obtain ⟨k, hk, htk⟩ := h
      have hle : G.sampledTime k ≤ T := by
        exact (G.sampledTime_mono (Finset.mem_range.mp hk).le).trans_eq
          (sampledTime_size T q)
      linarith
    change |(if h : ∃ k ∈ Finset.range (size T q), t = G.sampledTime k then
      rowInverseCoefficient u n a T S F mu alpha (Classical.choose h) omega else 0)| ≤ 2
    simp only [hgrid]
    norm_num
  · by_cases hgrid : ∃ k ∈ Finset.range (size T q), t = G.sampledTime k
    · change |(if h : ∃ k ∈ Finset.range (size T q), t = G.sampledTime k then
        rowInverseCoefficient u n a T S F mu alpha (Classical.choose h) omega else 0)| ≤ 2
      simp only [hgrid]
      exact rowInverseCoefficient_uniform_abs_le_two_of_le_hitting
        u n a T S F mu alpha hAlpha (Classical.choose hgrid) omega
    · change |(if h : ∃ k ∈ Finset.range (size T q), t = G.sampledTime k then
        rowInverseCoefficient u n a T S F mu alpha (Classical.choose h) omega else 0)| ≤ 2
      simp only [hgrid]
      norm_num

theorem rowInverseCoefficient_zero_at_horizon
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (k : Nat) (omega : Omega)
    (hk : k < size T (rowCommonLevel u n))
    (htime : (grid T (rowCommonLevel u n)).sampledTime k = T) :
    rowInverseCoefficient u n a T S F mu alpha k omega = 0 := by
  rw [rowInverseCoefficient]
  split_ifs with hactive
  · exact False.elim <| (not_lt_of_ge
      ((grid T (rowCommonLevel u n)).sampledTime_mono (Nat.succ_le_of_lt hk) |>.trans_eq
        (sampledTime_size T (rowCommonLevel u n))))
      (by simpa [htime] using hactive.2)
  · rfl

theorem rowInverseCoefficientProcess_at_sampledTime
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (k : Nat) (hk : k < size T (rowCommonLevel u n)) (omega : Omega) :
    rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
      u n a T alpha
        ((grid T (rowCommonLevel u n)).sampledTime k) omega =
      rowInverseCoefficient u n a T S F mu alpha k omega := by
  let q := rowCommonLevel u n
  let G := grid T q
  have hgrid : ∃ j ∈ Finset.range (size T q), G.sampledTime k = G.sampledTime j :=
    ⟨k, Finset.mem_range.mpr hk, rfl⟩
  let j := Classical.choose hgrid
  have hj : j ∈ Finset.range (size T q) := (Classical.choose_spec hgrid).1
  have htime : G.sampledTime j = G.sampledTime k :=
    (Classical.choose_spec hgrid).2.symm
  change (if h : ∃ i ∈ Finset.range (size T q), G.sampledTime k = G.sampledTime i then
      rowInverseCoefficient u n a T S F mu alpha (Classical.choose h) omega else 0) =
    rowInverseCoefficient u n a T S F mu alpha k omega
  simp only [hgrid]
  change rowInverseCoefficient u n a T S F mu alpha j omega =
    rowInverseCoefficient u n a T S F mu alpha k omega
  by_cases hTk : G.sampledTime k = T
  · have hTj : G.sampledTime j = T := htime.trans hTk
    rw [rowInverseCoefficient_zero_at_horizon u n a T alpha j omega
      (Finset.mem_range.mp hj) hTj,
      rowInverseCoefficient_zero_at_horizon u n a T alpha k omega hk hTk]
  · have hltk : G.sampledTime k < T := lt_of_le_of_ne
      ((G.sampledTime_mono hk.le).trans_eq (sampledTime_size T q)) hTk
    have hj_eq : j = k := by
      have hjlt : G.sampledTime j < T := by simpa [htime] using hltk
      have hjform : G.sampledTime j = (j : NNReal) /
          (q.factorial : NNReal) := by
        let j' : Fin (size T q + 1) :=
          ⟨j, Nat.lt_succ_of_lt (Finset.mem_range.mp hj)⟩
        have hjtime : G.time j' < T := by
          rw [← G.sampledTime_fin_eq j']
          exact hjlt
        have hjratio : (j : NNReal) / (q.factorial : NNReal) < T := by
          have hjtime' : min ((j : NNReal) / (q.factorial : NNReal)) T < T := by
            simpa only [G, grid_time] using hjtime
          exact (min_lt_iff.mp hjtime').resolve_right (lt_irrefl T)
        calc
          G.sampledTime j = G.sampledTime j' := by rfl
          _ = G.time j' := G.sampledTime_fin_eq j'
          _ = min ((j : NNReal) / (q.factorial : NNReal)) T := by
            dsimp [G]
          _ = (j : NNReal) / (q.factorial : NNReal) := min_eq_left hjratio.le
      have hkform : G.sampledTime k = (k : NNReal) /
          (q.factorial : NNReal) := by
        let k' : Fin (size T q + 1) :=
          ⟨k, Nat.lt_succ_of_lt hk⟩
        have hktime : G.time k' < T := by
          rw [← G.sampledTime_fin_eq k']
          exact hltk
        have hkratio : (k : NNReal) / (q.factorial : NNReal) < T := by
          have hktime' : min ((k : NNReal) / (q.factorial : NNReal)) T < T := by
            simpa only [G, grid_time] using hktime
          exact (min_lt_iff.mp hktime').resolve_right (lt_irrefl T)
        calc
          G.sampledTime k = G.sampledTime k' := by rfl
          _ = G.time k' := G.sampledTime_fin_eq k'
          _ = min ((k : NNReal) / (q.factorial : NNReal)) T := by
            dsimp [G]
          _ = (k : NNReal) / (q.factorial : NNReal) := min_eq_left hkratio.le
      rw [hjform, hkform] at htime
      have hmul := congrArg (fun x : NNReal =>
        x * (q.factorial : NNReal)) htime
      rw [div_mul_cancel₀ _ (by positivity), div_mul_cancel₀ _ (by positivity)] at hmul
      exact_mod_cast hmul
    rw [hj_eq]

private theorem rowGateCoefficient_antitone
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (omega : Omega) :
    Antitone (fun k => rowGateCoefficient u n a T S F mu k omega) := by
  intro k l hkl
  unfold rowGateCoefficient
  apply Finset.sum_le_sum
  intro r hr
  have hidx : rowNativeIndex u n r k ≤ rowNativeIndex u n r l := by
    exact Nat.div_le_div_right hkl
  have hvar := (grid T r).monotone_doobPredictableVariation S F mu hidx omega
  have hgate :
      (grid T r).doobVariationGate S F mu a
          (rowNativeIndex u n r l) omega ≤
        (grid T r).doobVariationGate S F mu a
          (rowNativeIndex u n r k) omega := by
    unfold ChronologicalGrid.doobVariationGate
    by_cases hl : (grid T r).doobPredictableVariation S F mu
        (rowNativeIndex u n r l) omega < a
    · have hk : (grid T r).doobPredictableVariation S F mu
          (rowNativeIndex u n r k) omega < a := lt_of_le_of_lt hvar hl
      simp [hl, hk]
    · simp only [hl, ↓reduceIte]
      split_ifs <;> norm_num
  exact mul_le_mul_of_nonneg_left hgate ((u n).nonneg r hr)

private theorem finite_variation_prefix_drop_le
    (N j : Nat) (f : Nat → Real) (hj : j ≤ N)
    (hzero : ∀ k, j ≤ k → f k = 0)
    (hpos : ∀ k, k < j → 0 ≤ f k)
    (hmono : ∀ ⦃k l : Nat⦄, k < j → l < j → k ≤ l → f k ≤ f l)
    (h0 : f 0 = 1)
    (hbound : ∀ k, k < j → f k ≤ 2) :
    ∑ k ∈ Finset.range N, |f (k + 1) - f k| ≤ 3 := by
  by_cases hj0 : j = 0
  · have hz := hzero 0 (by simp [hj0])
    linarith [h0, hz]
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hsplit :
      (∑ k ∈ Finset.range N, |f (k + 1) - f k|) =
        (∑ k ∈ Finset.range j, |f (k + 1) - f k|) +
          ∑ k ∈ Finset.Ico j N, |f (k + 1) - f k| := by
    rw [← Finset.sum_range_add_sum_Ico _ hj]
  have htail :
      (∑ k ∈ Finset.Ico j N, |f (k + 1) - f k|) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    rw [hzero k hk'.1, hzero (k + 1) (hk'.1.trans (Nat.le_succ _))]
    simp
  have hint :
      (∑ k ∈ Finset.range (j - 1), |f (k + 1) - f k|) =
        f (j - 1) - f 0 := by
    calc
      (∑ k ∈ Finset.range (j - 1), |f (k + 1) - f k|) =
          ∑ k ∈ Finset.range (j - 1), (f (k + 1) - f k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < j - 1 := Finset.mem_range.mp hk
        have hkl : f k ≤ f (k + 1) := hmono (by omega)
          (by omega) (Nat.le_succ k)
        rw [abs_of_nonneg (sub_nonneg.mpr hkl)]
      _ = f (j - 1) - f 0 := Finset.sum_range_sub f (j - 1)
  have hfirst :
      (∑ k ∈ Finset.range j, |f (k + 1) - f k|) ≤ 3 := by
    rw [show j = (j - 1) + 1 by omega, Finset.sum_range_succ, hint]
    have hprevpos : 0 ≤ f (j - 1) := hpos (j - 1) (by omega)
    have hprevbound : f (j - 1) ≤ 2 := hbound (j - 1) (by omega)
    have hsub : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
    have hneg : 0 - f (j - 1) ≤ 0 := by linarith
    rw [hsub, hzero j (by omega), abs_of_nonpos hneg, h0]
    linarith
  rw [hsplit, htail, add_zero]
  exact hfirst

private theorem grid_sampledTime_strict_of_le_of_lt
    (T : NNReal) (q k l : Nat)
    (hkl : k ≤ l) (hl : l < size T q)
    (hlt : (grid T q).sampledTime l < T) :
    (grid T q).sampledTime k < (grid T q).sampledTime (k + 1) := by
  have hk : k ≤ size T q := hkl.trans hl.le
  have hk1 : k + 1 ≤ size T q := by omega
  have hltk : (grid T q).sampledTime k < T :=
    (grid T q).sampledTime_mono hkl |>.trans_lt hlt
  unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
  simp only [min_eq_left hk, min_eq_left hk1, grid_time]
  have hxy : (k : NNReal) / (q.factorial : NNReal) <
      ((k + 1 : Nat) : NNReal) / (q.factorial : NNReal) := by
    exact div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self k)
      (by positivity)
  have hxT : (k : NNReal) / (q.factorial : NNReal) < T := by
    have hltk' : min ((k : NNReal) / (q.factorial : NNReal)) T < T := by
      simpa only [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
        min_eq_left hk, grid_time] using hltk
    exact (min_lt_iff.mp hltk').resolve_right (lt_irrefl T)
  rw [min_eq_left hxT.le]
  exact lt_min hxy hxT

theorem rowInverseCoefficient_variation_le_three
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (ha : 0 < a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    ∀ omega,
      ∑ k ∈ Finset.range (size T (rowCommonLevel u n)),
        |rowInverseCoefficient u n a T S F mu alpha (k + 1) omega -
          rowInverseCoefficient u n a T S F mu alpha k omega| ≤ 3 := by
  intro omega
  let q := rowCommonLevel u n
  let N := size T q
  let G := grid T q
  let active : Nat → Prop := fun k =>
    (G.sampledTime k : WithTop NNReal) < alpha omega ∧
      G.sampledTime k < G.sampledTime (k + 1)
  let f : Nat → Real := fun k =>
    rowInverseCoefficient u n a T S F mu alpha k omega
  have hactive_ltN : ∀ k, active k → k < N := by
    intro k hk
    by_contra hkN
    have hNk : N ≤ k := Nat.le_of_not_gt hkN
    have htimek : G.sampledTime k = T := by
      apply le_antisymm
      · exact min_le_right _ _
      · calc
          T = G.sampledTime N := (sampledTime_size T q).symm
          _ ≤ G.sampledTime k := G.sampledTime_mono hNk
    have htimek1 : G.sampledTime (k + 1) ≤ T := by
      exact min_le_right _ _
    linarith [hk.2, htimek, htimek1]
  have hactive_down : ∀ ⦃k l : Nat⦄, k ≤ l → l < N →
      active l → active k := by
    intro k l hkl hl hlactive
    have hltlT : G.sampledTime l < T := by
      exact hlactive.2.trans_le ((G.sampledTime_mono (Nat.succ_le_of_lt hl)).trans_eq
        (sampledTime_size T q))
    have hcell := grid_sampledTime_strict_of_le_of_lt T q k l hkl hl hltlT
    have htimeTop : (G.sampledTime k : WithTop NNReal) ≤
        (G.sampledTime l : WithTop NNReal) :=
      WithTop.coe_le_coe.mpr (G.sampledTime_mono hkl)
    exact ⟨htimeTop.trans_lt hlactive.1, hcell⟩
  have hactiveN : ¬ active N := by
    intro hN
    have hnext : G.sampledTime (N + 1) ≤ T := by
      exact min_le_right _ _
    have hnow : G.sampledTime N = T := sampledTime_size T q
    linarith [hN.2, hnext, hnow]
  let hExist : ∃ k, ¬ active k := ⟨N, hactiveN⟩
  let j := Nat.find hExist
  have hjN : j ≤ N := Nat.find_min' hExist hactiveN
  have hjnot : ¬ active j := Nat.find_spec hExist
  have hactive_lt : ∀ k, k < j → active k := by
    intro k hk
    exact Classical.not_not.mp (Nat.find_min hExist hk)
  have hzero : ∀ k, j ≤ k → f k = 0 := by
    intro k hjk
    by_cases hkactive : active k
    · have hkN : k < N := hactive_ltN k hkactive
      exact (hjnot (hactive_down hjk hkN hkactive)).elim
    · dsimp [f]
      unfold rowInverseCoefficient
      split_ifs with h
      · exact (hkactive (by simpa [active] using h)).elim
      · rfl
  have hgate0 : rowGateCoefficient u n a T S F mu 0 omega = 1 := by
    unfold rowGateCoefficient
    calc
      (∑ r ∈ (u n).support,
          (u n).weight r *
            (grid T r).doobVariationGate S F mu a
              (rowNativeIndex u n r 0) omega) =
          ∑ r ∈ (u n).support, (u n).weight r * 1 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hvar0 : (grid T r).doobPredictableVariation S F mu
            (rowNativeIndex u n r 0) omega = 0 := by
          simp [rowNativeIndex, ChronologicalGrid.doobPredictableVariation]
        rw [ChronologicalGrid.doobVariationGate, hvar0]
        simp [ha]
      _ = 1 := by
        rw [← Finset.sum_mul, (u n).sum_eq_one, one_mul]
  have hpos : ∀ k, k < j → 0 ≤ f k := by
    intro k hk
    have hkactive := hactive_lt k hk
    have hkN := hactive_ltN k hkactive
    have hgate := rowGateCoefficient_ge_half_of_lt_alpha u n a T S F mu alpha
      hAlpha k omega hkN hkactive.1 hkactive.2
    have hgatepos : 0 < rowGateCoefficient u n a T S F mu k omega :=
      lt_of_lt_of_le (by norm_num) hgate
    dsimp [f]
    rw [rowInverseCoefficient]
    split_ifs with h
    · exact inv_nonneg.mpr hgatepos.le
    · exact (h (by simpa [active] using hkactive)).elim
  have hbound : ∀ k, k < j → f k ≤ 2 := by
    intro k hk
    have hkactive := hactive_lt k hk
    have hkN := hactive_ltN k hkactive
    have hgate := rowGateCoefficient_ge_half_of_lt_alpha u n a T S F mu alpha
      hAlpha k omega hkN hkactive.1 hkactive.2
    have habs := rowInverseCoefficient_abs_le_two u n a T alpha k omega hgate
    exact (le_abs_self _).trans habs
  have hmono : ∀ ⦃k l : Nat⦄, k < j → l < j → k ≤ l → f k ≤ f l := by
    intro k l hk hl hkl
    have hkactive := hactive_lt k hk
    have hlactive := hactive_lt l hl
    have hkN := hactive_ltN k hkactive
    have hlN := hactive_ltN l hlactive
    have hgkl := rowGateCoefficient_antitone (S := S) (F := F) (mu := mu)
      u n a T omega hkl
    have hgk := rowGateCoefficient_ge_half_of_lt_alpha u n a T S F mu alpha
      hAlpha k omega hkN hkactive.1 hkactive.2
    have hgl := rowGateCoefficient_ge_half_of_lt_alpha u n a T S F mu alpha
      hAlpha l omega hlN hlactive.1 hlactive.2
    have hpk : 0 < rowGateCoefficient u n a T S F mu k omega :=
      lt_of_lt_of_le (by norm_num) hgk
    have hpl : 0 < rowGateCoefficient u n a T S F mu l omega :=
      lt_of_lt_of_le (by norm_num) hgl
    have hinv := (inv_le_inv₀ hpk hpl).2 hgkl
    dsimp [f]
    rw [rowInverseCoefficient, rowInverseCoefficient]
    rw [ite_eq_left (by simpa [active] using hkactive),
      ite_eq_left (by simpa [active] using hlactive)]
    exact hinv
  by_cases hj0 : j = 0
  · have hsum :
        (∑ k ∈ Finset.range N, |f (k + 1) - f k|) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hzero k (by omega), hzero (k + 1) (by omega)]
      simp
    change (∑ k ∈ Finset.range N, |f (k + 1) - f k|) ≤ 3
    rw [hsum]
    norm_num
  · have h0 : f 0 = 1 := by
      have hact0 : active 0 := hactive_lt 0 (by omega)
      dsimp [f]
      rw [rowInverseCoefficient]
      split_ifs with h
      · rw [hgate0]
        norm_num
      · exact (h (by simpa [active] using hact0)).elim
    exact finite_variation_prefix_drop_le N j f hjN hzero hpos hmono h0 hbound

/-! ## Finite-grid increments of a transform

The residual row below is a finite-grid stochastic transform.  We record the
prefix and one-step formulas explicitly so that subsequent variation bounds
do not silently replace the transform by a pointwise product. -/

omit [MeasurableSpace Omega] in
private theorem martingaleIntegralProcess_at_sampledTime_eq_prefix
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K M : Process Omega) (k : Nat) (hk : k ≤ N) (omega : Omega) :
    G.martingaleIntegralProcess K M (G.sampledTime k) omega =
      ∑ j ∈ Finset.range k,
        K (G.sampledTime j) omega *
          (M (G.sampledTime (j + 1)) omega - M (G.sampledTime j) omega) := by
  unfold ChronologicalGrid.martingaleIntegralProcess
  simp only [Finset.sum_apply]
  rw [← Finset.sum_range_add_sum_Ico _ hk]
  have hPrefix :
      (∑ j ∈ Finset.range k,
        deterministicIntervalMartingaleTransform K M
          (G.sampledTime j) (G.sampledTime (j + 1))
          (G.sampledTime k) omega) =
        ∑ j ∈ Finset.range k,
          K (G.sampledTime j) omega *
            (M (G.sampledTime (j + 1)) omega - M (G.sampledTime j) omega) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < k := Finset.mem_range.mp hj
    have hj1k : j + 1 ≤ k := Nat.succ_le_iff.mpr hjlt
    rw [deterministicIntervalMartingaleTransform_eq_of_le K M
      (G.sampledTime_mono (Nat.le_succ j))
      (G.sampledTime_mono hj1k)]
  have hTail :
      (∑ j ∈ Finset.Ico k N,
        deterministicIntervalMartingaleTransform K M
          (G.sampledTime j) (G.sampledTime (j + 1))
          (G.sampledTime k) omega) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hkj : k ≤ j := hj'.1
    rw [deterministicIntervalMartingaleTransform_eq_zero_of_le K M
      (G.sampledTime_mono (Nat.le_succ j))
      (G.sampledTime_mono hkj)]
    simp
  rw [hPrefix, hTail, add_zero]

theorem grid_exists_cell_of_pos
    (T : NNReal) (r : Nat) (t : NNReal) (ht : t ≤ T) (hT : 0 < T) :
    ∃ k, k < size T r ∧
      (grid T r).sampledTime k ≤ t ∧
        t ≤ (grid T r).sampledTime (k + 1) := by
  have hsizepos : 0 < size T r := by
    unfold size
    exact Nat.mul_pos (Nat.ceil_pos.mpr hT) (Nat.factorial_pos r)
  by_cases ht0 : t = 0
  · refine ⟨0, hsizepos, ?_, ?_⟩
    · simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
        grid_time]
    · simp [ht0]
  · have htpos : 0 < t := pos_of_ne_zero ht0
    let q := (approxIndex T t ht r).1
    have hqN : q ≤ size T r := by
      dsimp [q]
      exact Nat.lt_succ_iff.mp (approxIndex T t ht r).isLt
    have hqpos : 0 < q := by
      dsimp [q, approxIndex]
      exact Nat.ceil_pos.mpr (mul_pos htpos (by positivity))
    let k := q - 1
    have hklt : k < size T r := by
      dsimp [k]
      exact (Nat.sub_lt hqpos (by norm_num)).trans_le hqN
    have hkq : (approxIndex T t ht r).1 = k + 1 := by
      dsimp [k, q]
      exact (Nat.sub_add_cancel hqpos).symm
    have hleft : (grid T r).sampledTime k ≤ t :=
      approxIndex_previous_time_le T t ht r hkq
    have hqTime : (grid T r).sampledTime q =
        (grid T r).time (approxIndex T t ht r) := by
      have hqIndex : (grid T r).natIndex q = approxIndex T t ht r := by
        ext
        change min q (size T r) = (approxIndex T t ht r).1
        exact min_eq_left hqN
      unfold ChronologicalGrid.sampledTime
      rw [hqIndex]
    have hright : t ≤ (grid T r).sampledTime q := by
      rw [hqTime, grid_time_approxIndex]
      exact le_min (FactorialChronologicalGrid.le_approx r t) ht
    have hkqNat : q - 1 + 1 = q := Nat.sub_add_cancel hqpos
    refine ⟨k, hklt, hleft, ?_⟩
    rw [show k + 1 = q by exact hkqNat]
    exact hright

omit [MeasurableSpace Omega] in
theorem martingaleIntegralProcess_diff_eq_block
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K M : Process Omega) (t : NNReal) (s m : Nat)
    (hs : s + m ≤ N)
    (hleft : G.sampledTime s ≤ t)
    (hright : t ≤ G.sampledTime (s + m)) (omega : Omega) :
    G.martingaleIntegralProcess K M t omega -
        G.martingaleIntegralProcess K M (G.sampledTime s) omega =
      ∑ j ∈ Finset.range m,
        K (G.sampledTime (s + j)) omega *
          (M (min t (G.sampledTime (s + j + 1))) omega -
            M (min t (G.sampledTime (s + j))) omega) := by
  have hDiff :
      (∑ j ∈ Finset.range N,
          deterministicIntervalMartingaleTransform K M
            (G.sampledTime j) (G.sampledTime (j + 1)) t omega) -
        ∑ j ∈ Finset.range N,
          deterministicIntervalMartingaleTransform K M
            (G.sampledTime j) (G.sampledTime (j + 1))
            (G.sampledTime s) omega =
        ∑ j ∈ Finset.range m,
          K (G.sampledTime (s + j)) omega *
            (M (min t (G.sampledTime (s + j + 1))) omega -
              M (min t (G.sampledTime (s + j))) omega) := by
    let d : Nat → Real := fun j =>
      deterministicIntervalMartingaleTransform K M
          (G.sampledTime j) (G.sampledTime (j + 1)) t omega -
        deterministicIntervalMartingaleTransform K M
          (G.sampledTime j) (G.sampledTime (j + 1))
          (G.sampledTime s) omega
    have hsub : Finset.Ico s (s + m) ⊆ Finset.range N := by
      intro j hj
      have hjupper : j < s + m := (Finset.mem_Ico.mp hj).2
      exact Finset.mem_range.mpr (hjupper.trans_le hs)
    have hzero : ∀ j ∈ Finset.range N,
        j ∉ Finset.Ico s (s + m) → d j = 0 := by
      intro j hj hnot
      have hjN : j < N := Finset.mem_range.mp hj
      by_cases hjs : j < s
      · have hj1s : j + 1 ≤ s := Nat.succ_le_of_lt hjs
        have hj1t : G.sampledTime (j + 1) ≤ t :=
          (G.sampledTime_mono hj1s).trans hleft
        have hj1s' : G.sampledTime (j + 1) ≤ G.sampledTime s :=
          G.sampledTime_mono hj1s
        dsimp [d]
        rw [deterministicIntervalMartingaleTransform_eq_of_le K M
          (G.sampledTime_mono (Nat.le_succ j)) hj1t,
          deterministicIntervalMartingaleTransform_eq_of_le K M
            (G.sampledTime_mono (Nat.le_succ j)) hj1s']
        simp
      · have hsle : s ≤ j := Nat.le_of_not_gt hjs
        have hsupper : s + m ≤ j ∨ j < s + m := by omega
        rcases hsupper with htail | hmid
        · have hst : t ≤ G.sampledTime j :=
            hright.trans (G.sampledTime_mono htail)
          have hsj : G.sampledTime s ≤ G.sampledTime j :=
            G.sampledTime_mono hsle
          dsimp [d]
          rw [deterministicIntervalMartingaleTransform_eq_zero_of_le K M
            (G.sampledTime_mono (Nat.le_succ j)) hst,
            deterministicIntervalMartingaleTransform_eq_zero_of_le K M
              (G.sampledTime_mono (Nat.le_succ j)) hsj]
          simp
        · exact (hnot (Finset.mem_Ico.mpr ⟨hsle, hmid⟩)).elim
    have hsumIco :
        (∑ j ∈ Finset.Ico s (s + m), d j) =
          ∑ j ∈ Finset.range N, d j :=
      Finset.sum_subset hsub hzero
    have hsumRange :
        (∑ j ∈ Finset.range N, d j) =
          ∑ j ∈ Finset.Ico s (s + m), d j := hsumIco.symm
    have hsumMap :
        (∑ j ∈ Finset.Ico s (s + m), d j) =
          ∑ j ∈ Finset.range m, d (s + j) := by
      have h := Finset.sum_Ico_add d 0 m s
      rw [show (0 + s : Nat) = s by simp,
        show m + s = s + m by omega] at h
      simpa using h.symm
    rw [← Finset.sum_sub_distrib]
    change (∑ j ∈ Finset.range N, d j) = _
    rw [hsumRange, hsumMap]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j < m := Finset.mem_range.mp hj
    have hsj : s ≤ s + j := Nat.le_add_right s j
    have hzeroAt :
        deterministicIntervalMartingaleTransform K M
          (G.sampledTime (s + j)) (G.sampledTime (s + j + 1))
          (G.sampledTime s) omega = 0 := by
      rw [deterministicIntervalMartingaleTransform_eq_zero_of_le K M
        (G.sampledTime_mono (Nat.le_succ (s + j)))
        (G.sampledTime_mono hsj)]
      change (0 : Real) = 0
      rfl
    dsimp [d]
    rw [hzeroAt]
    simp
    simp only [deterministicIntervalMartingaleTransform,
      stoppedProcess_const_apply]
  unfold ChronologicalGrid.martingaleIntegralProcess
  simp only [Finset.sum_apply]
  linarith

omit [MeasurableSpace Omega] in
private theorem finite_block_transform_eq_summation_by_parts
    (f g : Nat → Real) (s m : Nat) :
    ∑ j ∈ Finset.range m,
        f (s + j) * (g (s + j + 1) - g (s + j)) =
      f s * (g (s + m) - g s) +
        ∑ j ∈ Finset.range m,
          (f (s + j + 1) - f (s + j)) *
            (g (s + m) - g (s + j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hTail :
          (∑ j ∈ Finset.range m,
            (f (s + j + 1) - f (s + j)) *
              (g (s + (m + 1)) - g (s + j + 1))) =
            (∑ j ∈ Finset.range m,
              (f (s + j + 1) - f (s + j)) *
                (g (s + m) - g (s + j + 1))) +
              (f (s + m) - f s) *
                (g (s + (m + 1)) - g (s + m)) := by
        have hsumDelta :
            (f (s + m) - f s) *
                (g (s + (m + 1)) - g (s + m)) =
              ∑ x ∈ Finset.range m,
                (f (s + x + 1) - f (s + x)) *
                  (g (s + (m + 1)) - g (s + m)) := by
          have hsumf :
              (∑ x ∈ Finset.range m, (f (s + x + 1) - f (s + x))) =
                f (s + m) - f s := by
            simpa [Nat.add_assoc] using
              Finset.sum_range_sub (fun x => f (s + x)) m
          rw [← hsumf, Finset.sum_mul]
        rw [hsumDelta, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hTail]
      simp only [Nat.add_assoc]
      ring

omit [MeasurableSpace Omega] in
theorem finite_block_transform_abs_le
    (f g : Nat → Real) (s m : Nat) (C : Real)
    (hgc : ∀ j ≤ m, |g (s + j)| ≤ C) :
    |∑ j ∈ Finset.range m,
        f (s + j) * (g (s + j + 1) - g (s + j))| ≤
      |f s| * |g (s + m) - g s| +
        2 * C * ∑ j ∈ Finset.range m,
          |f (s + j + 1) - f (s + j)| := by
  rw [finite_block_transform_eq_summation_by_parts]
  have htail : ∀ j ∈ Finset.range m,
      |g (s + m) - g (s + j + 1)| ≤ 2 * C := by
    intro j hj
    have hjm : j < m := Finset.mem_range.mp hj
    have hj1m : j + 1 ≤ m := Nat.succ_le_iff.mpr hjm
    calc
      |g (s + m) - g (s + j + 1)| ≤
          |g (s + m)| + |g (s + j + 1)| := by
            calc
              |g (s + m) - g (s + j + 1)| =
                  |g (s + m) + -(g (s + j + 1))| := by
                    congr 1
              _ ≤ |g (s + m)| + |-(g (s + j + 1))| :=
                abs_add_le _ _
              _ = |g (s + m)| + |g (s + j + 1)| := by rw [abs_neg]
      _ ≤ C + C := add_le_add (hgc m le_rfl) (hgc (j + 1) hj1m)
      _ = 2 * C := by ring
  have hsum :
      (∑ j ∈ Finset.range m,
        |f (s + j + 1) - f (s + j)| *
          |g (s + m) - g (s + j + 1)|) ≤
        ∑ j ∈ Finset.range m,
          |f (s + j + 1) - f (s + j)| * (2 * C) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (htail j hj) (abs_nonneg _)
  calc
    |f s * (g (s + m) - g s) +
        ∑ j ∈ Finset.range m,
          (f (s + j + 1) - f (s + j)) *
            (g (s + m) - g (s + j + 1))| ≤
      |f s * (g (s + m) - g s)| +
        |∑ j ∈ Finset.range m,
          (f (s + j + 1) - f (s + j)) *
            (g (s + m) - g (s + j + 1))| := abs_add_le _ _
    _ ≤ |f s| * |g (s + m) - g s| +
        ∑ j ∈ Finset.range m,
          |f (s + j + 1) - f (s + j)| *
            |g (s + m) - g (s + j + 1)| := by
      apply add_le_add
      · rw [abs_mul]
      · simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
          (fun j => (f (s + j + 1) - f (s + j)) *
            (g (s + m) - g (s + j + 1))) (Finset.range m)
    _ ≤ |f s| * |g (s + m) - g s| +
        ∑ j ∈ Finset.range m,
          |f (s + j + 1) - f (s + j)| * (2 * C) :=
      add_le_add_right hsum _
    _ = |f s| * |g (s + m) - g s| +
        2 * C * ∑ j ∈ Finset.range m,
          |f (s + j + 1) - f (s + j)| := by
      rw [← Finset.sum_mul]
      ring

omit [MeasurableSpace Omega] in
theorem sum_shifted_range_le_of_nonneg
    (f : Nat → Real) (s m L : Nat) (hs : s + m ≤ L)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ j ∈ Finset.range m, f (s + j)) ≤
      ∑ i ∈ Finset.range L, f i := by
  have hMap :
      (∑ j ∈ Finset.range m, f (s + j)) =
        ∑ i ∈ Finset.Ico s (s + m), f i := by
    have h := Finset.sum_Ico_add f 0 m s
    rw [show (0 + s : Nat) = s by simp,
      show m + s = s + m by omega] at h
    simpa using h
  rw [hMap]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    have hil : i < s + m := (Finset.mem_Ico.mp hi).2
    exact Finset.mem_range.mpr (hil.trans_le hs)
  · intro i hi hnot
    exact hf i

omit [MeasurableSpace Omega] in
private theorem sum_range_block_eq
    (m N : Nat) (F : Nat → Real) :
    ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range m, F (m * k + j) =
      ∑ i ∈ Finset.range (m * N), F i := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]

omit [MeasurableSpace Omega] in
theorem rowCommonLevel_ge_self
    (u : ∀ n, TailConvexWeights n) (n : Nat) :
    n ≤ rowCommonLevel u n := by
  have hne : (u n).support ≠ ∅ := by
    intro h
    have hsum := (u n).sum_eq_one
    rw [h] at hsum
    simp at hsum
  obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact ((u n).tail r hr).trans (rowCommonLevel_ge u n r hr)

omit [MeasurableSpace Omega] in
theorem finite_partition_transform_variation_le
    (m N : Nat) (f g : Nat → Real) (C VF VG CF : Real)
    (hC : 0 ≤ C) (hCF : 0 ≤ CF)
    (hF : (∑ i ∈ Finset.range (m * N),
        |f (i + 1) - f i|) ≤ VF)
    (hG : (∑ k ∈ Finset.range N,
        |g (m * (k + 1)) - g (m * k)|) ≤ VG)
    (hfs : ∀ k, k < N → |f (m * k)| ≤ CF)
    (hgc : ∀ k, k < N → ∀ j, j ≤ m → |g (m * k + j)| ≤ C) :
    (∑ k ∈ Finset.range N,
      |∑ j ∈ Finset.range m,
        f (m * k + j) * (g (m * k + j + 1) - g (m * k + j))|) ≤
      2 * C * VF + CF * VG := by
  have hblock : ∀ k, k < N →
      |∑ j ∈ Finset.range m,
        f (m * k + j) * (g (m * k + j + 1) - g (m * k + j))| ≤
        |f (m * k)| * |g (m * (k + 1)) - g (m * k)| +
          2 * C * ∑ j ∈ Finset.range m,
            |f (m * k + j + 1) - f (m * k + j)| := by
    intro k hk
    have h := finite_block_transform_abs_le f g (m * k) m C
      (fun j hj => hgc k hk j hj)
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hEndpoint :
      (∑ k ∈ Finset.range N,
        |f (m * k)| * |g (m * (k + 1)) - g (m * k)|) ≤ CF * VG := by
    calc
      (∑ k ∈ Finset.range N,
          |f (m * k)| * |g (m * (k + 1)) - g (m * k)|) ≤
          ∑ k ∈ Finset.range N,
            CF * |g (m * (k + 1)) - g (m * k)| := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right
          (hfs k (Finset.mem_range.mp hk)) (abs_nonneg _)
      _ = CF * (∑ k ∈ Finset.range N,
          |g (m * (k + 1)) - g (m * k)|) := by
        rw [Finset.mul_sum]
      _ ≤ CF * VG := mul_le_mul_of_nonneg_left hG hCF
  have hCoefficient :
      (∑ k ∈ Finset.range N,
        2 * C * ∑ j ∈ Finset.range m,
          |f (m * k + j + 1) - f (m * k + j)|) ≤ 2 * C * VF := by
    calc
      (∑ k ∈ Finset.range N,
          2 * C * ∑ j ∈ Finset.range m,
            |f (m * k + j + 1) - f (m * k + j)|) =
          2 * C * (∑ k ∈ Finset.range N,
            ∑ j ∈ Finset.range m,
              |f (m * k + j + 1) - f (m * k + j)|) := by
        rw [Finset.mul_sum]
      _ = 2 * C * (∑ i ∈ Finset.range (m * N),
          |f (i + 1) - f i|) := by
        rw [sum_range_block_eq m N (fun i => |f (i + 1) - f i|)]
      _ ≤ 2 * C * VF := mul_le_mul_of_nonneg_left hF (by positivity)
  calc
    (∑ k ∈ Finset.range N,
        |∑ j ∈ Finset.range m,
          f (m * k + j) * (g (m * k + j + 1) - g (m * k + j))|) ≤
        ∑ k ∈ Finset.range N,
          (|f (m * k)| * |g (m * (k + 1)) - g (m * k)| +
            2 * C * ∑ j ∈ Finset.range m,
              |f (m * k + j + 1) - f (m * k + j)|) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hblock k (Finset.mem_range.mp hk)
    _ = (∑ k ∈ Finset.range N,
        |f (m * k)| * |g (m * (k + 1)) - g (m * k)|) +
        (∑ k ∈ Finset.range N,
          2 * C * ∑ j ∈ Finset.range m,
            |f (m * k + j + 1) - f (m * k + j)|) := by
      rw [Finset.sum_add_distrib]
    _ ≤ CF * VG + 2 * C * VF := add_le_add hEndpoint hCoefficient
    _ = 2 * C * VF + CF * VG := by ring

noncomputable def rowInverseResidualGain
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (_hAlphaStop : IsStoppingTime F alpha) : Process Omega :=
  (grid T (rowCommonLevel u n)).martingaleIntegralProcess
    (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
      u n a T alpha)
    (nativeResidualConvexRow u n hUsual source ha T)

private theorem rowInverseResidualGain_baseGrid_increment_eq_block
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (k : Nat) (hk : k < size T n) (omega : Omega) :
    rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
        ((grid T n).sampledTime (k + 1)) omega -
      rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
        ((grid T n).sampledTime k) omega =
      ∑ j ∈ Finset.range (factorialRatio n (rowCommonLevel u n)),
        rowInverseCoefficient u n a T S F mu alpha
            (factorialRatio n (rowCommonLevel u n) * k + j) omega *
          (nativeResidualConvexRow u n hUsual source ha T
              ((grid T (rowCommonLevel u n)).sampledTime
                (factorialRatio n (rowCommonLevel u n) * k + j + 1)) omega -
            nativeResidualConvexRow u n hUsual source ha T
              ((grid T (rowCommonLevel u n)).sampledTime
                (factorialRatio n (rowCommonLevel u n) * k + j)) omega) := by
  classical
  let q := rowCommonLevel u n
  let m := factorialRatio n q
  let N := size T n
  let L := size T q
  let G := grid T q
  let H := grid T n
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := nativeResidualConvexRow u n hUsual source ha T
  let f : Nat → Real := fun i =>
    rowInverseCoefficient u n a T S F mu alpha i omega
  let g : Nat → Real := fun i => M (G.sampledTime i) omega
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
  have hK_eq : ∀ j, j < L → K (G.sampledTime j) omega = f j := by
    intro j hj
    dsimp [K, f, G, q]
    exact rowInverseCoefficientProcess_at_sampledTime u n a T alpha j hj omega
  have hprefix1 :
      G.martingaleIntegralProcess K M (G.sampledTime (m * (k + 1))) omega =
        ∑ j ∈ Finset.range (m * (k + 1)),
          f j * (g (j + 1) - g j) := by
    rw [martingaleIntegralProcess_at_sampledTime_eq_prefix G K M
      (m * (k + 1)) hmk1 omega]
    apply Finset.sum_congr rfl
    intro j hj
    have hjL : j < L := lt_of_lt_of_le
      (Finset.mem_range.mp hj) hmk1
    rw [hK_eq j hjL]
  have hprefix0 :
      G.martingaleIntegralProcess K M (G.sampledTime (m * k)) omega =
        ∑ j ∈ Finset.range (m * k),
          f j * (g (j + 1) - g j) := by
    rw [martingaleIntegralProcess_at_sampledTime_eq_prefix G K M
      (m * k) hmk omega]
    apply Finset.sum_congr rfl
    intro j hj
    have hjL : j < L := lt_of_lt_of_le
      (Finset.mem_range.mp hj) hmk
    rw [hK_eq j hjL]
  have hsplit :
      (∑ j ∈ Finset.range (m * (k + 1)),
        f j * (g (j + 1) - g j)) =
        (∑ j ∈ Finset.range (m * k),
          f j * (g (j + 1) - g j)) +
          ∑ j ∈ Finset.range m,
            f (m * k + j) *
              (g (m * k + j + 1) - g (m * k + j)) := by
    rw [Nat.mul_succ, Finset.sum_range_add]
  change G.martingaleIntegralProcess K M (H.sampledTime (k + 1)) omega -
      G.martingaleIntegralProcess K M (H.sampledTime k) omega = _
  rw [← htime1, ← htime0, hprefix1, hprefix0, hsplit]
  simp only [g, M, G, q, m]
  ring

theorem rowInverseResidualGain_baseGridVariation_le_of_bounds
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    {VT CT CB VB : Real} (hCT : 0 ≤ CT) (hCB : 0 ≤ CB)
    (hCoeffVar : ∀ omega,
      (∑ i ∈ Finset.range (size T (rowCommonLevel u n)),
        |rowInverseCoefficient u n a T S F mu alpha (i + 1) omega -
          rowInverseCoefficient u n a T S F mu alpha i omega|) ≤ VT)
    (hCoeffBound : ∀ i omega,
      |rowInverseCoefficient u n a T S F mu alpha i omega| ≤ CT)
    (hResidualSup : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |nativeResidualConvexRow u n hUsual source ha T t omega| ≤ CB)
    (hResidualVar : ∀ᵐ omega ∂mu,
      nativeResidualConvexRow_baseGridVariation u n hUsual source ha T omega ≤ VB) :
    ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
            ((grid T n).sampledTime (k + 1)) omega -
          rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
            ((grid T n).sampledTime k) omega|) ≤
        2 * CB * VT + CT * VB := by
  classical
  let q := rowCommonLevel u n
  let m := factorialRatio n q
  let N := size T n
  let L := size T q
  let G := grid T q
  let H := grid T n
  let f : Nat → Omega → Real := fun i omega =>
    rowInverseCoefficient u n a T S F mu alpha i omega
  let g : Nat → Omega → Real := fun i omega =>
    nativeResidualConvexRow u n hUsual source ha T (G.sampledTime i) omega
  have hnq : n ≤ q := by
    dsimp [q]
    exact rowCommonLevel_ge_self u n
  have hmpos : 0 < m := by
    dsimp [m]
    exact factorialRatio_pos n q hnq
  have hsize : m * N = L := by
    dsimp [m, N, L, q]
    exact factorialRatio_mul_size T n (rowCommonLevel u n) hnq
  have htime_block : ∀ k, k < N → ∀ j, j ≤ m →
      G.sampledTime (m * k + j) ≤ T := by
    intro k hk j hj
    have hkj : m * k + j ≤ L := by
      calc
        m * k + j ≤ m * k + m := by omega
        _ = m * (k + 1) := by rw [Nat.mul_succ]
        _ ≤ L := by
          rw [← hsize]
          exact Nat.mul_le_mul_left m (Nat.succ_le_iff.mpr hk)
    exact (G.sampledTime_mono hkj).trans_eq (sampledTime_size T q)
  have htime_base : ∀ k, k ≤ N →
      G.sampledTime (m * k) = H.sampledTime k := by
    intro k hk
    dsimp [G, H, m, q]
    simpa [factorialGridEmbedding] using
      (factorialGridEmbedding_sampledTime T n (rowCommonLevel u n)
        hnq k hk)
  have hInc : ∀ k, k < N → ∀ omega,
      rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
          (H.sampledTime (k + 1)) omega -
        rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
          (H.sampledTime k) omega =
      ∑ j ∈ Finset.range m,
        f (m * k + j) omega *
          (g (m * k + j + 1) omega - g (m * k + j) omega) := by
    intro k hk omega
    have h := rowInverseResidualGain_baseGrid_increment_eq_block
      u n hUsual source ha T alpha hAlphaStop k hk omega
    simpa [f, g, H, m, q, G] using h
  have hIncAll : ∀ᵐ omega ∂mu, ∀ k ∈ Finset.range N,
      rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
          (H.sampledTime (k + 1)) omega -
      rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
          (H.sampledTime k) omega =
      ∑ j ∈ Finset.range m,
        f (m * k + j) omega *
          (g (m * k + j + 1) omega - g (m * k + j) omega) := by
    exact Filter.Eventually.of_forall (fun omega k hk =>
      hInc k (Finset.mem_range.mp hk) omega)
  filter_upwards [hResidualSup, hResidualVar, hIncAll] with omega hSup hVar hIncOmega
  let fω : Nat → Real := fun i => f i omega
  let gω : Nat → Real := fun i => g i omega
  have hF :
      (∑ i ∈ Finset.range (m * N), |fω (i + 1) - fω i|) ≤ VT := by
    simpa [fω, f, L, q, hsize] using hCoeffVar omega
  have hG :
      (∑ k ∈ Finset.range N,
        |gω (m * (k + 1)) - gω (m * k)|) ≤ VB := by
    calc
      (∑ k ∈ Finset.range N,
          |gω (m * (k + 1)) - gω (m * k)|) =
          ∑ k ∈ Finset.range N,
            |nativeResidualConvexRow u n hUsual source ha T
                (H.sampledTime (k + 1)) omega -
              nativeResidualConvexRow u n hUsual source ha T
                (H.sampledTime k) omega| := by
        apply Finset.sum_congr rfl
        intro k hk
        change |nativeResidualConvexRow u n hUsual source ha T
            (G.sampledTime (m * (k + 1))) omega -
              nativeResidualConvexRow u n hUsual source ha T
                (G.sampledTime (m * k)) omega| = _
        rw [htime_base (k + 1)
              (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)),
          htime_base k (Finset.mem_range.mp hk).le]
      _ = nativeResidualConvexRow_baseGridVariation u n hUsual source ha T omega := by
        rfl
      _ ≤ VB := hVar
  have hfs : ∀ k, k < N → |fω (m * k)| ≤ CT := by
    intro k hk
    simpa [fω, f] using hCoeffBound (m * k) omega
  have hgc : ∀ k, k < N → ∀ j, j ≤ m → |gω (m * k + j)| ≤ CB := by
    intro k hk j hj
    simpa [gω, g] using
      hSup (G.sampledTime (m * k + j)) (htime_block k hk j hj)
  have hBound := finite_partition_transform_variation_le m N fω gω CB VT VB CT
    hCB hCT hF hG hfs hgc
  calc
    (∑ k ∈ Finset.range N,
        |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
            (H.sampledTime (k + 1)) omega -
          rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
          (H.sampledTime k) omega|) =
        ∑ k ∈ Finset.range N,
          |∑ j ∈ Finset.range m,
            fω (m * k + j) *
              (gω (m * k + j + 1) - gω (m * k + j))| := by
      apply Finset.sum_congr rfl
      intro k hk
      simpa [fω, gω] using congrArg abs (hIncOmega k hk)
    _ ≤ 2 * CB * VT + CT * VB := hBound

theorem rowInverseResidualGain_baseGridVariation_le_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 < a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |rowInverseResidualGain u n hUsual source ha.le T alpha hAlphaStop
            ((grid T n).sampledTime (k + 1)) omega -
          rowInverseResidualGain u n hUsual source ha.le T alpha hAlphaStop
            ((grid T n).sampledTime k) omega|) ≤
        6 * (a + 4 * max source.bound 0) +
          2 * (a + 2 * max source.bound 0) := by
  have hCB : 0 ≤ a + 4 * max source.bound 0 := by
    have hbound : 0 ≤ max source.bound 0 := le_max_right _ _
    linarith
  have h := rowInverseResidualGain_baseGridVariation_le_of_bounds
    (u := u) (n := n) (hUsual := hUsual) (source := source)
    (ha := ha.le) (T := T) (alpha := alpha) (hAlphaStop := hAlphaStop)
    (VT := 3) (CT := 2) (CB := a + 4 * max source.bound 0)
    (VB := a + 2 * max source.bound 0) (by norm_num) hCB
    (fun omega => rowInverseCoefficient_variation_le_three
      u n a ha T alpha hAlpha omega)
    (fun i omega => rowInverseCoefficient_uniform_abs_le_two_of_le_hitting
      u n a T S F mu alpha hAlpha i omega)
    (nativeResidualConvexRow_ae_abs_le_on_horizon u n hUsual source ha.le T)
    (nativeResidualConvexRow_baseGridVariation_le_ae u n hUsual source ha.le T)
  filter_upwards [h] with omega hOmega
  convert hOmega using 1; ring

omit [MeasurableSpace Omega] in
theorem martingaleIntegralProcess_at_zero
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K M : Process Omega) (omega : Omega) :
    G.martingaleIntegralProcess K M 0 omega = 0 := by
  unfold ChronologicalGrid.martingaleIntegralProcess
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [deterministicIntervalMartingaleTransform_eq_zero_of_le K M
    (G.sampledTime_mono (Nat.le_succ j)) (by exact bot_le)]
  change (0 : Real) = 0
  rfl

theorem rowInverseResidualGain_horizon_sup_le_of_bounds
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    {VT CT CB VB VD : Real} (hCT : 0 ≤ CT) (hCB : 0 ≤ CB)
    (hVD : 0 ≤ VD)
    (hCoeffVar : ∀ omega,
      (∑ i ∈ Finset.range (size T (rowCommonLevel u n)),
        |rowInverseCoefficient u n a T S F mu alpha (i + 1) omega -
          rowInverseCoefficient u n a T S F mu alpha i omega|) ≤ VT)
    (hCoeffBound : ∀ i omega,
      |rowInverseCoefficient u n a T S F mu alpha i omega| ≤ CT)
    (hResidualSup : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |nativeResidualConvexRow u n hUsual source ha T t omega| ≤ CB)
    (hGainVar : ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
            ((grid T n).sampledTime (k + 1)) omega -
          rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
            ((grid T n).sampledTime k) omega|) ≤ VB)
    (hCellIncrement : ∀ᵐ omega ∂mu, ∀ k, k < size T n → ∀ t,
      (grid T n).sampledTime k ≤ t →
        t ≤ (grid T n).sampledTime (k + 1) →
      |nativeResidualConvexRow u n hUsual source ha T t omega -
        nativeResidualConvexRow u n hUsual source ha T
          ((grid T n).sampledTime k) omega| ≤ VD) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop t omega| ≤
        VB + CT * VD + 2 * CB * VT := by
  classical
  let q := rowCommonLevel u n
  let m := factorialRatio n q
  let N := size T n
  let L := size T q
  let G := grid T q
  let H := grid T n
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := nativeResidualConvexRow u n hUsual source ha T
  filter_upwards [hResidualSup, hGainVar, hCellIncrement] with omega hSup hVar hCell
  intro t ht
  by_cases hT0 : T = 0
  · have ht0 : t = 0 := by
      have ht_le_zero : t ≤ 0 := by simpa [hT0] using ht
      exact le_antisymm ht_le_zero (by positivity)
    subst t
    subst T
    unfold rowInverseResidualGain
    rw [martingaleIntegralProcess_at_zero
      (grid 0 (rowCommonLevel u n))
      (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
        u n a 0 alpha)
      (nativeResidualConvexRow u n hUsual source ha 0) omega]
    have hVT : 0 ≤ VT := by
      simpa [size] using hCoeffVar omega
    have hVB : 0 ≤ VB := by
      simpa [size] using hVar
    simp only [abs_zero]
    positivity
  · have hTpos : 0 < T := pos_of_ne_zero hT0
    obtain ⟨k, hk, hleft, hright⟩ :=
      grid_exists_cell_of_pos T n t ht hTpos
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
    have hK_eq : ∀ j, j < L → K (G.sampledTime j) omega =
        rowInverseCoefficient u n a T S F mu alpha j omega := by
      intro j hj
      dsimp [K, G, q]
      exact rowInverseCoefficientProcess_at_sampledTime u n a T alpha j hj omega
    have hPrefix :
        |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
            (H.sampledTime k) omega| ≤ VB := by
      have hPrefixEq :
          rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
              (H.sampledTime k) omega =
            ∑ i ∈ Finset.range k,
              (rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                  (H.sampledTime (i + 1)) omega -
                rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                  (H.sampledTime i) omega) := by
        have hzero : rowInverseResidualGain u n hUsual source ha T alpha
              hAlphaStop (H.sampledTime 0) omega = 0 := by
          dsimp [H]
          unfold rowInverseResidualGain
          have hH0 : (grid T n).sampledTime 0 = 0 := by
            simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
              grid_time]
          rw [hH0]
          exact martingaleIntegralProcess_at_zero
            (grid T (rowCommonLevel u n))
            (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
              u n a T alpha)
            (nativeResidualConvexRow u n hUsual source ha T) omega
        calc
          rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
              (H.sampledTime k) omega =
              rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                (H.sampledTime k) omega - 0 := by simp
          _ = rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                (H.sampledTime k) omega -
              rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                (H.sampledTime 0) omega := by rw [hzero]
          _ = ∑ i ∈ Finset.range k,
              (rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                  (H.sampledTime (i + 1)) omega -
                rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                  (H.sampledTime i) omega) := by
            exact (Finset.sum_range_sub
              (fun i => rowInverseResidualGain u n hUsual source ha T alpha
                hAlphaStop (H.sampledTime i) omega) k).symm
      rw [hPrefixEq]
      calc
        |∑ i ∈ Finset.range k,
            (rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                (H.sampledTime (i + 1)) omega -
              rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                (H.sampledTime i) omega)| ≤
            ∑ i ∈ Finset.range k,
              |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                  (H.sampledTime (i + 1)) omega -
                rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                  (H.sampledTime i) omega| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range N,
              |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                  (H.sampledTime (i + 1)) omega -
                rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                  (H.sampledTime i) omega| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            exact Finset.mem_range.mpr
              ((Finset.mem_range.mp hi).trans_le hk.le)
          · intro i hi hnot
            exact abs_nonneg _
        _ ≤ VB := by simpa [H] using hVar
    have hleftG : G.sampledTime (m * k) ≤ t := by
      rw [htime0]
      exact hleft
    have hrightG : t ≤ G.sampledTime (m * k + m) := by
      rw [show m * k + m = m * (k + 1) by rw [Nat.mul_succ], htime1]
      exact hright
    have hBlockRaw := martingaleIntegralProcess_diff_eq_block G K M t
      (m * k) m hmk1 hleftG hrightG omega
    let fω : Nat → Real := fun i =>
      rowInverseCoefficient u n a T S F mu alpha i omega
    let gω : Nat → Real := fun i =>
      nativeResidualConvexRow u n hUsual source ha T
        (min t (G.sampledTime i)) omega
    have hBlock :
        rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop t omega -
            rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
              (H.sampledTime k) omega =
          ∑ j ∈ Finset.range m,
            fω (m * k + j) *
              (gω (m * k + j + 1) - gω (m * k + j)) := by
      change G.martingaleIntegralProcess K M t omega -
          G.martingaleIntegralProcess K M (H.sampledTime k) omega = _
      rw [← htime0, hBlockRaw]
      apply Finset.sum_congr rfl
      intro j hj
      have hjL : m * k + j < L := by
        have hjm : j < m := Finset.mem_range.mp hj
        calc
          m * k + j < m * k + m := Nat.add_lt_add_left hjm _
          _ = m * (k + 1) := by rw [Nat.mul_succ]
          _ ≤ L := hmk1
      dsimp [fω, gω]
      rw [hK_eq (m * k + j) hjL]
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
    have hgc : ∀ j, j ≤ m → |gω (m * k + j)| ≤ CB := by
      intro j hj
      dsimp [gω]
      apply hSup
      exact (min_le_left _ _).trans ht
    have hEndpoint :
        |gω (m * k + m) - gω (m * k)| ≤ VD := by
      have h := hCell k hk t hleft hright
      have hmin0 : min t (G.sampledTime (m * k)) = H.sampledTime k := by
        calc
          min t (G.sampledTime (m * k)) = G.sampledTime (m * k) :=
            min_eq_right hleftG
          _ = H.sampledTime k := htime0
      have hmin1 : min t (G.sampledTime (m * k + m)) = t := by
        exact min_eq_left hrightG
      dsimp [gω]
      rw [hmin1, hmin0]
      exact h
    have hfs : |fω (m * k)| ≤ CT := by
      dsimp [fω]
      exact hCoeffBound (m * k) omega
    have hTransform := finite_block_transform_abs_le fω gω
      (m * k) m CB hgc
    have hCurrent :
        |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop t omega -
            rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
              (H.sampledTime k) omega| ≤
          CT * VD + 2 * CB * VT := by
      rw [hBlock]
      calc
        |∑ j ∈ Finset.range m,
            fω (m * k + j) *
              (gω (m * k + j + 1) - gω (m * k + j))| ≤
            |fω (m * k)| *
                |gω (m * k + m) - gω (m * k)| +
              2 * CB *
                ∑ j ∈ Finset.range m,
                  |fω (m * k + j + 1) - fω (m * k + j)| := hTransform
        _ ≤ CT * VD + 2 * CB * VT := by
          apply add_le_add
          · exact mul_le_mul hfs hEndpoint (abs_nonneg _) hCT
          · exact mul_le_mul_of_nonneg_left hFblock (by positivity)
    calc
      |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop t omega| =
          |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
              (H.sampledTime k) omega +
            (rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop t omega -
              rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                (H.sampledTime k) omega)| := by
        congr 1
        ring
      _ ≤
          |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
              (H.sampledTime k) omega| +
            |rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop t omega -
              rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop
                (H.sampledTime k) omega| := abs_add_le _ _
      _ ≤ VB + (CT * VD + 2 * CB * VT) :=
        add_le_add hPrefix hCurrent
      _ = VB + CT * VD + 2 * CB * VT := by ring

theorem rowInverseResidualGain_horizon_sup_le_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 < a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |rowInverseResidualGain u n hUsual source ha.le T alpha hAlphaStop t omega| ≤
        16 * (a + 4 * max source.bound 0) +
          2 * (a + 2 * max source.bound 0) := by
  have hCB : 0 ≤ a + 4 * max source.bound 0 := by
    have hbound : 0 ≤ max source.bound 0 := le_max_right _ _
    linarith
  have hSup := nativeResidualConvexRow_ae_abs_le_on_horizon
    u n hUsual source ha.le T
  have hCell : ∀ᵐ omega ∂mu, ∀ k, k < size T n → ∀ t,
      (grid T n).sampledTime k ≤ t →
        t ≤ (grid T n).sampledTime (k + 1) →
      |nativeResidualConvexRow u n hUsual source ha.le T t omega -
        nativeResidualConvexRow u n hUsual source ha.le T
          ((grid T n).sampledTime k) omega| ≤
        2 * (a + 4 * max source.bound 0) := by
    filter_upwards [hSup] with omega hOmega
    intro k hk t hleft hright
    have hleftT : (grid T n).sampledTime k ≤ T :=
      (grid T n).sampledTime_mono hk.le |>.trans_eq (sampledTime_size T n)
    have hrightT : (grid T n).sampledTime (k + 1) ≤ T :=
      (grid T n).sampledTime_mono (Nat.succ_le_iff.mpr hk) |>.trans_eq
        (sampledTime_size T n)
    calc
      |nativeResidualConvexRow u n hUsual source ha.le T t omega -
          nativeResidualConvexRow u n hUsual source ha.le T
            ((grid T n).sampledTime k) omega| ≤
        |nativeResidualConvexRow u n hUsual source ha.le T t omega| +
          |nativeResidualConvexRow u n hUsual source ha.le T
            ((grid T n).sampledTime k) omega| := abs_sub _ _
      _ ≤ (a + 4 * max source.bound 0) +
          (a + 4 * max source.bound 0) := add_le_add
        (hOmega t (hright.trans hrightT))
        (hOmega ((grid T n).sampledTime k) hleftT)
      _ = 2 * (a + 4 * max source.bound 0) := by ring
  have hGainVar := rowInverseResidualGain_baseGridVariation_le_ae
    u n hUsual source ha T alpha hAlphaStop hAlpha
  have hBound := rowInverseResidualGain_horizon_sup_le_of_bounds
    (u := u) (n := n) (hUsual := hUsual) (source := source)
    (ha := ha.le) (T := T) (alpha := alpha) (hAlphaStop := hAlphaStop)
    hAlpha (VT := 3) (CT := 2)
    (CB := a + 4 * max source.bound 0)
    (VB := 6 * (a + 4 * max source.bound 0) +
      2 * (a + 2 * max source.bound 0))
    (VD := 2 * (a + 4 * max source.bound 0))
    (by norm_num) hCB (by positivity) (by
      intro omega
      exact rowInverseCoefficient_variation_le_three
        u n a ha T alpha hAlpha omega) (by
      intro i omega
      exact rowInverseCoefficient_uniform_abs_le_two_of_le_hitting
        u n a T S F mu alpha hAlpha i omega)
    hSup hGainVar hCell
  filter_upwards [hBound] with omega hOmega
  convert hOmega using 1
  ring_nf

/-! ## The actual `L²` martingale row -/

theorem nativeMartingaleProcess_memLp_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) (t : NNReal) :
    MemLp (nativeMartingaleProcess hUsual source ha T r t)
      (2 : ℝ≥0∞) mu := by
  let terminal := nativeMartingaleTerminal source ha T r
  have hTerminal : MemLp (terminal : Omega → Real) (2 : ℝ≥0∞) mu :=
    Lp.memLp terminal
  have hCond : MemLp
      (condExpMartingaleProcess mu F terminal t)
      (2 : ℝ≥0∞) mu := by
    change MemLp (mu[(terminal : Omega → Real) | F t])
      (2 : ℝ≥0∞) mu
    exact hTerminal.condExp (by norm_num)
  have hVersion := (nativeMartingaleProcess_spec hUsual source ha T r).2.2.2 t
  exact hCond.ae_eq hVersion.symm

theorem nativeMartingaleConvexRow_memLp_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T t : NNReal) :
    MemLp (nativeMartingaleConvexRow u n hUsual source ha T t)
      (2 : ℝ≥0∞) mu := by
  classical
  unfold nativeMartingaleConvexRow TailConvexWeights.apply
  induction (u n).support using Finset.induction_on with
  | empty =>
      simp
  | @insert r s hrs ih =>
      have hsum :=
        (nativeMartingaleProcess_memLp_two hUsual source ha T r t).const_smul
          ((u n).weight r) |>.add ih
      convert hsum using 1
      ext omega
      simp [Finset.sum_insert hrs, smul_eq_mul]

noncomputable def rowInverseMartingaleGain
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (_hAlphaStop : IsStoppingTime F alpha) : Process Omega :=
  (grid T (rowCommonLevel u n)).martingaleIntegralProcess
    (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
      u n a T alpha)
    (nativeMartingaleConvexRow u n hUsual source ha T)

theorem rowInverseStrategy_gain_eq_martingale_add_residual
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (t : NNReal) (omega : Omega) :
    ElementaryStrategy.gain
        (nativeGateGainConvexRow u n a T S F mu)
        (rowInverseStrategy (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop).toElementary
        t omega =
      rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop t omega +
        rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop t omega := by
  let q := rowCommonLevel u n
  let G := grid T q
  rw [show rowInverseStrategy (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop =
      G.adaptedElementaryStrategy F
        (rowInverseCoefficient u n a T S F mu alpha)
        (rowInverseCoefficient_stronglyAdapted
          (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop) by
    rfl]
  rw [adaptedElementaryStrategy_gain_at]
  unfold rowInverseMartingaleGain rowInverseResidualGain
    ChronologicalGrid.martingaleIntegralProcess
  simp only [Finset.sum_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < size T q := Finset.mem_range.mp hk
  simp only [deterministicIntervalMartingaleTransform,
    stoppedProcess_const_apply]
  rw [rowInverseCoefficientProcess_at_sampledTime u n a T alpha k hk' omega]
  have hGate := congrFun (congrFun
    (nativeGateGainConvexRow_eq_martingale_add_residual u n hUsual source ha T)
    (min t (G.sampledTime (k + 1)))) omega
  have hGate' := congrFun (congrFun
    (nativeGateGainConvexRow_eq_martingale_add_residual u n hUsual source ha T)
    (min t (G.sampledTime k))) omega
  simp only [Pi.add_apply] at hGate hGate'
  rw [hGate, hGate']
  ring

theorem rowInverseMartingaleGain_martingale
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    Martingale
      (rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop) F mu := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := nativeMartingaleConvexRow u n hUsual source ha T
  have hK : StronglyAdapted F K := by
    exact rowInverseCoefficientProcess_stronglyAdapted
      (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop
  have hKBound : ∀ t, ∀ᵐ omega ∂mu, |K t omega| ≤ (2 : Real) := by
    intro t
    exact Filter.Eventually.of_forall fun omega =>
      rowInverseCoefficientProcess_abs_le_two u n a T alpha hAlpha t omega
  have hM : Martingale M F mu :=
    nativeMartingaleConvexRow_martingale u n hUsual source ha T
  have hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t :=
    nativeMartingaleConvexRow_rightContinuous u n hUsual source ha T
  change Martingale (G.martingaleIntegralProcess K M) F mu
  exact G.martingaleIntegralProcess_isMartingale_of_stronglyAdapted
    hM hMRight hK hKBound

theorem rowInverseMartingaleGain_terminal_memLp_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    MemLp
      (rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop
        ((grid T (rowCommonLevel u n)).sampledTime (size T (rowCommonLevel u n))))
      (2 : ℝ≥0∞) mu := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := nativeMartingaleConvexRow u n hUsual source ha T
  have hM : Martingale M F mu :=
    nativeMartingaleConvexRow_martingale u n hUsual source ha T
  have hMLp : ∀ k, MemLp (G.natSample M k) (2 : ℝ≥0∞) mu := by
    intro k
    change MemLp (M (G.sampledTime k)) (2 : ℝ≥0∞) mu
    exact nativeMartingaleConvexRow_memLp_two u n hUsual source ha T
      (G.sampledTime k)
  have hK : StronglyAdapted F K := by
    exact rowInverseCoefficientProcess_stronglyAdapted
      (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop
  have hKBound : ∀ k, ∀ᵐ omega ∂mu, |G.natSample K k omega| ≤ (2 : Real) := by
    intro k
    exact Filter.Eventually.of_forall fun omega => by
      change |K (G.sampledTime k) omega| ≤ (2 : Real)
      exact rowInverseCoefficientProcess_abs_le_two u n a T alpha hAlpha
        (G.sampledTime k) omega
  have hDiscrete : MemLp
      (discretePredictableIntegral (G.natSample K) (G.natSample M)
        (size T q)) (2 : ℝ≥0∞) mu :=
    DiscretePredictableIntegral.memLp_two
      (ChronologicalGrid.Martingale.natSample (G := G) hM)
      hMLp (G.stronglyAdapted_natSample hK) hKBound (size T q)
  change MemLp
    (G.martingaleIntegralProcess K M (G.sampledTime (size T q)))
    (2 : ℝ≥0∞) mu
  rw [G.martingaleIntegralProcess_last K M]
  exact hDiscrete

theorem rowInverseMartingaleGain_terminal_L2_bound
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    MemLp
        (rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop
          ((grid T (rowCommonLevel u n)).sampledTime
            (size T (rowCommonLevel u n))))
        (2 : ℝ≥0∞) mu ∧
      (∫ omega,
        (rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop
          ((grid T (rowCommonLevel u n)).sampledTime
            (size T (rowCommonLevel u n))) omega) ^ 2 ∂mu) ≤
        4 * (∫ omega,
          (nativeMartingaleConvexRow u n hUsual source ha T T omega -
            nativeMartingaleConvexRow u n hUsual source ha T 0 omega) ^ 2 ∂mu) := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := nativeMartingaleConvexRow u n hUsual source ha T
  have hMemLp := rowInverseMartingaleGain_terminal_memLp_two
    u n hUsual source ha T alpha hAlphaStop hAlpha
  have hMartingale : Martingale M F mu :=
    nativeMartingaleConvexRow_martingale u n hUsual source ha T
  have hMLp : ∀ k, MemLp (G.natSample M k) (2 : ℝ≥0∞) mu := by
    intro k
    change MemLp (M (G.sampledTime k)) (2 : ℝ≥0∞) mu
    exact nativeMartingaleConvexRow_memLp_two u n hUsual source ha T
      (G.sampledTime k)
  have hK : StronglyAdapted F K := by
    exact rowInverseCoefficientProcess_stronglyAdapted
      (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop
  have hKBound : ∀ k, ∀ᵐ omega ∂mu, |G.natSample K k omega| ≤ (2 : Real) := by
    intro k
    exact Filter.Eventually.of_forall fun omega => by
      change |K (G.sampledTime k) omega| ≤ (2 : Real)
      exact rowInverseCoefficientProcess_abs_le_two u n a T alpha hAlpha
        (G.sampledTime k) omega
  have hContract :
      (∫ omega,
        (discretePredictableIntegral (G.natSample K) (G.natSample M)
          (size T q) omega) ^ 2 ∂mu) ≤
        (2 : Real) ^ 2 * (∫ omega,
          (G.natSample M (size T q) omega - G.natSample M 0 omega) ^ 2 ∂mu) := by
    exact DiscretePredictableIntegral.integral_sq_le_mul_terminalIncrement_sq
      (ChronologicalGrid.Martingale.natSample (G := G) hMartingale)
      hMLp (G.stronglyAdapted_natSample hK) (by norm_num) hKBound (size T q)
  have hLast : G.sampledTime (size T q) = T := sampledTime_size T q
  have hZero : G.sampledTime 0 = 0 := by
    change (grid T q).sampledTime 0 = 0
    simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex, grid_time]
  have hIncrement :
      (fun omega =>
        (G.natSample M (size T q) omega - G.natSample M 0 omega) ^ 2) =
      (fun omega => (M T omega - M 0 omega) ^ 2) := by
    funext omega
    simp only [ChronologicalGrid.natSample, hLast, hZero]
  have hTerminal :
      rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop
          (G.sampledTime (size T q)) =
        discretePredictableIntegral (G.natSample K) (G.natSample M)
          (size T q) := by
    unfold rowInverseMartingaleGain
    exact G.martingaleIntegralProcess_last K M
  have hContract' :
      (∫ omega,
        (discretePredictableIntegral (G.natSample K) (G.natSample M)
          (size T q) omega) ^ 2 ∂mu) ≤
        4 * (∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu) := by
    rw [hIncrement] at hContract
    norm_num at hContract ⊢
    exact hContract
  refine ⟨?_, ?_⟩
  · simpa [q, G] using hMemLp
  · rw [hTerminal]
    simpa [q, G] using hContract'

theorem rowInverseStoppedSource_eq_martingale_add_residual
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (hNoCross : ∀ k, k < size T (rowCommonLevel u n) → ∀ omega,
      ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
          alpha omega →
        (grid T (rowCommonLevel u n)).sampledTime k <
          (grid T (rowCommonLevel u n)).sampledTime (k + 1) →
        ((grid T (rowCommonLevel u n)).sampledTime (k + 1) : WithTop NNReal) ≤
          alpha omega)
    (t : NNReal) (omega : Omega) :
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop t omega +
        rowInverseResidualGain u n hUsual source ha T alpha hAlphaStop t omega := by
  exact (rowInverseStrategy_gain_eq_stoppedSource_sub_initial
    (S := S) (F := F) (mu := mu) u n a T alpha
    hAlphaStop hAlpha hNoCross t omega).symm.trans
    (rowInverseStrategy_gain_eq_martingale_add_residual u n hUsual source ha T
      alpha hAlphaStop t omega)

/-! The row-level consumer gathers the coefficient variation, residual-gain
variation and horizon bounds, exact decomposition, and martingale estimates
for one common stopping row. -/

def RowInverseDecompositionData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 < a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha) : Prop :=
  (∀ omega,
    (∑ i ∈ Finset.range (size T (rowCommonLevel u n)),
      |rowInverseCoefficient u n a T S F mu alpha (i + 1) omega -
        rowInverseCoefficient u n a T S F mu alpha i omega|) ≤ 3) ∧
  (∀ᵐ omega ∂mu,
    (∑ k ∈ Finset.range (size T n),
      |rowInverseResidualGain u n hUsual source ha.le T alpha hAlphaStop
          ((grid T n).sampledTime (k + 1)) omega -
        rowInverseResidualGain u n hUsual source ha.le T alpha hAlphaStop
          ((grid T n).sampledTime k) omega|) ≤
      6 * (a + 4 * max source.bound 0) +
        2 * (a + 2 * max source.bound 0)) ∧
  (∀ᵐ omega ∂mu, ∀ t, t ≤ T →
    |rowInverseResidualGain u n hUsual source ha.le T alpha hAlphaStop t omega| ≤
      16 * (a + 4 * max source.bound 0) +
        2 * (a + 2 * max source.bound 0)) ∧
  (∀ t omega,
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      rowInverseMartingaleGain u n hUsual source ha.le T alpha hAlphaStop t omega +
        rowInverseResidualGain u n hUsual source ha.le T alpha hAlphaStop t omega) ∧
  Martingale
    (rowInverseMartingaleGain u n hUsual source ha.le T alpha hAlphaStop) F mu ∧
  (MemLp
      (rowInverseMartingaleGain u n hUsual source ha.le T alpha hAlphaStop
        ((grid T (rowCommonLevel u n)).sampledTime
          (size T (rowCommonLevel u n))))
      (2 : ℝ≥0∞) mu ∧
    (∫ omega,
      (rowInverseMartingaleGain u n hUsual source ha.le T alpha hAlphaStop
        ((grid T (rowCommonLevel u n)).sampledTime
          (size T (rowCommonLevel u n))) omega) ^ 2 ∂mu) ≤
      4 * (∫ omega,
        (nativeMartingaleConvexRow u n hUsual source ha.le T T omega -
          nativeMartingaleConvexRow u n hUsual source ha.le T 0 omega) ^ 2 ∂mu))

theorem rowInverseDecompositionData_of_hitting
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 < a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (hNoCross : ∀ k, k < size T (rowCommonLevel u n) → ∀ omega,
      ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
          alpha omega →
        (grid T (rowCommonLevel u n)).sampledTime k <
          (grid T (rowCommonLevel u n)).sampledTime (k + 1) →
        ((grid T (rowCommonLevel u n)).sampledTime (k + 1) : WithTop NNReal) ≤
          alpha omega) :
    RowInverseDecompositionData u n hUsual source ha T alpha hAlphaStop
      := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro omega
    exact rowInverseCoefficient_variation_le_three u n a ha T alpha hAlpha omega
  · exact rowInverseResidualGain_baseGridVariation_le_ae
      u n hUsual source ha T alpha hAlphaStop hAlpha
  · exact rowInverseResidualGain_horizon_sup_le_ae
      u n hUsual source ha T alpha hAlphaStop hAlpha
  · intro t omega
    exact rowInverseStoppedSource_eq_martingale_add_residual
      u n hUsual source ha.le T alpha hAlphaStop hAlpha hNoCross t omega
  · exact rowInverseMartingaleGain_martingale
      u n hUsual source ha.le T alpha hAlphaStop hAlpha
  · exact rowInverseMartingaleGain_terminal_L2_bound
      u n hUsual source ha.le T alpha hAlphaStop hAlpha

end HorizonFactorialGrid

end FTAPTheorem42
