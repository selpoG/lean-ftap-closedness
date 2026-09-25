/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.FiniteGridPredictableElementaryStrategy
import FTAPTheorem42.Stochastic.Integral.Elementary.DiscretePredictableIntegral
import FTAPTheorem42.Stochastic.Decomposition.Source.Variation

/-!
# Source-independent finite-grid compensator kernel

This module contains the finite-sum and predictable-step algebra shared by
the bounded and square-integrable compensator constructions.  The increment
sequence is an arbitrary sequence of real random variables.  Source-specific
facts (clipping, conditional-expectation equality, and moment estimates) are
supplied by the two adapters.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

/-- Source increment shared by bounded and square-integrable compensator rows. -/
noncomputable def gridIncrement
    (V : Process Ω) (T : NNReal) (r k : Nat) : Ω → Real :=
  fun omega => V ((grid T r).sampledTime (k + 1)) omega -
    V ((grid T r).sampledTime k) omega

/-- Conditional source increment before choosing a clipped representative. -/
noncomputable def rawCompensatorIncrement
    (V : Process Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T : NNReal) (r k : Nat) : Ω → Real :=
  mu[gridIncrement V T r k | F ((grid T r).sampledTime k)]

noncomputable def finiteGridCompensatorCumulative
    (_T : NNReal) (D : Nat → Ω → Real) (_r n : Nat) : Ω → Real :=
  fun omega => ∑ k ∈ Finset.range n, D k omega

noncomputable def finiteGridCompensatorStepTerm
    (T : NNReal) (D : Nat → Ω → Real) (r k : Nat) : Process Ω :=
  fun t omega =>
    if (grid T r).sampledTime k < t then D k omega else 0

noncomputable def finiteGridPredictableCompensatorProcess
    (T : NNReal) (D : Nat → Ω → Real) (r : Nat) : Process Ω :=
  fun t omega => ∑ k ∈ Finset.range (size T r),
    finiteGridCompensatorStepTerm T D r k t omega

omit [MeasurableSpace Ω] in
@[simp] theorem finiteGridCompensatorCumulative_succ
    (_T : NNReal) (D : Nat → Ω → Real) (_r n : Nat) :
    finiteGridCompensatorCumulative T D r (n + 1) =
      finiteGridCompensatorCumulative T D r n + D n := by
  funext omega
  simp [finiteGridCompensatorCumulative, Finset.sum_range_succ]

omit [MeasurableSpace Ω] in
theorem finiteGrid_sampledTime_le_horizon
    (T : NNReal) (r k : Nat) (hk : k ≤ size T r) :
    (grid T r).sampledTime k ≤ T := by
  exact ((grid T r).sampledTime_mono hk).trans_eq (sampledTime_size T r)

theorem finiteGridCompensatorStepTerm_isStronglyPredictable
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (T : NNReal) (D : Nat → Ω → Real) (r k : Nat)
    (hD : StronglyMeasurable[F ((grid T r).sampledTime k)] (D k)) :
    IsStronglyPredictable F
      (finiteGridCompensatorStepTerm T D r k) := by
  have hZero : MeasurableSet[F.predictable]
      (Ioi ((grid T r).sampledTime k) ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioi_prod MeasurableSet.univ
  apply Measurable.stronglyMeasurable
  intro u hu
  have hOn : MeasurableSet[F.predictable]
      (Ioi ((grid T r).sampledTime k) ×ˢ (D k ⁻¹' u)) :=
    measurableSet_predictable_Ioi_prod (hD.measurable hu)
  by_cases hzero : (0 : Real) ∈ u
  · rw [show (Function.uncurry
          (finiteGridCompensatorStepTerm T D r k)) ⁻¹' u =
        (Ioi ((grid T r).sampledTime k) ×ˢ (D k ⁻¹' u)) ∪
          (Ioi ((grid T r).sampledTime k) ×ˢ (Set.univ : Set Ω))ᶜ by
      ext p
      change (if (grid T r).sampledTime k < p.1 then D k p.2 else 0) ∈ u ↔
        (p.1 ∈ Ioi ((grid T r).sampledTime k) ∧ D k p.2 ∈ u) ∨
          ¬(p.1 ∈ Ioi ((grid T r).sampledTime k) ∧
            p.2 ∈ (Set.univ : Set Ω))
      by_cases hp : p.1 ∈ Ioi ((grid T r).sampledTime k)
      · have hp' : (grid T r).sampledTime k < p.1 := hp
        simp [hp']
      · have hp' : ¬((grid T r).sampledTime k < p.1) := hp
        simp [hp', hzero]]
    exact hOn.union hZero.compl
  · rw [show (Function.uncurry
          (finiteGridCompensatorStepTerm T D r k)) ⁻¹' u =
        Ioi ((grid T r).sampledTime k) ×ˢ (D k ⁻¹' u) by
      ext p
      change (if (grid T r).sampledTime k < p.1 then D k p.2 else 0) ∈ u ↔
        p.1 ∈ Ioi ((grid T r).sampledTime k) ∧ D k p.2 ∈ u
      by_cases hp : p.1 ∈ Ioi ((grid T r).sampledTime k)
      · have hp' : (grid T r).sampledTime k < p.1 := hp
        simp [hp']
      · have hp' : ¬((grid T r).sampledTime k < p.1) := hp
        simp [hp', hzero]]
    exact hOn

theorem finiteGridCompensatorProcess_isStronglyPredictable
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (T : NNReal) (D : Nat → Ω → Real) (r : Nat)
    (hD : ∀ k, StronglyMeasurable[F ((grid T r).sampledTime k)] (D k)) :
    IsStronglyPredictable F
      (finiteGridPredictableCompensatorProcess T D r) := by
  have hEq : Function.uncurry
      (finiteGridPredictableCompensatorProcess T D r) =
      ∑ k ∈ Finset.range (size T r), Function.uncurry
        (finiteGridCompensatorStepTerm T D r k) := by
    funext p
    change (∑ k ∈ Finset.range (size T r),
        finiteGridCompensatorStepTerm T D r k p.1 p.2) = _
    simp only [Finset.sum_apply]
    rfl
  unfold IsStronglyPredictable
  rw [hEq]
  apply Finset.stronglyMeasurable_sum
  intro k _
  exact finiteGridCompensatorStepTerm_isStronglyPredictable T D r k (hD k)

omit [MeasurableSpace Ω] in
@[simp] theorem finiteGridPredictableCompensatorProcess_zero
    (T : NNReal) (D : Nat → Ω → Real) (r : Nat) :
    finiteGridPredictableCompensatorProcess T D r 0 = 0 := by
  funext omega
  unfold finiteGridPredictableCompensatorProcess
  apply Finset.sum_eq_zero
  intro k hk
  simp [finiteGridCompensatorStepTerm]

omit [MeasurableSpace Ω] in
theorem finiteGridPredictableCompensatorProcess_nonneg
    (T : NNReal) (D : Nat → Ω → Real) (r : Nat)
    (hD : ∀ k omega, 0 ≤ D k omega) (t : NNReal) (omega : Ω) :
    0 ≤ finiteGridPredictableCompensatorProcess T D r t omega := by
  unfold finiteGridPredictableCompensatorProcess
  apply Finset.sum_nonneg
  intro k hk
  unfold finiteGridCompensatorStepTerm
  split_ifs
  · exact hD k omega
  · simp

omit [MeasurableSpace Ω] in
theorem finiteGridPredictableCompensatorProcess_mono
    (T : NNReal) (D : Nat → Ω → Real) (r : Nat)
    (hD : ∀ k omega, 0 ≤ D k omega) (omega : Ω) :
    Monotone (finiteGridPredictableCompensatorProcess T D r · omega) := by
  intro s t hst
  unfold finiteGridPredictableCompensatorProcess
  apply Finset.sum_le_sum
  intro k hk
  unfold finiteGridCompensatorStepTerm
  by_cases hks : (grid T r).sampledTime k < s
  · have hkt : (grid T r).sampledTime k < t := hks.trans_le hst
    simp [hks, hkt]
  · by_cases hkt : (grid T r).sampledTime k < t
    · rw [ite_eq_left hkt, ite_eq_right hks]
      exact hD k omega
    · simp [hks, hkt]

omit [MeasurableSpace Ω] in
theorem finiteGridPredictableCompensatorProcess_constant_after
    (T : NNReal) (D : Nat → Ω → Real) (r : Nat)
    (hDzero : ∀ k, k < size T r →
      (grid T r).sampledTime k = (grid T r).sampledTime (k + 1) → D k = 0)
    (omega : Ω) (t : NNReal) (ht : T ≤ t) :
    finiteGridPredictableCompensatorProcess T D r t omega =
      finiteGridPredictableCompensatorProcess T D r T omega := by
  unfold finiteGridPredictableCompensatorProcess
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < size T r := Finset.mem_range.mp hk
  have htk : (grid T r).sampledTime k ≤ T :=
    finiteGrid_sampledTime_le_horizon T r k hklt.le
  unfold finiteGridCompensatorStepTerm
  by_cases htk_lt : (grid T r).sampledTime k < T
  · have htk_t : (grid T r).sampledTime k < t := htk_lt.trans_le ht
    simp [htk_lt, htk_t]
  · have htk_eq : (grid T r).sampledTime k = T :=
      le_antisymm htk (le_of_not_gt htk_lt)
    have htk1 : (grid T r).sampledTime (k + 1) ≤ T :=
      finiteGrid_sampledTime_le_horizon T r (k + 1) (Nat.succ_le_iff.mpr hklt)
    have htk1_le : (grid T r).sampledTime (k + 1) ≤
        (grid T r).sampledTime k := htk1.trans_eq htk_eq.symm
    have htk_le : (grid T r).sampledTime k ≤
        (grid T r).sampledTime (k + 1) :=
      (grid T r).sampledTime_mono (Nat.le_succ k)
    have heq : (grid T r).sampledTime k =
        (grid T r).sampledTime (k + 1) := le_antisymm htk_le htk1_le
    have hzero : D k = 0 := hDzero k hklt heq
    simp [htk_eq, hzero]

omit [MeasurableSpace Ω] in
theorem finiteGridPredictableCompensatorProcess_terminal_eq_cumulative
    (T : NNReal) (D : Nat → Ω → Real) (r : Nat)
    (hDzero : ∀ k, k < size T r →
      (grid T r).sampledTime k = (grid T r).sampledTime (k + 1) → D k = 0) :
    finiteGridPredictableCompensatorProcess T D r T =
      finiteGridCompensatorCumulative T D r (size T r) := by
  funext omega
  unfold finiteGridPredictableCompensatorProcess
    finiteGridCompensatorCumulative
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < size T r := Finset.mem_range.mp hk
  have htk1 : (grid T r).sampledTime (k + 1) ≤ T :=
    finiteGrid_sampledTime_le_horizon T r (k + 1) (Nat.succ_le_iff.mpr hklt)
  unfold finiteGridCompensatorStepTerm
  by_cases hlt : (grid T r).sampledTime k <
      (grid T r).sampledTime (k + 1)
  · have htk : (grid T r).sampledTime k < T := hlt.trans_le htk1
    simp [htk]
  · have hle : (grid T r).sampledTime (k + 1) ≤
      (grid T r).sampledTime k := le_of_not_gt hlt
    have hmono : (grid T r).sampledTime k ≤
        (grid T r).sampledTime (k + 1) :=
      (grid T r).sampledTime_mono (Nat.le_succ k)
    have heq : (grid T r).sampledTime k =
        (grid T r).sampledTime (k + 1) := le_antisymm hmono hle
    have hzero : D k = 0 := hDzero k hklt heq
    simp [hzero]

omit [MeasurableSpace Ω] in
theorem finiteGridCompensatorCumulative_nonneg
    (T : NNReal) (D : Nat → Ω → Real) (r n : Nat)
    (hD : ∀ k omega, 0 ≤ D k omega) (omega : Ω) :
    0 ≤ finiteGridCompensatorCumulative T D r n omega := by
  unfold finiteGridCompensatorCumulative
  apply Finset.sum_nonneg
  intro k hk
  exact hD k omega

omit [MeasurableSpace Ω] in
theorem finiteGridCompensatorCumulative_mono
    (T : NNReal) (D : Nat → Ω → Real) (r m n : Nat) (hmn : m ≤ n)
    (hD : ∀ k omega, 0 ≤ D k omega) (omega : Ω) :
    finiteGridCompensatorCumulative T D r m omega ≤
      finiteGridCompensatorCumulative T D r n omega := by
  unfold finiteGridCompensatorCumulative
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro k _hkm _hkn
  exact hD k omega

theorem finiteGridCompensatorCumulative_stronglyMeasurable
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (T : NNReal) (D : Nat → Ω → Real) (r n : Nat)
    (hD : ∀ k, StronglyMeasurable[F ((grid T r).sampledTime k)] (D k)) :
    StronglyMeasurable[F ((grid T r).sampledTime n)]
      (finiteGridCompensatorCumulative T D r n) := by
  unfold finiteGridCompensatorCumulative
  have hEq :
      (fun omega => ∑ k ∈ Finset.range n, D k omega) =
      ((∑ k ∈ Finset.range n, D k) : Ω → Real) := by
    funext omega
    simp
  rw [hEq]
  apply Finset.stronglyMeasurable_sum
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  exact (hD k).mono (F.mono ((grid T r).sampledTime_mono hklt.le))

omit [MeasurableSpace Ω] in
theorem finiteGridCompensatorCumulative_terminal_sq_identity
    (T : NNReal) (D : Nat → Ω → Real) (r : Nat) :
    (fun omega => finiteGridCompensatorCumulative T D r (size T r) omega ^ 2) =
      (fun omega => ∑ k ∈ Finset.range (size T r),
        (2 * finiteGridCompensatorCumulative T D r k omega * D k omega +
          D k omega ^ 2)) := by
  funext omega
  induction size T r with
  | zero => simp [finiteGridCompensatorCumulative]
  | succ n ih =>
      rw [finiteGridCompensatorCumulative_succ T D r n]
      rw [Finset.sum_range_succ]
      change (finiteGridCompensatorCumulative T D r n omega + D n omega) ^ 2 = _
      calc
        (finiteGridCompensatorCumulative T D r n omega + D n omega) ^ 2 =
            finiteGridCompensatorCumulative T D r n omega ^ 2 +
              (2 * finiteGridCompensatorCumulative T D r n omega * D n omega +
                D n omega ^ 2) := by ring
        _ = _ := by rw [ih]

theorem finiteGrid_predictable_cross_term_identity
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    (T : NNReal) (D M : Nat → Ω → Real) (P : Ω → Real) (r k : Nat)
    (hD_raw : D k =ᵐ[mu]
      mu[M (k + 1) - M k | F ((grid T r).sampledTime k)])
    (hPMeas : StronglyMeasurable[F ((grid T r).sampledTime k)] P)
    (hMInt : Integrable (M (k + 1) - M k) mu)
    (hPMInt : Integrable (P * (M (k + 1) - M k)) mu) :
    (∫ omega, P omega * D k omega ∂mu) =
      ∫ omega, P omega * (M (k + 1) - M k) omega ∂mu := by
  have hPull := condExp_mul_of_stronglyMeasurable_left
    hPMeas hPMInt hMInt
  calc
    (∫ omega, P omega * D k omega ∂mu) =
        ∫ omega, P omega *
          mu[M (k + 1) - M k |
            F ((grid T r).sampledTime k)] omega ∂mu := by
      apply integral_congr_ae
      filter_upwards [hD_raw] with omega hEq
      rw [hEq]
    _ = ∫ omega, mu[P * (M (k + 1) - M k) |
          F ((grid T r).sampledTime k)] omega ∂mu := by
      apply integral_congr_ae
      filter_upwards [hPull] with omega hEq
      exact hEq.symm
    _ = ∫ omega, P omega * (M (k + 1) - M k) omega ∂mu :=
      integral_condExp (F.le ((grid T r).sampledTime k))

omit [MeasurableSpace Ω] in
theorem finiteGridPredictableCompensatorProcess_sampled_increment
    (T : NNReal) (D : Nat → Ω → Real) (r i : Nat) (hi : i < size T r)
    (hDzero : ∀ k, k < size T r →
      (grid T r).sampledTime k = (grid T r).sampledTime (k + 1) → D k = 0) :
    (fun omega =>
      finiteGridPredictableCompensatorProcess T D r
          ((grid T r).sampledTime (i + 1)) omega -
        finiteGridPredictableCompensatorProcess T D r
          ((grid T r).sampledTime i) omega) = D i := by
  funext omega
  unfold finiteGridPredictableCompensatorProcess
  rw [← Finset.sum_sub_distrib]
  have hterm (k : Nat) (hk : k < size T r) :
      (if (grid T r).sampledTime k <
          (grid T r).sampledTime (i + 1) then D k omega else 0) -
        (if (grid T r).sampledTime k <
          (grid T r).sampledTime i then D k omega else 0) =
      if k = i then D i omega else 0 := by
    by_cases hki : k < i
    · have hki0 : (grid T r).sampledTime k ≤
          (grid T r).sampledTime i := (grid T r).sampledTime_mono hki.le
      have hki1 : (grid T r).sampledTime (k + 1) ≤
          (grid T r).sampledTime i :=
        (grid T r).sampledTime_mono (Nat.succ_le_iff.mpr hki)
      by_cases hkt : (grid T r).sampledTime k <
          (grid T r).sampledTime i
      · have hkt1 : (grid T r).sampledTime k <
            (grid T r).sampledTime (i + 1) :=
          hkt.trans_le ((grid T r).sampledTime_mono (Nat.le_succ i))
        have hne : k ≠ i := Nat.ne_of_lt hki
        simp [hkt, hkt1, hne]
      · have hkeq : (grid T r).sampledTime k =
            (grid T r).sampledTime i := le_antisymm hki0 (le_of_not_gt hkt)
        have hki1' : (grid T r).sampledTime (k + 1) =
            (grid T r).sampledTime i :=
          le_antisymm hki1 (by
            simpa [hkeq] using (grid T r).sampledTime_mono (Nat.le_succ k))
        have houter : ¬((grid T r).sampledTime k <
            (grid T r).sampledTime (k + 1)) := by
          rw [hkeq, hki1']
          exact lt_irrefl _
        have heq : (grid T r).sampledTime k =
            (grid T r).sampledTime (k + 1) := hkeq.trans hki1'.symm
        have hzero : D k = 0 := hDzero k hk heq
        have hne : k ≠ i := Nat.ne_of_lt hki
        simp [hkeq, hne, hzero]
    · by_cases hik : k = i
      · subst k
        by_cases hlt : (grid T r).sampledTime i <
            (grid T r).sampledTime (i + 1)
        · simp [hlt]
        · have hle : (grid T r).sampledTime (i + 1) ≤
              (grid T r).sampledTime i := le_of_not_gt hlt
          have hmono : (grid T r).sampledTime i ≤
              (grid T r).sampledTime (i + 1) :=
            (grid T r).sampledTime_mono (Nat.le_succ i)
          have heq : (grid T r).sampledTime i =
              (grid T r).sampledTime (i + 1) := le_antisymm hmono hle
          have hzero : D i = 0 := hDzero i hi heq
          simp [hlt, hzero]
      · have hik' : i < k := Nat.lt_of_le_of_ne
            (le_of_not_gt hki) (Ne.symm hik)
        have hi1k : i + 1 ≤ k := Nat.succ_le_iff.mpr hik'
        have htime : (grid T r).sampledTime (i + 1) ≤
            (grid T r).sampledTime k := (grid T r).sampledTime_mono hi1k
        have htime0 : (grid T r).sampledTime i ≤
            (grid T r).sampledTime k := (grid T r).sampledTime_mono hik'.le
        simp [not_lt_of_ge htime, not_lt_of_ge htime0, hik]
  simp only [finiteGridCompensatorStepTerm]
  have hsum :
      (∑ k ∈ Finset.range (size T r),
        ((if (grid T r).sampledTime k <
            (grid T r).sampledTime (i + 1) then D k omega else 0) -
          (if (grid T r).sampledTime k <
            (grid T r).sampledTime i then D k omega else 0))) =
        ∑ k ∈ Finset.range (size T r),
          (if k = i then D i omega else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k (Finset.mem_range.mp hk)
  rw [hsum]
  simp [hi]

theorem finiteGrid_predictable_testing_identity
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    (T : NNReal) (D M : Nat → Ω → Real) (r N : Nat)
    (hD_raw : ∀ k, k < N →
      D k =ᵐ[mu] mu[M (k + 1) - M k |
        F ((grid T r).sampledTime k)])
    (K : Nat → Ω → Real)
    (hK : StronglyAdapted ((grid T r).sampledFiltration F) K)
    (hMInt : ∀ k, k < N → Integrable (M (k + 1) - M k) mu)
    (hSourceInt : ∀ k, Integrable
      (K k * (M (k + 1) - M k)) mu)
    (hCompInt : ∀ k, Integrable (K k * D k) mu) :
    (∫ omega, discretePredictableIntegral K M N omega ∂mu) =
      ∫ omega, (∑ k ∈ Finset.range N, K k omega * D k omega) ∂mu := by
  unfold discretePredictableIntegral
  rw [integral_finsetSum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < N := Finset.mem_range.mp hk
    have hKk : StronglyMeasurable[F ((grid T r).sampledTime k)] (K k) := by
      have hKk' := hK k
      change StronglyMeasurable[F ((grid T r).sampledTime k)] (K k) at hKk'
      exact hKk'
    have hPull := condExp_mul_of_stronglyMeasurable_left
      hKk (hSourceInt k) (hMInt k hklt)
    have hIntCond :
        (∫ omega, mu[K k * (M (k + 1) - M k) |
          F ((grid T r).sampledTime k)] omega ∂mu) =
          ∫ omega, K k omega * (M (k + 1) - M k) omega ∂mu :=
      integral_condExp (F.le ((grid T r).sampledTime k))
    calc
      (∫ omega, K k omega *
          (M (k + 1) omega - M k omega) ∂mu) =
          ∫ omega, K k omega * (M (k + 1) - M k) omega ∂mu := by
            rfl
      _ = ∫ omega, mu[K k * (M (k + 1) - M k) |
          F ((grid T r).sampledTime k)] omega ∂mu := hIntCond.symm
      _ = ∫ omega, K k omega *
          mu[M (k + 1) - M k |
            F ((grid T r).sampledTime k)] omega ∂mu :=
        integral_congr_ae hPull
      _ = ∫ omega, K k omega * D k omega ∂mu := by
        apply integral_congr_ae
        filter_upwards [hD_raw k hklt] with omega hEq
        rw [hEq]
  · intro k hk
    exact hCompInt k
  · intro k hk
    exact hSourceInt k

end HorizonFactorialGrid

end FTAPTheorem42
