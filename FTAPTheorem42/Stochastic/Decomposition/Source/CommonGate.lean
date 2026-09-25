/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedCadlagRowConvergence
import FTAPTheorem42.Stochastic.Decomposition.Source.Variation
import FTAPTheorem42.Stochastic.Stopping.LeftContinuousHittingTime
import FTAPTheorem42.Stochastic.Compactness.CountableInMeasureDiagonal
import FTAPTheorem42.Trading.VanishingRisk
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Common gate localization on a fixed factorial horizon

The finite-grid variation gates are extended to left-continuous predictable
processes.  One further tail convexification is then applied to the terminal
gates, and its weights are composed with the component weights already chosen
by the stopped-component endpoint.  The resulting terminal gate has an
`L²` limit and the threshold first-passage times have one common infimum.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## Full-time gate paths -/

noncomputable def variationGatePath
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Set.Iic T → Omega → Real :=
  fun t omega =>
    (grid T r).doobVariationGate S F mu a
      ((approxIndex T t.1 t.2 r).1 - 1) omega

noncomputable def variationGateProcess
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Process Omega :=
  fun t omega =>
    variationGatePath a T r S F mu
      ⟨min t T, min_le_right t T⟩ omega

theorem variationGateApproximation_stronglyMeasurable_at
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {a : Real} (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    StronglyMeasurable[F t]
      (variationGatePath a T r S F mu ⟨t, ht⟩) := by
  let n := (approxIndex T t ht r).1 - 1
  have hn : StronglyMeasurable[(grid T r).sampledFiltration F n]
      ((grid T r).doobVariationGate S F mu a n) :=
    (grid T r).stronglyAdapted_doobVariationGate S F mu a n
  have htime : (grid T r).sampledTime n ≤ t := by
    let q := (approxIndex T t ht r).1
    by_cases hq : q = 0
    · simp [n, q, hq, ChronologicalGrid.sampledTime,
        ChronologicalGrid.natIndex]
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      have hqceil : q = Nat.ceil (t * (r.factorial : NNReal)) := by
        rfl
      have hlower : (q - 1 : NNReal) < t * (r.factorial : NNReal) := by
        have hlt : q - 1 < Nat.ceil (t * (r.factorial : NNReal)) := by
          rw [hqceil]
          omega
        simpa [Nat.cast_sub hqpos.le] using
          ((Nat.lt_ceil (α := NNReal)).mp hlt)
      have hqsize : q - 1 ≤ size T r := by
        exact (Nat.sub_le q 1).trans (Nat.le_of_lt_succ
          (approxIndex T t ht r).2)
      change (grid T r).sampledTime (q - 1) ≤ t
      rw [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex]
      simp only [hqsize, min_eq_left]
      rw [grid_time]
      change min (((q - 1 : Nat) : NNReal) /
        (r.factorial : NNReal)) T ≤ t
      have hdiv : ((q - 1 : Nat) : NNReal) /
          (r.factorial : NNReal) < t := by
        apply (div_lt_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
          positivity)).2
        simpa [Nat.cast_sub hqpos.le] using hlower
      exact (min_le_left _ _).trans hdiv.le
  change StronglyMeasurable[F t]
    ((grid T r).doobVariationGate S F mu a n)
  exact hn.mono (Filtration.mono F htime)

theorem stronglyAdapted_variationGateProcess
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r : Nat) :
    StronglyAdapted F (variationGateProcess a T r S F mu) := by
  intro t
  by_cases ht : t ≤ T
  · unfold variationGateProcess
    simpa [min_eq_left ht] using
      (variationGateApproximation_stronglyMeasurable_at
        (S := S) (F := F) (mu := mu) (a := a) T t ht r)
  · have hT := variationGateApproximation_stronglyMeasurable_at
      (S := S) (F := F) (mu := mu) (a := a) T T le_rfl r
    have hT' : StronglyMeasurable[F t]
        (variationGatePath a T r S F mu ⟨T, (show T ≤ T from le_rfl)⟩) :=
      hT.mono (F.mono (le_of_not_ge ht))
    unfold variationGateProcess
    simpa [min_eq_right (le_of_not_ge ht)] using hT'

private theorem variationGatePath_continuousWithinAt_Iic
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (omega : Omega) (t : Set.Iic T) :
    ContinuousWithinAt
      (fun u => variationGatePath a T r S F mu u omega)
      (Set.Iic t) t := by
  generalize hq : (approxIndex T t.1 t.2 r).1 = n
  cases n with
  | zero =>
      have ht0 : t.1 = 0 := by
        have hceil : Nat.ceil (t.1 * (r.factorial : NNReal)) = 0 := by
          simpa [approxIndex] using hq
        have hmul : t.1 * (r.factorial : NNReal) = 0 := by
          apply le_antisymm (Nat.ceil_eq_zero.mp hceil)
          positivity
        exact (mul_eq_zero.mp hmul).resolve_right (by positivity)
      let zeroT : Set.Iic T := ⟨0, (show (0 : NNReal) ≤ T from bot_le)⟩
      have htSub : t = zeroT := by
        apply Subtype.ext
        exact ht0
      have hEventually : ∀ᶠ u in 𝓝[Set.Iic t] t,
          variationGatePath a T r S F mu u omega =
            variationGatePath a T r S F mu zeroT omega := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu0 : u = zeroT := by
          apply Subtype.ext
          have huLe : u ≤ zeroT := by
            simpa [htSub] using hu
          exact le_antisymm (show (u : NNReal) ≤ 0 from huLe) bot_le
        rw [hu0]
      exact continuousWithinAt_const.congr_of_eventuallyEq
        hEventually (by rw [htSub])
  | succ k =>
      have hceil : Nat.ceil (t.1 * (r.factorial : NNReal)) = k + 1 := by
        simpa [approxIndex] using hq
      have hLowerNat : k < Nat.ceil (t.1 * (r.factorial : NNReal)) := by
        rw [hceil]
        exact Nat.lt_succ_self k
      have hLower : (k : NNReal) / (r.factorial : NNReal) < t.1 := by
        have hmul : (k : NNReal) < t.1 * (r.factorial : NNReal) :=
          (Nat.lt_ceil (α := NNReal)).mp (by simp [hceil])
        exact (div_lt_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
          positivity)).2 (by simpa [mul_comm] using hmul)
      let p : Set.Iic T :=
        ⟨(k : NNReal) / (r.factorial : NNReal),
          hLower.le.trans t.2⟩
      have hp : p < t := hLower
      have hEventually : ∀ᶠ u in 𝓝[Set.Iic t] t,
          variationGatePath a T r S F mu u omega =
            variationGatePath a T r S F mu t omega := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
            (Ioi_mem_nhds hp),
          self_mem_nhdsWithin] with u hu hIic
        have huT : u.1 ≤ T := u.2
        have hceilU : Nat.ceil (u.1 * (r.factorial : NNReal)) = k + 1 := by
          apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).2
          constructor
          · have : (k : NNReal) < u.1 * (r.factorial : NNReal) := by
              apply (div_lt_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
                positivity)).1
              exact (show (k : NNReal) / (r.factorial : NNReal) < u.1 from hu)
            simpa only [Nat.succ_sub_one, Nat.cast_id] using this
          · have htc : t.1 * (r.factorial : NNReal) ≤ (k.succ : NNReal) := by
              have htc0 := Nat.le_ceil (t.1 * (r.factorial : NNReal))
              rw [hceil] at htc0
              simpa [Nat.cast_succ] using htc0
            exact (mul_le_mul_of_nonneg_right (show u.1 ≤ t.1 from hIic)
              (by positivity)).trans htc
        have hIndex : approxIndex T u.1 huT r =
            approxIndex T t.1 t.2 r := by
          apply Fin.ext
          simp only [approxIndex]
          exact hceilU.trans hceil.symm
        simp [variationGatePath, hIndex]
      exact continuousWithinAt_const.congr_of_eventuallyEq
        hEventually (by rfl)

theorem continuousWithinAt_variationGateProcess_Iic
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (omega : Omega) (t : NNReal) :
    ContinuousWithinAt
      (variationGateProcess a T r S F mu · omega)
      (Set.Iic t) t := by
  let phi : NNReal → Set.Iic T := fun u =>
    ⟨min u T, min_le_right u T⟩
  have hphi : Tendsto phi (𝓝[Set.Iic t] t)
      (𝓝[Set.Iic (phi t)] (phi t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · apply tendsto_subtype_rng.mpr
      exact (continuous_id.min continuous_const).continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change min u T ≤ min t T
      exact min_le_min_right T hu
  exact (variationGatePath_continuousWithinAt_Iic
    a T r S F mu omega (phi t)).tendsto.comp hphi

theorem variationGateProcess_eq_zero_or_one
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (t : NNReal) (omega : Omega) :
    variationGateProcess a T r S F mu t omega = 0 ∨
      variationGateProcess a T r S F mu t omega = 1 := by
  unfold variationGateProcess variationGatePath
  unfold ChronologicalGrid.doobVariationGate
  split_ifs <;> norm_num

theorem variationGateProcess_nonneg_le_one
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (t : NNReal) (omega : Omega) :
    0 ≤ variationGateProcess a T r S F mu t omega ∧
      variationGateProcess a T r S F mu t omega ≤ 1 := by
  rcases variationGateProcess_eq_zero_or_one a T r S F mu t omega with h | h
  · simp [h]
  · simp [h]

theorem monotone_variationGateProcess
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) :
    Antitone (variationGateProcess a T r S F mu · ·) := by
  intro s t hst omega
  let hs : Set.Iic T := ⟨min s T, min_le_right s T⟩
  let ht : Set.Iic T := ⟨min t T, min_le_right t T⟩
  have hsT : hs.1 ≤ T := hs.2
  have htT : ht.1 ≤ T := ht.2
  have hmin : min s T ≤ min t T := min_le_min_right T hst
  have hi : (approxIndex T hs.1 hsT r).1 ≤
      (approxIndex T ht.1 htT r).1 := by
    simp only [hs, ht, approxIndex]
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_right hmin (by positivity))
  have hi' : (approxIndex T hs.1 hsT r).1 - 1 ≤
      (approxIndex T ht.1 htT r).1 - 1 := Nat.sub_le_sub_right hi 1
  change (if (grid T r).doobPredictableVariation S F mu
      ((approxIndex T ht.1 htT r).1 - 1) omega < a then 1 else 0) ≤
    (if (grid T r).doobPredictableVariation S F mu
      ((approxIndex T hs.1 hsT r).1 - 1) omega < a then 1 else 0)
  by_cases hvar : (grid T r).doobPredictableVariation S F mu
      ((approxIndex T ht.1 htT r).1 - 1) omega < a
  · simp only [ite_eq_left hvar]
    by_cases hvar' : (grid T r).doobPredictableVariation S F mu
        ((approxIndex T hs.1 hsT r).1 - 1) omega < a
    · simp [ite_eq_left hvar']
    · exact False.elim (hvar' (lt_of_le_of_lt
        ((grid T r).monotone_doobPredictableVariation S F mu hi' omega) hvar))
  · simp only [ite_eq_right hvar]
    split_ifs <;> norm_num

/-! ## Convex rows of gates -/

noncomputable def variationGateConvexRow
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Process Omega :=
  fun t omega =>
    (w n).apply (fun r => variationGateProcess a T r S F mu t) omega

theorem stronglyAdapted_variationGateConvexRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal) :
    StronglyAdapted F (variationGateConvexRow w n a T S F mu) := by
  intro t
  change StronglyMeasurable[F t]
    (fun omega => ∑ r ∈ (w n).support,
      (w n).weight r * variationGateProcess a T r S F mu t omega)
  apply (w n).support.stronglyMeasurable_fun_sum
  intro r hr
  exact ((stronglyAdapted_variationGateProcess (S := S) (F := F) (mu := mu) a T r t).const_mul
    ((w n).weight r))

theorem continuousWithinAt_variationGateConvexRow_Iic
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (omega : Omega) (t : NNReal) :
    ContinuousWithinAt
      (variationGateConvexRow w n a T S F mu · omega)
      (Set.Iic t) t := by
  change ContinuousWithinAt
    (fun u => ∑ r ∈ (w n).support,
      (w n).weight r * variationGateProcess a T r S F mu u omega)
    (Set.Iic t) t
  induction (w n).support using Finset.induction_on with
  | empty =>
      simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => (0 : Real)) (Set.Iic t) t)
  | @insert r s hrs ih =>
      simp only [Finset.sum_insert hrs]
      exact (((continuousWithinAt_variationGateProcess_Iic
        a T r S F mu omega t).const_mul ((w n).weight r)).add ih)

theorem variationGateConvexRow_nonneg_le_one
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (t : NNReal) (omega : Omega) :
    0 ≤ variationGateConvexRow w n a T S F mu t omega ∧
      variationGateConvexRow w n a T S F mu t omega ≤ 1 := by
  have hnonneg : ∀ r ∈ (w n).support,
      0 ≤ (w n).weight r * variationGateProcess a T r S F mu t omega := by
    intro r hr
    exact mul_nonneg ((w n).nonneg r hr)
      ((variationGateProcess_nonneg_le_one a T r S F mu t omega).1)
  have hone : ∑ r ∈ (w n).support, (w n).weight r * (1 : Real) = 1 := by
    simpa using (w n).sum_eq_one
  constructor
  · exact Finset.sum_nonneg hnonneg
  · calc
      variationGateConvexRow w n a T S F mu t omega =
          ∑ r ∈ (w n).support,
            (w n).weight r * variationGateProcess a T r S F mu t omega := rfl
      _ ≤ ∑ r ∈ (w n).support,
          (w n).weight r * 1 := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left
          ((variationGateProcess_nonneg_le_one a T r S F mu t omega).2)
          ((w n).nonneg r hr)
      _ = 1 := hone

theorem monotone_variationGateConvexRow
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) :
    Antitone (variationGateConvexRow w n a T S F mu · ·) := by
  intro s t hst omega
  change ∑ r ∈ (w n).support,
      (w n).weight r * variationGateProcess a T r S F mu t omega ≤
    ∑ r ∈ (w n).support,
      (w n).weight r * variationGateProcess a T r S F mu s omega
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left
    (monotone_variationGateProcess a T r S F mu hst omega)
    ((w n).nonneg r hr)

/-! ## Composing the old component weights with gate weights -/

noncomputable def composeTailConvexWeights
    (v w : ∀ n, TailConvexWeights n) (n : Nat) : TailConvexWeights n where
  support := (v n).support.biUnion (fun i => (w i).support)
  weight := fun r => ∑ i ∈ (v n).support, (v n).weight i * (w i).coeff r
  tail := by
    intro r hr
    simp only [Finset.mem_biUnion] at hr
    obtain ⟨i, hi, hir⟩ := hr
    exact (v n).tail i hi |>.trans ((w i).tail r hir)
  nonneg := by
    intro r hr
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg ((v n).nonneg i hi) ((w i).coeff_nonneg r)
  sum_eq_one := by
    have hsum : ∑ r ∈ (v n).support.biUnion (fun i => (w i).support),
        ∑ i ∈ (v n).support, (v n).weight i * (w i).coeff r =
        ∑ i ∈ (v n).support,
          (v n).weight i * ∑ r ∈ (w i).support, (w i).coeff r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      symm
      apply Finset.sum_subset
      · intro r hr
        exact Finset.mem_biUnion.mpr ⟨i, hi, hr⟩
      · intro r _hr hri
        simp [TailConvexWeights.coeff_of_not_mem (w i) hri]
    rw [hsum]
    simp_rw [TailConvexWeights.sum_coeff_eq_one, mul_one]
    rw [(v n).sum_eq_one]

omit [MeasurableSpace Omega] in
theorem composeTailConvexWeights_apply
    (v w : ∀ n, TailConvexWeights n) (n : Nat)
    (G : Nat → Omega → Real) :
      (composeTailConvexWeights v w n).apply G =
      (v n).apply (fun i => (w i).apply G) := by
  funext omega
  change
    (∑ r ∈ (v n).support.biUnion (fun i => (w i).support),
      (∑ i ∈ (v n).support, (v n).weight i * (w i).coeff r) * G r omega) =
      ∑ i ∈ (v n).support,
        (v n).weight i * (∑ r ∈ (w i).support,
          (w i).weight r * G r omega)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  symm
  calc
    ∑ r ∈ (w i).support,
        (v n).weight i * ((w i).weight r * G r omega) =
      ∑ r ∈ (w i).support,
        (v n).weight i * (w i).coeff r * G r omega := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [TailConvexWeights.coeff_of_mem (w i) hr]
          ring
    _ = ∑ r ∈ (v n).support.biUnion (fun j => (w j).support),
        (v n).weight i * (w i).coeff r * G r omega := by
          apply Finset.sum_subset
          · intro r hr
            exact Finset.mem_biUnion.mpr ⟨i, hi, hr⟩
          · intro r _hr hri
            simp [TailConvexWeights.coeff_of_not_mem (w i) hri]

theorem composeTailConvexWeights_applyVector
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (v w : ∀ n, TailConvexWeights n) (n : Nat)
    (G : Nat → E) :
    (composeTailConvexWeights v w n).applyVector G =
      (v n).applyVector (fun i => (w i).applyVector G) := by
  change
    (∑ r ∈ (v n).support.biUnion (fun i => (w i).support),
      (∑ i ∈ (v n).support, (v n).weight i * (w i).coeff r) • G r) =
      ∑ i ∈ (v n).support,
        (v n).weight i • (∑ r ∈ (w i).support,
          (w i).weight r • G r)
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.smul_sum]
  symm
  calc
    ∑ r ∈ (w i).support,
        (v n).weight i • ((w i).weight r • G r) =
      ∑ r ∈ (w i).support,
        (v n).weight i • ((w i).coeff r • G r) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [TailConvexWeights.coeff_of_mem (w i) hr]
    _ = ∑ r ∈ (v n).support.biUnion (fun j => (w j).support),
        ((v n).weight i * (w i).coeff r) • G r := by
          have hs := Finset.sum_subset
            (s₁ := (w i).support)
            (s₂ := (v n).support.biUnion (fun j => (w j).support))
            (f := fun r => (v n).weight i •
              ((w i).coeff r • G r))
            (fun r hr => Finset.mem_biUnion.mpr ⟨i, hi, hr⟩)
            (by
              intro r _hr hri
              simp [TailConvexWeights.coeff_of_not_mem (w i) hri])
          simpa [smul_smul, smul_eq_mul] using hs

omit [MeasurableSpace Omega] in
theorem TailConvexWeights.tendsto_applyVector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ∀ n, TailConvexWeights n) {x : Nat → E} {a : E}
    (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun n => (w n).applyVector x) atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop] at hx ⊢
  intro ε hε
  rcases hx (ε / 2) (half_pos hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hclose : ∀ i ∈ (w n).support, ‖x i - a‖ ≤ ε / 2 := by
    intro i hi
    have hNi : N ≤ i := le_trans hn ((w n).tail i hi)
    have hdist := hN i hNi
    exact le_of_lt (by simpa [dist_eq_norm] using hdist)
  have hsum_const :
      (∑ i ∈ (w n).support, (w n).weight i • a) = a := by
    rw [← Finset.sum_smul, (w n).sum_eq_one, one_smul]
  have hsub_eq :
      (w n).applyVector x - a =
        ∑ i ∈ (w n).support, (w n).weight i • (x i - a) := by
    change (∑ i ∈ (w n).support, (w n).weight i • x i) - a = _
    calc
      (∑ i ∈ (w n).support, (w n).weight i • x i) - a =
          (∑ i ∈ (w n).support, (w n).weight i • x i) -
            ∑ i ∈ (w n).support, (w n).weight i • a := by
              rw [hsum_const]
      _ = ∑ i ∈ (w n).support,
          ((w n).weight i • x i - (w n).weight i • a) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i ∈ (w n).support,
          (w n).weight i • (x i - a) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [smul_sub]
  have hnorm_le : ‖(w n).applyVector x - a‖ ≤ ε / 2 := by
    rw [hsub_eq]
    calc
      ‖∑ i ∈ (w n).support, (w n).weight i • (x i - a)‖ ≤
          ∑ i ∈ (w n).support,
            ‖(w n).weight i • (x i - a)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ (w n).support,
          (w n).weight i * (ε / 2) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg ((w n).nonneg i hi)]
            exact mul_le_mul_of_nonneg_left (hclose i hi)
              ((w n).nonneg i hi)
      _ = ε / 2 := by
            rw [← Finset.sum_mul, (w n).sum_eq_one, one_mul]
  have hdist_le : dist ((w n).applyVector x) a ≤ ε / 2 := by
    simpa [dist_eq_norm] using hnorm_le
  linarith

/-! ## Terminal gates and their expectation bound -/

noncomputable def variationGateTerminal
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Omega → Real :=
  variationGateProcess a T r S F mu T

theorem stronglyMeasurable_variationGateTerminal
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r : Nat) :
    StronglyMeasurable (variationGateTerminal a T r S F mu) := by
  exact (stronglyAdapted_variationGateProcess (S := S) (F := F) (mu := mu) a T r T).mono (F.le T)

theorem memLp_two_variationGateTerminal
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r : Nat) :
    MemLp (variationGateTerminal a T r S F mu) (2 : ENNReal) mu := by
  apply MemLp.of_bound
    (stronglyMeasurable_variationGateTerminal
      (S := S) (F := F) (mu := mu) a T r).aestronglyMeasurable 1
  filter_upwards [] with omega
  change ‖variationGateTerminal a T r S F mu omega‖ ≤ 1
  rw [variationGateTerminal]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (variationGateProcess_nonneg_le_one a T r S F mu T omega).1]
  exact (variationGateProcess_nonneg_le_one a T r S F mu T omega).2

noncomputable def variationGateTerminalToLp
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r : Nat) : Lp Real 2 mu :=
  (memLp_two_variationGateTerminal (S := S) (F := F) (mu := mu) a T r).toLp
    (variationGateTerminal a T r S F mu)

theorem variationGateTerminalToLp_norm_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r : Nat) :
    ‖variationGateTerminalToLp (S := S) (F := F) (mu := mu) a T r‖ ≤ 1 := by
  rw [variationGateTerminalToLp, Lp.norm_toLp]
  have hnorm : ∀ᵐ omega ∂mu,
      ‖variationGateTerminal a T r S F mu omega‖ ≤ 1 := by
    filter_upwards [] with omega
    rw [variationGateTerminal]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (variationGateProcess_nonneg_le_one a T r S F mu T omega).1]
    exact (variationGateProcess_nonneg_le_one a T r S F mu T omega).2
  have h := eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
    (memLp_two_variationGateTerminal (S := S) (F := F) (mu := mu) a T r).aestronglyMeasurable hnorm
  calc
    (eLpNorm (variationGateTerminal a T r S F mu)
        (2 : ENNReal) mu).toReal ≤
      (mu Set.univ ^ (ENNReal.toReal 2)⁻¹ * ENNReal.ofReal 1).toReal :=
      ENNReal.toReal_mono (by simp) h
    _ = 1 := by simp [measure_univ]

theorem variationGateTerminal_zero_subset
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {a : Real} (_ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    {omega | variationGateTerminal a T r S F mu omega = 0} ⊆
      {omega | a - 1 <
        |terminalDoobVariation T r S F mu omega|} := by
  intro omega hzero
  change variationGateTerminal a T r S F mu omega = 0 at hzero
  have hzero' : (grid T r).doobVariationGate S F mu a
      ((approxIndex T T le_rfl r).1 - 1) omega = 0 := by
    simpa [variationGateTerminal, variationGateProcess, variationGatePath] using hzero
  have hvar : a ≤ (grid T r).doobPredictableVariation S F mu
      ((approxIndex T T le_rfl r).1 - 1) omega := by
    by_contra hnot
    have hlt : (grid T r).doobPredictableVariation S F mu
        ((approxIndex T T le_rfl r).1 - 1) omega < a := lt_of_not_ge hnot
    have hzero'' := hzero'
    change (if (grid T r).doobPredictableVariation S F mu
        ((approxIndex T T le_rfl r).1 - 1) omega < a then 1 else 0) = 0 at hzero''
    rw [ite_eq_left hlt] at hzero''
    norm_num at hzero''
  have hidx : (approxIndex T T le_rfl r).1 - 1 ≤ size T r :=
    (Nat.sub_le _ _).trans (Nat.le_of_lt_succ (approxIndex T T le_rfl r).2)
  have hmono := (grid T r).monotone_doobPredictableVariation S F mu hidx omega
  have hterm : a ≤ terminalDoobVariation T r S F mu omega := by
    change a ≤ (grid T r).doobPredictableVariation S F mu (size T r) omega
    exact hvar.trans hmono
  have hapos : 0 ≤ terminalDoobVariation T r S F mu omega :=
    (grid T r).doobPredictableVariation_nonneg S F mu (size T r) omega
  have habs : |terminalDoobVariation T r S F mu omega| =
      terminalDoobVariation T r S F mu omega := abs_of_nonneg hapos
  change a - 1 < |terminalDoobVariation T r S F mu omega|
  rw [habs]
  linarith

theorem measure_variationGateTerminal_zero_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat)
    {eta : Real}
    (hTail : ∀ r, mu {omega |
      a - 1 < |terminalDoobVariation T r S F mu omega|} ≤
        ENNReal.ofReal eta) :
    mu {omega | variationGateTerminal a T r S F mu omega = 0} ≤
      ENNReal.ofReal eta := by
  exact (measure_mono (variationGateTerminal_zero_subset (S := S) (F := F) (mu := mu) ha T r)).trans
    (hTail r)

/-! ## Component data after the composed weights -/

private theorem commonGate_dependent_time_eq
    {β : Type*} {p : NNReal → Prop}
    (f : (u : NNReal) → p u → β)
    {u v : NNReal} (h : u = v) (hu : p u) (hv : p v) :
    f u hu = f v hv := by
  subst v
  rfl

private theorem stoppedSourceConvexRow_commonGate_skeleton_apply
    (u : ∀ n, TailConvexWeights n)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (n i : Nat) :
    stoppedSourceConvexRow u n a T S F mu
        (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      (u n).apply (fun r => stoppedSourceApproximation a T
        (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r S F mu) := by
  have hiT : (stoppedLimitSkeleton T i).1 ≤ T :=
    (stoppedLimitSkeleton T i).2
  have hrow : stoppedSourceConvexRow u n a T S F mu
      (stoppedLimitSkeleton T i).1 =
      (u n).apply (fun r => stoppedSourceApproximation a T
        (stoppedLimitSkeleton T i).1 hiT r S F mu) := by
    funext omega
    unfold stoppedSourceConvexRow
    change (∑ r ∈ (u n).support,
      (u n).weight r * stoppedSourceApproximation a T
        (min (stoppedLimitSkeleton T i).1 T)
          (min_le_right (stoppedLimitSkeleton T i).1 T) r S F mu omega) =
      ∑ r ∈ (u n).support,
        (u n).weight r * stoppedSourceApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu omega
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    exact commonGate_dependent_time_eq
      (f := fun t ht => stoppedSourceApproximation a T t ht r S F mu omega)
      (min_eq_left hiT) (min_le_right (stoppedLimitSkeleton T i).1 T) hiT
  rw [hrow]

private theorem stoppedMartingaleConvexRow_commonGate_skeleton_apply
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    (u : ∀ n, TailConvexWeights n)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (n i : Nat) :
    stoppedMartingaleConvexRow u n a T S F mu
        (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      (((u n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
        Lp Real 2 mu) : Omega → Real) := by
  have hiT : (stoppedLimitSkeleton T i).1 ≤ T :=
    (stoppedLimitSkeleton T i).2
  have hRaw :
      (((u n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 hiT r) : Lp Real 2 mu) :
        Omega → Real) =ᵐ[mu]
        (u n).apply (fun r => stoppedMartingaleApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu) := by
    exact (u n).applyVector_coeFn_ae
      (fun r => stoppedMartingaleApproximationToLp source ha T
        (stoppedLimitSkeleton T i).1 hiT r)
      (fun r => stoppedMartingaleApproximation a T
        (stoppedLimitSkeleton T i).1 hiT r S F mu)
      (fun r => MemLp.coeFn_toLp
        (memLp_two_stoppedMartingaleApproximation source ha T
          (stoppedLimitSkeleton T i).1 hiT r))
  have hrow : stoppedMartingaleConvexRow u n a T S F mu
      (stoppedLimitSkeleton T i).1 =
      (u n).apply (fun r => stoppedMartingaleApproximation a T
        (stoppedLimitSkeleton T i).1 hiT r S F mu) := by
    funext omega
    unfold stoppedMartingaleConvexRow
    change (∑ r ∈ (u n).support,
      (u n).weight r * stoppedMartingaleApproximation a T
        (min (stoppedLimitSkeleton T i).1 T)
          (min_le_right (stoppedLimitSkeleton T i).1 T) r S F mu omega) =
      ∑ r ∈ (u n).support,
        (u n).weight r * stoppedMartingaleApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu omega
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    exact commonGate_dependent_time_eq
      (f := fun t ht => stoppedMartingaleApproximation a T t ht r S F mu omega)
      (min_eq_left hiT) (min_le_right (stoppedLimitSkeleton T i).1 T) hiT
  rw [hrow]
  exact hRaw.symm

private theorem stoppedPredictableConvexRow_commonGate_skeleton_apply
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    (u : ∀ n, TailConvexWeights n)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (n i : Nat) :
    stoppedPredictableConvexRow u n a T S F mu
        (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      (((u n).applyVector (fun r =>
        stoppedPredictableApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
        Lp Real 2 mu) : Omega → Real) := by
  have hiT : (stoppedLimitSkeleton T i).1 ≤ T :=
    (stoppedLimitSkeleton T i).2
  have hRaw :
      (((u n).applyVector (fun r =>
        stoppedPredictableApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 hiT r) : Lp Real 2 mu) :
        Omega → Real) =ᵐ[mu]
        (u n).apply (fun r => stoppedPredictableApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu) := by
    exact (u n).applyVector_coeFn_ae
      (fun r => stoppedPredictableApproximationToLp source ha T
        (stoppedLimitSkeleton T i).1 hiT r)
      (fun r => stoppedPredictableApproximation a T
        (stoppedLimitSkeleton T i).1 hiT r S F mu)
      (fun r => MemLp.coeFn_toLp
        (memLp_two_stoppedPredictableApproximation source ha T
          (stoppedLimitSkeleton T i).1 hiT r))
  have hrow : stoppedPredictableConvexRow u n a T S F mu
      (stoppedLimitSkeleton T i).1 =
      (u n).apply (fun r => stoppedPredictableApproximation a T
        (stoppedLimitSkeleton T i).1 hiT r S F mu) := by
    funext omega
    unfold stoppedPredictableConvexRow
    change (∑ r ∈ (u n).support,
      (u n).weight r * stoppedPredictableProcess a T r S F mu
        (stoppedLimitSkeleton T i).1 omega) =
      ∑ r ∈ (u n).support,
        (u n).weight r * stoppedPredictableApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu omega
    apply Finset.sum_congr rfl
    intro r hr
    have hprocess : stoppedPredictableProcess a T r S F mu
        (stoppedLimitSkeleton T i).1 omega =
        stoppedPredictableApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu omega := by
      unfold stoppedPredictableProcess stoppedPredictablePath
      exact commonGate_dependent_time_eq
        (f := fun t ht => stoppedPredictableApproximation a T t ht r S F mu omega)
        (min_eq_left hiT) (min_le_right (stoppedLimitSkeleton T i).1 T) hiT
    rw [hprocess]
  rw [hrow]
  exact hRaw.symm

theorem exists_composedStoppedCadlagRowsData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (w v u : ∀ n, TailConvexWeights n)
    (hu : u = composeTailConvexWeights v w)
    (predictableLimit martingaleLimit : Nat → Lp Real 2 mu)
    (M : Process Omega)
    (XbarW MbarW AW : Nat → Process Omega)
    (terminalW : Nat → Lp Real 2 mu)
    (McadW XcorrW : Nat → Process Omega)
    (hRows : StoppedCadlagRowsData source ha T w predictableLimit
      martingaleLimit M XbarW MbarW AW terminalW McadW XcorrW) :
    ∃ (Xbar Mbar A : Nat → Process Omega)
      (terminal : Nat → Lp Real 2 mu)
      (Mcad Xcorr : Nat → Process Omega),
      StoppedCadlagRowsData source ha T u predictableLimit martingaleLimit M
        Xbar Mbar A terminal Mcad Xcorr := by
  rcases hRows with ⟨hPredictableW, hMartingaleW, hM, hMRight, hMLeft,
      hMSkeleton, hXbarW, hAPredictableW, hAStopW, hABVW, hAVarW,
      hXbarSkeletonW, hMbarSkeletonW, hASkeletonW, hTerminalW,
      hMcadW, hMcadRightW, hMcadLeftW, hMcadVersionW, hBaseGridW,
      hSkeletonEqW, hXcorrW, hDifferenceW⟩
  have hPredictableU : ∀ j, Tendsto
      (fun n => (u n).applyVector (fun r =>
        stoppedPredictableApproximationToLp source ha T
          (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r))
      atTop (𝓝 (predictableLimit j)) := by
    intro j
    simpa [hu, composeTailConvexWeights_applyVector] using
      (TailConvexWeights.tendsto_applyVector v (hPredictableW j))
  have hMartingaleU : ∀ j, Tendsto
      (fun n => (u n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r))
      atTop (𝓝 (martingaleLimit j)) := by
    intro j
    simpa [hu, composeTailConvexWeights_applyVector] using
      (TailConvexWeights.tendsto_applyVector v (hMartingaleW j))
  let Xbar : Nat → Process Omega := fun n =>
    stoppedSourceConvexRow u n a T S F mu
  let Mbar : Nat → Process Omega := fun n =>
    stoppedMartingaleConvexRow u n a T S F mu
  let A : Nat → Process Omega := fun n =>
    stoppedPredictableConvexRow u n a T S F mu
  let terminal : Nat → Lp Real 2 mu := fun n =>
    (u n).applyVector (fun r =>
      stoppedMartingaleApproximationToLp source ha T
        (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).1
        (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).2 r)
  have hCadlag (n : Nat) :=
    exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual
      (terminal n)
  choose Mcad hMcad hMcadRight hMcadLeft hMcadVersion using hCadlag
  let Xcorr : Nat → Process Omega := fun n => Mcad n + A n
  have hXbar : ∀ n, Xbar n = Mbar n + A n := by
    intro n
    simpa [Xbar, Mbar, A] using
      (stoppedSourceConvexRow_eq_add u n a T S F mu)
  have hAPredictable : ∀ n, IsStronglyPredictable F (A n) := by
    intro n
    exact isStronglyPredictable_stoppedPredictableConvexRow source ha T u n
  have hAStop : ∀ n, MeasureTheory.stoppedProcess (A n)
      (fun _ : Omega => (T : WithTop NNReal)) = A n := by
    intro n
    exact stoppedPredictableConvexRow_stopAt u n a T S F mu
  have hABV : ∀ n omega, BoundedVariationOn (A n · omega) Set.univ := by
    intro n omega
    exact boundedVariationOn_stoppedPredictableConvexRow u n a T S F mu omega
  have hAVar : ∀ n, ∀ᵐ omega ∂mu,
      eVariationOn (A n · omega) Set.univ ≤
        ENNReal.ofReal (a + 2 * max source.bound 0) := by
    intro n
    exact ae_eVariationOn_stoppedPredictableConvexRow_le source ha T u n
  have hXbarSkeleton : ∀ n i, Xbar n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      (u n).apply (fun r => stoppedSourceApproximation a T
        (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r S F mu) := by
    intro n i
    simpa [Xbar] using stoppedSourceConvexRow_commonGate_skeleton_apply
      u a T S F mu n i
  have hMbarSkeleton : ∀ n i, Mbar n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      (((u n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
        Lp Real 2 mu) : Omega → Real) := by
    intro n i
    simpa [Mbar] using stoppedMartingaleConvexRow_commonGate_skeleton_apply
      source u ha T n i
  have hASkeleton : ∀ n i, A n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      (((u n).applyVector (fun r =>
        stoppedPredictableApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
        Lp Real 2 mu) : Omega → Real) := by
    intro n i
    simpa [A] using stoppedPredictableConvexRow_commonGate_skeleton_apply
      source u ha T n i
  have hTerminal : ∀ n, terminal n =
      (u n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).1
          (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).2 r) := by
    intro n
    rfl
  have hSkeletonEq : ∀ n i, (Nat.unpair i).1 ≤ n →
      Mcad n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
        Mbar n (stoppedLimitSkeleton T i).1 := by
    intro n i hin
    exact stoppedCadlagRow_eq_rawRow_on_skeleton source ha T u
      terminal Mbar Mcad hTerminal hMbarSkeleton hMcadVersion n i hin
  have hBaseGrid : ∀ n (k : Fin (size T n + 1)),
      Mcad n ((grid T n).time k) =ᵐ[mu]
        Mbar n ((grid T n).time k) := by
    intro n k
    have hSkel := hSkeletonEq n (Nat.pair n k.1) (by simp)
    have hTime : (stoppedLimitSkeleton T (Nat.pair n k.1)).1 =
        (grid T n).time k := by
      change (grid T (Nat.unpair (Nat.pair n k.1)).1).sampledTime
          (Nat.unpair (Nat.pair n k.1)).2 = (grid T n).time k
      rw [show Nat.unpair (Nat.pair n k.1) = (n, k.1) by simp]
      exact (grid T n).sampledTime_fin_eq k
    rw [hTime] at hSkel
    exact hSkel
  have hXcorr : ∀ n, Xcorr n = Mcad n + A n := by
    intro n
    rfl
  have hDifference : ∀ n, Xcorr n - Xbar n = Mcad n - Mbar n := by
    intro n
    funext t omega
    change Mcad n t omega + A n t omega - Xbar n t omega =
      Mcad n t omega - Mbar n t omega
    rw [congrFun (congrFun (hXbar n) t) omega]
    simp only [Pi.add_apply]
    ring
  have hRowsU : StoppedCadlagRowsData source ha T u predictableLimit
      martingaleLimit M Xbar Mbar A terminal Mcad Xcorr := by
    exact ⟨hPredictableU, hMartingaleU, hM, hMRight, hMLeft, hMSkeleton,
      hXbar, hAPredictable, hAStop, hABV, hAVar, hXbarSkeleton,
      hMbarSkeleton, hASkeleton, hTerminal, hMcad, hMcadRight,
      hMcadLeft, hMcadVersion, hBaseGrid, hSkeletonEq, hXcorr,
      hDifference⟩
  exact ⟨Xbar, Mbar, A, terminal, Mcad, Xcorr, hRowsU⟩

/-! ## Main row-5 endpoint -/

theorem exists_commonGateRows
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (source : BoundedSemimartingaleSource S F mu)
    (T : NNReal) {eta : Real} (heta : 0 < eta) :
    ∃ (a : Real) (w v u : ∀ n, TailConvexWeights n)
      (predictableLimit martingaleLimit : Nat → Lp Real 2 mu)
      (M : Process Omega) (Xbar Mbar A : Nat → Process Omega)
      (terminal : Nat → Lp Real 2 mu) (Mcad Xcorr : Nat → Process Omega)
      (selection : Nat → Nat)
      (R : Omega → Real) (gLimit : Lp Real 2 mu)
      (alphaSeq : Nat → Omega → WithTop NNReal)
      (alpha : Omega → WithTop NNReal),
      0 ≤ a ∧
      0 < a ∧
      (∀ r, mu {omega | variationGateTerminal a T r S F mu omega = 0} ≤
        ENNReal.ofReal eta) ∧
      (u = composeTailConvexWeights v w) ∧
      (∃ ha : 0 ≤ a, StoppedCadlagRowsData source ha T u predictableLimit
        martingaleLimit M Xbar Mbar A terminal Mcad Xcorr) ∧
      StrictMono selection ∧
      (∀ k, mu {omega |
        (1 / 6 : Real) ≤ dist (((u (selection k)).apply (fun r =>
            variationGateTerminal a T r S F mu)) omega) (R omega)} ≤
        ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1)))) ∧
      (∀ k omega, alphaSeq k omega = min (T : WithTop NNReal)
        (LeftContinuousHittingTime.strictHittingAfter
          (fun t omega =>
            -variationGateConvexRow u (selection k) a T S F mu t omega)
          (-1 / 2) omega)) ∧
      (∀ n, ∀ omega, 0 ≤ variationGateConvexRow u n a T S F mu T omega ∧
        variationGateConvexRow u n a T S F mu T omega ≤ 1) ∧
      Tendsto
        (fun n => (u n).applyVector (fun r =>
          variationGateTerminalToLp (S := S) (F := F) (mu := mu) a T r)) atTop (𝓝 gLimit) ∧
      (∀ᵐ omega ∂mu, Tendsto
        (fun n => (u n).apply (fun r =>
          variationGateTerminal a T r S F mu) omega) atTop (𝓝 (R omega))) ∧
      (∀ᵐ omega ∂mu, 0 ≤ R omega ∧ R omega ≤ 1) ∧
      (1 - eta ≤ ∫ omega, R omega ∂mu) ∧
      (∀ n, IsStoppingTime F (alphaSeq n)) ∧
      IsStoppingTime F alpha ∧
      (∀ omega, alpha omega = ⨅ k, alphaSeq k omega) ∧
      (∀ n omega, alpha omega ≤ alphaSeq n omega) ∧
      mu {omega | alpha omega < (T : WithTop NNReal)} ≤
        ENNReal.ofReal (4 * eta) := by
  classical
  have hBIP := boundedInProbability_terminalDoobVariation hS source T
  obtain ⟨B, hB, hTail⟩ := hBIP eta heta
  let a : Real := B + 1
  have ha : 0 ≤ a := by linarith
  have haPos : 0 < a := by linarith
  have hRnonneg : a - 1 ≥ 0 := by simp [a, hB]
  have hGateTail : ∀ r, mu {omega |
      variationGateTerminal a T r S F mu omega = 0} ≤
      ENNReal.ofReal eta := by
    intro r
    apply measure_variationGateTerminal_zero_le ha T r
    intro r
    simpa [a] using hTail r
  obtain ⟨w, predictableLimit, martingaleLimit, M, XbarW, MbarW, AW,
      terminalW, McadW, XcorrW, hRows, _hTerminalNormW, _hMcadMemW,
      _hMMemW, _hDifferenceMemW, _hEnvelopeMemW, _hEnvelopeBoundW,
      _hEnvelopeNormW, _hEnvelopeInMeasureW, _hEnvelopeDominatesW⟩ :=
    exists_stoppedProcessConvexification_cadlag_rows_terminal_envelope
      hUsual source ha T
  let x : Nat → Lp Real 2 mu := fun r =>
    variationGateTerminalToLp (S := S) (F := F) (mu := mu) a T r
  let xComp : Nat → Lp Real 2 mu := fun n => (w n).applyVector x
  have hx : ∀ r, ‖x r‖ ≤ 1 := fun r =>
    variationGateTerminalToLp_norm_le (S := S) (F := F) (mu := mu) a T r
  have hxComp : ∀ n, ‖xComp n‖ ≤ 1 := by
    intro n
    change ‖∑ r ∈ (w n).support, (w n).weight r • x r‖ ≤ 1
    calc
      ‖∑ r ∈ (w n).support, (w n).weight r • x r‖ ≤
          ∑ r ∈ (w n).support, ‖(w n).weight r • x r‖ := norm_sum_le _ _
      _ = ∑ r ∈ (w n).support, (w n).weight r * ‖x r‖ := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ((w n).nonneg r hr)]
      _ ≤ ∑ r ∈ (w n).support, (w n).weight r * 1 := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (hx r) ((w n).nonneg r hr)
      _ = 1 := by simpa using (w n).sum_eq_one
  obtain ⟨gLimit, hgLimit⟩ :=
    TailConvexWeights.exists_tendsto_tailNormSqNearMinimizers hxComp
      (by norm_num)
  let v₀ : ∀ n, TailConvexWeights n :=
    TailConvexWeights.tailNormSqNearMinimizers xComp
  have hg₀ : Tendsto (fun n => (v₀ n).applyVector xComp)
      atTop (𝓝 gLimit) := hgLimit
  have hInMeasure₀ : TendstoInMeasure mu
      (fun n => (v₀ n).apply (fun i => (w i).apply
        (fun r => variationGateTerminal a T r S F mu)))
      atTop (gLimit : Omega → Real) := by
    have hLp := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hg₀
    refine TendstoInMeasure.congr_left ?_ hLp
    intro n
    exact (v₀ n).applyVector_coeFn_ae xComp
      (fun i => (w i).apply (fun r => variationGateTerminal a T r S F mu))
      (fun i => (w i).applyVector_coeFn_ae x
        (fun r => variationGateTerminal a T r S F mu)
        (fun r => MemLp.coeFn_toLp (memLp_two_variationGateTerminal
          (S := S) (F := F) (mu := mu) a T r)))
  obtain ⟨cutoff, hcutoff, hAE₀⟩ :=
    exists_strictMono_tendstoAE_of_countable_tendstoInMeasure
      (f := fun n _ => (v₀ n).apply (fun i => (w i).apply
        (fun r => variationGateTerminal a T r S F mu)))
      (g := fun _ => (gLimit : Omega → Real))
      (fun _ => hInMeasure₀)
  have hcut_ge : ∀ n, n ≤ cutoff n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ihn =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ihn
          (hcutoff (Nat.lt_succ_self n)))
  let v : ∀ n, TailConvexWeights n := fun n =>
    (v₀ (cutoff n)).mono (hcut_ge n)
  let u : ∀ n, TailConvexWeights n := composeTailConvexWeights v w
  obtain ⟨Xbar, Mbar, A, terminal, Mcad, Xcorr, hRowsU⟩ :=
    exists_composedStoppedCadlagRowsData hUsual source ha T w v u
      (by rfl) predictableLimit martingaleLimit M XbarW MbarW AW terminalW
      McadW XcorrW hRows
  have hgv : Tendsto (fun n => (u n).applyVector x)
      atTop (𝓝 gLimit) := by
    have hcomp := hg₀.comp hcutoff.tendsto_atTop
    have hcomp' : Tendsto (fun n => (v₀ (cutoff n)).applyVector xComp)
        atTop (𝓝 gLimit) := by
      exact hcomp
    simpa [u, v, xComp, composeTailConvexWeights_applyVector,
      TailConvexWeights.applyVector_mono] using hcomp'
  let R : Omega → Real := gLimit
  have hAE : ∀ᵐ omega ∂mu, Tendsto
      (fun n => (u n).apply (fun r => variationGateTerminal a T r S F mu) omega)
      atTop (𝓝 (R omega)) := by
    filter_upwards [hAE₀ 0] with omega homega
    simpa [u, R, v, composeTailConvexWeights_apply,
      TailConvexWeights.mono_apply] using homega
  have hRbounds : ∀ᵐ omega ∂mu, 0 ≤ R omega ∧ R omega ≤ 1 := by
    have hmem : MemLp (gLimit : Omega → Real) (2 : ENNReal) mu :=
      Lp.memLp gLimit
    have hlim : ∀ᵐ omega ∂mu, Tendsto
        (fun n => (u n).apply (fun r => variationGateTerminal a T r S F mu) omega)
        atTop (𝓝 (R omega)) := by
      filter_upwards [hAE₀ 0] with omega homega
      simpa [u, v, composeTailConvexWeights_apply,
        TailConvexWeights.mono_apply, R] using homega
    have hrowBounds : ∀ n, ∀ omega, 0 ≤
        (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ∧
        (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ≤ 1 := by
      intro n omega
      exact variationGateConvexRow_nonneg_le_one u n a T S F mu T omega
    filter_upwards [hlim] with omega hω
    have hnonneg : ∀ n, 0 ≤
        (u n).apply (fun r => variationGateTerminal a T r S F mu) omega :=
      fun n => (hrowBounds n omega).1
    have hupper : ∀ n,
        (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ≤ 1 :=
      fun n => (hrowBounds n omega).2
    exact ⟨ge_of_tendsto hω (Filter.Eventually.of_forall hnonneg),
      le_of_tendsto hω (Filter.Eventually.of_forall hupper)⟩
  have hGateIntegral : ∀ r, 1 - eta ≤
      ∫ omega, variationGateTerminal a T r S F mu omega ∂mu := by
    intro r
    let Z : Set Omega := {omega |
      variationGateTerminal a T r S F mu omega = 0}
    have hZ : MeasurableSet Z := by
      change MeasurableSet (variationGateTerminal a T r S F mu ⁻¹' ({0} : Set Real))
      exact (stronglyMeasurable_variationGateTerminal (S := S) (F := F) (mu := mu) a T r).measurable
        (measurableSet_singleton 0)
    have hZbound : mu.real Z ≤ eta := by
      rw [measureReal_def]
      have hto : (mu Z).toReal ≤ (ENNReal.ofReal eta).toReal :=
        (ENNReal.toReal_le_toReal (measure_ne_top _ _)
          ENNReal.ofReal_ne_top).2 (by simpa [Z] using hGateTail r)
      simpa [heta.le] using hto
    have hInd : variationGateTerminal a T r S F mu =
        Zᶜ.indicator (fun _ => (1 : Real)) := by
      funext omega
      by_cases hz : variationGateTerminal a T r S F mu omega = 0
      · simp [Z, hz]
      · have h01 := variationGateProcess_eq_zero_or_one
          a T r S F mu T omega
        rcases h01 with h0 | h1
        · exact False.elim (hz h0)
        · rw [variationGateTerminal]
          simp [Z, hz, h1]
    rw [hInd]
    have hIntInd : (∫ omega, Zᶜ.indicator (fun _ => (1 : Real)) omega ∂mu) =
        mu.real Zᶜ := by
      change (∫ omega, Zᶜ.indicator (1 : Omega → Real) omega ∂mu) =
        mu.real Zᶜ
      exact integral_indicator_one hZ.compl
    rw [hIntInd, measureReal_compl hZ]
    simp
    linarith
  have hRowRawAe : ∀ n, ∀ᵐ omega ∂mu,
      (((u n).applyVector x : Lp Real 2 mu) : Omega → Real) omega =
        (u n).apply (fun r => variationGateTerminal a T r S F mu) omega := by
    intro n
    exact (u n).applyVector_coeFn_ae
      (fun r => variationGateTerminalToLp (S := S) (F := F) (mu := mu) a T r)
      (fun r => variationGateTerminal a T r S F mu)
      (fun r => MemLp.coeFn_toLp (memLp_two_variationGateTerminal
        (S := S) (F := F) (mu := mu) a T r))
  have hInMeasureU : TendstoInMeasure mu
      (fun n omega =>
        (u n).apply (fun r => variationGateTerminal a T r S F mu) omega)
      atTop (gLimit : Omega → Real) := by
    have hLpIn : TendstoInMeasure mu
        (fun n omega =>
          (((u n).applyVector x : Lp Real 2 mu) : Omega → Real) omega)
        atTop (gLimit : Omega → Real) :=
      MeasureTheory.tendstoInMeasure_of_tendsto_Lp hgv
    refine TendstoInMeasure.congr_left ?_ hLpIn
    intro n
    exact hRowRawAe n
  have hRowMem : ∀ n, MemLp
      ((u n).apply (fun r => variationGateTerminal a T r S F mu))
      (2 : ENNReal) mu := by
    intro n
    exact (memLp_congr_ae (hRowRawAe n)).mp (Lp.memLp ((u n).applyVector x))
  have hRowInt : ∀ n, Integrable
      ((u n).apply (fun r => variationGateTerminal a T r S F mu)) mu := by
    intro n
    exact (hRowMem n).integrable (by norm_num)
  have hRInt : Integrable R mu := by
    exact (Lp.memLp gLimit).integrable (by norm_num)
  have hLp2 : Tendsto (fun n => eLpNorm
      (((u n).apply (fun r => variationGateTerminal a T r S F mu)) - R)
      (2 : ENNReal) mu) atTop (𝓝 0) := by
    have hLp2' := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun n => (u n).applyVector x) gLimit).mp hgv
    apply hLp2'.congr'
    filter_upwards [] with n
    apply eLpNorm_congr_ae
    filter_upwards [hRowRawAe n] with omega homega
    simp only [Pi.sub_apply, R]
    rw [homega]
  have hLp1 : Tendsto (fun n => eLpNorm
      (((u n).apply (fun r => variationGateTerminal a T r S F mu)) - R)
      (1 : ENNReal) mu) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hLp2 ?_ ?_
    · exact fun _ => bot_le
    · intro n
      exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hIntegralTendsto : Tendsto (fun n => ∫ omega,
      (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ∂mu)
      atTop (𝓝 (∫ omega, R omega ∂mu)) := by
    exact tendsto_integral_of_L1' R
      (Filter.Eventually.of_forall hRowInt) hLp1
  have hRowLower : ∀ n, 1 - eta ≤ ∫ omega,
      (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ∂mu := by
    intro n
    change 1 - eta ≤ ∫ omega, ∑ r ∈ (u n).support,
      (u n).weight r * variationGateTerminal a T r S F mu omega ∂mu
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
      calc
        1 - eta = ∑ r ∈ (u n).support,
            (u n).weight r * (1 - eta) := by
              rw [← Finset.sum_mul, (u n).sum_eq_one]
              simp
        _ ≤ ∑ r ∈ (u n).support,
            (u n).weight r *
              ∫ omega, variationGateTerminal a T r S F mu omega ∂mu := by
              apply Finset.sum_le_sum
              intro r hr
              exact mul_le_mul_of_nonneg_left (hGateIntegral r)
                ((u n).nonneg r hr)
    · intro r hr
      exact ((memLp_two_variationGateTerminal (S := S) (F := F) (mu := mu) a T r).integrable
        (by norm_num)).const_mul ((u n).weight r)
  have hExpectation : 1 - eta ≤ ∫ omega, R omega ∂mu :=
    ge_of_tendsto hIntegralTendsto (Filter.Eventually.of_forall hRowLower)
  let errorSet : Nat → Set Omega := fun n => {omega |
    (1 / 6 : Real) ≤ dist (((u n).apply
      (fun r => variationGateTerminal a T r S F mu)) omega)
        (R omega)}
  have hErrorMeasureTendsto : Tendsto (fun n => mu.real (errorSet n))
      atTop (𝓝 0) := by
    have hdist := (tendstoInMeasure_iff_measureReal_dist.mp hInMeasureU)
      (1 / 6 : Real) (by norm_num)
    simpa [errorSet] using hdist
  obtain ⟨selection, hselection, hselectionError⟩ :=
    exists_strictMono_subsequence_lt_of_tendsto_zero
      (δ := fun n => mu.real (errorSet n))
      (r := fun k => eta * ((1 / 2 : Real) ^ (k + 1)))
      hErrorMeasureTendsto
      (by intro k; positivity)
  have hSelectionError : ∀ k, mu (errorSet (selection k)) ≤
      ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1))) := by
    intro k
    calc
      mu (errorSet (selection k)) =
          ENNReal.ofReal (mu.real (errorSet (selection k))) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1))) :=
        ENNReal.ofReal_le_ofReal (hselectionError k).le
  let gateRow : Nat → Process Omega := fun n =>
    variationGateConvexRow u n a T S F mu
  let alphaSeq : Nat → Omega → WithTop NNReal := fun k omega =>
    min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -gateRow (selection k) t omega)
        (-1 / 2) omega)
  let alpha : Omega → WithTop NNReal := fun omega => ⨅ k, alphaSeq k omega
  let : F.IsRightContinuous := hUsual.rightContinuous
  have hAlphaSeqStopping : ∀ k, IsStoppingTime F (alphaSeq k) := by
    intro k
    have hAdapt : StronglyAdapted F (gateRow (selection k)) := by
      exact stronglyAdapted_variationGateConvexRow (S := S) (F := F) (mu := mu) u (selection k) a T
    have hLeft : ∀ omega s, ContinuousWithinAt
        ((gateRow (selection k)) · omega) (Set.Iic s) s := by
      intro omega s
      exact continuousWithinAt_variationGateConvexRow_Iic u (selection k)
        a T S F mu omega s
    have hHit : IsStoppingTime F
        (LeftContinuousHittingTime.strictHittingAfter
          (fun t omega => -gateRow (selection k) t omega) (-1 / 2)) := by
      apply LeftContinuousHittingTime.strictHittingAfter_isStoppingTime
        (hAdapt.neg)
      intro omega s
      exact (hLeft omega s).neg
    simpa [alphaSeq] using (isStoppingTime_const F T).min hHit
  have hAlphaStopping : IsStoppingTime F alpha := by
    exact IsStoppingTime.iInf hAlphaSeqStopping
  have hAlphaLe : ∀ k omega, alpha omega ≤ alphaSeq k omega := by
    intro k omega
    exact iInf_le (fun j => alphaSeq j omega) k
  have hAlphaSeqTerminal : ∀ k omega, alphaSeq k omega <
      (T : WithTop NNReal) → gateRow (selection k) T omega < 1 / 2 := by
    intro k omega hk
    have hHit :
        LeftContinuousHittingTime.strictHittingAfter
          (fun t omega => -gateRow (selection k) t omega) (-1 / 2) omega <
          (T : WithTop NNReal) := by
      by_cases hTh : (T : WithTop NNReal) ≤
          LeftContinuousHittingTime.strictHittingAfter
            (fun t omega => -gateRow (selection k) t omega) (-1 / 2) omega
      · have hEq : min (T : WithTop NNReal)
            (LeftContinuousHittingTime.strictHittingAfter
              (fun t omega => -gateRow (selection k) t omega) (-1 / 2) omega) =
            (T : WithTop NNReal) := min_eq_left hTh
        rw [← hEq] at hk
        exact False.elim ((not_lt_of_ge le_rfl) hk)
      · exact lt_of_not_ge hTh
    have hHit' : MeasureTheory.hittingAfter
          (fun t omega => -gateRow (selection k) t omega)
          (Set.Ioi (-1 / 2)) 0 omega < T := hHit
    rw [MeasureTheory.hittingAfter_lt_iff] at hHit'
    obtain ⟨s, hs, hsGate⟩ := hHit'
    have hs_le : s ≤ T := hs.2.le
    have hmono := monotone_variationGateConvexRow u (selection k)
      a T S F mu hs_le omega
    have hsGate' : -1 / 2 < -gateRow (selection k) s omega := by
      simpa [gateRow] using hsGate
    dsimp [gateRow] at hmono ⊢
    linarith
  have hErrorSetSummable :
      (∑' k : Nat, ENNReal.ofReal
        (eta * ((1 / 2 : Real) ^ (k + 1)))) ≤ ENNReal.ofReal eta := by
    have hsum : Summable (fun k : Nat =>
        eta * ((1 / 2 : Real) ^ (k + 1))) := by
      simpa [pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using summable_geometric_two.mul_left (eta / 2)
    rw [← ENNReal.ofReal_tsum_of_nonneg (by intro k; positivity) hsum]
    have : (∑' k : Nat, eta * ((1 / 2 : Real) ^ (k + 1))) = eta := by
      simpa [pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using tsum_geometric_two' eta
    rw [this]
  have hRBad : mu {omega | R omega ≤ 2 / 3} ≤
      ENNReal.ofReal (3 * eta) := by
    let f : Omega → Real := fun omega => 3 * (1 - R omega)
    have hf : Integrable f mu := by
      have h := ((integrable_const (1 : Real)).sub hRInt).const_mul (3 : Real)
      simpa [f] using h
    have hf_nonneg : 0 ≤ᵐ[mu] f := by
      filter_upwards [hRbounds] with omega hω
      dsimp [f]
      linarith [hω.2]
    have hmeasure : mu {omega | R omega ≤ 2 / 3} ≤
        ENNReal.ofReal (∫ omega, f omega ∂mu) :=
      hf.measure_le_integral hf_nonneg
        (fun omega homega => by
          dsimp [f] at *
          linarith [homega])
    have hIntegralF : (∫ omega, f omega ∂mu) =
        3 * (1 - ∫ omega, R omega ∂mu) := by
      dsimp [f]
      rw [integral_const_mul, integral_sub (integrable_const _ ) hRInt,
        integral_const]
      have hmuReal : mu.real Set.univ = 1 := by
        simp [measureReal_def]
      rw [hmuReal]
      ring
    rw [hIntegralF] at hmeasure
    apply hmeasure.trans
    exact ENNReal.ofReal_le_ofReal (by linarith [hExpectation])
  have hAlphaEventSubset : {omega | alpha omega < (T : WithTop NNReal)} ⊆
      {omega | R omega ≤ 2 / 3} ∪ ⋃ k, errorSet (selection k) := by
    intro omega hω
    change (⨅ k, alphaSeq k omega) < (T : WithTop NNReal) at hω
    obtain ⟨k, hk⟩ := (iInf_lt_iff.mp hω)
    by_cases hR : R omega ≤ 2 / 3
    · exact Or.inl hR
    · right
      apply mem_iUnion.2 ⟨k, ?_⟩
      by_contra hnot
      have hErr : dist
          (((u (selection k)).apply
            (fun r => variationGateTerminal a T r S F mu)) omega)
          (R omega) < 1 / 6 := lt_of_not_ge hnot
      have hGate := hAlphaSeqTerminal k omega hk
      have hrowR :
          ((u (selection k)).apply (fun r => variationGateTerminal a T r S F mu))
            omega < 1 / 2 + 1 / 6 := by
        have hGate' :
            ((u (selection k)).apply
              (fun r => variationGateTerminal a T r S F mu)) omega < 1 / 2 := by
          change ((u (selection k)).apply
            (fun r => variationGateProcess a T r S F mu T)) omega < 1 / 2 at hGate
          simpa [variationGateTerminal] using hGate
        exact hGate'.trans (by norm_num)
      have hupper : R omega -
          ((u (selection k)).apply
            (fun r => variationGateTerminal a T r S F mu)) omega < 1 / 6 := by
        have hdist : |((u (selection k)).apply
            (fun r => variationGateTerminal a T r S F mu)) omega - R omega| <
            1 / 6 := by
          simpa [Real.dist_eq] using hErr
        have habs : |R omega -
            ((u (selection k)).apply
              (fun r => variationGateTerminal a T r S F mu)) omega| <
            1 / 6 := by
          simpa [abs_sub_comm] using hdist
        exact (le_abs_self _).trans_lt habs
      have hR' : (2 / 3 : Real) < R omega := lt_of_not_ge hR
      have hGate' :
          ((u (selection k)).apply
            (fun r => variationGateTerminal a T r S F mu)) omega < 1 / 2 := by
        change ((u (selection k)).apply
          (fun r => variationGateProcess a T r S F mu T)) omega < 1 / 2 at hGate
        simpa [variationGateTerminal] using hGate
      linarith [hR', hGate', hupper]
  have hAlphaMeasure : mu {omega | alpha omega < (T : WithTop NNReal)} ≤
      ENNReal.ofReal (4 * eta) := by
    calc
      mu {omega | alpha omega < (T : WithTop NNReal)} ≤
          mu ({omega | R omega ≤ 2 / 3} ∪ ⋃ k, errorSet (selection k)) :=
        measure_mono hAlphaEventSubset
      _ ≤ mu {omega | R omega ≤ 2 / 3} +
          mu (⋃ k, errorSet (selection k)) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (3 * eta) +
          ∑' k, ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1))) := by
        refine add_le_add hRBad ?_
        exact (measure_iUnion_le _).trans
          (ENNReal.tsum_le_tsum fun k => hSelectionError k)
      _ ≤ ENNReal.ofReal (4 * eta) := by
        calc
          ENNReal.ofReal (3 * eta) +
              ∑' k, ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1))) ≤
            ENNReal.ofReal (3 * eta) + ENNReal.ofReal eta :=
              add_le_add (le_refl _) hErrorSetSummable
          _ = ENNReal.ofReal (4 * eta) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
  refine ⟨a, w, v, u, predictableLimit, martingaleLimit, M, Xbar, Mbar, A,
    terminal, Mcad, Xcorr, selection, R, gLimit, alphaSeq, alpha,
    ha, haPos, hGateTail, rfl, ⟨ha, hRowsU⟩, hselection, ?_, ?_, ?_, hgv, hAE,
    hRbounds, hExpectation, hAlphaSeqStopping, hAlphaStopping, (fun _ => rfl), hAlphaLe,
    hAlphaMeasure⟩
  · intro k
    simpa [errorSet] using hSelectionError k
  · intro k omega
    simp [alphaSeq, gateRow]
  · intro n omega
    exact variationGateConvexRow_nonneg_le_one u n a T S F mu T omega

end HorizonFactorialGrid

end FTAPTheorem42
