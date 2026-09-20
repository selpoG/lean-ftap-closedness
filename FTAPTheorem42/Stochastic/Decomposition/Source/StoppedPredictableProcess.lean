/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedComponents
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath

/-!
# Full-time stopped predictable factorial paths

The right-factorial predictable Doob path is a left-continuous step path on
`[0,T]`: on an interval `(t_k,t_{k+1}]` it has the `(k+1)`-st predictable
component, which is measurable with respect to the filtration at `t_k`.  This
file extends that path constantly after `T`.  The extension is used by the
process-level convexification, so its regularity and variation estimates are
stated for the same process.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- Extend a stopped right-factorial predictable path constantly after the
fixed horizon. -/
noncomputable def stoppedPredictableProcess
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Process Omega :=
  fun t omega =>
    stoppedPredictablePath a T r S F mu
      ⟨min t T, min_le_right t T⟩ omega

@[simp]
theorem stoppedPredictableProcess_stopAt
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) :
    MeasureTheory.stoppedProcess
        (stoppedPredictableProcess a T r S F mu)
        (fun _ : Omega => (T : WithTop NNReal)) =
      stoppedPredictableProcess a T r S F mu := by
  funext t omega
  change stoppedPredictableProcess a T r S F mu (min t T) omega =
    stoppedPredictableProcess a T r S F mu t omega
  simp only [stoppedPredictableProcess]
  congr 2
  simp

private theorem ceil_eq_of_mem_Ioc
    {r k : Nat} {t : NNReal}
    (ht : t ∈ Set.Ioc ((k : NNReal) / (r.factorial : NNReal))
      (((k + 1 : Nat) : NNReal) / (r.factorial : NNReal))) :
    Nat.ceil (t * (r.factorial : NNReal)) = k + 1 := by
  have hf : (0 : NNReal) < (r.factorial : NNReal) := by positivity
  have hLower : (k : NNReal) < t * (r.factorial : NNReal) := by
    exact (div_lt_iff₀ hf).mp ht.1
  have hUpper : t * (r.factorial : NNReal) ≤ (k + 1 : Nat) := by
    exact_mod_cast (le_div_iff₀ hf).mp ht.2
  apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).2
  constructor
  · simpa only [Nat.succ_sub_one, Nat.cast_id] using hLower
  · exact_mod_cast hUpper

theorem approxIndex_previous_time_lt
    (T t : NNReal) (ht : t ≤ T) (r : Nat)
    {k : Nat}
    (hk : (approxIndex T t ht r).1 = k + 1) :
    (grid T r).sampledTime k < t := by
  have hceil : Nat.ceil (t * (r.factorial : NNReal)) = k + 1 := by
    simpa [approxIndex] using hk
  have hLowerNat : k < Nat.ceil (t * (r.factorial : NNReal)) := by
    rw [hceil]
    exact Nat.lt_succ_self k
  have hLower : (k : NNReal) < t * (r.factorial : NNReal) :=
    (Nat.lt_ceil (α := NNReal)).mp hLowerNat
  have hDiv : (k : NNReal) / (r.factorial : NNReal) < t := by
    apply (div_lt_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
      positivity)).2
    simpa [mul_comm] using hLower
  have hkSize : k ≤ size T r := by
    have hq := (approxIndex T t ht r).isLt
    rw [show (approxIndex T t ht r).1 = k + 1 from hk] at hq
    exact (Nat.le_succ k).trans
      (Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using hq))
  rw [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex]
  simp only [hkSize, min_eq_left]
  change min ((k : NNReal) / (r.factorial : NNReal)) T < t
  exact min_lt_of_left_lt hDiv

theorem approxIndex_previous_time_le
    (T t : NNReal) (ht : t ≤ T) (r : Nat)
    {k : Nat}
    (hk : (approxIndex T t ht r).1 = k + 1) :
    (grid T r).sampledTime k ≤ t :=
  (approxIndex_previous_time_lt T t ht r hk).le

private theorem stoppedPredictableApproximation_stronglyMeasurable_at
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (_source : BoundedSemimartingaleSource S F mu)
    {a : Real} (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    StronglyMeasurable[F t]
      (stoppedPredictableApproximation a T t ht r S F mu) := by
  change StronglyMeasurable[F t]
    ((grid T r).doobVariationStoppedPredictablePart S F mu a
      (approxIndex T t ht r).1)
  generalize hq : (approxIndex T t ht r).1 = n
  cases n with
  | zero =>
      exact stronglyMeasurable_const
  | succ k =>
      have hA : StronglyMeasurable[(grid T r).sampledFiltration F k]
          ((grid T r).doobVariationStoppedPredictablePart S F mu a (k + 1)) := by
        unfold ChronologicalGrid.doobVariationStoppedPredictablePart
          discretePredictableIntegral
        have hsum : StronglyMeasurable[(grid T r).sampledFiltration F k]
            (fun omega => ∑ j ∈ Finset.range (k + 1),
              (grid T r).doobVariationGate S F mu a j omega *
                ((grid T r).doobPredictablePart S F mu (j + 1) omega -
                  (grid T r).doobPredictablePart S F mu j omega)) := by
          refine Finset.stronglyMeasurable_fun_sum (M := Real)
            (s := Finset.range (k + 1)) ?_
          intro j hj
          rw [Finset.mem_range] at hj
          have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
          have hGate := (grid T r).stronglyAdapted_doobVariationGate
            S F mu a j
          have hNext := stronglyAdapted_predictablePart
            (f := (grid T r).natSample S)
            (ℱ := (grid T r).sampledFiltration F) (μ := mu) j
          have hNow := stronglyAdapted_predictablePart'
            (f := (grid T r).natSample S)
            (ℱ := (grid T r).sampledFiltration F) (μ := mu) j
          exact ((hGate.mono
            (Filtration.mono ((grid T r).sampledFiltration F) hjk)).mul
            ((hNext.mono
              (Filtration.mono ((grid T r).sampledFiltration F) hjk)).sub
              (hNow.mono
                (Filtration.mono ((grid T r).sampledFiltration F) hjk))))
        exact hsum
      have hPrev := approxIndex_previous_time_le T t ht r (by
        exact hq)
      have hA' : StronglyMeasurable[F t]
          ((grid T r).doobVariationStoppedPredictablePart S F mu a (k + 1)) :=
        hA.mono (Filtration.mono F hPrev)
      exact hA'

theorem stronglyAdapted_stoppedPredictableProcess
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (_ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    StronglyAdapted F (stoppedPredictableProcess a T r S F mu) := by
  intro t
  by_cases ht : t ≤ T
  · unfold stoppedPredictableProcess
    simpa [stoppedPredictablePath, min_eq_left ht] using
      (stoppedPredictableApproximation_stronglyMeasurable_at
        (a := a) source T t ht r)
  · have hT := stoppedPredictableApproximation_stronglyMeasurable_at
      (a := a) source T T le_rfl r
    have hT' : StronglyMeasurable[F t]
        (stoppedPredictableApproximation a T T le_rfl r S F mu) :=
      hT.mono (F.mono (le_of_not_ge ht))
    unfold stoppedPredictableProcess
    simpa [stoppedPredictablePath, min_eq_right (le_of_not_ge ht)] using hT'

private theorem stoppedPredictablePath_continuousWithinAt_Iic
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (omega : Omega) (t : Set.Iic T) :
    ContinuousWithinAt
      (fun u => stoppedPredictablePath a T r S F mu u omega)
      (Set.Iic t) t := by
  generalize hq : (approxIndex T t.1 t.2 r).1 = n
  cases n with
  | zero =>
      have ht0 : t.1 = 0 := by
        have : Nat.ceil (t.1 * (r.factorial : NNReal)) = 0 := by
          simpa [approxIndex] using hq
        have hnonneg : 0 ≤ t.1 * (r.factorial : NNReal) := by positivity
        have hmul : t.1 * (r.factorial : NNReal) = 0 :=
          le_antisymm (Nat.ceil_eq_zero.mp this) hnonneg
        exact (mul_eq_zero.mp hmul).resolve_right (by positivity)
      let zeroT : Set.Iic T := ⟨0, show (0 : NNReal) ≤ T from bot_le⟩
      have htSub : t = zeroT := by
        apply Subtype.ext
        exact ht0
      have hEventually : ∀ᶠ u in 𝓝[Set.Iic t] t,
          stoppedPredictablePath a T r S F mu u omega =
            stoppedPredictablePath a T r S F mu zeroT omega := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu0 : u = zeroT := by
          apply Subtype.ext
          have huLe : u ≤ zeroT := by
            simpa [htSub] using hu
          have hu' : (u : NNReal) ≤ 0 := huLe
          exact le_antisymm hu' bot_le
        rw [hu0]
      have hConst : ContinuousWithinAt
          (fun _ : Set.Iic T =>
            stoppedPredictablePath a T r S F mu zeroT omega)
          (Set.Iic t) t := continuousWithinAt_const
      have hAt : stoppedPredictablePath a T r S F mu t omega =
          stoppedPredictablePath a T r S F mu zeroT omega := by
        rw [htSub]
      exact hConst.congr_of_eventuallyEq hEventually hAt
  | succ k =>
      have hceil : Nat.ceil (t.1 * (r.factorial : NNReal)) = k + 1 := by
        simpa [approxIndex] using hq
      have hLowerNat : k < Nat.ceil (t.1 * (r.factorial : NNReal)) := by
        rw [hceil]
        exact Nat.lt_succ_self k
      have hLower : (k : NNReal) < t.1 * (r.factorial : NNReal) :=
        (Nat.lt_ceil (α := NNReal)).mp hLowerNat
      have hPrev : (k : NNReal) / (r.factorial : NNReal) < t.1 := by
        apply (div_lt_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
          positivity)).2
        simpa [mul_comm] using hLower
      let p : Set.Iic T :=
        ⟨(k : NNReal) / (r.factorial : NNReal),
          hPrev.le.trans t.2⟩
      have hPrevSub : p < t := hPrev
      have hEventually : ∀ᶠ u in 𝓝[Set.Iic t] t,
          stoppedPredictablePath a T r S F mu u omega =
            stoppedPredictablePath a T r S F mu t omega := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hPrevSub),
          self_mem_nhdsWithin] with u hu hIic
        have huT : u.1 ≤ T := u.2
        have hceilU : Nat.ceil (u.1 * (r.factorial : NNReal)) = k + 1 := by
          apply ceil_eq_of_mem_Ioc
          constructor
          · exact (div_lt_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
              positivity)).2 (by
                have huVal : (k : NNReal) / (r.factorial : NNReal) < u.1 := hu
                exact (div_lt_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
                  positivity)).1 huVal)
          · have : u.1 ≤ t.1 := hIic
            have htCeil : t.1 * (r.factorial : NNReal) ≤
                (k + 1 : Nat) := by
              have h := Nat.le_ceil (t.1 * (r.factorial : NNReal))
              rw [hceil] at h
              exact h
            apply (le_div_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
              positivity)).2
            exact (mul_le_mul_of_nonneg_right this (by positivity)).trans htCeil
        have hIndex : approxIndex T u.1 u.2 r =
            approxIndex T t.1 t.2 r := by
          apply Fin.ext
          change Nat.ceil (u.1 * (r.factorial : NNReal)) =
            Nat.ceil (t.1 * (r.factorial : NNReal))
          exact hceilU.trans hceil.symm
        simp [stoppedPredictablePath, stoppedPredictableApproximation,
          hIndex]
      exact continuousWithinAt_const.congr_of_eventuallyEq hEventually (by rfl)

theorem continuousWithinAt_stoppedPredictableProcess_Iic
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (omega : Omega) (t : NNReal) :
    ContinuousWithinAt
      (stoppedPredictableProcess a T r S F mu · omega)
      (Set.Iic t) t := by
  let phi : NNReal → Set.Iic T := fun u =>
    ⟨min u T, min_le_right u T⟩
  let u := phi t
  have hphiValue : ContinuousWithinAt (fun v : NNReal => min v T)
      (Set.Iic t) t :=
    (continuous_id.min continuous_const).continuousWithinAt
  have hphiMaps : MapsTo (fun v : NNReal => min v T)
      (Set.Iic t) (Set.Iic (min t T)) := by
    intro v hv
    exact min_le_min_right T hv
  have hphiNhds : Tendsto phi (𝓝[Set.Iic t] t) (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    exact hphiValue
  have hphi : Tendsto phi (𝓝[Set.Iic t] t)
      (𝓝[Set.Iic u] u) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hphiNhds,
      (by
        filter_upwards [self_mem_nhdsWithin] with v hv
        exact hphiMaps hv)⟩
  have hpath := stoppedPredictablePath_continuousWithinAt_Iic
    a T r S F mu omega u
  exact hpath.tendsto.comp hphi

theorem isStronglyPredictable_stoppedPredictableProcess
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    IsStronglyPredictable F (stoppedPredictableProcess a T r S F mu) :=
  LeftContinuousPredictable.stronglyPredictable_of_leftContinuous
    (stronglyAdapted_stoppedPredictableProcess source ha T r)
    (continuousWithinAt_stoppedPredictableProcess_Iic a T r S F mu)

private theorem eVariationOn_stoppedPredictablePath_le
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (omega : Omega) :
    eVariationOn
        (fun t => stoppedPredictablePath a T r S F mu t omega) Set.univ ≤
      ENNReal.ofReal
        ((grid T r).doobVariationStoppedAccumulation S F mu a (size T r) omega) := by
  let A : Nat → Real := fun n =>
    (grid T r).doobVariationStoppedPredictablePart S F mu a n omega
  let phi : Set.Iic T → Nat := fun t => (approxIndex T t.1 t.2 r).1
  have hPhi : Monotone phi := monotone_approxIndex_val T r
  have hMaps : MapsTo phi Set.univ (Set.Iic (size T r)) := by
    intro t _ht
    exact approxIndex_val_le_size T r t
  calc
    eVariationOn
        (fun t => stoppedPredictablePath a T r S F mu t omega) Set.univ =
        eVariationOn (A ∘ phi) Set.univ := by rfl
    _ ≤ eVariationOn A (Set.Iic (size T r)) :=
      eVariationOn.comp_le_of_monotoneOn A phi
        (hPhi.monotoneOn Set.univ) hMaps
    _ = ∑ k ∈ Finset.range (size T r), edist (A k) (A (k + 1)) := by
      simpa using eVariationOn.image_range_of_monotone A monotone_id (size T r)
    _ = ENNReal.ofReal
        (∑ k ∈ Finset.range (size T r),
          |A (k + 1) - A k|) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [edist_dist, Real.dist_eq, abs_sub_comm]
    _ = ENNReal.ofReal
        ((grid T r).doobVariationStoppedAccumulation S F mu a (size T r) omega) := by
      rw [(grid T r).sum_abs_doobVariationStoppedPredictablePart_increment
        S F mu a (size T r) omega]

theorem boundedVariationOn_stoppedPredictableProcess
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (omega : Omega) :
    BoundedVariationOn
      (stoppedPredictableProcess a T r S F mu · omega) Set.univ := by
  change eVariationOn
      (fun t => stoppedPredictableProcess a T r S F mu t omega) Set.univ ≠ ∞
  have hPath := eVariationOn_stoppedPredictablePath_le
    a T r S F mu omega
  let phi : NNReal → Set.Iic T := fun t =>
    ⟨min t T, min_le_right t T⟩
  have hPhi : Monotone phi := by
    intro s t hst
    change min s T ≤ min t T
    exact min_le_min_right T hst
  refine ne_top_of_le_ne_top
    (b := ENNReal.ofReal
      ((grid T r).doobVariationStoppedAccumulation S F mu a (size T r) omega))
    ENNReal.ofReal_ne_top ?_
  calc
    eVariationOn
        (fun t => stoppedPredictableProcess a T r S F mu t omega) Set.univ ≤
      eVariationOn
        (fun u : Set.Iic T => stoppedPredictablePath a T r S F mu u omega)
          Set.univ := by
      change eVariationOn
          ((fun u : Set.Iic T => stoppedPredictablePath a T r S F mu u omega) ∘ phi)
          Set.univ ≤ _
      exact eVariationOn.comp_le_of_monotoneOn
        (t := (Set.univ : Set NNReal))
        (fun u : Set.Iic T => stoppedPredictablePath a T r S F mu u omega)
        phi
        (hPhi.monotoneOn Set.univ)
        (mapsTo_univ _ _)
    _ ≤ ENNReal.ofReal
        ((grid T r).doobVariationStoppedAccumulation S F mu a (size T r) omega) := hPath

theorem ae_eVariationOn_stoppedPredictableProcess_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    ∀ᵐ omega ∂mu,
      eVariationOn
          (stoppedPredictableProcess a T r S F mu · omega) Set.univ ≤
        ENNReal.ofReal (a + 2 * max source.bound 0) := by
  filter_upwards [ae_eVariationOn_stoppedPredictablePath_le source ha T r]
    with omega hPath
  let phi : NNReal → Set.Iic T := fun t =>
    ⟨min t T, min_le_right t T⟩
  have hPhi : Monotone phi := by
    intro s t hst
    change min s T ≤ min t T
    exact min_le_min_right T hst
  change eVariationOn
      ((fun u : Set.Iic T => stoppedPredictablePath a T r S F mu u omega) ∘ phi)
      Set.univ ≤ _
  exact (eVariationOn.comp_le_of_monotoneOn
      (t := (Set.univ : Set NNReal))
      (fun u : Set.Iic T => stoppedPredictablePath a T r S F mu u omega)
      phi
      (hPhi.monotoneOn (Set.univ : Set NNReal))
      (mapsTo_univ _ _)).trans hPath

end HorizonFactorialGrid

end FTAPTheorem42
