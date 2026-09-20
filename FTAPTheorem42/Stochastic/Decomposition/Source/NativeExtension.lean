/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.CommonGate
import FTAPTheorem42.Stochastic.Integral.Elementary.FiniteGridAdaptedElementaryStrategy
import FTAPTheorem42.Stochastic.Decomposition.Source.CommonRefinement

/-!
# Native factorial-grid gain and martingale representatives

This module fixes the native (rather than transported) factorial grid at a
single variation level.  The variation gate is first turned into the actual
finite predictable elementary strategy whose running gain is the source-side
gain.  Separately, the terminal stopped discrete martingale coordinate is
regularized as a càdlàg martingale in the ambient filtration.  Their
difference is the canonical residual representative.

Only identities which are already available at the native terminal grid time
are used to construct the rows.  In particular, this module does not transport
a coarse Doob component to a finer filtration and does not claim
predictability or finite variation for the residual between native grid
points.  The fixed-time cell estimate is synchronized on the canonical
right-dense skeleton and then extended by right continuity to one common
full-measure set.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## A conditional-expectation cell estimate -/

theorem residual_cell_bound_of_condExp
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {Y m A : Process Omega} {t q : NNReal} {C : Real}
    (hM : Martingale m F mu)
    (hYtMeas : StronglyMeasurable[F t] (Y t))
    (hYtInt : Integrable (Y t) mu)
    (hYqInt : Integrable (Y q) mu)
    (hmqInt : Integrable (m q) mu)
    (hAInt : Integrable (A q) mu)
    (hA_meas : StronglyMeasurable[F t] (A q))
    (hEq : Y q =ᵐ[mu] m q + A q)
    (htq : t ≤ q)
    (hDiff : ∀ᵐ omega ∂mu, ‖(Y t - Y q) omega‖ ≤ C) :
    ∀ᵐ omega ∂mu,
      |(Y t omega - m t omega) - (Y q omega - m q omega)| ≤ C := by
  have hMRel : mu[m q | F t] =ᵐ[mu] m t :=
    hM.condExp_ae_eq htq
  have hACond : mu[A q | F t] =ᵐ[mu] A q :=
    Filter.Eventually.of_forall
      (fun omega => congrFun
        (condExp_of_stronglyMeasurable (F.le t) hA_meas hAInt) omega)
  have hCEY : mu[Y q | F t] =ᵐ[mu] m t + A q := by
    exact (condExp_congr_ae hEq).trans <|
      (condExp_add hmqInt hAInt (F t)).trans <|
        hMRel.add hACond
  have hYtCond : mu[Y t | F t] =ᵐ[mu] Y t :=
    Filter.Eventually.of_forall
      (fun omega => congrFun
        (condExp_of_stronglyMeasurable (F.le t) hYtMeas hYtInt) omega)
  have hCEdiff : mu[Y t - Y q | F t] =ᵐ[mu]
      Y t - mu[Y q | F t] := by
    exact (condExp_sub hYtInt hYqInt (F t)).trans <|
      hYtCond.sub EventuallyEq.rfl
  have hBound := ae_bdd_norm_condExp_of_ae_bdd_norm
    (m := F t) (f := Y t - Y q) hDiff
  filter_upwards [hEq, hCEY, hCEdiff, hBound] with omega hEqOmega
      hCEYOmega hCEdiffOmega hBoundOmega
  have hResidual :
      (Y t omega - m t omega) - (Y q omega - m q omega) =
        mu[Y t - Y q | F t] omega := by
    calc
      (Y t omega - m t omega) - (Y q omega - m q omega) =
          (Y t - mu[Y q | F t]) omega := by
        rw [Pi.sub_apply, hCEYOmega, hEqOmega]
        simp only [Pi.add_apply]
        ring
      _ = mu[Y t - Y q | F t] omega := hCEdiffOmega.symm
  rw [hResidual]
  simpa only [Real.norm_eq_abs] using hBoundOmega

/-! ## The native gate strategy -/

noncomputable def nativeGateStrategy
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) [IsProbabilityMeasure mu] :
    PredictableElementaryStrategy F :=
  (grid T r).adaptedElementaryStrategy F
    ((grid T r).doobVariationGate S F mu a)
    ((grid T r).stronglyAdapted_doobVariationGate S F mu a)

noncomputable def nativeGateGain
    (a : Real) (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) [IsProbabilityMeasure mu] : Process Omega :=
  ElementaryStrategy.gain S
    (nativeGateStrategy a T r S F mu).toElementary

theorem nativeGateGain_rightContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    (a : Real) (T : NNReal) (r : Nat) :
    ∀ omega t, ContinuousWithinAt
      (nativeGateGain a T r S F mu · omega) (Ici t) t := by
  intro omega t
  exact PredictableElementaryStrategy.rightContinuous_gain S
    source.rightContinuous (nativeGateStrategy a T r S F mu) omega t

theorem nativeGateGain_sum
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r : Nat) (t : NNReal) (omega : Omega) :
    nativeGateGain a T r S F mu t omega =
      ∑ j ∈ Finset.range (size T r),
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega) := by
  unfold nativeGateGain nativeGateStrategy
    ChronologicalGrid.adaptedElementaryStrategy
    ChronologicalGrid.adaptedElementaryBlock
    PredictableElementaryStrategy.toElementary ElementaryStrategy.gain
    ElementaryInterval.gain
  simp only [List.map_map]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, Function.comp_apply]

theorem nativeGateGain_ae_abs_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    (a : Real) (T : NNReal) (r : Nat) :
    ∀ᵐ omega ∂mu, ∀ t,
      |nativeGateGain a T r S F mu t omega| ≤
        (size T r : Real) * (2 * max source.bound 0) := by
  filter_upwards [source.uniformBound] with omega hS t
  rw [nativeGateGain_sum]
  calc
    |∑ j ∈ Finset.range (size T r),
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega)| ≤
      ∑ j ∈ Finset.range (size T r),
        |(grid T r).doobVariationGate S F mu a j omega *
          (S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (size T r),
        (2 * max source.bound 0) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      have hGate := (grid T r).abs_doobVariationGate_le_one
        S F mu a j omega
      have hDiff :
          |S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega| ≤
            2 * max source.bound 0 := by
        calc
          _ ≤ |S (min t ((grid T r).sampledTime (j + 1)) ) omega| +
              |S (min t ((grid T r).sampledTime j)) omega| := abs_sub _ _
          _ ≤ max source.bound 0 + max source.bound 0 := by
            apply add_le_add
            · exact (hS _).trans (le_max_left _ _)
            · exact (hS _).trans (le_max_left _ _)
          _ = 2 * max source.bound 0 := by ring
      calc
        |(grid T r).doobVariationGate S F mu a j omega| *
            |S (min t ((grid T r).sampledTime (j + 1))) omega -
              S (min t ((grid T r).sampledTime j)) omega| ≤
            1 * (2 * max source.bound 0) := by
          exact mul_le_mul hGate hDiff (abs_nonneg _) (by norm_num)
        _ = 2 * max source.bound 0 := by ring
    _ = (size T r : Real) * (2 * max source.bound 0) := by
      simp

theorem nativeGateGain_stronglyMeasurable_at
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    (a : Real) (T : NNReal) (r : Nat) (t : NNReal) :
    StronglyMeasurable[F t] (nativeGateGain a T r S F mu t) := by
  have hProgressive : IsStronglyProgressive F S :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      source.stronglyAdapted source.rightContinuous
  simpa [nativeGateGain] using
    (PredictableElementaryStrategy.stronglyAdapted_gain S hProgressive
      (nativeGateStrategy a T r S F mu) t)

theorem nativeGateGain_integrable_at
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    (a : Real) (T : NNReal) (r : Nat) (t : NNReal) :
    Integrable (nativeGateGain a T r S F mu t) mu := by
  apply Integrable.of_bound
    ((nativeGateGain_stronglyMeasurable_at source a T r t).mono
      (F.le t)).aestronglyMeasurable
    ((size T r : Real) * (2 * max source.bound 0))
  filter_upwards [nativeGateGain_ae_abs_le source a T r] with omega homega
  simpa only [Real.norm_eq_abs] using homega t

theorem stoppedPredictablePart_stronglyMeasurable_at_cell
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T t : NNReal) (r q : Nat)
    (_hq : 0 < q) (hprev : (grid T r).sampledTime (q - 1) ≤ t) :
    StronglyMeasurable[F t]
      ((grid T r).doobVariationStoppedPredictablePart S F mu a q) := by
  have hA : StronglyMeasurable[(grid T r).sampledFiltration F (q - 1)]
      ((grid T r).doobVariationStoppedPredictablePart S F mu a q) := by
    unfold ChronologicalGrid.doobVariationStoppedPredictablePart
      discretePredictableIntegral
    have hsum : StronglyMeasurable[(grid T r).sampledFiltration F (q - 1)]
        (fun omega => ∑ j ∈ Finset.range q,
          (grid T r).doobVariationGate S F mu a j omega *
            ((grid T r).doobPredictablePart S F mu (j + 1) omega -
              (grid T r).doobPredictablePart S F mu j omega)) := by
      refine Finset.stronglyMeasurable_fun_sum (M := Real)
        (s := Finset.range q) ?_
      intro j hj
      rw [Finset.mem_range] at hj
      have hjq : j ≤ q - 1 := Nat.le_sub_one_of_lt hj
      have hGate := (grid T r).stronglyAdapted_doobVariationGate
        S F mu a j
      have hNext := stronglyAdapted_predictablePart
        (f := (grid T r).natSample S)
        (ℱ := (grid T r).sampledFiltration F) (μ := mu) j
      have hNow := stronglyAdapted_predictablePart'
        (f := (grid T r).natSample S)
        (ℱ := (grid T r).sampledFiltration F) (μ := mu) j
      exact ((hGate.mono
        (Filtration.mono ((grid T r).sampledFiltration F) hjq)).mul
        ((hNext.mono
          (Filtration.mono ((grid T r).sampledFiltration F) hjq)).sub
          (hNow.mono
            (Filtration.mono ((grid T r).sampledFiltration F) hjq))))
    exact hsum
  exact hA.mono (Filtration.mono F hprev)

theorem nativeGateGain_cell_eq
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r q : Nat) (t : NNReal) (omega : Omega)
    (hq : 0 < q) (hqN : q ≤ size T r)
    (hleft : (grid T r).sampledTime (q - 1) ≤ t)
    (hright : t ≤ (grid T r).sampledTime q) :
    nativeGateGain a T r S F mu t omega =
      (grid T r).doobVariationStoppedSourcePart S F mu a (q - 1) omega +
        (grid T r).doobVariationGate S F mu a (q - 1) omega *
          (S t omega - (S ((grid T r).sampledTime (q - 1)) omega)) := by
  have hY := nativeGateGain_sum (S := S) (F := F) (mu := mu)
    a T r t omega
  rw [hY]
  unfold ChronologicalGrid.doobVariationStoppedSourcePart
    discretePredictableIntegral
  have htail :
      (∑ j ∈ Finset.range (size T r),
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega)) =
      ∑ j ∈ Finset.range q,
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hqN)
    intro j _hjN hjq
    have hqj : q ≤ j := Nat.le_of_not_gt (fun h => hjq (Finset.mem_range.mpr h))
    have hqj1 : t ≤ (grid T r).sampledTime (j + 1) :=
      hright.trans ((grid T r).sampledTime_mono
        (hqj.trans (Nat.le_succ j)))
    have hqj0 : t ≤ (grid T r).sampledTime j :=
      hright.trans ((grid T r).sampledTime_mono hqj)
    rw [min_eq_left hqj1, min_eq_left hqj0, sub_self, mul_zero]
  rw [htail]
  have hqeq : q = (q - 1) + 1 := (Nat.sub_add_cancel hq).symm
  have hsumq :
      (∑ j ∈ Finset.range q,
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega)) =
      (∑ j ∈ Finset.range (q - 1),
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega)) +
        (grid T r).doobVariationGate S F mu a (q - 1) omega *
          (S (min t ((grid T r).sampledTime ((q - 1) + 1))) omega -
            S (min t ((grid T r).sampledTime (q - 1))) omega) := by
    conv_lhs => rw [hqeq]
    rw [Finset.sum_range_succ]
  have hprefix :
      (∑ j ∈ Finset.range (q - 1),
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega)) =
      ∑ j ∈ Finset.range (q - 1),
        (grid T r).doobVariationGate S F mu a j omega *
          ((grid T r).natSample S (j + 1) omega -
            (grid T r).natSample S j omega) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < q - 1 := Finset.mem_range.mp hj
    have hj1q : j + 1 ≤ q - 1 := Nat.succ_le_iff.mpr hjlt
    have hjq : j ≤ q - 1 := (Nat.le_succ j).trans hj1q
    have hj1left : (grid T r).sampledTime (j + 1) ≤ t :=
      ((grid T r).sampledTime_mono hj1q).trans hleft
    have hjleft : (grid T r).sampledTime j ≤ t :=
      ((grid T r).sampledTime_mono hjq).trans hleft
    rw [min_eq_right hj1left, min_eq_right hjleft]
    rfl
  rw [hsumq, hprefix]
  have hqleft : (grid T r).sampledTime (q - 1) ≤ t := hleft
  have hqright : t ≤ (grid T r).sampledTime ((q - 1) + 1) := by
    rw [← hqeq]
    exact hright
  rw [min_eq_left hqright, min_eq_right hqleft]

theorem nativeGateGain_at_native_grid
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r k : Nat) (hk : k ≤ size T r)
    (omega : Omega) :
    nativeGateGain a T r S F mu ((grid T r).sampledTime k) omega =
      (grid T r).doobVariationStoppedSourcePart S F mu a k omega := by
  classical
  unfold nativeGateGain nativeGateStrategy
    ChronologicalGrid.adaptedElementaryStrategy
    ChronologicalGrid.adaptedElementaryBlock
    PredictableElementaryStrategy.toElementary ElementaryStrategy.gain
    ElementaryInterval.gain
    ChronologicalGrid.doobVariationStoppedSourcePart
    discretePredictableIntegral
  simp only [List.map_map]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  simp only [Function.comp_apply]
  simp only [ChronologicalGrid.natSample]
  have hsum :
      (∑ j ∈ Finset.range (size T r),
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min ((grid T r).sampledTime k)
            ((grid T r).sampledTime (j + 1))) omega -
            S (min ((grid T r).sampledTime k)
              ((grid T r).sampledTime j)) omega)) =
      ∑ j ∈ Finset.range k,
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min ((grid T r).sampledTime k)
            ((grid T r).sampledTime (j + 1))) omega -
            S (min ((grid T r).sampledTime k)
              ((grid T r).sampledTime j)) omega) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hk)
    intro j _hjN hjk
    have hkj : k ≤ j := Nat.le_of_not_gt (fun h => hjk (Finset.mem_range.mpr h))
    have hkj1 : (grid T r).sampledTime k ≤
        (grid T r).sampledTime (j + 1) :=
      (grid T r).sampledTime_mono (hkj.trans (Nat.le_succ j))
    have hkj0 : (grid T r).sampledTime k ≤
        (grid T r).sampledTime j :=
      (grid T r).sampledTime_mono hkj
    rw [min_eq_left hkj1, min_eq_left hkj0, sub_self, mul_zero]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < k := Finset.mem_range.mp hj
  have hj1k : j + 1 ≤ k := Nat.succ_le_iff.mpr hjlt
  rw [min_eq_right ((grid T r).sampledTime_mono hj1k),
    min_eq_right ((grid T r).sampledTime_mono hjlt.le)]

/-! The right approximation of a grid point never lies to its right.  The
terminal grid point is allowed to have several indices; this inequality is
the form needed to discard the zero increments in that terminal tail. -/

theorem approxIndex_val_at_sampledTime_le
    (T : NNReal) (r k : Nat) (hk : k ≤ size T r) :
    (approxIndex T ((grid T r).sampledTime k)
      ((grid T r).sampledTime_mono hk |>.trans_eq (sampledTime_size T r)) r).1 ≤ k := by
  change Nat.ceil ((grid T r).sampledTime k * (r.factorial : NNReal)) ≤ k
  rw [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex, grid_time]
  simp only [min_eq_left hk]
  by_cases hkt : (k : NNReal) / (r.factorial : NNReal) ≤ T
  · rw [min_eq_left hkt]
    have hfac : (r.factorial : NNReal) ≠ 0 := by positivity
    have hmul : (k : NNReal) / (r.factorial : NNReal) *
        (r.factorial : NNReal) = k := by
      exact div_mul_cancel₀ (k : NNReal) hfac
    rw [hmul, Nat.ceil_natCast]
  · have hT : T ≤ (k : NNReal) / (r.factorial : NNReal) := le_of_not_ge hkt
    rw [min_eq_right hT]
    apply Nat.ceil_le.mpr
    have hmul := (le_div_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
      positivity)).mp hT
    exact_mod_cast hmul

/-- The shared factorial-grid index specialized to the terminal horizon. -/
noncomputable def nativeTerminalIndex (T : NNReal) (r : Nat) : Nat :=
  FactorialChronologicalGrid.approxNatIndex r T

theorem nativeTerminalIndex_le_size (T : NNReal) (r : Nat) :
    nativeTerminalIndex T r ≤ size T r := by
  apply Nat.ceil_le.mpr
  unfold size
  have h := mul_le_mul_of_nonneg_right (Nat.le_ceil T)
    (show (0 : NNReal) ≤ (r.factorial : NNReal) by positivity)
  exact_mod_cast h

theorem sampledTime_eq_horizon_of_nativeTerminalIndex_le_any
    (T : NNReal) (r j : Nat)
    (hK : nativeTerminalIndex T r ≤ j) :
    (grid T r).sampledTime j = T := by
  change Nat.ceil (T * (r.factorial : NNReal)) ≤ j at hK
  have hK' : Nat.ceil (T * (r.factorial : NNReal)) ≤ min j (size T r) :=
    le_min hK (nativeTerminalIndex_le_size T r)
  change Nat.ceil (T * (r.factorial : NNReal)) ≤
    min j (size T r) at hK'
  unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
  simp only [grid_time]
  apply min_eq_right
  apply (le_div_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
    positivity)).2
  exact Nat.ceil_le.mp hK'

theorem approxIndex_val_at_sampledTime_eq_of_lt_horizon
    (T : NNReal) (r k : Nat) (hk : k ≤ size T r)
    (hlt : (grid T r).sampledTime k < T) :
    (approxIndex T ((grid T r).sampledTime k)
      ((grid T r).sampledTime_mono hk |>.trans_eq (sampledTime_size T r)) r).1 = k := by
  change Nat.ceil ((grid T r).sampledTime k * (r.factorial : NNReal)) = k
  unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
  simp only [min_eq_left hk, grid_time]
  unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex at hlt
  simp only [min_eq_left hk, grid_time] at hlt
  have hratio : (k : NNReal) / (r.factorial : NNReal) < T := by
    have hlt' : min ((k : NNReal) / (r.factorial : NNReal)) T < T := hlt
    exact (min_lt_iff.mp hlt').resolve_right (lt_irrefl T)
  rw [min_eq_left hratio.le]
  have hfac : (r.factorial : NNReal) ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hfac, Nat.ceil_natCast]

theorem approxIndex_val_at_sampledTime_eq_nativeTerminal_of_eq_horizon
    (T : NNReal) (r k : Nat) (hk : k ≤ size T r)
    (hT : (grid T r).sampledTime k = T) :
    (approxIndex T ((grid T r).sampledTime k)
      ((grid T r).sampledTime_mono hk |>.trans_eq (sampledTime_size T r)) r).1 =
      nativeTerminalIndex T r := by
  change Nat.ceil ((grid T r).sampledTime k * (r.factorial : NNReal)) = _
  rw [hT]
  rfl

omit [MeasurableSpace Omega] in
theorem natSample_eq_horizon_of_nativeTerminalIndex_le
    {S : Process Omega} (T : NNReal) (r j : Nat)
    (hK : nativeTerminalIndex T r ≤ j) :
    (grid T r).natSample S j = S T := by
  funext omega
  exact congrArg (fun t => S t omega)
    (sampledTime_eq_horizon_of_nativeTerminalIndex_le_any T r j hK)

theorem doobPredictablePart_succ_eq_of_nativeTerminalIndex_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (T : NNReal) (r j : Nat) (hK : nativeTerminalIndex T r ≤ j) :
    (grid T r).doobPredictablePart S F mu (j + 1) =ᵐ[mu]
      (grid T r).doobPredictablePart S F mu j := by
  have hNat := natSample_eq_horizon_of_nativeTerminalIndex_le
    (S := S) T r j hK
  have hNat' := natSample_eq_horizon_of_nativeTerminalIndex_le
    (S := S) T r (j + 1) (hK.trans (Nat.le_succ j))
  unfold ChronologicalGrid.doobPredictablePart
  have hzeroRaw :
      (grid T r).natSample S (j + 1) -
        (grid T r).natSample S j =ᵐ[mu] 0 := by
    filter_upwards [] with omega
    simp only [Pi.sub_apply]
    rw [congrFun hNat' omega, congrFun hNat omega]
    simp
  have hzero :
      mu[(grid T r).natSample S (j + 1) -
        (grid T r).natSample S j | (grid T r).sampledFiltration F j] =ᵐ[mu] 0 :=
    (condExp_congr_ae hzeroRaw).trans
      (Filter.Eventually.of_forall (fun omega => congrFun
        (condExp_zero (μ := mu) (m := (grid T r).sampledFiltration F j)) omega))
  rw [predictablePart_add_one]
  filter_upwards [hzero] with omega hzeroOmega
  simp only [Pi.add_apply]
  simpa using hzeroOmega

theorem doobMartingalePart_succ_eq_of_nativeTerminalIndex_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (T : NNReal) (r j : Nat) (hK : nativeTerminalIndex T r ≤ j) :
    (grid T r).doobMartingalePart S F mu (j + 1) =ᵐ[mu]
      (grid T r).doobMartingalePart S F mu j := by
  have hNat := natSample_eq_horizon_of_nativeTerminalIndex_le
    (S := S) T r j hK
  have hNat' := natSample_eq_horizon_of_nativeTerminalIndex_le
    (S := S) T r (j + 1) (hK.trans (Nat.le_succ j))
  have hPred := doobPredictablePart_succ_eq_of_nativeTerminalIndex_le
    (S := S) (F := F) (mu := mu) T r j hK
  unfold ChronologicalGrid.doobMartingalePart
  simp only [ChronologicalGrid.doobPredictablePart] at hPred
  filter_upwards [hPred] with omega hPredOmega
  simp only [martingalePart, Pi.sub_apply]
  rw [congrFun hNat' omega, congrFun hNat omega, hPredOmega]

theorem discretePredictableIntegral_eq_of_succ_eq_ae
    {mu : Measure Omega} {K M : Nat → Omega → Real} (K0 j : Nat)
    (hK : K0 ≤ j)
    (hStep : ∀ i, K0 ≤ i → i < j → M (i + 1) =ᵐ[mu] M i) :
    discretePredictableIntegral K M j =ᵐ[mu]
      discretePredictableIntegral K M K0 := by
  have hAll : ∀ᵐ omega ∂mu, ∀ i, K0 ≤ i → i < j →
      M (i + 1) omega = M i omega := by
    apply ae_all_iff.2
    intro i
    by_cases hi : K0 ≤ i
    · by_cases hij : i < j
      · filter_upwards [hStep i hi hij] with omega hEq
        intro _hK _hij
        exact hEq
      · exact Filter.Eventually.of_forall (fun omega _hK hJ => (hij hJ).elim)
    · exact Filter.Eventually.of_forall (fun omega hK _hJ => (hi hK).elim)
  filter_upwards [hAll] with omega hOmega
  unfold discretePredictableIntegral
  symm
  apply Finset.sum_subset (Finset.range_mono hK)
  intro i hiJ hiK
  have hi : K0 ≤ i := Nat.le_of_not_gt (fun h => hiK (Finset.mem_range.mpr h))
  rw [hOmega i hi (Finset.mem_range.mp hiJ), sub_self, mul_zero]

theorem doobVariationStoppedMartingalePart_eq_nativeTerminal_after
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r j : Nat)
    (hK : nativeTerminalIndex T r ≤ j) :
    (grid T r).doobVariationStoppedMartingalePart S F mu a j =ᵐ[mu]
      (grid T r).doobVariationStoppedMartingalePart S F mu a
        (nativeTerminalIndex T r) := by
  apply discretePredictableIntegral_eq_of_succ_eq_ae
    (mu := mu) (K := (grid T r).doobVariationGate S F mu a)
    (M := (grid T r).doobMartingalePart S F mu)
    (nativeTerminalIndex T r) j hK
  intro i hi _hij
  exact doobMartingalePart_succ_eq_of_nativeTerminalIndex_le
    (S := S) (F := F) (mu := mu) T r i hi

/-! ## The ambient càdlàg martingale representative -/

noncomputable def nativeMartingaleTerminal
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) : Lp Real 2 mu :=
  stoppedMartingaleApproximationToLp source ha T T le_rfl r

noncomputable def nativeMartingaleProcess
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) : Process Omega :=
  Classical.choose (exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual
    (nativeMartingaleTerminal source ha T r))

theorem nativeMartingaleProcess_spec
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    Martingale (nativeMartingaleProcess hUsual source ha T r) F mu ∧
      (∀ omega t, ContinuousWithinAt
        (nativeMartingaleProcess hUsual source ha T r · omega) (Ici t) t) ∧
      ProcessHasLeftLimits (nativeMartingaleProcess hUsual source ha T r) ∧
      (∀ t, nativeMartingaleProcess hUsual source ha T r t =ᵐ[mu]
        condExpMartingaleProcess mu F (nativeMartingaleTerminal source ha T r) t) := by
  exact Classical.choose_spec
    (exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual
      (nativeMartingaleTerminal source ha T r))

theorem nativeMartingaleProcess_at_native_grid_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r k : Nat)
    (_hk : k ≤ size T r) :
    nativeMartingaleProcess hUsual source ha T r
        ((grid T r).sampledTime k) =ᵐ[mu]
      stoppedMartingaleApproximation a T
        ((grid T r).sampledTime k)
        (by
          unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
          rw [grid_time]
          exact min_le_right _ _)
        r S F mu := by
  let t : NNReal := (grid T r).sampledTime k
  have ht : t ≤ T := by
    dsimp [t]
    unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
    rw [grid_time]
    exact min_le_right _ _
  have hmem : t ∈ Set.range (grid T r).time := by
    refine ⟨(grid T r).natIndex k, ?_⟩
    rfl
  have hRaw := condExp_stoppedMartingaleApproximation_ae_eq
    source a T t T ht le_rfl ht r
  change mu[
      stoppedMartingaleApproximation a T T le_rfl r S F mu |
        F ((grid T r).sampledTime (approxIndex T t ht r))] =ᵐ[mu]
      stoppedMartingaleApproximation a T t ht r S F mu at hRaw
  rw [(grid T r).sampledTime_fin_eq (approxIndex T t ht r)] at hRaw
  rw [grid_time_approxIndex_eq_of_mem_range T t ht r hmem] at hRaw
  have hVersion := (nativeMartingaleProcess_spec hUsual source ha T r).2.2.2 t
  have hCoe : (nativeMartingaleTerminal source ha T r : Omega → Real) =ᵐ[mu]
      stoppedMartingaleApproximation a T T le_rfl r S F mu := by
    exact MemLp.coeFn_toLp
      (memLp_two_stoppedMartingaleApproximation source ha T T le_rfl r)
  have hCondProcess :
      condExpMartingaleProcess mu F (nativeMartingaleTerminal source ha T r) t =ᵐ[mu]
        mu[stoppedMartingaleApproximation a T T le_rfl r S F mu | F t] := by
    simpa [condExpMartingaleProcess] using (condExp_congr_ae hCoe)
  filter_upwards [hVersion, hCondProcess, hRaw] with omega hVersionOmega
      hCondOmega hRawOmega
  change nativeMartingaleProcess hUsual source ha T r t omega = _
  rw [hVersionOmega, hCondOmega, hRawOmega] at ⊢

theorem nativeMartingaleProcess_at_native_grid_doobPart_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r k : Nat)
    (hk : k ≤ size T r) :
    nativeMartingaleProcess hUsual source ha T r
        ((grid T r).sampledTime k) =ᵐ[mu]
      (grid T r).doobVariationStoppedMartingalePart S F mu a k := by
  let t : NNReal := (grid T r).sampledTime k
  have ht : t ≤ T := by
    dsimp [t]
    exact (grid T r).sampledTime_mono hk |>.trans_eq (sampledTime_size T r)
  let q : Nat := (approxIndex T t ht r).1
  have hqk : q ≤ k := by
    exact approxIndex_val_at_sampledTime_le T r k hk
  have hApprox := nativeMartingaleProcess_at_native_grid_ae
    hUsual source ha T r k hk
  have hApprox' :
      nativeMartingaleProcess hUsual source ha T r t =ᵐ[mu]
        (grid T r).doobVariationStoppedMartingalePart S F mu a q := by
    simpa [t, q, stoppedMartingaleApproximation] using hApprox
  by_cases hlt : t < T
  · have hqeq : q = k := by
      exact approxIndex_val_at_sampledTime_eq_of_lt_horizon T r k hk hlt
    simpa [t, hqeq] using hApprox'
  · have htT : t = T := le_antisymm ht (le_of_not_gt hlt)
    have hqeq : q = nativeTerminalIndex T r := by
      exact approxIndex_val_at_sampledTime_eq_nativeTerminal_of_eq_horizon
        T r k hk htT
    have hkK : nativeTerminalIndex T r ≤ k := by
      rw [← hqeq]
      exact hqk
    have hConst := doobVariationStoppedMartingalePart_eq_nativeTerminal_after
      (S := S) (F := F) (mu := mu) a T r k hkK
    filter_upwards [hApprox', hConst] with omega hApproxOmega hConstOmega
    rw [hqeq] at hApproxOmega
    exact hApproxOmega.trans hConstOmega.symm

/-! ## The residual and the exact native-time identity -/

noncomputable def nativeResidual
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) : Process Omega :=
  nativeGateGain a T r S F mu - nativeMartingaleProcess hUsual source ha T r

theorem nativeGateGain_eq_martingale_add_residual
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    nativeGateGain a T r S F mu =
      nativeMartingaleProcess hUsual source ha T r +
        nativeResidual hUsual source ha T r := by
  funext t omega
  simp [nativeResidual]

/-! ## The native cell estimate

The predictable endpoint at the right hand side of a native cell is already
measurable at the left endpoint of that cell.  The conditional-expectation
estimate above can therefore be applied with the discrete Doob identity at
that endpoint. -/

theorem nativeResidual_cell_bound_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r q : Nat) (t : NNReal)
    (hq : 0 < q) (hqN : q ≤ size T r)
    (hleft : (grid T r).sampledTime (q - 1) ≤ t)
    (hright : t ≤ (grid T r).sampledTime q) :
    ∀ᵐ omega ∂mu,
      |nativeResidual hUsual source ha T r t omega -
          nativeResidual hUsual source ha T r ((grid T r).sampledTime q) omega| ≤
        2 * max source.bound 0 := by
  let A : Process Omega := fun _omega =>
    (grid T r).doobVariationStoppedPredictablePart S F mu a q
  have hM := nativeMartingaleProcess_spec hUsual source ha T r
  have hYtMeas := nativeGateGain_stronglyMeasurable_at source a T r t
  have hYtInt := nativeGateGain_integrable_at source a T r t
  have hYqInt := nativeGateGain_integrable_at source a T r
    ((grid T r).sampledTime q)
  have hmQInt : Integrable
      (nativeMartingaleProcess hUsual source ha T r
        ((grid T r).sampledTime q)) mu :=
    (hM.1.integrable ((grid T r).sampledTime q))
  have hAInt : Integrable (A ((grid T r).sampledTime q)) mu := by
    change Integrable
      ((grid T r).doobVariationStoppedPredictablePart S F mu a q) mu
    exact (grid T r).memLp_two_doobVariationStoppedPredictablePart source ha q
      |>.integrable (by norm_num)
  have hAMeas : StronglyMeasurable[F t]
      (A ((grid T r).sampledTime q)) := by
    change StronglyMeasurable[F t]
      ((grid T r).doobVariationStoppedPredictablePart S F mu a q)
    exact stoppedPredictablePart_stronglyMeasurable_at_cell (S := S) (mu := mu)
      a T t r q hq hleft
  have hEq :
      nativeGateGain a T r S F mu ((grid T r).sampledTime q) =ᵐ[mu]
        nativeMartingaleProcess hUsual source ha T r
            ((grid T r).sampledTime q) +
          A ((grid T r).sampledTime q) := by
    have hY := nativeGateGain_at_native_grid
      (S := S) (F := F) (mu := mu) a T r q hqN
    have hm := nativeMartingaleProcess_at_native_grid_doobPart_ae
      hUsual source ha T r q hqN
    have hDec := (grid T r).doobVariationStoppedSourcePart_eq_add
      S F mu a q
    filter_upwards [hm] with omega hmOmega
    have hYOmega := hY omega
    have hDecOmega := congrFun hDec omega
    change nativeGateGain a T r S F mu ((grid T r).sampledTime q) omega =
      nativeMartingaleProcess hUsual source ha T r
          ((grid T r).sampledTime q) omega +
        (grid T r).doobVariationStoppedPredictablePart S F mu a q omega
    rw [hYOmega, hmOmega]
    exact hDecOmega
  have hDiff : ∀ᵐ omega ∂mu,
      ‖(nativeGateGain a T r S F mu t -
          nativeGateGain a T r S F mu ((grid T r).sampledTime q)) omega‖ ≤
        2 * max source.bound 0 := by
    filter_upwards [source.uniformBound] with omega hS
    have hCellT := nativeGateGain_cell_eq
      (S := S) (F := F) (mu := mu) a T r q t omega hq hqN hleft hright
    have hCellQ := nativeGateGain_cell_eq
      (S := S) (F := F) (mu := mu) a T r q
        ((grid T r).sampledTime q) omega hq hqN
        ((grid T r).sampledTime_mono (Nat.sub_le q 1)) le_rfl
    have hDiffEq :
        nativeGateGain a T r S F mu t omega -
            nativeGateGain a T r S F mu ((grid T r).sampledTime q) omega =
          (grid T r).doobVariationGate S F mu a (q - 1) omega *
            (S t omega - S ((grid T r).sampledTime q) omega) := by
      rw [hCellT, hCellQ]
      ring
    change |nativeGateGain a T r S F mu t omega -
      nativeGateGain a T r S F mu ((grid T r).sampledTime q) omega| ≤
      2 * max source.bound 0
    rw [hDiffEq, abs_mul]
    have hGate := (grid T r).abs_doobVariationGate_le_one
      S F mu a (q - 1) omega
    have hSdiff : |S t omega - S ((grid T r).sampledTime q) omega| ≤
        2 * max source.bound 0 := by
      calc
        |S t omega - S ((grid T r).sampledTime q) omega| ≤
            |S t omega| + |S ((grid T r).sampledTime q) omega| :=
          abs_sub _ _
        _ ≤ max source.bound 0 + max source.bound 0 := by
          exact add_le_add (hS t |>.trans (le_max_left _ _))
            (hS ((grid T r).sampledTime q) |>.trans (le_max_left _ _))
        _ = 2 * max source.bound 0 := by ring
    calc
      |(grid T r).doobVariationGate S F mu a (q - 1) omega| *
          |S t omega - S ((grid T r).sampledTime q) omega| ≤
          1 * (2 * max source.bound 0) := by
        exact mul_le_mul hGate hSdiff (abs_nonneg _) (by norm_num)
      _ = 2 * max source.bound 0 := by ring
  have hCell := residual_cell_bound_of_condExp
    (F := F) (mu := mu)
    (Y := nativeGateGain a T r S F mu)
    (m := nativeMartingaleProcess hUsual source ha T r)
    (A := A) (t := t) (q := (grid T r).sampledTime q)
    (C := 2 * max source.bound 0)
    hM.1 hYtMeas hYtInt hYqInt hmQInt hAInt hAMeas hEq hright hDiff
  simpa [nativeResidual, A] using hCell

theorem nativeResidual_rightContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    ∀ omega t, ContinuousWithinAt
      (nativeResidual hUsual source ha T r · omega) (Ici t) t := by
  intro omega t
  have hMcont := (nativeMartingaleProcess_spec hUsual source ha T r).2.1 omega t
  change ContinuousWithinAt
    ((fun x => nativeGateGain a T r S F mu x omega) -
      (fun x => nativeMartingaleProcess hUsual source ha T r x omega))
    (Ici t) t
  exact (nativeGateGain_rightContinuous source a T r omega t).sub hMcont

/-! The fixed-time cell estimate can be synchronized on the countable
right-dense skeleton.  Right continuity then gives the same estimate at every
time, with the right endpoint selected by the native approximation index. -/

theorem nativeResidual_cell_bound_ae_all
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    ∀ᵐ omega ∂mu, ∀ (t : NNReal) (ht : t ≤ T),
      |nativeResidual hUsual source ha T r t omega -
          nativeResidual hUsual source ha T r
            ((grid T r).sampledTime
              (approxIndex T t ht r).1) omega| ≤
        2 * max source.bound 0 := by
  let C : Real := 2 * max source.bound 0
  have hSkeleton : ∀ᵐ omega ∂mu, ∀ q i, 0 < q → q ≤ size T r →
      (grid T r).sampledTime (q - 1) ≤
          (stoppedLimitSkeleton T i).1 →
      (stoppedLimitSkeleton T i).1 ≤ (grid T r).sampledTime q →
      |nativeResidual hUsual source ha T r
          (stoppedLimitSkeleton T i).1 omega -
        nativeResidual hUsual source ha T r
          ((grid T r).sampledTime q) omega| ≤ C := by
    apply ae_all_iff.2
    intro q
    apply ae_all_iff.2
    intro i
    by_cases hq : 0 < q
    · by_cases hqN : q ≤ size T r
      · by_cases hleft : (grid T r).sampledTime (q - 1) ≤
            (stoppedLimitSkeleton T i).1
        · by_cases hright : (stoppedLimitSkeleton T i).1 ≤
              (grid T r).sampledTime q
          · filter_upwards [nativeResidual_cell_bound_ae
                hUsual source ha T r q (stoppedLimitSkeleton T i).1
                hq hqN hleft hright] with omega hOmega
            exact fun _ _ _ _ => by simpa [C] using hOmega
          · exact Filter.Eventually.of_forall (fun _omega _ _ _ h =>
              (hright h).elim)
        · exact Filter.Eventually.of_forall (fun _omega _ _ h _ =>
            (hleft h).elim)
      · exact Filter.Eventually.of_forall (fun _omega _ h _ _ =>
          (hqN h).elim)
    · exact Filter.Eventually.of_forall (fun _omega h _ _ _ =>
        (hq h).elim)
  filter_upwards [hSkeleton] with omega hSkeletonOmega
  intro t ht
  have hCellQ : ∀ q, 0 < q → q ≤ size T r →
      (grid T r).sampledTime (q - 1) < t →
      t < (grid T r).sampledTime q →
      |nativeResidual hUsual source ha T r t omega -
          nativeResidual hUsual source ha T r
            ((grid T r).sampledTime q) omega| ≤ C := by
    intro q hq hqN hleft hright
    by_contra hnot
    have hgt : C < |nativeResidual hUsual source ha T r t omega -
        nativeResidual hUsual source ha T r
          ((grid T r).sampledTime q) omega| := lt_of_not_ge hnot
    have hrightT : (grid T r).sampledTime q ≤ T :=
      (grid T r).sampledTime_mono hqN |>.trans_eq (sampledTime_size T r)
    have htT : t < T := hright.trans_le hrightT
    let tSub : Set.Iic T := ⟨t, htT.le⟩
    let right : NNReal := (grid T r).sampledTime q
    let rightSub : Set.Iic T := ⟨right, hrightT⟩
    have htrightSub : tSub < rightSub := by
      exact hright
    have hBase : ContinuousWithinAt
        (fun u : Set.Iic T =>
          nativeResidual hUsual source ha T r u.1 omega)
        (Set.Ici tSub) tSub := by
      have hCont := nativeResidual_rightContinuous
        hUsual source ha T r omega t
      have hVal : ContinuousWithinAt
          ((↑) : Set.Iic T → NNReal) (Set.Ici tSub) tSub :=
        continuousAt_subtype_val.continuousWithinAt.mono
          (Set.subset_univ _)
      have hMaps : MapsTo ((↑) : Set.Iic T → NNReal)
          (Set.Ici tSub) (Set.Ici t) := by
        intro v hv
        exact hv
      change ContinuousWithinAt
        ((fun x => nativeResidual hUsual source ha T r x omega) ∘
          Subtype.val) (Set.Ici tSub) tSub
      exact hCont.comp hVal hMaps
    have hContDiff : ContinuousWithinAt
        (fun u : Set.Iic T =>
          nativeResidual hUsual source ha T r u.1 omega -
            nativeResidual hUsual source ha T r right omega)
        (Set.Ici tSub) tSub :=
      hBase.sub continuousWithinAt_const
    have hNorm : ContinuousWithinAt
        (fun u : Set.Iic T =>
          ‖nativeResidual hUsual source ha T r u.1 omega -
            nativeResidual hUsual source ha T r right omega‖)
        (Set.Ici tSub) tSub := hContDiff.norm
    have hEvNorm : ∀ᶠ u in 𝓝[Set.Ici tSub] tSub,
        C < ‖nativeResidual hUsual source ha T r u.1 omega -
          nativeResidual hUsual source ha T r right omega‖ := by
      apply hNorm.eventually
      have hgt' : C < ‖nativeResidual hUsual source ha T r t omega -
          nativeResidual hUsual source ha T r right omega‖ := by
        simpa [right, Real.norm_eq_abs] using hgt
      exact Ioi_mem_nhds hgt'
    have hEvRight : ∀ᶠ u in 𝓝[Set.Ici tSub] tSub,
        u.1 ≤ right := by
      have hIic : Set.Iic rightSub ∈ 𝓝 tSub :=
        Iic_mem_nhds htrightSub
      filter_upwards [mem_nhdsWithin_of_mem_nhds hIic] with u hu
      exact hu
    have hEv : ∀ᶠ u in
        𝓝[Set.range (stoppedLimitSkeleton T) ∩ Set.Ici tSub] tSub,
        C < ‖nativeResidual hUsual source ha T r u.1 omega -
          nativeResidual hUsual source ha T r right omega‖ ∧
          u.1 ≤ right :=
      Filter.Eventually.filter_mono
        (nhdsWithin_mono tSub Set.inter_subset_right)
        (hEvNorm.and hEvRight)
    have hDense := stoppedLimitSkeleton_rightDense T tSub
    have hNe : NeBot
        (𝓝[Set.range (stoppedLimitSkeleton T) ∩ Set.Ici tSub] tSub) :=
      mem_closure_iff_nhdsWithin_neBot.1 hDense
    obtain ⟨u, hu, huMem⟩ := (hEv.and self_mem_nhdsWithin).exists
    rcases huMem.1 with ⟨i, rfl⟩
    have hleftI : (grid T r).sampledTime (q - 1) ≤
        (stoppedLimitSkeleton T i).1 := by
      exact hleft.le.trans huMem.2
    have hrightI : (stoppedLimitSkeleton T i).1 ≤
        (grid T r).sampledTime q := hu.2
    have hGrid := hSkeletonOmega q i hq hqN hleftI hrightI
    apply (not_lt_of_ge hGrid)
    simpa [right, Real.norm_eq_abs] using hu.1
  let q : Nat := (approxIndex T t ht r).1
  change |nativeResidual hUsual source ha T r t omega -
      nativeResidual hUsual source ha T r
        ((grid T r).sampledTime q) omega| ≤ C
  have hqN : q ≤ size T r :=
    Nat.lt_succ_iff.mp (approxIndex T t ht r).isLt
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
  by_cases hq0 : q = 0
  · have hceil : Nat.ceil (t * (r.factorial : NNReal)) = 0 := by
      simpa [q, approxIndex] using hq0
    have hmul : t * (r.factorial : NNReal) = 0 :=
      le_antisymm (Nat.ceil_eq_zero.mp hceil) (by positivity)
    have ht0 : t = 0 :=
      (mul_eq_zero.mp hmul).resolve_right (by positivity)
    have hqTime0 : (grid T r).sampledTime q = 0 := by
      rw [hq0]
      simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
        grid_time]
    have htime0 : t = (grid T r).sampledTime q := ht0.trans hqTime0.symm
    simp [htime0, C]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    by_cases heq : t = (grid T r).sampledTime q
    · simp [heq, C]
    · have hrightlt : t < (grid T r).sampledTime q :=
        lt_of_le_of_ne hright heq
      have hrightT : (grid T r).sampledTime q ≤ T :=
        (grid T r).sampledTime_mono hqN |>.trans_eq (sampledTime_size T r)
      have htt : t < T := hrightlt.trans_le hrightT
      have hleft : (grid T r).sampledTime (q - 1) < t := by
        apply approxIndex_previous_time_lt T t ht r
        simpa [q] using (Nat.sub_add_cancel hqpos).symm
      simpa [q, C] using hCellQ q hqpos hqN hleft hrightlt

theorem nativeResidual_at_native_grid_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r k : Nat)
    (hk : k ≤ size T r) :
    nativeResidual hUsual source ha T r ((grid T r).sampledTime k) =ᵐ[mu]
      (grid T r).doobVariationStoppedPredictablePart S F mu a k := by
  have hY := nativeGateGain_at_native_grid
    (S := S) (F := F) (mu := mu) a T r k hk
  have hm := nativeMartingaleProcess_at_native_grid_doobPart_ae
    hUsual source ha T r k hk
  have hDec := (grid T r).doobVariationStoppedSourcePart_eq_add
    S F mu a k
  filter_upwards [hm] with omega hmOmega
  have hYOmega := hY omega
  have hDecOmega := congrFun hDec omega
  change nativeGateGain a T r S F mu ((grid T r).sampledTime k) omega -
      nativeMartingaleProcess hUsual source ha T r
        ((grid T r).sampledTime k) omega =
    (grid T r).doobVariationStoppedPredictablePart S F mu a k omega
  rw [hYOmega, hmOmega]
  simp only [Pi.add_apply] at hDecOmega
  linarith

theorem nativeResidual_native_grid_abs_le_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    ∀ᵐ omega ∂mu, ∀ k, k ≤ size T r →
      |nativeResidual hUsual source ha T r
          ((grid T r).sampledTime k) omega| ≤
        a + 2 * max source.bound 0 := by
  have hBound := (grid T r).ae_abs_doobVariationStoppedPredictablePart_le
    source ha
  apply ae_all_iff.2
  intro k
  by_cases hk : k ≤ size T r
  · have hGrid := nativeResidual_at_native_grid_ae
      hUsual source ha T r k hk
    filter_upwards [hBound, hGrid] with omega hBoundOmega hGridOmega
    intro _hk
    rw [hGridOmega]
    exact hBoundOmega k
  · exact Filter.Eventually.of_forall (fun _omega h => (hk h).elim)

theorem nativeResidual_ae_abs_le_on_horizon
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (r : Nat) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |nativeResidual hUsual source ha T r t omega| ≤
        a + 4 * max source.bound 0 := by
  have hGrid := nativeResidual_native_grid_abs_le_ae
    hUsual source ha T r
  have hCell := nativeResidual_cell_bound_ae_all hUsual source ha T r
  filter_upwards [hGrid, hCell] with omega hGridOmega hCellOmega
  have hSkeleton : ∀ i, ‖nativeResidual hUsual source ha T r
        ((stoppedLimitSkeleton T i).1) omega‖ ≤
      a + 4 * max source.bound 0 := by
    intro i
    let q : Nat := (approxIndex T (stoppedLimitSkeleton T i).1
      (stoppedLimitSkeleton T i).2 r).1
    have hqN : q ≤ size T r :=
      Nat.lt_succ_iff.mp (approxIndex T (stoppedLimitSkeleton T i).1
        (stoppedLimitSkeleton T i).2 r).isLt
    have hEndpoint := hGridOmega q hqN
    have hCellI : |nativeResidual hUsual source ha T r
          ((stoppedLimitSkeleton T i).1) omega -
          nativeResidual hUsual source ha T r
            ((grid T r).sampledTime q) omega| ≤
        2 * max source.bound 0 := by
      simpa [q] using hCellOmega
        ((stoppedLimitSkeleton T i).1) (stoppedLimitSkeleton T i).2
    have hAbs : |nativeResidual hUsual source ha T r
          ((stoppedLimitSkeleton T i).1) omega| ≤
        2 * max source.bound 0 +
          (a + 2 * max source.bound 0) := by
      calc
        |nativeResidual hUsual source ha T r
              ((stoppedLimitSkeleton T i).1) omega| =
            |(nativeResidual hUsual source ha T r
                ((stoppedLimitSkeleton T i).1) omega -
              nativeResidual hUsual source ha T r
                ((grid T r).sampledTime q) omega) +
              nativeResidual hUsual source ha T r
                ((grid T r).sampledTime q) omega| := by
          congr 1
          ring
        _ ≤ |nativeResidual hUsual source ha T r
                ((stoppedLimitSkeleton T i).1) omega -
              nativeResidual hUsual source ha T r
                ((grid T r).sampledTime q) omega| +
              |nativeResidual hUsual source ha T r
                ((grid T r).sampledTime q) omega| := abs_add_le _ _
        _ ≤ 2 * max source.bound 0 +
              (a + 2 * max source.bound 0) :=
          add_le_add hCellI hEndpoint
    simpa only [Real.norm_eq_abs] using hAbs.trans_eq (by ring)
  have hRightContSub : ∀ u : Set.Iic T,
      ContinuousWithinAt
        (fun v : Set.Iic T => nativeResidual hUsual source ha T r v.1 omega)
        (Set.Ici u) u := by
    intro u
    have hCont := nativeResidual_rightContinuous hUsual source ha T r omega u.1
    have hVal : ContinuousWithinAt
        ((↑) : Set.Iic T → NNReal) (Set.Ici u) u :=
      continuousAt_subtype_val.continuousWithinAt.mono
        (Set.subset_univ _)
    have hMaps : MapsTo ((↑) : Set.Iic T → NNReal)
        (Set.Ici u) (Set.Ici u.1) := by
      intro v hv
      exact hv
    change ContinuousWithinAt
      ((fun x => nativeResidual hUsual source ha T r x omega) ∘
        Subtype.val) (Set.Ici u) u
    exact hCont.comp hVal hMaps
  have hAllSub : ∀ u : Set.Iic T,
      ‖nativeResidual hUsual source ha T r u.1 omega‖ ≤
        a + 4 * max source.bound 0 := by
    apply norm_le_of_rightDense_skeleton (stoppedLimitSkeleton T)
      (stoppedLimitSkeleton_rightDense T) _ hRightContSub
    intro i
    exact hSkeleton i
  intro t ht
  simpa only [Real.norm_eq_abs] using hAllSub ⟨t, ht⟩

theorem nativeResidual_at_base_grid_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (n r k : Nat)
    (hnr : n ≤ r) (hk : k ≤ size T n) :
    nativeResidual hUsual source ha T r ((grid T n).sampledTime k) =ᵐ[mu]
      (grid T r).doobVariationStoppedPredictablePart S F mu a
        (factorialRatio n r * k) := by
  have hl : factorialRatio n r * k ≤ size T r := by
    rw [← factorialRatio_mul_size T n r hnr]
    exact Nat.mul_le_mul_left _ hk
  have htime :
      (grid T r).sampledTime (factorialRatio n r * k) =
        (grid T n).sampledTime k := by
    simpa [factorialGridEmbedding] using
      (factorialGridEmbedding_sampledTime T n r hnr k hk)
  have hnative := nativeResidual_at_native_grid_ae
    hUsual source ha T r (factorialRatio n r * k) hl
  filter_upwards [hnative] with omega homega
  rw [← htime]
  exact homega

theorem nativeResidual_baseGrid_increment_eq_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (n r k : Nat)
    (hnr : n ≤ r) (hk : k < size T n) :
    nativeResidual hUsual source ha T r ((grid T n).sampledTime (k + 1)) -
        nativeResidual hUsual source ha T r ((grid T n).sampledTime k) =ᵐ[mu]
      (fun omega =>
        (grid T r).doobVariationStoppedPredictablePart S F mu a
            (factorialRatio n r * (k + 1)) omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a
            (factorialRatio n r * k) omega) := by
  have hk0 : k ≤ size T n := Nat.le_of_lt hk
  have hk1 : k + 1 ≤ size T n := Nat.succ_le_iff.mpr hk
  have h1 := nativeResidual_at_base_grid_ae
    hUsual source ha T n r (k + 1) hnr hk1
  have h0 := nativeResidual_at_base_grid_ae
    hUsual source ha T n r k hnr hk0
  filter_upwards [h1, h0] with omega h1Omega h0Omega
  change nativeResidual hUsual source ha T r
      ((grid T n).sampledTime (k + 1)) omega -
      nativeResidual hUsual source ha T r
        ((grid T n).sampledTime k) omega = _
  rw [h1Omega, h0Omega]

theorem native_sum_abs_sub_mul_le
    (m N : Nat) (A : Nat → Real) :
    ∑ k ∈ Finset.range N, |A (m * (k + 1)) - A (m * k)| ≤
      ∑ i ∈ Finset.range (m * N), |A (i + 1) - A i| := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hblock :
          |A (m * (N + 1)) - A (m * N)| ≤
            ∑ j ∈ Finset.range m,
              |A (m * N + j + 1) - A (m * N + j)| := by
        have hsum :
            (∑ j ∈ Finset.range m,
              (A (m * N + j + 1) - A (m * N + j))) =
              A (m * (N + 1)) - A (m * N) := by
          simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using (Finset.sum_range_sub (fun j => A (m * N + j)) m)
        calc
          |A (m * (N + 1)) - A (m * N)| =
              |∑ j ∈ Finset.range m,
                (A (m * N + j + 1) - A (m * N + j))| := by rw [hsum]
          _ ≤ ∑ j ∈ Finset.range m,
              |A (m * N + j + 1) - A (m * N + j)| :=
            Finset.abs_sum_le_sum_abs _ _
      calc
        ∑ k ∈ Finset.range (N + 1),
            |A (m * (k + 1)) - A (m * k)| =
            (∑ k ∈ Finset.range N,
              |A (m * (k + 1)) - A (m * k)|) +
              |A (m * (N + 1)) - A (m * N)| := by
                rw [Finset.sum_range_succ]
        _ ≤ (∑ i ∈ Finset.range (m * N), |A (i + 1) - A i|) +
              |A (m * (N + 1)) - A (m * N)| :=
                by
                  simpa [add_comm] using
                    (add_le_add_right ih
                      |A (m * (N + 1)) - A (m * N)|)
        _ ≤ (∑ i ∈ Finset.range (m * N), |A (i + 1) - A i|) +
              ∑ j ∈ Finset.range m,
                |A (m * N + j + 1) - A (m * N + j)| :=
                add_le_add_right hblock _
        _ = ∑ i ∈ Finset.range (m * (N + 1)), |A (i + 1) - A i| := by
              rw [Nat.mul_succ, Finset.sum_range_add]

theorem nativeResidual_baseGridVariation_le_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (n r : Nat)
    (hnr : n ≤ r) :
    ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |nativeResidual hUsual source ha T r
            ((grid T n).sampledTime (k + 1)) omega -
          nativeResidual hUsual source ha T r
            ((grid T n).sampledTime k) omega|) ≤
        a + 2 * max source.bound 0 := by
  have hInc : ∀ k, k < size T n →
      nativeResidual hUsual source ha T r ((grid T n).sampledTime (k + 1)) -
          nativeResidual hUsual source ha T r ((grid T n).sampledTime k) =ᵐ[mu]
        (fun omega =>
          (grid T r).doobVariationStoppedPredictablePart S F mu a
              (factorialRatio n r * (k + 1)) omega -
            (grid T r).doobVariationStoppedPredictablePart S F mu a
              (factorialRatio n r * k) omega) := by
    intro k hk
    exact nativeResidual_baseGrid_increment_eq_ae
      hUsual source ha T n r k hnr hk
  have hIncAll : ∀ᵐ omega ∂mu, ∀ k ∈ Finset.range (size T n),
      nativeResidual hUsual source ha T r ((grid T n).sampledTime (k + 1)) omega -
          nativeResidual hUsual source ha T r ((grid T n).sampledTime k) omega =
        (grid T r).doobVariationStoppedPredictablePart S F mu a
            (factorialRatio n r * (k + 1)) omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a
            (factorialRatio n r * k) omega := by
    apply ae_all_iff.2
    intro k
    by_cases hk : k < size T n
    · filter_upwards [hInc k hk] with omega hOmega
      intro _hkMem
      exact hOmega
    · exact Filter.Eventually.of_forall (fun _omega hkMem =>
        (hk (Finset.mem_range.mp hkMem)).elim)
  have hVar := (grid T r).ae_sum_abs_doobVariationStoppedPredictablePart_increment_le
    source ha
  filter_upwards [hIncAll, hVar] with omega hIncOmega hVarOmega
  calc
    (∑ k ∈ Finset.range (size T n),
        |nativeResidual hUsual source ha T r
            ((grid T n).sampledTime (k + 1)) omega -
          nativeResidual hUsual source ha T r
            ((grid T n).sampledTime k) omega|) =
      ∑ k ∈ Finset.range (size T n),
        |(grid T r).doobVariationStoppedPredictablePart S F mu a
              (factorialRatio n r * (k + 1)) omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a
              (factorialRatio n r * k) omega| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hIncOmega k hk]
    _ ≤ ∑ i ∈ Finset.range (factorialRatio n r * size T n),
        |(grid T r).doobVariationStoppedPredictablePart S F mu a
              (i + 1) omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a i omega| := by
        exact native_sum_abs_sub_mul_le (factorialRatio n r) (size T n)
          (fun i => (grid T r).doobVariationStoppedPredictablePart
            S F mu a i omega)
    _ = ∑ i ∈ Finset.range (size T r),
        |(grid T r).doobVariationStoppedPredictablePart S F mu a
              (i + 1) omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a i omega| := by
        rw [factorialRatio_mul_size T n r hnr]
    _ ≤ a + 2 * max source.bound 0 := hVarOmega (size T r)

/-! ## Common-weight native rows

The final tail weights are applied only after each native grid has been
regularized in the ambient filtration.  Thus all four rows below use the
same weights, while no Doob component is reinterpreted on a different grid. -/

noncomputable def nativeGateGainConvexRow
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) [IsProbabilityMeasure mu] : Process Omega :=
  fun t omega =>
    (u n).apply (fun r => nativeGateGain a T r S F mu t) omega

noncomputable def nativeMartingaleConvexRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) : Process Omega :=
  fun t omega =>
    (u n).apply (fun r => nativeMartingaleProcess hUsual source ha T r t) omega

noncomputable def nativeResidualConvexRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    : Process Omega :=
  fun t omega =>
    (u n).apply (fun r => nativeResidual hUsual source ha T r t) omega

noncomputable def nativeResidualConvexRow_baseGridVariation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) : Omega → Real :=
  fun omega =>
    ∑ k ∈ Finset.range (size T n),
      |nativeResidualConvexRow u n hUsual source ha T
          ((grid T n).sampledTime (k + 1)) omega -
        nativeResidualConvexRow u n hUsual source ha T
          ((grid T n).sampledTime k) omega|

theorem nativeResidualConvexRow_baseGridVariation_le_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
    ∀ᵐ omega ∂mu,
      nativeResidualConvexRow_baseGridVariation u n hUsual source ha T omega ≤
        a + 2 * max source.bound 0 := by
  have hVar : ∀ᵐ omega ∂mu, ∀ r ∈ (u n).support,
      (∑ k ∈ Finset.range (size T n),
        |nativeResidual hUsual source ha T r
            ((grid T n).sampledTime (k + 1)) omega -
          nativeResidual hUsual source ha T r
            ((grid T n).sampledTime k) omega|) ≤
        a + 2 * max source.bound 0 := by
    apply (u n).support.eventually_all.mpr
    intro r hr
    exact nativeResidual_baseGridVariation_le_ae hUsual source ha T n r
      ((u n).tail r hr)
  filter_upwards [hVar] with omega hVarOmega
  have hPoint : ∀ k ∈ Finset.range (size T n),
      |nativeResidualConvexRow u n hUsual source ha T
          ((grid T n).sampledTime (k + 1)) omega -
        nativeResidualConvexRow u n hUsual source ha T
          ((grid T n).sampledTime k) omega| ≤
      ∑ r ∈ (u n).support, (u n).weight r *
        |nativeResidual hUsual source ha T r
            ((grid T n).sampledTime (k + 1)) omega -
          nativeResidual hUsual source ha T r
            ((grid T n).sampledTime k) omega| := by
    intro k hk
    unfold nativeResidualConvexRow TailConvexWeights.apply
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ r ∈ (u n).support,
          ((u n).weight r *
              nativeResidual hUsual source ha T r
                ((grid T n).sampledTime (k + 1)) omega -
            (u n).weight r *
              nativeResidual hUsual source ha T r
                ((grid T n).sampledTime k) omega)| =
          |∑ r ∈ (u n).support, (u n).weight r *
            (nativeResidual hUsual source ha T r
                ((grid T n).sampledTime (k + 1)) omega -
              nativeResidual hUsual source ha T r
                ((grid T n).sampledTime k) omega)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ ≤ ∑ r ∈ (u n).support,
          |(u n).weight r *
            (nativeResidual hUsual source ha T r
                ((grid T n).sampledTime (k + 1)) omega -
              nativeResidual hUsual source ha T r
                ((grid T n).sampledTime k) omega)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r ∈ (u n).support, (u n).weight r *
          |nativeResidual hUsual source ha T r
              ((grid T n).sampledTime (k + 1)) omega -
            nativeResidual hUsual source ha T r
              ((grid T n).sampledTime k) omega| := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [abs_mul, abs_of_nonneg ((u n).nonneg r hr)]
  calc
    nativeResidualConvexRow_baseGridVariation u n hUsual source ha T omega =
        ∑ k ∈ Finset.range (size T n),
          |nativeResidualConvexRow u n hUsual source ha T
              ((grid T n).sampledTime (k + 1)) omega -
            nativeResidualConvexRow u n hUsual source ha T
              ((grid T n).sampledTime k) omega| := by rfl
    _ ≤ ∑ k ∈ Finset.range (size T n),
        ∑ r ∈ (u n).support, (u n).weight r *
          |nativeResidual hUsual source ha T r
              ((grid T n).sampledTime (k + 1)) omega -
            nativeResidual hUsual source ha T r
              ((grid T n).sampledTime k) omega| := by
      apply Finset.sum_le_sum
      intro k hk
      exact hPoint k hk
    _ = ∑ r ∈ (u n).support, (u n).weight r *
        (∑ k ∈ Finset.range (size T n),
          |nativeResidual hUsual source ha T r
              ((grid T n).sampledTime (k + 1)) omega -
            nativeResidual hUsual source ha T r
              ((grid T n).sampledTime k) omega|) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.mul_sum]
    _ ≤ ∑ r ∈ (u n).support, (u n).weight r *
        (a + 2 * max source.bound 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hVarOmega r hr)
        ((u n).nonneg r hr)
    _ = a + 2 * max source.bound 0 := by
      rw [← Finset.sum_mul, (u n).sum_eq_one, one_mul]

theorem nativeMartingaleConvexRow_rightContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
    ∀ omega t, ContinuousWithinAt
      (nativeMartingaleConvexRow u n hUsual source ha T · omega) (Ici t) t := by
  intro omega t
  unfold nativeMartingaleConvexRow TailConvexWeights.apply
  induction (u n).support using Finset.induction_on with
  | empty =>
      simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => (0 : Real)) (Ici t) t)
  | @insert r s hrs ih =>
      simp only [Finset.sum_insert hrs]
      exact ((nativeMartingaleProcess_spec hUsual source ha T r).2.1 omega t
        |>.const_mul ((u n).weight r)).add ih

theorem nativeMartingaleConvexRow_leftLimits
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
    ProcessHasLeftLimits (nativeMartingaleConvexRow u n hUsual source ha T) := by
  unfold nativeMartingaleConvexRow TailConvexWeights.apply
  induction (u n).support using Finset.induction_on with
  | empty =>
      change ProcessHasLeftLimits (fun _ _ => 0)
      intro omega t
      exact tendsto_leftLim_of_tendsto
        (f := fun _ : NNReal => (0 : Real)) (a := t)
        ⟨0, tendsto_const_nhds⟩
  | @insert r s hrs ih =>
      simp only [Finset.sum_insert hrs]
      exact ((nativeMartingaleProcess_spec hUsual source ha T r).2.2.1.const_mul
        ((u n).weight r)).add ih

theorem nativeGateGainConvexRow_eq_martingale_add_residual
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
      nativeGateGainConvexRow u n a T S F mu =
      nativeMartingaleConvexRow u n hUsual source ha T +
        nativeResidualConvexRow u n hUsual source ha T := by
  funext t omega
  unfold nativeGateGainConvexRow nativeMartingaleConvexRow
    nativeResidualConvexRow TailConvexWeights.apply
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have h := congrFun (congrFun
      (nativeGateGain_eq_martingale_add_residual hUsual source ha T r) t) omega
  simp only [Pi.add_apply] at h
  rw [h]
  ring

theorem nativeMartingaleConvexRow_martingale
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
    Martingale (nativeMartingaleConvexRow u n hUsual source ha T) F mu := by
  have hSum : Martingale
      (∑ r ∈ (u n).support,
        (u n).weight r • nativeMartingaleProcess hUsual source ha T r)
      F mu := by
    induction (u n).support using Finset.induction_on with
    | empty =>
        simpa using (martingale_zero Real F mu)
    | @insert r s hrs ih =>
        rw [Finset.sum_insert hrs]
        exact (nativeMartingaleProcess_spec hUsual source ha T r).1
          |>.smul ((u n).weight r) |>.add ih
  have hEq : nativeMartingaleConvexRow u n hUsual source ha T =
      ∑ r ∈ (u n).support,
        (u n).weight r • nativeMartingaleProcess hUsual source ha T r := by
    funext t omega
    simp [nativeMartingaleConvexRow, TailConvexWeights.apply,
      Finset.sum_apply, Pi.smul_apply]
  rw [hEq]
  exact hSum

theorem nativeResidualConvexRow_ae_abs_le_on_horizon
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |nativeResidualConvexRow u n hUsual source ha T t omega| ≤
        a + 4 * max source.bound 0 := by
  have hSupport : ∀ r ∈ (u n).support, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |nativeResidual hUsual source ha T r t omega| ≤
        a + 4 * max source.bound 0 := by
    intro r hr
    exact nativeResidual_ae_abs_le_on_horizon hUsual source ha T r
  have hAll := (u n).support.eventually_all.mpr hSupport
  filter_upwards [hAll] with omega hOmega t ht
  unfold nativeResidualConvexRow TailConvexWeights.apply
  calc
    |∑ r ∈ (u n).support,
        (u n).weight r * nativeResidual hUsual source ha T r t omega| ≤
      ∑ r ∈ (u n).support,
        |(u n).weight r * nativeResidual hUsual source ha T r t omega| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ (u n).support,
        (u n).weight r * (a + 4 * max source.bound 0) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [abs_mul, abs_of_nonneg ((u n).nonneg r hr)]
      exact mul_le_mul_of_nonneg_left (hOmega r hr t ht)
        ((u n).nonneg r hr)
    _ = a + 4 * max source.bound 0 := by
      rw [← Finset.sum_mul, (u n).sum_eq_one, one_mul]

end HorizonFactorialGrid

end FTAPTheorem42
