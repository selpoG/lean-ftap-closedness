/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.CommonGateEnvelope
import FTAPTheorem42.Stochastic.Decomposition.Source.RowInverse
import FTAPTheorem42.Stochastic.Decomposition.Source.RowDecomposition
import FTAPTheorem42.Stochastic.Decomposition.Source.NativeExtension
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobComponentStopping
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRows

/-!
# Common stopped rows under a square-integrable envelope

This module is the source-free row consumer for the common-gate endpoint.  It
rebuilds the finite-grid martingale coordinates from the `L²` envelope and
keeps the gate, coefficient family, and stopping times supplied by that
endpoint.  In particular, it does not manufacture a
`BoundedSemimartingaleSource` from a random envelope.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## Source-free finite-grid `L²` coordinates -/

theorem envelope_doobPredictablePart_memLp_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (G : ChronologicalGrid NNReal N) (n : Nat) :
    MemLp (G.doobPredictablePart S F mu n) (2 : ENNReal) mu := by
  change MemLp
    (predictablePart (G.natSample S) (G.sampledFiltration F) mu n)
    (2 : ENNReal) mu
  unfold predictablePart
  apply memLp_finsetSum'
  intro k hk
  exact ((G.sample_memLp_two_of_memLp_two_envelope hSAdapted ξ hξ hSBound (k + 1)).sub
    (G.sample_memLp_two_of_memLp_two_envelope hSAdapted ξ hξ hSBound k)).condExp
    (by norm_num)

theorem envelope_doobMartingalePart_memLp_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (G : ChronologicalGrid NNReal N) (n : Nat) :
    MemLp (G.doobMartingalePart S F mu n) (2 : ENNReal) mu := by
  change MemLp
    (martingalePart (G.natSample S) (G.sampledFiltration F) mu n)
    (2 : ENNReal) mu
  unfold martingalePart
  exact (G.sample_memLp_two_of_memLp_two_envelope hSAdapted ξ hξ hSBound n).sub
    (envelope_doobPredictablePart_memLp_two hSAdapted ξ hξ hSBound G n)

theorem envelope_doobMartingalePart_martingale
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (G : ChronologicalGrid NNReal N) :
    Martingale (G.doobMartingalePart S F mu)
      (G.sampledFiltration F) mu := by
  have hSampleAdapted : StronglyAdapted (G.sampledFiltration F) (G.natSample S) := by
    intro n
    exact hSAdapted (G.sampledTime n)
  apply martingale_martingalePart
  · exact hSampleAdapted
  · intro n
    exact (G.sample_memLp_two_of_memLp_two_envelope hSAdapted ξ hξ hSBound n).integrable
      (by norm_num)

theorem envelope_doobVariationStoppedMartingalePart_memLp_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (G : ChronologicalGrid NNReal N) (a : Real) (n : Nat) :
  MemLp (G.doobVariationStoppedMartingalePart S F mu a n)
      (2 : ENNReal) mu := by
  apply DiscretePredictableIntegral.memLp_two
    (envelope_doobMartingalePart_martingale
      hSAdapted ξ hξ hSBound G)
    (fun k => envelope_doobMartingalePart_memLp_two
      hSAdapted ξ hξ hSBound G k)
    (G.stronglyAdapted_doobVariationGate S F mu a)
  · intro k
    exact ae_of_all mu fun omega =>
      G.abs_doobVariationGate_le_one S F mu a k omega

noncomputable def envelopeNativeMartingaleTerminal
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) : Lp Real 2 mu :=
  (envelope_doobVariationStoppedMartingalePart_memLp_two
    hSAdapted ξ hξ hSBound (grid T r) a (size T r)).toLp
    ((grid T r).doobVariationStoppedMartingalePart S F mu a (size T r))

noncomputable def envelopeNativeMartingaleProcess
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) : Process Omega :=
  Classical.choose (exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual
    (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r))

theorem envelopeNativeMartingaleProcess_spec
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) :
    Martingale (envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r) F mu ∧
      (∀ omega t, ContinuousWithinAt
        (envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r · omega)
        (Ici t) t) ∧
      ProcessHasLeftLimits
        (envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r) ∧
      (∀ t, envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r t =ᵐ[mu]
        condExpMartingaleProcess mu F
          (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r) t) := by
  exact Classical.choose_spec
    (exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r))

theorem envelopeNativeMartingaleProcess_memLp_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) (t : NNReal) :
    MemLp (envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r t)
      (2 : ENNReal) mu := by
  have hTerminal : MemLp
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r : Omega → Real)
      (2 : ENNReal) mu := Lp.memLp _
  have hCond : MemLp
      (condExpMartingaleProcess mu F
        (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r) t)
      (2 : ENNReal) mu := by
    change MemLp (mu[(envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
      Omega → Real) | F t]) (2 : ENNReal) mu
    exact hTerminal.condExp (by norm_num)
  have hVersion := (envelopeNativeMartingaleProcess_spec hUsual hSAdapted ξ hξ
    hSBound a T r).2.2.2 t
  exact hCond.ae_eq hVersion.symm

noncomputable def envelopeNativeMartingaleConvexRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) : Process Omega :=
  fun t omega =>
    (u n).apply (fun r =>
      envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r t) omega

theorem envelopeNativeMartingaleConvexRow_martingale
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) :
    Martingale
      (envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T)
      F mu := by
  have hSum : Martingale
      (∑ r ∈ (u n).support,
        (u n).weight r •
          envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r)
      F mu := by
    induction (u n).support using Finset.induction_on with
    | empty =>
        simpa using (martingale_zero Real F mu)
    | @insert r s hrs ih =>
        rw [Finset.sum_insert hrs]
        exact (envelopeNativeMartingaleProcess_spec hUsual hSAdapted ξ hξ hSBound
          a T r).1 |>.smul ((u n).weight r) |>.add ih
  have hEq :
      envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T =
        ∑ r ∈ (u n).support,
          (u n).weight r •
            envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r := by
    funext t omega
    simp [envelopeNativeMartingaleConvexRow, TailConvexWeights.apply,
      Finset.sum_apply, Pi.smul_apply]
  rw [hEq]
  exact hSum

private theorem envelopeNativeMartingaleConvexRow_rightContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) :
    ∀ omega t, ContinuousWithinAt
      (envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T · omega)
      (Ici t) t := by
  intro omega t
  unfold envelopeNativeMartingaleConvexRow TailConvexWeights.apply
  induction (u n).support using Finset.induction_on with
  | empty =>
      simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => (0 : Real)) (Ici t) t)
  | @insert r s hrs ih =>
      simp only [Finset.sum_insert hrs]
      exact ((envelopeNativeMartingaleProcess_spec hUsual hSAdapted ξ hξ hSBound
        a T r).2.1 omega t |>.const_mul ((u n).weight r)).add ih

theorem envelopeNativeMartingaleConvexRow_memLp_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T t : NNReal) :
    MemLp
      (envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T t)
      (2 : ENNReal) mu := by
  classical
  unfold envelopeNativeMartingaleConvexRow TailConvexWeights.apply
  induction (u n).support using Finset.induction_on with
  | empty => simp
  | @insert r s hrs ih =>
      have hsum :=
        (envelopeNativeMartingaleProcess_memLp_two hUsual hSAdapted ξ hξ hSBound
          a T r t).const_smul ((u n).weight r) |>.add ih
      convert hsum using 1
      ext omega
      simp [Finset.sum_insert hrs, smul_eq_mul]

/-! The common-grid coefficient process can be regularized without a bounded
source: all measurability statements use only the sampled gate and the
stopping time. -/

private theorem envelope_rowCommonGrid_sampledTime_le_native_succ
    (u : ∀ n, TailConvexWeights n) (n r k : Nat)
    (hr : r ∈ (u n).support) (hk : k < size T (rowCommonLevel u n)) :
    (grid T (rowCommonLevel u n)).sampledTime (k + 1) ≤
      (grid T r).sampledTime (rowNativeIndex u n r k + 1) := by
  let q := rowCommonLevel u n
  let m := factorialRatio r q
  let l := rowNativeIndex u n r k
  have hrq : r ≤ q := rowCommonLevel_ge u n r hr
  have hm : 0 < m := factorialRatio_pos r q hrq
  have hsize : m * size T r = size T q :=
    factorialRatio_mul_size T r q hrq
  have hkq : k + 1 ≤ size T q := Nat.succ_le_of_lt hk
  have hlr : l + 1 ≤ size T r := by
    dsimp [l, rowNativeIndex]
    apply Nat.succ_le_of_lt
    apply (Nat.div_lt_iff_lt_mul hm).2
    have hsize' : size T r * m = size T q := by
      simpa [Nat.mul_comm] using hsize
    rw [hsize']
    exact hk
  have hdiv : k + 1 ≤ (k / m + 1) * m := by
    have hrem := Nat.mod_lt k hm
    have hdecomp := Nat.div_add_mod k m
    have hdecomp' : k / m * m + k % m = k := by
      simpa [Nat.mul_comm] using hdecomp
    calc
      k + 1 = k / m * m + k % m + 1 := by rw [hdecomp']
      _ ≤ k / m * m + m := by omega
      _ = (k / m + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
  have hqfac : (q.factorial : NNReal) =
      (r.factorial : NNReal) * (m : NNReal) := by
    exact_mod_cast (factorialRatio_mul r q hrq).symm
  have hfacr : 0 < (r.factorial : NNReal) := by positivity
  have hfacq : 0 < (q.factorial : NNReal) := by positivity
  have hratio : ((k + 1 : Nat) : NNReal) /
      (q.factorial : NNReal) ≤ ((l + 1 : Nat) : NNReal) /
      (r.factorial : NNReal) := by
    rw [div_le_div_iff₀ hfacq hfacr]
    rw [hqfac]
    have hdiv' : ((k + 1 : Nat) : NNReal) ≤
        ((l + 1 : Nat) : NNReal) * (m : NNReal) := by
      exact_mod_cast hdiv
    calc
      ((k + 1 : Nat) : NNReal) * (r.factorial : NNReal) ≤
          (((l + 1 : Nat) : NNReal) * (m : NNReal)) *
            (r.factorial : NNReal) := by
        exact mul_le_mul_of_nonneg_right hdiv' (by positivity)
      _ = ((l + 1 : Nat) : NNReal) *
          ((r.factorial : NNReal) * (m : NNReal)) := by ring
  have hqtime : (grid T q).sampledTime (k + 1) =
      min (((k + 1 : Nat) : NNReal) / (q.factorial : NNReal)) T := by
    unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
    simp only [Nat.min_eq_left hkq, grid_time]
  have hltime : (grid T r).sampledTime (l + 1) =
      min (((l + 1 : Nat) : NNReal) / (r.factorial : NNReal)) T := by
    unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
    simp only [Nat.min_eq_left hlr, grid_time]
  rw [hqtime, hltime]
  exact min_le_min hratio le_rfl

private theorem envelope_nativeGateGainConvexRow_cell_eq
    (u : ∀ n, TailConvexWeights n) (n k : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (hk : k < size T (rowCommonLevel u n))
    (t : NNReal) (omega : Omega) :
    nativeGateGainConvexRow u n a T S F mu
        (min t ((grid T (rowCommonLevel u n)).sampledTime (k + 1))) omega -
      nativeGateGainConvexRow u n a T S F mu
        (min t ((grid T (rowCommonLevel u n)).sampledTime k)) omega =
      rowGateCoefficient u n a T S F mu k omega *
        (S (min t ((grid T (rowCommonLevel u n)).sampledTime (k + 1))) omega -
          S (min t ((grid T (rowCommonLevel u n)).sampledTime k)) omega) := by
  let q := rowCommonLevel u n
  let G := grid T q
  change nativeGateGainConvexRow u n a T S F mu
      (min t (G.sampledTime (k + 1))) omega -
    nativeGateGainConvexRow u n a T S F mu
      (min t (G.sampledTime k)) omega =
    rowGateCoefficient u n a T S F mu k omega *
      (S (min t (G.sampledTime (k + 1))) omega -
        S (min t (G.sampledTime k)) omega)
  by_cases htk : t ≤ G.sampledTime k
  · have hmin : min t (G.sampledTime (k + 1)) =
        min t (G.sampledTime k) := by
      rw [min_eq_left (htk.trans (G.sampledTime_mono (Nat.le_succ k))),
        min_eq_left htk]
    rw [hmin]
    simp [G]
  · have hleft : G.sampledTime k < t := lt_of_not_ge htk
    have hmin0 : min t (G.sampledTime k) = G.sampledTime k :=
      min_eq_right hleft.le
    have hleft_to_one : G.sampledTime k ≤
        min t (G.sampledTime (k + 1)) := by
      exact le_min hleft.le (G.sampledTime_mono (Nat.le_succ k))
    have hupper (r : Nat) (hr : r ∈ (u n).support) :
        G.sampledTime (k + 1) ≤
          (grid T r).sampledTime (rowNativeIndex u n r k + 1) :=
      envelope_rowCommonGrid_sampledTime_le_native_succ u n r k hr hk
    have hrow : ∀ r ∈ (u n).support,
        nativeGateGain a T r S F mu
            (min t (G.sampledTime (k + 1))) omega -
          nativeGateGain a T r S F mu
            (min t (G.sampledTime k)) omega =
        (grid T r).doobVariationGate S F mu a
            (rowNativeIndex u n r k) omega *
          (S (min t (G.sampledTime (k + 1))) omega -
            S (min t (G.sampledTime k)) omega) := by
      intro r hr
      let l := rowNativeIndex u n r k
      have hlr : l + 1 ≤ size T r := by
        dsimp [l]
        apply Nat.succ_le_of_lt
        have hrq : r ≤ q := rowCommonLevel_ge u n r hr
        have hm : 0 < factorialRatio r q := factorialRatio_pos r q hrq
        apply (Nat.div_lt_iff_lt_mul hm).2
        have hsize' : size T r * factorialRatio r q = size T q := by
          simpa [Nat.mul_comm] using factorialRatio_mul_size T r q hrq
        rw [hsize']
        exact hk
      have hlk : (grid T r).sampledTime l ≤ G.sampledTime k := by
        exact rowCommonGrid_sampledTime_nativeIndex_le u n r k hr hk.le
      have hright0 : G.sampledTime k ≤
          (grid T r).sampledTime (l + 1) :=
        (G.sampledTime_mono (Nat.le_succ k)).trans (hupper r hr)
      have hleft0 : (grid T r).sampledTime (l + 1 - 1) ≤
          min t (G.sampledTime k) := by
        simpa [Nat.add_sub_cancel] using hlk.trans_eq hmin0.symm
      have hright0' : min t (G.sampledTime k) ≤
          (grid T r).sampledTime (l + 1) := by
        rw [hmin0]
        exact hright0
      have hright1 : min t (G.sampledTime (k + 1)) ≤
          (grid T r).sampledTime (l + 1) := by
        exact (min_le_right _ _).trans (hupper r hr)
      have hleft1 : (grid T r).sampledTime (l + 1 - 1) ≤
          min t (G.sampledTime (k + 1)) := by
        simpa [Nat.add_sub_cancel] using hlk.trans hleft_to_one
      have hcell0 := nativeGateGain_cell_eq (S := S) (F := F) (mu := mu)
        a T r (l + 1) (min t (G.sampledTime k)) omega
        (by positivity) hlr hleft0 hright0'
      have hcell1 := nativeGateGain_cell_eq (S := S) (F := F) (mu := mu)
        a T r (l + 1) (min t (G.sampledTime (k + 1))) omega
        (by positivity) hlr hleft1 hright1
      dsimp [l] at hcell0 hcell1 ⊢
      rw [hcell1, hcell0]
      ring
    unfold nativeGateGainConvexRow TailConvexWeights.apply
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ r ∈ (u n).support,
          ((u n).weight r *
              nativeGateGain a T r S F mu
                (min t (G.sampledTime (k + 1))) omega -
            (u n).weight r *
              nativeGateGain a T r S F mu
                (min t (G.sampledTime k)) omega)) =
          ∑ r ∈ (u n).support, (u n).weight r *
            (nativeGateGain a T r S F mu
                (min t (G.sampledTime (k + 1))) omega -
              nativeGateGain a T r S F mu
                (min t (G.sampledTime k)) omega) := by
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ =
          ∑ r ∈ (u n).support, (u n).weight r *
            ((grid T r).doobVariationGate S F mu a
              (rowNativeIndex u n r k) omega *
              (S (min t (G.sampledTime (k + 1))) omega -
                S (min t (G.sampledTime k)) omega)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hrow r hr]
      _ = rowGateCoefficient u n a T S F mu k omega *
          (S (min t (G.sampledTime (k + 1))) omega -
            S (min t (G.sampledTime k)) omega) := by
        unfold rowGateCoefficient
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        ring

/-! ## One row in the ambient filtration -/

noncomputable def envelopeNativeResidualConvexRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) : Process Omega :=
  nativeGateGainConvexRow u n a T S F mu -
    envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T

noncomputable def envelopeRowInverseGain
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (_hAlphaStop : IsStoppingTime F alpha) : Process Omega :=
  (grid T (rowCommonLevel u n)).martingaleIntegralProcess
    (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
      u n a T alpha)
    (nativeGateGainConvexRow u n a T S F mu)

noncomputable def envelopeRowInverseMartingaleGain
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
    (_hAlphaStop : IsStoppingTime F alpha) : Process Omega :=
  (grid T (rowCommonLevel u n)).martingaleIntegralProcess
    (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
      u n a T alpha)
    (envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T)

noncomputable def envelopeRowInverseResidualGain
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
    (_hAlphaStop : IsStoppingTime F alpha) : Process Omega :=
  (grid T (rowCommonLevel u n)).martingaleIntegralProcess
    (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
      u n a T alpha)
    (envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T)

private theorem envelopeRowInverseGain_eq_add
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
    (hAlphaStop : IsStoppingTime F alpha) :
    envelopeRowInverseGain (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop =
      envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop +
      envelopeRowInverseResidualGain (S := S) (F := F) (mu := mu)
        u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop := by
  funext t omega
  unfold envelopeRowInverseGain envelopeRowInverseMartingaleGain
    envelopeRowInverseResidualGain envelopeNativeResidualConvexRow
    ChronologicalGrid.martingaleIntegralProcess
  simp only [Finset.sum_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [deterministicIntervalMartingaleTransform,
    stoppedProcess_const_apply]
  simp only [Pi.sub_apply]
  ring_nf

private theorem envelopeRowInverseGain_eq_activeCellSum
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (t : NNReal) (omega : Omega) :
    envelopeRowInverseGain (S := S) (F := F) (mu := mu) u n a T alpha
        hAlphaStop t omega =
      ∑ k ∈ Finset.range (size T (rowCommonLevel u n)),
        (if ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
              alpha omega ∧
            (grid T (rowCommonLevel u n)).sampledTime k <
              (grid T (rowCommonLevel u n)).sampledTime (k + 1) then
          (1 : Real) else 0) *
          (S (min t ((grid T (rowCommonLevel u n)).sampledTime (k + 1))) omega -
            S (min t ((grid T (rowCommonLevel u n)).sampledTime k)) omega) := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let Y := nativeGateGainConvexRow u n a T S F mu
  change G.martingaleIntegralProcess K Y t omega = _
  unfold ChronologicalGrid.martingaleIntegralProcess
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < size T q := Finset.mem_range.mp hk
  have hK := rowInverseCoefficientProcess_at_sampledTime
    (S := S) (F := F) (mu := mu) u n a T alpha k hk' omega
  have hY := envelope_nativeGateGainConvexRow_cell_eq
    (u := u) (n := n) (k := k) (a := a) (T := T)
    (S := S) (F := F) (mu := mu) hk' t omega
  have hprod := rowInverseCoefficient_mul_gate_eq_activeIndicator
    u n a T S F mu alpha hAlpha k omega hk'
  dsimp [K, Y, G, q] at hK hY ⊢
  rw [deterministicIntervalMartingaleTransform,
    stoppedProcess_const_apply, stoppedProcess_const_apply,
    hK, hY]
  rw [← mul_assoc, hprod]
  rfl

private theorem envelopeRowInverseGain_eq_stoppedSource_sub_initial
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
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
    envelopeRowInverseGain (S := S) (F := F) (mu := mu) u n a T alpha
        hAlphaStop t omega =
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega := by
  rw [envelopeRowInverseGain_eq_activeCellSum u n a T alpha hAlphaStop
    hAlpha t omega]
  exact activeCellSum_eq_stoppedSource_sub_initial S T (rowCommonLevel u n) alpha
    (fun omega => (hAlpha omega).trans (min_le_left _ _)) hNoCross t omega

private theorem envelopeRowInverseMartingaleGain_martingale
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
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    Martingale
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop) F mu := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
  change Martingale (G.martingaleIntegralProcess K M) F mu
  have hM := envelopeNativeMartingaleConvexRow_martingale
    (S := S) (F := F) (mu := mu) u n hUsual hSAdapted ξ hξ hSBound a T
  have hMRight := envelopeNativeMartingaleConvexRow_rightContinuous
    (S := S) (F := F) (mu := mu) u n hUsual hSAdapted ξ hξ hSBound a T
  have hK := rowInverseCoefficientProcess_stronglyAdapted
    (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop
  have hKBound : ∀ v, ∀ᵐ omega ∂mu, |K v omega| ≤ (2 : Real) := by
    intro v
    exact ae_of_all mu (fun omega =>
      rowInverseCoefficientProcess_abs_le_two
        (S := S) (F := F) (mu := mu) u n a T alpha hAlpha v omega)
  exact G.martingaleIntegralProcess_isMartingale_of_stronglyAdapted
    hM hMRight hK hKBound

private theorem envelopeRowInverseMartingaleGain_terminal_memLp_two
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
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    MemLp
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
          ((grid T (rowCommonLevel u n)).sampledTime
            (size T (rowCommonLevel u n))))
      (2 : ENNReal) mu := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
  have hM : Martingale M F mu := by
    exact envelopeNativeMartingaleConvexRow_martingale
      (S := S) (F := F) (mu := mu) u n hUsual hSAdapted ξ hξ hSBound a T
  have hMLp : ∀ k, MemLp (M (G.sampledTime k)) (2 : ENNReal) mu := by
    intro k
    exact envelopeNativeMartingaleConvexRow_memLp_two
      (S := S) (F := F) (mu := mu) u n hUsual hSAdapted ξ hξ hSBound
      a T (G.sampledTime k)
  have hK : StronglyAdapted F K := by
    exact rowInverseCoefficientProcess_stronglyAdapted
      (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop
  have hKBound : ∀ v, ∀ᵐ omega ∂mu, |K v omega| ≤ (2 : Real) := by
    intro v
    exact ae_of_all mu (fun omega =>
      rowInverseCoefficientProcess_abs_le_two
        (S := S) (F := F) (mu := mu) u n a T alpha hAlpha v omega)
  have hDiscrete := DiscretePredictableIntegral.memLp_two
    (μ := mu) (ℱ := G.sampledFiltration F)
    (M := G.natSample M) (K := G.natSample K) (C := fun _ => (2 : Real))
    (ChronologicalGrid.Martingale.natSample (G := G) hM)
    hMLp (G.stronglyAdapted_natSample hK)
    (fun k => hKBound (G.sampledTime k)) (size T q)
  change MemLp (G.martingaleIntegralProcess K M
    (G.sampledTime (size T q))) (2 : ENNReal) mu
  rw [G.martingaleIntegralProcess_last K M]
  exact hDiscrete

theorem envelopeRowInverseMartingaleGain_rightContinuous
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
    (hAlphaStop : IsStoppingTime F alpha) :
    ∀ omega t, ContinuousWithinAt
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop · omega)
      (Ici t) t := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
  change ∀ omega t, ContinuousWithinAt (G.martingaleIntegralProcess K M · omega)
    (Ici t) t
  intro omega t
  exact G.martingaleIntegralProcess_rightContinuous K M
    (envelopeNativeMartingaleConvexRow_rightContinuous
      (S := S) (F := F) (mu := mu) u n hUsual hSAdapted ξ hξ hSBound a T)
    omega t

/-! A single selected row, with all random-envelope identities kept at the
same coefficient family and at the same two stopping times.  The terminal
`L²` fields below are fixed-grid feasibility statements; no uniform bound in
the selected-row index is asserted here. -/

structure EnvelopeStoppedRowData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real)
    (u : ∀ n, TailConvexWeights n) (r : Nat)
    (a : Real) (T : NNReal)
    (alphaSeq : Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaSeqStop : IsStoppingTime F alphaSeq)
    (hAlphaStop : IsStoppingTime F alpha)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) : Prop where
  alphaSeq_le_T : ∀ omega, alphaSeq omega ≤ (T : WithTop NNReal)
  alpha_le_alphaSeq : ∀ omega, alpha omega ≤ alphaSeq omega
  row_gain_eq_stoppedSource : ∀ t omega,
    envelopeRowInverseGain (S := S) (F := F) (mu := mu) u r a T alphaSeq
        hAlphaSeqStop t omega =
      MeasureTheory.stoppedProcess S alphaSeq t omega - S 0 omega
  row_gain_eq_martingale_add_residual : ∀ t omega,
    envelopeRowInverseGain (S := S) (F := F) (mu := mu) u r a T alphaSeq
        hAlphaSeqStop t omega =
      envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop t omega +
      envelopeRowInverseResidualGain (S := S) (F := F) (mu := mu)
        u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop t omega
  row_martingale : Martingale
    (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
      u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop) F mu
  row_terminal_memLp : MemLp
    (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
      u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop
        ((grid T (rowCommonLevel u r)).sampledTime
          (size T (rowCommonLevel u r)))) (2 : ENNReal) mu
  stopped_martingale : Martingale
    (MeasureTheory.stoppedProcess
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop) alpha) F mu
  stopped_terminal_memLp : MemLp
    (MeasureTheory.stoppedProcess
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop) alpha T)
      (2 : ENNReal) mu
  stoppedSource_eq_martingale_add_residual : ∀ t omega,
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      MeasureTheory.stoppedProcess
          (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
            u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop) alpha
          t omega +
        MeasureTheory.stoppedProcess
          (envelopeRowInverseResidualGain (S := S) (F := F) (mu := mu)
            u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop) alpha
          t omega

theorem envelopeStoppedRowData_of_exact_hitting
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real)
    (u : ∀ n, TailConvexWeights n) (r : Nat)
    (a : Real) (T : NNReal)
    (alphaSeq : Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaSeqStop : IsStoppingTime F alphaSeq)
    (hAlphaStop : IsStoppingTime F alpha)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (hAlphaSeqLe : ∀ omega, alphaSeq omega ≤ (T : WithTop NNReal))
    (hAlphaLe : ∀ omega, alpha omega ≤ alphaSeq omega)
    (hAlphaSeq : ∀ omega, alphaSeq omega = min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u r a T S F mu t omega)
        (-1 / 2) omega)) :
    EnvelopeStoppedRowData ξ u r a T alphaSeq alpha hAlphaSeqStop hAlphaStop
      hUsual hSAdapted hξ hSBound := by
  let hAlpha : ∀ omega, alphaSeq omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u r a T S F mu t omega)
        (-1 / 2) omega) := fun omega => le_of_eq (hAlphaSeq omega)
  have hNoCross : ∀ k, k < size T (rowCommonLevel u r) → ∀ omega,
      ((grid T (rowCommonLevel u r)).sampledTime k : WithTop NNReal) <
          alphaSeq omega →
        (grid T (rowCommonLevel u r)).sampledTime k <
          (grid T (rowCommonLevel u r)).sampledTime (k + 1) →
        ((grid T (rowCommonLevel u r)).sampledTime (k + 1) : WithTop NNReal) ≤
          alphaSeq omega := by
    intro k hk omega hleft hcell
    exact rowAlpha_noCross_of_exact_hitting u r a T S F mu alphaSeq
      hAlphaSeq k omega hk hleft
  have hGain : ∀ t omega,
      envelopeRowInverseGain (S := S) (F := F) (mu := mu) u r a T alphaSeq
          hAlphaSeqStop t omega =
        MeasureTheory.stoppedProcess S alphaSeq t omega - S 0 omega := by
    intro t omega
    exact envelopeRowInverseGain_eq_stoppedSource_sub_initial
      u r a T alphaSeq hAlphaSeqStop hAlpha hNoCross t omega
  have hGainAdd : ∀ t omega,
      envelopeRowInverseGain (S := S) (F := F) (mu := mu) u r a T alphaSeq
          hAlphaSeqStop t omega =
        envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop t omega +
        envelopeRowInverseResidualGain (S := S) (F := F) (mu := mu)
          u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop t omega := by
    intro t omega
    exact congrFun (congrFun (envelopeRowInverseGain_eq_add
      u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop) t) omega
  have hRowM := envelopeRowInverseMartingaleGain_martingale
    (S := S) (F := F) (mu := mu) u r hUsual hSAdapted ξ hξ hSBound a T
      alphaSeq hAlphaSeqStop hAlpha
  have hRowTerm := envelopeRowInverseMartingaleGain_terminal_memLp_two
    (S := S) (F := F) (mu := mu) u r hUsual hSAdapted ξ hξ hSBound a T
      alphaSeq hAlphaSeqStop hAlpha
  have hRowMRight := envelopeRowInverseMartingaleGain_rightContinuous
    (S := S) (F := F) (mu := mu) u r hUsual hSAdapted ξ hξ hSBound a T
      alphaSeq hAlphaSeqStop
  have hStoppedM :=
    RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hRowM hAlphaStop hRowMRight
  have hMConstant : ∀ omega,
      envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop
          (T + 1) omega =
        envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop
          T omega := by
    let q := rowCommonLevel u r
    let G := grid T q
    let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
      u r a T alphaSeq
    let M := envelopeNativeMartingaleConvexRow u r hUsual hSAdapted ξ hξ hSBound a T
    have hLast : G.martingaleIntegralProcess K M (T + 1) =
        G.martingaleIntegralProcess K M (G.sampledTime (size T q)) := by
      rw [G.martingaleIntegralProcess_eq_last_of_le K M]
      simp [G]
    have hSize : G.sampledTime (size T q) = T := sampledTime_size T q
    intro omega
    change G.martingaleIntegralProcess K M (T + 1) omega =
      G.martingaleIntegralProcess K M T omega
    rw [hLast, hSize]
  have hRowTermT : MemLp
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop T)
      (2 : ENNReal) mu := by
    simpa [sampledTime_size] using hRowTerm
  have hStoppedTerm := martingale_stoppedProcess_memLp_two_and_integral_sq_le
    hRowM hRowMRight hAlphaStop hRowTermT hMConstant
  have hStoppedDec : ∀ t omega,
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
        MeasureTheory.stoppedProcess
            (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
              u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop) alpha
            t omega +
          MeasureTheory.stoppedProcess
            (envelopeRowInverseResidualGain (S := S) (F := F) (mu := mu)
              u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop) alpha
            t omega := by
    intro t omega
    let N : Process Omega :=
      envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop
    let B : Process Omega :=
      envelopeRowInverseResidualGain (S := S) (F := F) (mu := mu)
        u r hUsual hSAdapted ξ hξ hSBound a T alphaSeq hAlphaSeqStop
    have hRowEq : (fun s omega =>
        MeasureTheory.stoppedProcess S alphaSeq s omega - S 0 omega) = N + B := by
      funext s omega
      simpa [N, B] using (hGain s omega).symm.trans (hGainAdd s omega)
    have hStopped := congrArg
      (fun P : Process Omega => MeasureTheory.stoppedProcess P alpha) hRowEq
    have hSourceStop :
        MeasureTheory.stoppedProcess
            (MeasureTheory.stoppedProcess S alphaSeq) alpha =
          MeasureTheory.stoppedProcess S alpha :=
      MeasureTheory.stoppedProcess_stoppedProcess_of_le_right hAlphaLe
    rw [stoppedProcess_sub_const, stoppedProcess_add, hSourceStop] at hStopped
    have hPoint := congrFun (congrFun hStopped t) omega
    simpa [N, B] using hPoint
  refine
    { alphaSeq_le_T := hAlphaSeqLe
      alpha_le_alphaSeq := hAlphaLe
      row_gain_eq_stoppedSource := hGain
      row_gain_eq_martingale_add_residual := hGainAdd
      row_martingale := hRowM
      row_terminal_memLp := hRowTerm
      stopped_martingale := hStoppedM
      stopped_terminal_memLp := hStoppedTerm.1
      stoppedSource_eq_martingale_add_residual := hStoppedDec }

/-! This endpoint consumes the common-gate producer directly.  Its row field
is deliberately a feasibility certificate: the exact stopped decomposition,
the true stopped martingale, and fixed-horizon `L²` membership are supplied
for every selected row, while the level-independent maximal `L²` and
finite-variation estimates remain a separate boundary. -/

structure EnvelopeDominatedCommonStoppedRowsFeasibilityEndpoint
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (ξ : Omega → Real) (eta : Real)
    (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (T : NNReal)
    (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) : Prop where
  commonGate : EnvelopeDominatedCommonGateEndpoint
    (S := S) (F := F) (mu := mu) ξ eta u selection a T alphaSeq alpha R
  rowData : ∀ k, EnvelopeStoppedRowData ξ u (selection k) a T
    (alphaSeq k) alpha (commonGate.alphaSeq_stopping k)
    commonGate.alpha_stopping hUsual hSAdapted hξ hSBound

theorem exists_commonGateStoppedRows_of_memLp_two_envelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real)
    (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (T : NNReal) {eta : Real} (heta : 0 < eta) :
    ∃ (a : Real) (u : ∀ n, TailConvexWeights n)
      (selection : Nat → Nat)
      (alphaSeq : Nat → Omega → WithTop NNReal)
      (alpha : Omega → WithTop NNReal) (R : Omega → Real),
      EnvelopeDominatedCommonStoppedRowsFeasibilityEndpoint
        (S := S) (F := F) (mu := mu) ξ eta u selection a T alphaSeq alpha R
        hUsual hSAdapted hξ hSBound := by
  obtain ⟨a, u, selection, alphaSeq, alpha, R, hGate⟩ :=
    exists_commonGate_of_memLp_two_envelope
      hUsual hS hSAdapted ξ hξ hSBound T heta
  have hRows : ∀ k, EnvelopeStoppedRowData ξ u (selection k) a T
      (alphaSeq k) alpha (hGate.alphaSeq_stopping k) hGate.alpha_stopping
      hUsual hSAdapted hξ hSBound := by
    intro k
    exact envelopeStoppedRowData_of_exact_hitting
      ξ u (selection k) a T (alphaSeq k) alpha
      (hGate.alphaSeq_stopping k) hGate.alpha_stopping hUsual hSAdapted hξ hSBound
      (hGate.alphaSeq_le_T k) (hGate.alpha_le_alphaSeq k) (fun omega =>
        hGate.alphaSeq_eq k omega)
  refine ⟨a, u, selection, alphaSeq, alpha, R, ?_⟩
  exact { commonGate := hGate, rowData := hRows }

end HorizonFactorialGrid

end FTAPTheorem42
