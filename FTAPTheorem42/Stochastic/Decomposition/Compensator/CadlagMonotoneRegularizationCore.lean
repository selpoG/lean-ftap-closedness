/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagCandidateCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonAESubsequenceCore
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Foundations.ProcessIndistinguishable
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale

/-!
# Source-independent monotone regularization of càdlàg candidates

The Hilbert and common-a.e. certificates provide nonnegative increasing rows on
one right-dense skeleton.  This module contains only the path argument which
extends those inequalities to all times and zeroes one common time-zero null
set.  It does not construct a predictable projection or assert optional
sampling.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {T : NNReal}
  {source : Ω → Real} {row : Nat → Process Ω}
  {residual : Nat → Ω → Real} {sourceBound rowBound : Real}

namespace CommonHilbertRowsData

/-! ## Order extension from a right-dense skeleton -/

private theorem monotone_of_rightContinuous_of_rightDense
    {Time : Type*} [TopologicalSpace Time] [LinearOrder Time]
    [OrderTopology Time]
    (f : Time → Real) (skeleton : Nat → Time)
    (hDense : ∀ t, t ∈ closure (Set.range skeleton ∩ Set.Ici t))
    (hRight : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hSkel : ∀ i j, skeleton i ≤ skeleton j →
      f (skeleton i) ≤ f (skeleton j)) :
    Monotone f := by
  intro s t hst
  by_cases hEq : s = t
  · subst t
    exact le_rfl
  have hstlt : s < t := lt_of_le_of_ne hst hEq
  let Ds : Set Time := Set.range skeleton ∩ Set.Ici s
  let Dt : Set Time := Set.range skeleton ∩ Set.Ici t
  have hNs : NeBot (𝓝[Ds] s) := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    simpa [Ds] using hDense s
  have hNt : NeBot (𝓝[Dt] t) := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    simpa [Dt] using hDense t
  have hst_mem : ∀ᶠ u in 𝓝[Ds] s, u < t := by
    have hlt_nhds : Set.Iio t ∈ 𝓝 s := Iio_mem_nhds hstlt
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hlt_nhds
  have hfu : Tendsto f (𝓝[Ds] s) (𝓝 (f s)) := by
    apply (hRight s).mono
    exact Set.inter_subset_right
  have hfv : Tendsto f (𝓝[Dt] t) (𝓝 (f t)) := by
    apply (hRight t).mono
    exact Set.inter_subset_right
  have hfu_le : ∀ᶠ u in 𝓝[Ds] s, f u ≤ f t := by
    have hmemDs : ∀ᶠ u in 𝓝[Ds] s, u ∈ Ds := self_mem_nhdsWithin
    filter_upwards [hst_mem, hmemDs] with u hu hU
    rcases hU.1 with ⟨i, rfl⟩
    have hfu' : f (skeleton i) ≤ f t := by
      have horder : ∀ᶠ v in 𝓝[Dt] t, f (skeleton i) ≤ f v := by
        filter_upwards [self_mem_nhdsWithin] with v hv
        rcases hv.1 with ⟨j, rfl⟩
        exact hSkel i j (hu.le.trans hv.2)
      exact ge_of_tendsto hfv horder
    exact hfu'
  exact le_of_tendsto hfu hfu_le

private theorem nonnegative_of_rightContinuous_of_rightDense
    {Time : Type*} [TopologicalSpace Time] [LinearOrder Time]
    [OrderTopology Time]
    (f : Time → Real) (skeleton : Nat → Time)
    (hDense : ∀ t, t ∈ closure (Set.range skeleton ∩ Set.Ici t))
    (hRight : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hSkel : ∀ i, 0 ≤ f (skeleton i)) :
    ∀ t, 0 ≤ f t := by
  intro t
  let D : Set Time := Set.range skeleton ∩ Set.Ici t
  have hN : NeBot (𝓝[D] t) := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    simpa [D] using hDense t
  have hft : Tendsto f (𝓝[D] t) (𝓝 (f t)) := by
    apply (hRight t).mono
    exact Set.inter_subset_right
  have hnonneg : ∀ᶠ u in 𝓝[D] t, 0 ≤ f u := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rcases hu.1 with ⟨i, rfl⟩
    exact hSkel i
  exact ge_of_tendsto hft hnonneg

/-! ## A common full-measure constant-after set -/

omit [IsProbabilityMeasure mu] in
private theorem cadlagCandidate_constant_after_common_ae
    {h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound}
    {w : ∀ n, TailConvexWeights n}
    {y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal)}
    {hCommon : CommonHilbertConvexificationData h w y}
    {source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu}
    {X : Process Ω}
    {hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X}
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad) :
    ∀ᵐ omega ∂mu, ∀ t, T ≤ t → Pcad t omega = Pcad T omega := by
  let Pstop : Process Ω :=
    MeasureTheory.stoppedProcess Pcad (fun _ : Ω => (T : WithTop NNReal))
  have hPstopRight : ∀ omega t,
      ContinuousWithinAt (Pstop · omega) (Ici t) t := by
    intro omega t
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      Pcad hCad.Pcad_rightContinuous omega t
  have hEqSkeleton : ∀ k,
      Pcad (NNRealRightDenseSkeleton.skeleton k) =ᵐ[mu]
        Pstop (NNRealRightDenseSkeleton.skeleton k) := by
    intro k
    let s := NNRealRightDenseSkeleton.skeleton k
    by_cases hs : s ≤ T
    · filter_upwards [] with omega
      change Pcad s omega =
        MeasureTheory.stoppedProcess Pcad
          (fun _ : Ω => (T : WithTop NNReal)) s omega
      change Pcad s omega = Pcad (min s T) omega
      rw [min_eq_left hs]
    · have hTs : T ≤ s := le_of_not_ge hs
      filter_upwards [hCad.Pcad_constant_after s hTs] with omega hω
      change Pcad s omega =
        MeasureTheory.stoppedProcess Pcad
          (fun _ : Ω => (T : WithTop NNReal)) s omega
      change Pcad s omega = Pcad (min s T) omega
      rw [min_eq_right hTs]
      exact hω
  have hIndist : ProcessIndistinguishable mu Pcad Pstop :=
    ProcessIndistinguishable.of_ae_eq_on_rightDense Pcad Pstop
      NNRealRightDenseSkeleton.skeleton
      NNRealRightDenseSkeleton.skeleton_rightDense
      (Filter.Eventually.of_forall hCad.Pcad_rightContinuous)
      (Filter.Eventually.of_forall hPstopRight)
      hEqSkeleton
  filter_upwards [hIndist] with omega hω
  intro t ht
  have hStop := hω t
  change Pcad t omega = Pcad (min t T) omega at hStop
  rw [min_eq_right ht] at hStop
  exact hStop

/-! ## The source-independent certificate -/

structure CadlagMonotoneRegularizationData
    {h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound}
    {w : ∀ n, TailConvexWeights n}
    {y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)}
    {hCommon : CommonHilbertConvexificationData h w y}
    {source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu}
    {X : Process Ω}
    {hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X}
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω) : Prop where
  bad_null : mu bad = 0
  bad_measurable : MeasurableSet[F 0] bad
  Preg_eq_zeroOn : Preg = ProcessNullSetRegularization.zeroOn bad Pcad
  Preg_stronglyAdapted : StronglyAdapted F Preg
  Preg_adapted : Adapted F Preg
  Preg_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Preg · omega) (Ici t) t
  Preg_leftLimits : ProcessHasLeftLimits Preg
  Preg_nonnegative : ∀ omega t, 0 ≤ Preg t omega
  Preg_monotone : ∀ omega, Monotone (Preg · omega)
  Preg_zero : Preg 0 = 0
  Preg_constant_after : ∀ omega t, T ≤ t →
    Preg t omega = Preg T omega
  Preg_indistinguishable : ProcessIndistinguishable mu Preg Pcad

/-! ## Candidate regularization -/

omit [IsProbabilityMeasure mu] in
theorem exists_cadlagMonotoneRegularization
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y)
    (source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu)
    (X : Process Ω)
    (hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    (cutoff : Nat → Nat)
    (hData : CommonAESubsequenceData h w y hCommon cutoff)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ (bad : Set Ω) (Preg : Process Ω),
      CadlagMonotoneRegularizationData hCad bad Preg := by
  have hCoordinateNonnegative (n j : Nat) :
      0 ≤ h.convexCoordinateToLp (w (cutoff n)) j := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hCommon.skeleton_coordinate_coeFn_ae (cutoff n) j]
      with omega hOmega
    rw [hOmega]
    exact hData.row_nonnegative n
      (stoppedLimitSkeleton T j).1 omega
  have hLimitNonnegative (j : Nat) :
      0 ≤ h.coordinateLimit y (j + 1) := by
    have hTendsto : Tendsto
        (fun n => h.convexCoordinateToLp (w (cutoff n)) j) atTop
        (𝓝 (h.coordinateLimit y (j + 1))) :=
      (hCommon.skeleton_coordinate_tendsto j).comp
        hData.cutoff_strictMono.tendsto_atTop
    apply ge_of_tendsto hTendsto
    exact Filter.Eventually.of_forall (fun n => hCoordinateNonnegative n j)
  have hLimitNonnegativeAE (j : Nat) :
      0 ≤ᵐ[mu] (h.coordinateLimit y (j + 1) : Ω → Real) :=
    (Lp.coeFn_nonneg _).mpr (hLimitNonnegative j)
  have hCoordinateLe (n i j : Nat)
      (hij : (stoppedLimitSkeleton T i).1 ≤
        (stoppedLimitSkeleton T j).1) :
      h.convexCoordinateToLp (w (cutoff n)) i ≤
        h.convexCoordinateToLp (w (cutoff n)) j := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hCommon.skeleton_coordinate_coeFn_ae (cutoff n) i,
      hCommon.skeleton_coordinate_coeFn_ae (cutoff n) j] with omega hI hJ
    rw [hI, hJ]
    exact hData.row_mono n omega hij
  have hLimitLe (i j : Nat)
      (hij : (stoppedLimitSkeleton T i).1 ≤
        (stoppedLimitSkeleton T j).1) :
      h.coordinateLimit y (i + 1) ≤
        h.coordinateLimit y (j + 1) := by
    have hTi : Tendsto
        (fun n => h.convexCoordinateToLp (w (cutoff n)) i) atTop
        (𝓝 (h.coordinateLimit y (i + 1))) :=
      (hCommon.skeleton_coordinate_tendsto i).comp
        hData.cutoff_strictMono.tendsto_atTop
    have hTj : Tendsto
        (fun n => h.convexCoordinateToLp (w (cutoff n)) j) atTop
        (𝓝 (h.coordinateLimit y (j + 1))) :=
      (hCommon.skeleton_coordinate_tendsto j).comp
        hData.cutoff_strictMono.tendsto_atTop
    apply le_of_tendsto_of_tendsto hTi hTj
    exact Filter.Eventually.of_forall (fun n => hCoordinateLe n i j hij)
  have hLimitLeAE (i j : Nat)
      (hij : (stoppedLimitSkeleton T i).1 ≤
        (stoppedLimitSkeleton T j).1) :
      (h.coordinateLimit y (i + 1) : Ω → Real) ≤ᵐ[mu]
        (h.coordinateLimit y (j + 1) : Ω → Real) :=
    (Lp.coeFn_le _ _).mpr (hLimitLe i j hij)
  have hSkeletonNonnegative : ∀ᵐ omega ∂mu, ∀ j,
      0 ≤ Pcad (stoppedLimitSkeleton T j).1 omega := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hCad.Pcad_skeleton j, hLimitNonnegativeAE j]
      with omega hP hL
    exact hP ▸ hL
  have hSkeletonMonotone : ∀ᵐ omega ∂mu, ∀ i j,
      (stoppedLimitSkeleton T i).1 ≤
        (stoppedLimitSkeleton T j).1 →
        Pcad (stoppedLimitSkeleton T i).1 omega ≤
          Pcad (stoppedLimitSkeleton T j).1 omega := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : (stoppedLimitSkeleton T i).1 ≤
        (stoppedLimitSkeleton T j).1
    · filter_upwards [hCad.Pcad_skeleton i, hCad.Pcad_skeleton j,
        hLimitLeAE i j hij] with omega hI hJ hL
      exact (by
        simpa only [hij, true_implies] using (hI ▸ hJ ▸ hL))
    · simp [hij]
  have hConstantAfter :
      ∀ᵐ omega ∂mu, ∀ t, T ≤ t → Pcad t omega = Pcad T omega :=
    cadlagCandidate_constant_after_common_ae hCad
  have hGood : ∀ᵐ omega ∂mu,
      (∀ j, 0 ≤ Pcad (stoppedLimitSkeleton T j).1 omega) ∧
      (∀ i j, (stoppedLimitSkeleton T i).1 ≤
        (stoppedLimitSkeleton T j).1 →
        Pcad (stoppedLimitSkeleton T i).1 omega ≤
          Pcad (stoppedLimitSkeleton T j).1 omega) ∧
      Pcad 0 omega = 0 ∧
      (∀ t, T ≤ t → Pcad t omega = Pcad T omega) := by
    filter_upwards [hSkeletonNonnegative, hSkeletonMonotone,
      hCad.Pcad_zero, hConstantAfter] with omega hNonnegative hMono
        hZero hAfter
    exact ⟨hNonnegative, hMono, hZero, hAfter⟩
  let good : Set Ω := {omega |
    (∀ j, 0 ≤ Pcad (stoppedLimitSkeleton T j).1 omega) ∧
    (∀ i j, (stoppedLimitSkeleton T i).1 ≤
      (stoppedLimitSkeleton T j).1 →
      Pcad (stoppedLimitSkeleton T i).1 omega ≤
        Pcad (stoppedLimitSkeleton T j).1 omega) ∧
    Pcad 0 omega = 0 ∧
    (∀ t, T ≤ t → Pcad t omega = Pcad T omega)}
  let bad : Set Ω := {omega | ¬good omega}
  have hGood' : ∀ᵐ omega ∂mu, good omega := by
    dsimp [good]
    exact hGood
  have hbadNull : mu bad = 0 := by
    simpa only [bad] using (ae_iff.mp hGood')
  have hbadMeasurable : MeasurableSet[F 0] bad :=
    hUsual.containsNullSetsAtZero bad hbadNull
  have hGoodOff : ∀ omega, omega ∉ bad → good omega := by
    intro omega hOmega
    simpa only [bad, Set.mem_ofPred_eq, not_not] using hOmega
  have hNonnegativeOnIic : ∀ omega, good omega → ∀ t, t ≤ T →
      0 ≤ Pcad t omega := by
    intro omega hOmega t ht
    let f : Set.Iic T → Real := fun s => Pcad s.1 omega
    have hRightSub : ∀ s : Set.Iic T,
        ContinuousWithinAt f (Set.Ici s) s := by
      intro s
      have hVal : ContinuousWithinAt (fun u : Set.Iic T => (u : NNReal))
          (Set.Ici s) s := by
        exact continuous_subtype_val.continuousAt.continuousWithinAt
      have hMaps : MapsTo (fun u : Set.Iic T => (u : NNReal))
          (Set.Ici s) (Set.Ici (s : NNReal)) := by
        intro u hu
        exact hu
      have hComp := (hCad.Pcad_rightContinuous omega s.1).comp
        hVal hMaps
      change ContinuousWithinAt
        ((fun x => Pcad x omega) ∘ Subtype.val) (Set.Ici s) s
      exact hComp
    have hNonnegativeSub : ∀ s : Set.Iic T, 0 ≤ f s := by
      intro s
      have hNonnegative := nonnegative_of_rightContinuous_of_rightDense f
        (stoppedLimitSkeleton T) hCommon.skeleton_rightDense hRightSub
        (fun j => by exact hOmega.1 j) s
      exact hNonnegative
    exact hNonnegativeSub ⟨t, ht⟩
  have hNonnegativeAll : ∀ omega, good omega → ∀ t, 0 ≤ Pcad t omega := by
    intro omega hOmega t
    by_cases ht : t ≤ T
    · exact hNonnegativeOnIic omega hOmega t ht
    · have hTt : T ≤ t := le_of_not_ge ht
      rw [hOmega.2.2.2 t hTt]
      exact hNonnegativeOnIic omega hOmega T le_rfl
  have hMonotoneOnIic : ∀ omega, good omega → ∀ s t, s ≤ T → t ≤ T →
      s ≤ t → Pcad s omega ≤ Pcad t omega := by
    intro omega hOmega s t hs ht hst
    let f : Set.Iic T → Real := fun u => Pcad u.1 omega
    have hRightSub : ∀ u : Set.Iic T,
        ContinuousWithinAt f (Set.Ici u) u := by
      intro u
      have hVal : ContinuousWithinAt (fun z : Set.Iic T => (z : NNReal))
          (Set.Ici u) u := by
        exact continuous_subtype_val.continuousAt.continuousWithinAt
      have hMaps : MapsTo (fun z : Set.Iic T => (z : NNReal))
          (Set.Ici u) (Set.Ici (u : NNReal)) := by
        intro z hz
        exact hz
      have hComp := (hCad.Pcad_rightContinuous omega u.1).comp
        hVal hMaps
      change ContinuousWithinAt
        ((fun x => Pcad x omega) ∘ Subtype.val) (Set.Ici u) u
      exact hComp
    have hMonotoneSub : Monotone f :=
      monotone_of_rightContinuous_of_rightDense f
        (stoppedLimitSkeleton T) hCommon.skeleton_rightDense hRightSub
        (fun i j hij => hOmega.2.1 i j hij)
    change f ⟨s, hs⟩ ≤ f ⟨t, ht⟩
    exact hMonotoneSub hst
  have hMonotoneAll : ∀ omega, good omega →
      Monotone (Pcad · omega) := by
    intro omega hOmega s t hst
    by_cases hs : s ≤ T
    · by_cases ht : t ≤ T
      · exact hMonotoneOnIic omega hOmega s t hs ht hst
      · have hTt : T ≤ t := le_of_not_ge ht
        calc
          Pcad s omega ≤ Pcad T omega :=
            hMonotoneOnIic omega hOmega s T hs le_rfl hs
          _ = Pcad t omega := (hOmega.2.2.2 t hTt).symm
    · have hTs : T ≤ s := le_of_not_ge hs
      have hTt : T ≤ t := hTs.trans hst
      change Pcad s omega ≤ Pcad t omega
      rw [hOmega.2.2.2 s hTs, hOmega.2.2.2 t hTt]
  let Preg : Process Ω :=
    ProcessNullSetRegularization.zeroOn bad Pcad
  have hPregStrong : StronglyAdapted F Preg := by
    dsimp [Preg]
    exact ProcessNullSetRegularization.stronglyAdapted_zeroOn
      hbadMeasurable hCad.Pcad_stronglyAdapted
  have hPregRight : ∀ omega t,
      ContinuousWithinAt (Preg · omega) (Ici t) t := by
    dsimp [Preg]
    apply ProcessNullSetRegularization.zeroOn_isRightContinuous
    intro omega hOmega
    exact hCad.Pcad_rightContinuous omega
  have hPregLeft : ProcessHasLeftLimits Preg := by
    dsimp [Preg]
    apply ProcessNullSetRegularization.zeroOn_hasLeftLimits
    intro omega hOmega t
    exact hCad.Pcad_leftLimits omega t
  have hPregNonnegative : ∀ omega t, 0 ≤ Preg t omega := by
    intro omega t
    by_cases hOmega : omega ∈ bad
    · simp [Preg, hOmega]
    · rw [show Preg t omega = Pcad t omega by
        simp [Preg, hOmega]]
      exact hNonnegativeAll omega (hGoodOff omega hOmega) t
  have hPregMonotone : ∀ omega, Monotone (Preg · omega) := by
    intro omega s t hst
    by_cases hOmega : omega ∈ bad
    · simp [Preg, hOmega]
    · change Preg s omega ≤ Preg t omega
      calc
        Preg s omega = Pcad s omega := by simp [Preg, hOmega]
        _ ≤ Pcad t omega := hMonotoneAll omega (hGoodOff omega hOmega) hst
        _ = Preg t omega := by simp [Preg, hOmega]
  have hPregZero : Preg 0 = 0 := by
    funext omega
    by_cases hOmega : omega ∈ bad
    · simp [Preg, hOmega]
    · simp [Preg, hOmega, (hGoodOff omega hOmega).2.2.1]
  have hPregConstantAfter : ∀ omega t, T ≤ t →
      Preg t omega = Preg T omega := by
    intro omega t ht
    by_cases hOmega : omega ∈ bad
    · simp [Preg, hOmega]
    · simp [Preg, hOmega, (hGoodOff omega hOmega).2.2.2 t ht]
  refine ⟨bad, Preg, {
    bad_null := hbadNull
    bad_measurable := hbadMeasurable
    Preg_eq_zeroOn := by rfl
    Preg_stronglyAdapted := hPregStrong
    Preg_adapted := hPregStrong.adapted
    Preg_rightContinuous := hPregRight
    Preg_leftLimits := hPregLeft
    Preg_nonnegative := hPregNonnegative
    Preg_monotone := hPregMonotone
    Preg_zero := hPregZero
    Preg_constant_after := hPregConstantAfter
    Preg_indistinguishable := by
      exact ProcessNullSetRegularization.zeroOn_indistinguishable
        hbadNull Pcad }⟩

end CommonHilbertRowsData

end HorizonFactorialGrid

end FTAPTheorem42
