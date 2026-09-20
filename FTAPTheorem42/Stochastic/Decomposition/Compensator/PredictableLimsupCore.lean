/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonAESubsequenceCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagMonotoneRegularizationCore

/-!
# Source-independent predictable limsup of compensator rows

This file contains the dense-path argument for the pointwise limsup of the
common tail-convex rows.  It only uses the common Hilbert row interface, the
common almost-everywhere diagonal, and the càdlàg monotone regularization.
Source-specific bounds, finite-grid projection, optional sampling, and the
process bridge are deliberately absent.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {T : NNReal}
  {source : Ω → Real} {row : Nat → Process Ω}
  {residual : Nat → Ω → Real} {sourceBound rowBound : Real}

namespace CommonHilbertRowsData

/-! ## Deterministic dense-path lemmas -/

theorem dense_of_rightDense_from_right
    {Time : Type*} [TopologicalSpace Time] [LinearOrder Time]
    {D : Set Time}
    (hDense : ∀ t, t ∈ closure (D ∩ Set.Ici t)) : Dense D := by
  intro t
  exact closure_mono inter_subset_left (hDense t)

theorem limsup_le_of_monotone_of_rightDense
    {Time : Type*} [TopologicalSpace Time] [LinearOrder Time]
    [OrderTopology Time]
    (u : Nat → Time → Real) (f : Time → Real) (D : Set Time)
    (hDense : ∀ t, t ∈ closure (D ∩ Set.Ici t))
    (hRight : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hMono : ∀ n, Monotone (u n))
    (hLower : ∀ n t, 0 ≤ u n t)
    (hConv : ∀ q, q ∈ D →
      Tendsto (fun n => u n q) atTop (𝓝 (f q))) :
    ∀ t, limsup (fun n => u n t) atTop ≤ f t := by
  intro t
  let Dt : Set Time := D ∩ Set.Ici t
  have hNt : NeBot (𝓝[Dt] t) := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    simpa only [Dt] using hDense t
  have hDtNonempty : Dt.Nonempty :=
    hNt.nonempty_of_mem self_mem_nhdsWithin
  obtain ⟨q, hqD, hqt⟩ := hDtNonempty
  have hBound : IsBoundedUnder (· ≤ ·) atTop (fun n => u n t) := by
    have hqUpper : ∀ᶠ n in atTop, u n q ≤ f q + 1 :=
      ((tendsto_order.1 (hConv q hqD)).2 (f q + 1) (by linarith)).mono
        (fun _ h => h.le)
    have htUpper : ∀ᶠ n in atTop, u n t ≤ f q + 1 := by
      filter_upwards [hqUpper] with n hn
      exact (hMono n hqt).trans hn
    exact isBoundedUnder_of_eventually_le htUpper
  have hUpperEps : ∀ ε : Real, 0 < ε →
      limsup (fun n => u n t) atTop ≤ f t + ε := by
    intro ε hε
    have hDenseFilter : ∀ᶠ q in 𝓝[Dt] t,
        limsup (fun n => u n t) atTop ≤ f q + ε := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      have hqUpper : ∀ᶠ n in atTop, u n q < f q + ε :=
        (tendsto_order.1 (hConv q hq.1)).2 (f q + ε) (by linarith)
      have htUpper : ∀ᶠ n in atTop, u n t ≤ f q + ε := by
        filter_upwards [hqUpper] with n hn
        exact (hMono n hq.2).trans hn.le
      exact limsup_le_of_le
        (isCoboundedUnder_le_of_le atTop (fun n => hLower n t)) htUpper
    have hRightLimit : Tendsto (fun q => f q + ε)
        (𝓝[Dt] t) (𝓝 (f t + ε)) := by
      exact ((hRight t).mono inter_subset_right).tendsto.add
        tendsto_const_nhds
    exact ge_of_tendsto hRightLimit hDenseFilter
  exact le_of_forall_pos_le_add hUpperEps

theorem limsup_eq_of_monotone_of_rightDense_of_leftDense
    {Time : Type*} [TopologicalSpace Time] [LinearOrder Time]
    [OrderTopology Time] [OrderBot Time] [DenselyOrdered Time]
    [FirstCountableTopology Time]
    (u : Nat → Time → Real) (f : Time → Real) (D : Set Time)
    (hDense : ∀ t, t ∈ closure (D ∩ Set.Ici t))
    (hLeftDense : ∀ t, t ≠ (⊥ : Time) →
      t ∈ closure (D ∩ Set.Iic t))
    (hRight : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hMono : ∀ n, Monotone (u n))
    (hLower : ∀ n t, 0 ≤ u n t)
    (hConv : ∀ q, q ∈ D →
      Tendsto (fun n => u n q) atTop (𝓝 (f q)))
    (hAtBot : limsup (fun n => u n (⊥ : Time)) atTop = f ⊥) :
    ∀ t, ContinuousAt f t →
      limsup (fun n => u n t) atTop = f t := by
  intro t ht
  apply le_antisymm
  · exact limsup_le_of_monotone_of_rightDense u f D hDense hRight hMono hLower hConv t
  · by_cases htbot : t = (⊥ : Time)
    · subst t
      exact hAtBot.symm.le
    · let Dt : Set Time := D ∩ Set.Iic t
      have hNt : NeBot (𝓝[Dt] t) := by
        apply mem_closure_iff_nhdsWithin_neBot.mp
        simpa only [Dt] using hLeftDense t htbot
      have hBound : IsBoundedUnder (· ≤ ·) atTop (fun n => u n t) := by
        let Dr : Set Time := D ∩ Set.Ici t
        have hNr : NeBot (𝓝[Dr] t) := by
          apply mem_closure_iff_nhdsWithin_neBot.mp
          simpa only [Dr] using hDense t
        obtain ⟨q, hqD, hqt⟩ := hNr.nonempty_of_mem self_mem_nhdsWithin
        have hqUpper : ∀ᶠ n in atTop, u n q ≤ f q + 1 :=
          ((tendsto_order.1 (hConv q hqD)).2 (f q + 1) (by linarith)).mono
            (fun _ h => h.le)
        have htUpper : ∀ᶠ n in atTop, u n t ≤ f q + 1 := by
          filter_upwards [hqUpper] with n hn
          exact (hMono n hqt).trans hn
        exact isBoundedUnder_of_eventually_le htUpper
      have hLowerFilter : ∀ᶠ q in 𝓝[Dt] t,
          f q ≤ limsup (fun n => u n t) atTop := by
        filter_upwards [self_mem_nhdsWithin] with q hq
        have hqCobounded : IsCoboundedUnder (· ≤ ·) atTop
            (fun n => u n q) :=
          isCoboundedUnder_le_of_le atTop (fun n => hLower n q)
        have hLimsupMono : limsup (fun n => u n q) atTop ≤
            limsup (fun n => u n t) atTop :=
          limsup_le_limsup
            (Filter.Eventually.of_forall fun n => hMono n hq.2)
            hqCobounded hBound
        rw [(hConv q hq.1).limsup_eq] at hLimsupMono
        exact hLimsupMono
      have hLeftLimit : Tendsto f (𝓝[Dt] t) (𝓝 (f t)) := by
        exact ht.tendsto.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto hLeftLimit hLowerFilter

/-! ## The raw predictable limsup -/

noncomputable def predictableLimsup
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n) (cutoff : Nat → Nat) : Process Ω :=
  fun t omega => limsup (fun n =>
    h.convexRow (w (cutoff n)) t omega) atTop

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem predictableLimsup_isStronglyPredictable
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n) (cutoff : Nat → Nat)
    (hRow : ∀ n, IsStronglyPredictable F
      (h.convexRow (w (cutoff n)))) :
    IsStronglyPredictable F (predictableLimsup h w cutoff) := by
  apply Measurable.stronglyMeasurable
  exact Measurable.limsup fun n => (hRow n).measurable

theorem leftDense_of_dense
    {Time : Type*} [TopologicalSpace Time] [LinearOrder Time]
    [OrderTopology Time] [OrderBot Time] [DenselyOrdered Time]
    [FirstCountableTopology Time]
    {D : Set Time} (hDense : Dense D) :
    ∀ t, t ≠ (⊥ : Time) → t ∈ closure (D ∩ Set.Iic t) := by
  intro t ht
  have hbotlt : (⊥ : Time) < t := by
    exact lt_of_le_of_ne bot_le (Ne.symm ht)
  obtain ⟨u, huMono, huMem, huTendsto⟩ :=
    hDense.exists_seq_strictMono_tendsto_of_lt hbotlt
  have huEventually : ∀ᶠ n in atTop, u n ∈ D ∩ Set.Iic t := by
    filter_upwards [] with n
    exact ⟨huMem n |>.2, (huMem n |>.1).2.le⟩
  exact mem_closure_of_tendsto huTendsto huEventually

/-! ## The common diagonal limsup certificate -/

structure PredictableLimsupData
    {h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound}
    {w : ∀ n, TailConvexWeights n}
    {y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)}
    {hCommon : CommonHilbertConvexificationData h w y}
    {source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu}
    {X : Process Ω}
    {hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X}
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    {bad : Set Ω} {Preg : Process Ω}
    (hReg : CadlagMonotoneRegularizationData hCad bad Preg)
    (cutoff : Nat → Nat)
    (hData : CommonAESubsequenceData h w y hCommon cutoff)
    (Ppred : Process Ω) : Prop where
  Ppred_definition : Ppred = predictableLimsup h w cutoff
  Ppred_isStronglyPredictable : IsStronglyPredictable F Ppred
  Ppred_le_Preg : ∀ᵐ omega ∂mu, ∀ t, Ppred t omega ≤ Preg t omega
  Ppred_eq_Preg_at_continuity : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
    ContinuousAt (Preg · omega) t → Ppred t omega = Preg t omega
  Ppred_zero : Ppred 0 = 0
  Ppred_constant_after : ∀ᵐ omega ∂mu, ∀ t, T ≤ t →
    Ppred t omega = Ppred T omega

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem exists_predictableLimsup
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y)
    (cutoff : Nat → Nat)
    (hData : CommonAESubsequenceData h w y hCommon cutoff)
    (source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu)
    (X : Process Ω)
    (hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : CadlagMonotoneRegularizationData hCad bad Preg) :
    PredictableLimsupData hCad hReg cutoff hData
      (predictableLimsup h w cutoff) := by
  have hRawPredictable : IsStronglyPredictable F
      (predictableLimsup h w cutoff) :=
    predictableLimsup_isStronglyPredictable h w cutoff
      hData.row_isStronglyPredictable
  have hPregSkeleton (j : Nat) :
      Preg (stoppedLimitSkeleton T j).1 =ᵐ[mu]
        (h.coordinateLimit y (j + 1) : Ω → Real) := by
    exact (hReg.Preg_indistinguishable.eventuallyEq_at
      (stoppedLimitSkeleton T j).1).trans (hCad.Pcad_skeleton j)
  have hSkeletonToPreg : ∀ᵐ omega ∂mu, ∀ j,
      Tendsto
        (fun n => h.convexRow (w (cutoff n))
            (stoppedLimitSkeleton T j).1 omega) atTop
        (𝓝 (Preg (stoppedLimitSkeleton T j).1 omega)) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hData.skeleton_tendstoAE j, hPregSkeleton j]
      with omega hConv hTarget
    simpa only [hTarget] using hConv
  have hUpperSub : ∀ᵐ omega ∂mu, ∀ t : Set.Iic T,
      (limsup (fun n => h.convexRow (w (cutoff n)) t.1 omega) atTop) ≤
        Preg t.1 omega := by
    filter_upwards [hSkeletonToPreg] with omega hConv
    intro t
    let u : Nat → Set.Iic T → Real := fun n s =>
      h.convexRow (w (cutoff n)) s.1 omega
    let f : Set.Iic T → Real := fun s => Preg s.1 omega
    have hRight : ∀ s : Set.Iic T,
        ContinuousWithinAt f (Set.Ici s) s := by
      intro s
      have hVal : ContinuousWithinAt
          (fun q : Set.Iic T => (q : NNReal)) (Set.Ici s) s := by
        exact continuous_subtype_val.continuousAt.continuousWithinAt
      have hMaps : MapsTo (fun q : Set.Iic T => (q : NNReal))
          (Set.Ici s) (Set.Ici (s : NNReal)) := by
        intro q hq
        exact hq
      have hComp := (hReg.Preg_rightContinuous omega s.1).comp
        hVal hMaps
      change ContinuousWithinAt
        ((fun q : NNReal => Preg q omega) ∘ Subtype.val)
          (Set.Ici s) s
      exact hComp
    have hMono : ∀ n, Monotone (u n) := by
      intro n s t hst
      exact hData.row_mono n omega hst
    have hLower : ∀ n s, 0 ≤ u n s := by
      intro n s
      exact hData.row_nonnegative n s.1 omega
    have hConv' : ∀ q, q ∈ Set.range (stoppedLimitSkeleton T) →
        Tendsto (fun n => u n q) atTop (𝓝 (f q)) := by
      rintro q ⟨j, rfl⟩
      exact hConv j
    exact limsup_le_of_monotone_of_rightDense
      u f (Set.range (stoppedLimitSkeleton T))
      hCommon.skeleton_rightDense hRight hMono hLower hConv' t
  have hUpper : ∀ᵐ omega ∂mu, ∀ t,
      predictableLimsup h w cutoff t omega ≤ Preg t omega := by
    filter_upwards [hUpperSub] with omega hUpperSubOmega
    intro t
    by_cases ht : t ≤ T
    · exact hUpperSubOmega ⟨t, ht⟩
    · have hTt : T ≤ t := le_of_not_ge ht
      have hRawAfter : predictableLimsup h w cutoff t omega =
          predictableLimsup h w cutoff T omega := by
        dsimp [predictableLimsup]
        apply limsup_congr
        exact Filter.Eventually.of_forall fun n =>
          hData.row_constant_after n omega t hTt
      rw [hRawAfter, hReg.Preg_constant_after omega t hTt]
      exact hUpperSubOmega ⟨T, Set.mem_Iic.mpr le_rfl⟩
  have hEqualitySub : ∀ᵐ omega ∂mu, ∀ t : Set.Iic T,
      ContinuousAt (fun s : Set.Iic T => Preg s.1 omega) t →
        (limsup (fun n => h.convexRow (w (cutoff n)) t.1 omega) atTop) =
          Preg t.1 omega := by
    filter_upwards [hSkeletonToPreg] with omega hConv
    intro t ht
    let u : Nat → Set.Iic T → Real := fun n s =>
      h.convexRow (w (cutoff n)) s.1 omega
    let f : Set.Iic T → Real := fun s => Preg s.1 omega
    have hRight : ∀ s : Set.Iic T,
        ContinuousWithinAt f (Set.Ici s) s := by
      intro s
      have hVal : ContinuousWithinAt
          (fun q : Set.Iic T => (q : NNReal)) (Set.Ici s) s := by
        exact continuous_subtype_val.continuousAt.continuousWithinAt
      have hMaps : MapsTo (fun q : Set.Iic T => (q : NNReal))
          (Set.Ici s) (Set.Ici (s : NNReal)) := by
        intro q hq
        exact hq
      have hComp := (hReg.Preg_rightContinuous omega s.1).comp
        hVal hMaps
      change ContinuousWithinAt
        ((fun q : NNReal => Preg q omega) ∘ Subtype.val)
          (Set.Ici s) s
      exact hComp
    have hMono : ∀ n, Monotone (u n) := by
      intro n s t hst
      exact hData.row_mono n omega hst
    have hLower : ∀ n s, 0 ≤ u n s := by
      intro n s
      exact hData.row_nonnegative n s.1 omega
    have hConv' : ∀ q, q ∈ Set.range (stoppedLimitSkeleton T) →
        Tendsto (fun n => u n q) atTop (𝓝 (f q)) := by
      rintro q ⟨j, rfl⟩
      exact hConv j
    have hLeftDense := leftDense_of_dense
      (dense_of_rightDense_from_right hCommon.skeleton_rightDense)
    have hAtBot : limsup (fun n => u n (⊥ : Set.Iic T)) atTop =
        f (⊥ : Set.Iic T) := by
      have hRowZero : ∀ n, u n (⊥ : Set.Iic T) = 0 := by
        intro n
        have hZero := congrFun (hData.row_zero n) omega
        simpa [u] using hZero
      have hPregZero : f (⊥ : Set.Iic T) = 0 := by
        have hZero := congrFun hReg.Preg_zero omega
        simpa [f] using hZero
      rw [show (fun n => u n (⊥ : Set.Iic T)) = (fun _ => 0) by
        funext n; exact hRowZero n]
      simp [hPregZero]
    exact limsup_eq_of_monotone_of_rightDense_of_leftDense
      u f (Set.range (stoppedLimitSkeleton T))
      hCommon.skeleton_rightDense hLeftDense hRight hMono hLower hConv' hAtBot t ht
  have hEquality : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      ContinuousAt (Preg · omega) t →
      predictableLimsup h w cutoff t omega = Preg t omega := by
    filter_upwards [hEqualitySub] with omega hEq
    intro t ht hCont
    have hContSub : ContinuousAt
        (fun s : Set.Iic T => Preg s.1 omega) ⟨t, ht⟩ := by
      change ContinuousAt
        ((fun q : NNReal => Preg q omega) ∘ Subtype.val) ⟨t, ht⟩
      exact hCont.comp continuous_subtype_val.continuousAt
    exact hEq ⟨t, ht⟩ hContSub
  have hZero : (predictableLimsup h w cutoff) 0 = 0 := by
    funext omega
    dsimp [predictableLimsup]
    have hRowsZero : ∀ n, h.convexRow (w (cutoff n)) 0 omega = 0 := by
      intro n
      exact congrFun (hData.row_zero n) omega
    rw [show (fun n => h.convexRow (w (cutoff n)) 0 omega) = (fun _ => 0) by
      funext n; exact hRowsZero n]
    simp
  have hConstantAfter : ∀ᵐ omega ∂mu, ∀ t, T ≤ t →
      predictableLimsup h w cutoff t omega =
        predictableLimsup h w cutoff T omega := by
    filter_upwards [] with omega t ht
    dsimp [predictableLimsup]
    apply limsup_congr
    exact Filter.Eventually.of_forall fun n =>
      hData.row_constant_after n omega t ht
  exact {
    Ppred_definition := rfl
    Ppred_isStronglyPredictable := hRawPredictable
    Ppred_le_Preg := hUpper
    Ppred_eq_Preg_at_continuity := hEquality
    Ppred_zero := hZero
    Ppred_constant_after := hConstantAfter }

end CommonHilbertRowsData

end HorizonFactorialGrid

end FTAPTheorem42
