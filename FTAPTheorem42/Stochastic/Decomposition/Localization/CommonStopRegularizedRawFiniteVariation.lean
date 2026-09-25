/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRawFiniteVariationDecomposition
import FTAPTheorem42.Stochastic.Decomposition.Source.RawFiniteVariationRegularizationCore
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Foundations.FiniteVariationPathMeasure

/-!
# Regularized common-stop finite variation and its Jordan components

The common-stop construction first gives a càdlàg residual and a total
variation estimate almost everywhere.  This module performs the one null-set
modification allowed by the usual conditions.  It also records the cumulative
variation and the two zero-normalized Jordan components of the resulting
pathwise finite-variation process.

The components in this file are adapted right-continuous increasing
processes.  Predictability is intentionally not part of this boundary.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

open _root_.FTAPTheorem42.FactorialChronologicalGrid

/-! ## The regularized package -/

structure CommonStopRegularizedRawDecompositionData
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
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Omega} {M : Process Omega}
    {cutoff : Nat → Nat}
    {A : Process Omega}
    (bad : Set Omega) (Atilde Aplus Aminus cumulativeVariation : Process Omega) : Prop where
  raw : CommonStopRawFiniteVariationDecompositionData
    endpoint v Z Nbar Bbar Xbar M cutoff A
  bad_null : mu bad = 0
  bad_measurable : MeasurableSet[F 0] bad
  Atilde_eq_zeroOn : Atilde = ProcessNullSetRegularization.zeroOn bad A
  Atilde_stronglyAdapted : StronglyAdapted F Atilde
  Atilde_adapted : Adapted F Atilde
  Atilde_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Atilde · omega) (Ici t) t
  Atilde_hasLeftLimits : ProcessHasLeftLimits Atilde
  Atilde_boundedVariation : ∀ omega,
    BoundedVariationOn (Atilde · omega) Set.univ
  Atilde_eVariation_bound : ∀ omega,
    eVariationOn (Atilde · omega) Set.univ ≤
      ENNReal.ofReal (commonStoppedRowsResidualVariationBound a source.bound)
  Atilde_zero : Atilde 0 = 0
  Atilde_constant_after : ∀ omega t, T ≤ t →
    Atilde t omega = Atilde T omega
  Atilde_indistinguishable : ProcessIndistinguishable mu Atilde A
  stoppedSource_indistinguishable : ProcessIndistinguishable mu
    (fun t omega => MeasureTheory.stoppedProcess S alpha t omega - S 0 omega)
    (fun t omega => M t omega + Atilde t omega)
  cumulativeVariation_eq_def : cumulativeVariation =
    localVariation Atilde
  cumulativeVariation_eq_signedMeasureVariation : ∀ t omega,
    cumulativeVariation t omega =
      (FiniteVariationPath.signedMeasure
        (Atilde_boundedVariation omega)).variation.real (Ioc 0 t)
  cumulativeVariation_stronglyAdapted : StronglyAdapted F cumulativeVariation
  cumulativeVariation_adapted : Adapted F cumulativeVariation
  cumulativeVariation_rightContinuous : ∀ omega t,
    ContinuousWithinAt (cumulativeVariation · omega) (Ici t) t
  cumulativeVariation_monotone : ∀ omega,
    Monotone (cumulativeVariation · omega)
  cumulativeVariation_zero : cumulativeVariation 0 = 0
  cumulativeVariation_constant_after : ∀ omega t, T ≤ t →
    cumulativeVariation t omega = cumulativeVariation T omega
  cumulativeVariation_totalVariation_bound : ∀ omega,
    cumulativeVariation T omega ≤
      commonStoppedRowsResidualVariationBound a source.bound
  jordanPositive_eq_def : Aplus = commonStopJordanPositive Atilde
  jordanNegative_eq_def : Aminus = commonStopJordanNegative Atilde
  jordanPositive_stronglyAdapted : StronglyAdapted F Aplus
  jordanNegative_stronglyAdapted : StronglyAdapted F Aminus
  jordanPositive_adapted : Adapted F Aplus
  jordanNegative_adapted : Adapted F Aminus
  jordanPositive_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Aplus · omega) (Ici t) t
  jordanNegative_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Aminus · omega) (Ici t) t
  jordanPositive_monotone : ∀ omega, Monotone (Aplus · omega)
  jordanNegative_monotone : ∀ omega, Monotone (Aminus · omega)
  jordanPositive_zero : Aplus 0 = 0
  jordanNegative_zero : Aminus 0 = 0
  jordanPositive_constant_after : ∀ omega t, T ≤ t →
    Aplus t omega = Aplus T omega
  jordanNegative_constant_after : ∀ omega t, T ≤ t →
    Aminus t omega = Aminus T omega
  jordan_decomposition : ∀ t omega,
    Atilde t omega = Aplus t omega - Aminus t omega
  jordanPositive_terminal_bound : ∀ omega,
    0 ≤ Aplus T omega ∧ Aplus T omega ≤
      commonStoppedRowsResidualVariationBound a source.bound
  jordanNegative_terminal_bound : ∀ omega,
    0 ≤ Aminus T omega ∧ Aminus T omega ≤
      commonStoppedRowsResidualVariationBound a source.bound

/-! ## Main regularization endpoint -/

theorem commonStop_regularizeRawDecomposition
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
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Omega} {M : Process Omega}
    {cutoff : Nat → Nat}
    {A : Process Omega}
    (hRaw : CommonStopRawFiniteVariationDecompositionData
      endpoint v Z Nbar Bbar Xbar M cutoff A) :
    ∃ (bad : Set Omega) (Atilde Aplus Aminus cumulativeVariation : Process Omega),
      CommonStopRegularizedRawDecompositionData
        (S := S) (F := F) (mu := mu) (eta := eta)
        (u := u) (selection := selection) (a := a) (T := T)
        (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
        (hUsual := hUsual) (source := source)
        (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
        (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
        endpoint bad Atilde Aplus Aminus cumulativeVariation := by
  let bad : Set Omega := {omega |
    ¬((A 0 omega = 0) ∧
      (∀ t, T ≤ t → A t omega = A T omega) ∧
      eVariationOn (A · omega) Set.univ ≤
        ENNReal.ofReal (commonStoppedRowsResidualVariationBound a source.bound))}
  have hRegular : ∀ᵐ omega ∂mu,
      (A 0 omega = 0) ∧
      (∀ t, T ≤ t → A t omega = A T omega) ∧
      eVariationOn (A · omega) Set.univ ≤
        ENNReal.ofReal (commonStoppedRowsResidualVariationBound a source.bound) := by
    filter_upwards [hRaw.zero_ae, hRaw.constant_after_ae,
      hRaw.full_variation_bound_ae] with omega hzero hconstant hbound
    exact ⟨hzero, hconstant, hbound⟩
  have hbadNull : mu bad = 0 := by
    simpa only [bad] using ae_iff.mp hRegular
  have hbadMeasurable : MeasurableSet[F 0] bad :=
    hUsual.containsNullSetsAtZero bad hbadNull
  let Atilde : Process Omega :=
    ProcessNullSetRegularization.zeroOn bad A
  have hAtildeEq : Atilde =
      ProcessNullSetRegularization.zeroOn bad A := rfl
  have hAtildeStrong : StronglyAdapted F Atilde := by
    exact ProcessNullSetRegularization.stronglyAdapted_zeroOn
      hbadMeasurable hRaw.stronglyAdapted
  have hAtildeRight : ∀ omega t,
      ContinuousWithinAt (Atilde · omega) (Ici t) t := by
    apply ProcessNullSetRegularization.zeroOn_isRightContinuous
    intro omega hω
    exact hRaw.rightContinuous omega
  have hAtildeLeft : ProcessHasLeftLimits Atilde := by
    apply ProcessNullSetRegularization.zeroOn_hasLeftLimits
    intro omega hω t
    exact hRaw.hasLeftLimits omega t
  let C : Real := commonStoppedRowsResidualVariationBound a source.bound
  have hCNonneg : 0 ≤ C := by
    dsimp [C, commonStoppedRowsResidualVariationBound]
    have ha : 0 < a := endpoint.a_pos
    positivity
  have hAtildeVariationBound : ∀ omega,
      eVariationOn (Atilde · omega) Set.univ ≤ ENNReal.ofReal C := by
    intro omega
    by_cases hω : omega ∈ bad
    · have hZeroPath : (Atilde · omega) =
          (fun _ : NNReal => (0 : Real)) := by
        funext s
        simp [Atilde, hω]
      rw [hZeroPath, eVariationOn.constant_on (by simp)]
      exact bot_le
    · have hPath : (Atilde · omega) = (A · omega) := by
        funext s
        change ProcessNullSetRegularization.zeroOn bad A s omega = A s omega
        exact ProcessNullSetRegularization.zeroOn_apply_of_notMem bad A hω
      have hRegω :
          (A 0 omega = 0) ∧
            (∀ t, T ≤ t → A t omega = A T omega) ∧
            eVariationOn (A · omega) Set.univ ≤ ENNReal.ofReal C := by
        simpa only [bad, C, Set.mem_ofPred_eq, not_not] using hω
      rw [hPath]
      exact hRegω.2.2
  have hAtildeBV : ∀ omega, BoundedVariationOn (Atilde · omega) Set.univ := by
    intro omega
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hAtildeVariationBound omega)
  have hAtildeZero : Atilde 0 = 0 := by
    funext omega
    by_cases hω : omega ∈ bad
    · simp [Atilde, hω]
    · have hRegω :
          (A 0 omega = 0) ∧
            (∀ t, T ≤ t → A t omega = A T omega) ∧
            eVariationOn (A · omega) Set.univ ≤
              ENNReal.ofReal
                (commonStoppedRowsResidualVariationBound a source.bound) := by
        simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
      simp [Atilde, hω, hRegω.1]
  have hAtildeConst : ∀ omega t, T ≤ t →
      Atilde t omega = Atilde T omega := by
    intro omega t htt
    by_cases hω : omega ∈ bad
    · simp [Atilde, hω]
    · have hRegω :
          (A 0 omega = 0) ∧
            (∀ t, T ≤ t → A t omega = A T omega) ∧
            eVariationOn (A · omega) Set.univ ≤
              ENNReal.ofReal
                (commonStoppedRowsResidualVariationBound a source.bound) := by
        simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
      change ProcessNullSetRegularization.zeroOn bad A t omega =
        ProcessNullSetRegularization.zeroOn bad A T omega
      rw [ProcessNullSetRegularization.zeroOn_apply_of_notMem bad A hω,
        ProcessNullSetRegularization.zeroOn_apply_of_notMem bad A hω]
      exact hRegω.2.1 t htt
  have hAtildeInd : ProcessIndistinguishable mu Atilde A :=
    ProcessNullSetRegularization.zeroOn_indistinguishable hbadNull A
  have hStoppedInd : ProcessIndistinguishable mu
      (fun t omega => MeasureTheory.stoppedProcess S alpha t omega - S 0 omega)
      (fun t omega => M t omega + Atilde t omega) := by
    have hRawDecomp : ProcessIndistinguishable mu
        (fun t omega => MeasureTheory.stoppedProcess S alpha t omega - S 0 omega)
        (fun t omega => M t omega + A t omega) := by
      exact Filter.Eventually.of_forall (fun omega t =>
        hRaw.source_decomposition t omega)
    have hAdd : ProcessIndistinguishable mu
        (fun t omega => M t omega + A t omega)
        (fun t omega => M t omega + Atilde t omega) := by
      exact ProcessIndistinguishable.add
        (ProcessIndistinguishable.refl mu M) hAtildeInd.symm
    exact hRawDecomp.trans hAdd
  have hCumulativeStrong : StronglyAdapted F
      (localVariation Atilde) := by
    intro t
    apply Measurable.stronglyMeasurable
    apply @FiniteVariationFactorialApproximation.measurable_variationOnFromTo_of_le
      Omega Real (F t) inferInstance inferInstance inferInstance inferInstance
      (fun s omega => Atilde s omega) t
    · intro s hst
      exact (hAtildeStrong.stronglyMeasurable_le hst).measurable
    · exact hAtildeRight
  have hCumulativeRight : ∀ omega t,
      ContinuousWithinAt (localVariation Atilde · omega)
        (Ici t) t := by
    exact commonStopCumulativeVariation_rightContinuous hAtildeBV hAtildeRight
  have hCumulativeMono : ∀ omega,
      Monotone (localVariation Atilde · omega) :=
    commonStopCumulativeVariation_monotone hAtildeBV
  have hCumulativeZero :
      localVariation Atilde 0 = 0 :=
    commonStopCumulativeVariation_zero Atilde
  have hCumulativeConst : ∀ omega t, T ≤ t →
      localVariation Atilde t omega =
        localVariation Atilde T omega := by
    exact commonStopCumulativeVariation_constant_after hAtildeBV hAtildeConst
  have hCumulativeBound : ∀ omega,
      localVariation Atilde T omega ≤ C := by
    intro omega
    by_cases hω : omega ∈ bad
    · have hZero : localVariation Atilde T omega = 0 := by
        dsimp [localVariation]
        rw [show (fun s => Atilde s omega) =
            (fun _ : NNReal => (0 : Real)) by
          funext s
          simp [Atilde, hω]]
        simp only [variationOnFromTo]
        rw [eVariationOn.constant_on (by simp)]
        simp
      rw [hZero]
      exact hCNonneg
    · have hRegω :
          (A 0 omega = 0) ∧
            (∀ t, T ≤ t → A t omega = A T omega) ∧
            eVariationOn (A · omega) Set.univ ≤ ENNReal.ofReal C := by
        simpa only [bad, C, Set.mem_ofPred_eq, not_not] using hω
      have hAtildePath : (Atilde · omega) = (A · omega) := by
        funext s
        change ProcessNullSetRegularization.zeroOn bad A s omega = A s omega
        exact ProcessNullSetRegularization.zeroOn_apply_of_notMem bad A hω
      have hVle :
          localVariation Atilde T omega ≤
            (eVariationOn (A · omega) Set.univ).toReal := by
        have h := variationOnFromTo.abs_le_eVariationOn
          (hAtildeBV omega) (a := (0 : NNReal)) (b := T)
        have hnonneg :
            0 ≤ variationOnFromTo (fun s => Atilde s omega) Set.univ
              (0 : NNReal) T :=
          variationOnFromTo.nonneg_of_le _ _ bot_le
        have h' :
            variationOnFromTo (fun s => Atilde s omega) Set.univ
                (0 : NNReal) T ≤
              (eVariationOn (Atilde · omega) Set.univ).toReal := by
          simpa only [abs_of_nonneg hnonneg] using h
        simpa [localVariation, hAtildePath] using h'
      have hToReal :
          (eVariationOn (A · omega) Set.univ).toReal ≤ C := by
        calc
          (eVariationOn (A · omega) Set.univ).toReal ≤
              (ENNReal.ofReal C).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hRegω.2.2
          _ = C := ENNReal.toReal_ofReal hCNonneg
      exact hVle.trans hToReal
  let Aplus : Process Omega := commonStopJordanPositive Atilde
  let Aminus : Process Omega := commonStopJordanNegative Atilde
  have hAplusStrong : StronglyAdapted F Aplus := by
    intro t
    change StronglyMeasurable[ F t]
      (fun x => (localVariation Atilde t x + Atilde t x) / 2)
    convert ((hCumulativeStrong t).add (hAtildeStrong t)).const_smul
      (1 / 2 : Real) using 1
    ext x
    dsimp
    ring
  have hAminusStrong : StronglyAdapted F Aminus := by
    intro t
    change StronglyMeasurable[ F t]
      (fun x => (localVariation Atilde t x - Atilde t x) / 2)
    convert ((hCumulativeStrong t).sub (hAtildeStrong t)).const_smul
      (1 / 2 : Real) using 1
    ext x
    dsimp
    ring
  have hAplusRight : ∀ omega t,
      ContinuousWithinAt (Aplus · omega) (Ici t) t := by
    intro omega t
    dsimp [Aplus, commonStopJordanPositive]
    exact ((hCumulativeRight omega t).add (hAtildeRight omega t)).div_const 2
  have hAminusRight : ∀ omega t,
      ContinuousWithinAt (Aminus · omega) (Ici t) t := by
    intro omega t
    dsimp [Aminus, commonStopJordanNegative]
    exact ((hCumulativeRight omega t).sub (hAtildeRight omega t)).div_const 2
  have hAplusMono : ∀ omega, Monotone (Aplus · omega) := by
    intro omega
    exact commonStopJordanPositive_monotone hAtildeBV omega
  have hAminusMono : ∀ omega, Monotone (Aminus · omega) := by
    intro omega
    exact commonStopJordanNegative_monotone hAtildeBV omega
  have hAplusZero : Aplus 0 = 0 := by
    dsimp [Aplus]
    exact commonStopJordanPositive_zero hAtildeZero
  have hAminusZero : Aminus 0 = 0 := by
    dsimp [Aminus]
    exact commonStopJordanNegative_zero hAtildeZero
  have hAplusConst : ∀ omega t, T ≤ t →
      Aplus t omega = Aplus T omega := by
    intro omega t htt
    change (localVariation Atilde t omega + Atilde t omega) / 2 =
      (localVariation Atilde T omega + Atilde T omega) / 2
    rw [hCumulativeConst omega t htt, hAtildeConst omega t htt]
  have hAminusConst : ∀ omega t, T ≤ t →
      Aminus t omega = Aminus T omega := by
    intro omega t htt
    change (localVariation Atilde t omega - Atilde t omega) / 2 =
      (localVariation Atilde T omega - Atilde T omega) / 2
    rw [hCumulativeConst omega t htt, hAtildeConst omega t htt]
  have hJordanDecomp : ∀ t omega,
      Atilde t omega = Aplus t omega - Aminus t omega := by
    intro t omega
    dsimp [Aplus, Aminus, commonStopJordanPositive,
      commonStopJordanNegative]
    ring
  have hAplusBound : ∀ omega, 0 ≤ Aplus T omega ∧ Aplus T omega ≤ C := by
    intro omega
    have hmono := hAplusMono omega (show (0 : NNReal) ≤ T from bot_le)
    have hzero : Aplus 0 omega = 0 := congrFun hAplusZero omega
    have hsum : Aplus T omega + Aminus T omega =
        localVariation Atilde T omega := by
      dsimp [Aplus, Aminus, commonStopJordanPositive,
        commonStopJordanNegative]
      ring
    have hnonneg : 0 ≤ Aplus T omega := by linarith
    have hleSum : Aplus T omega ≤
        localVariation Atilde T omega := by
      have hminus := hAminusMono omega (show (0 : NNReal) ≤ T from bot_le)
      have hminusZero : Aminus 0 omega = 0 := congrFun hAminusZero omega
      have hminusNonneg : 0 ≤ Aminus T omega := by linarith
      linarith
    exact ⟨hnonneg, hleSum.trans (hCumulativeBound omega)⟩
  have hAminusBound : ∀ omega, 0 ≤ Aminus T omega ∧ Aminus T omega ≤ C := by
    intro omega
    have hmono := hAminusMono omega (show (0 : NNReal) ≤ T from bot_le)
    have hzero : Aminus 0 omega = 0 := congrFun hAminusZero omega
    have hsum : Aplus T omega + Aminus T omega =
        localVariation Atilde T omega := by
      dsimp [Aplus, Aminus, commonStopJordanPositive,
        commonStopJordanNegative]
      ring
    have hnonneg : 0 ≤ Aminus T omega := by linarith
    have hleSum : Aminus T omega ≤
        localVariation Atilde T omega := by
      have hplus := hAplusMono omega (show (0 : NNReal) ≤ T from bot_le)
      have hplusZero : Aplus 0 omega = 0 := congrFun hAplusZero omega
      have hplusNonneg : 0 ≤ Aplus T omega := by linarith
      linarith
    exact ⟨hnonneg, hleSum.trans (hCumulativeBound omega)⟩
  refine ⟨bad, Atilde, Aplus, Aminus,
    localVariation Atilde, ?_⟩
  exact
    { raw := hRaw
      bad_null := hbadNull
      bad_measurable := hbadMeasurable
      Atilde_eq_zeroOn := hAtildeEq
      Atilde_stronglyAdapted := hAtildeStrong
      Atilde_adapted := hAtildeStrong.adapted
      Atilde_rightContinuous := hAtildeRight
      Atilde_hasLeftLimits := hAtildeLeft
      Atilde_boundedVariation := hAtildeBV
      Atilde_eVariation_bound := by
        simpa [C] using hAtildeVariationBound
      Atilde_zero := hAtildeZero
      Atilde_constant_after := hAtildeConst
      Atilde_indistinguishable := hAtildeInd
      stoppedSource_indistinguishable := hStoppedInd
      cumulativeVariation_eq_def := rfl
      cumulativeVariation_eq_signedMeasureVariation := by
        intro t omega
        exact commonStopCumulativeVariation_eq_variation
          (hA := hAtildeBV) (hRight := hAtildeRight) t omega
      cumulativeVariation_stronglyAdapted := hCumulativeStrong
      cumulativeVariation_adapted := hCumulativeStrong.adapted
      cumulativeVariation_rightContinuous := hCumulativeRight
      cumulativeVariation_monotone := hCumulativeMono
      cumulativeVariation_zero := hCumulativeZero
      cumulativeVariation_constant_after := hCumulativeConst
      cumulativeVariation_totalVariation_bound := by
        simpa [C] using hCumulativeBound
      jordanPositive_eq_def := rfl
      jordanNegative_eq_def := rfl
      jordanPositive_stronglyAdapted := hAplusStrong
      jordanNegative_stronglyAdapted := hAminusStrong
      jordanPositive_adapted := hAplusStrong.adapted
      jordanNegative_adapted := hAminusStrong.adapted
      jordanPositive_rightContinuous := hAplusRight
      jordanNegative_rightContinuous := hAminusRight
      jordanPositive_monotone := hAplusMono
      jordanNegative_monotone := hAminusMono
      jordanPositive_zero := hAplusZero
      jordanNegative_zero := hAminusZero
      jordanPositive_constant_after := hAplusConst
      jordanNegative_constant_after := hAminusConst
      jordan_decomposition := hJordanDecomp
      jordanPositive_terminal_bound := by simpa [C] using hAplusBound
      jordanNegative_terminal_bound := by simpa [C] using hAminusBound }

/-! ## Full common-stop producer -/

theorem exists_commonStop_regularizedRawDecomposition
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
          (cutoff : Nat → Nat) (A : Process Omega)
          (bad : Set Omega) (Atilde Aplus Aminus cumulativeVariation : Process Omega),
          CommonStopRegularizedRawDecompositionData
            (S := S) (F := F) (mu := mu) (eta := eta)
            (u := u) (selection := selection) (a := a) (T := T)
            (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
            (hUsual := hUsual) (source := source)
            (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
            (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
            endpoint bad Atilde Aplus Aminus cumulativeVariation := by
  obtain ⟨a, u, selection, alphaSeq, alpha, R, endpoint, v, Z,
      Nbar, Bbar, Xbar, M, cutoff, A, hRaw⟩ :=
    exists_commonStop_rawFiniteVariationDecomposition hUsual hS source T heta
  obtain ⟨bad, Atilde, Aplus, Aminus, cumulativeVariation, hReg⟩ :=
    commonStop_regularizeRawDecomposition endpoint hRaw
  exact ⟨a, u, selection, alphaSeq, alpha, R, endpoint, v, Z,
    Nbar, Bbar, Xbar, M, cutoff, A, bad, Atilde, Aplus, Aminus,
    cumulativeVariation, hReg⟩

end HorizonFactorialGrid

end FTAPTheorem42
