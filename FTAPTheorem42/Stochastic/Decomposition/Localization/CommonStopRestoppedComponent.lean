/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppedProcess
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale

/-!
# Source-independent re-stopping of a fixed-stop decomposition

This module isolates the component-level operation used by both bounded and
square-integrable common-stop routes.  Its input is only the already produced
martingale/finite-variation certificate and the stopped-source identity.  A
new stopping time is applied to those completed components; no convex rows or
other upstream data are reselected.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## Minimal fixed-stop component view -/

/-- The source-independent fields needed to re-stop a completed decomposition. -/
structure CommonStopUncenteredFixedStopComponentView
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Ω → WithTop NNReal}
    (hAlpha : IsStoppingTime F alpha)
    (Msource Ap : Process Ω) : Prop where
  Msource_martingale : Martingale Msource F mu
  Msource_stronglyAdapted : StronglyAdapted F Msource
  Msource_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Msource · omega) (Ici t) t
  Msource_leftLimits : ProcessHasLeftLimits Msource
  Msource_initial : Msource 0 =ᵐ[mu] S 0
  Ap_isStronglyPredictable : IsStronglyPredictable F Ap
  Ap_isStronglyAdapted : StronglyAdapted F Ap
  Ap_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Ap · omega) (Ici t) t
  Ap_leftLimits : ProcessHasLeftLimits Ap
  Ap_boundedVariation : ∀ omega,
    BoundedVariationOn (Ap · omega) Set.univ
  Ap_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (Ap · omega) Set.univ
  Ap_zero : Ap 0 = 0
  source_indistinguishable : ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess S alpha)
    (fun t omega => Msource t omega + Ap t omega)

/-! ## Re-stopped component certificate -/

/-- Re-stopping the two components of a fixed-stop source decomposition. -/
structure CommonStopUncenteredRestoppedComponentData
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Ω → WithTop NNReal}
    (hAlpha : IsStoppingTime F alpha)
    {Msource Ap : Process Ω}
    (hView : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu) hAlpha Msource Ap)
    (rho : Ω → WithTop NNReal)
    (hRho : IsStoppingTime F rho)
    (hRhoLeAlpha : ∀ omega, rho omega ≤ alpha omega)
    (Mρ Aρ : Process Ω) : Prop where
  Mρ_eq_stopped : Mρ = MeasureTheory.stoppedProcess Msource rho
  Aρ_eq_stopped : Aρ = MeasureTheory.stoppedProcess Ap rho
  source_doubleStop_eq :
    MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess S alpha) rho =
      MeasureTheory.stoppedProcess S rho
  source_doubleStop_indistinguishable :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess S alpha) rho)
      (MeasureTheory.stoppedProcess S rho)
  Mρ_martingale : Martingale Mρ F mu
  Mρ_stronglyAdapted : StronglyAdapted F Mρ
  Mρ_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Mρ · omega) (Ici t) t
  Mρ_leftLimits : ProcessHasLeftLimits Mρ
  Mρ_initial : Mρ 0 =ᵐ[mu] S 0
  Aρ_isStronglyPredictable : IsStronglyPredictable F Aρ
  Aρ_isStronglyAdapted : StronglyAdapted F Aρ
  Aρ_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Aρ · omega) (Ici t) t
  Aρ_leftLimits : ProcessHasLeftLimits Aρ
  Aρ_boundedVariation : ∀ omega,
    BoundedVariationOn (Aρ · omega) Set.univ
  Aρ_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (Aρ · omega) Set.univ
  Aρ_zero : Aρ 0 = 0
  source_indistinguishable : ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess S rho)
    (fun t omega => Mρ t omega + Aρ t omega)

namespace CommonStopUncenteredRestoppedComponentData

/-- Convert the source-independent re-stopped certificate to a special
semimartingale decomposition. -/
def toSpecialSemimartingaleDecomposition
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Ω → WithTop NNReal}
    (hAlpha : IsStoppingTime F alpha)
    {Msource Ap : Process Ω}
    (hView : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu) hAlpha Msource Ap)
    (rho : Ω → WithTop NNReal)
    (hRho : IsStoppingTime F rho)
    (hRhoLeAlpha : ∀ omega, rho omega ≤ alpha omega)
    {Mρ Aρ : Process Ω}
    (hRestopped : CommonStopUncenteredRestoppedComponentData
      hAlpha hView rho hRho hRhoLeAlpha Mρ Aρ) :
    SpecialSemimartingaleDecomposition
      (MeasureTheory.stoppedProcess S rho) F mu := by
  let D : SpecialSemimartingaleDecomposition
      (MeasureTheory.stoppedProcess S rho) F mu := {
    martingalePart := Mρ
    finiteVariationPart := Aρ
    martingalePart_isLocalMartingale :=
      ProbabilityTheory.Locally.of_prop hRestopped.Mρ_martingale
    finiteVariationPart_isPredictable :=
      hRestopped.Aρ_isStronglyPredictable
    finiteVariationPart_isLocallyBoundedVariation :=
      hRestopped.Aρ_locallyBoundedVariation
    decomposition := hRestopped.source_indistinguishable }
  exact D

end CommonStopUncenteredRestoppedComponentData

/-! ## Generic re-stopping consumer -/

theorem exists_commonStopUncenteredRestoppedComponentData
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Ω → WithTop NNReal}
    (hAlpha : IsStoppingTime F alpha)
    {Msource Ap : Process Ω}
    (hView : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu) hAlpha Msource Ap)
    (rho : Ω → WithTop NNReal)
    (hRho : IsStoppingTime F rho)
    (hRhoLeAlpha : ∀ omega, rho omega ≤ alpha omega) :
    ∃ Mρ Aρ : Process Ω,
      ∃ _hRestopped : CommonStopUncenteredRestoppedComponentData
        hAlpha hView rho hRho hRhoLeAlpha Mρ Aρ,
        Nonempty (SpecialSemimartingaleDecomposition
          (MeasureTheory.stoppedProcess S rho) F mu) := by
  let Mρ : Process Ω := MeasureTheory.stoppedProcess Msource rho
  let Aρ : Process Ω := MeasureTheory.stoppedProcess Ap rho
  have hMρ : Martingale Mρ F mu := by
    dsimp [Mρ]
    exact RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hView.Msource_martingale hRho hView.Msource_rightContinuous
  have hMρAdapted : StronglyAdapted F Mρ := hMρ.stronglyAdapted
  have hMρRight : ∀ omega t,
      ContinuousWithinAt (Mρ · omega) (Ici t) t := by
    dsimp [Mρ]
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      Msource hView.Msource_rightContinuous
  have hMρLeft : ProcessHasLeftLimits Mρ := by
    dsimp [Mρ]
    exact hView.Msource_leftLimits.stoppedProcess rho
  have hMρInitial : Mρ 0 =ᵐ[mu] S 0 := by
    filter_upwards [hView.Msource_initial] with omega hInitial
    change MeasureTheory.stoppedProcess Msource rho 0 omega = S 0 omega
    rw [MeasureTheory.stoppedProcess_eq_of_le (show
      (0 : WithTop NNReal) ≤ rho omega from bot_le)]
    exact hInitial
  have hAρPredictable : IsStronglyPredictable F Aρ := by
    dsimp [Aρ]
    exact IsStronglyPredictable.stoppedProcess_of_stoppingTime_withTop
      hView.Ap_isStronglyPredictable rho hRho
  have hAρAdapted : StronglyAdapted F Aρ := hAρPredictable.stronglyAdapted
  have hAρRight : ∀ omega t,
      ContinuousWithinAt (Aρ · omega) (Ici t) t := by
    dsimp [Aρ]
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      Ap hView.Ap_rightContinuous
  have hAρLeft : ProcessHasLeftLimits Aρ := by
    dsimp [Aρ]
    exact hView.Ap_leftLimits.stoppedProcess rho
  have hAρVariation : ∀ omega,
      BoundedVariationOn (Aρ · omega) Set.univ := by
    intro omega
    by_cases hRhoTop : rho omega = (⊤ : WithTop NNReal)
    · have hEq : (fun t => Aρ t omega) = (Ap · omega) := by
        funext t
        dsimp [Aρ]
        rw [MeasureTheory.stoppedProcess_eq_of_le]
        simp only [hRhoTop, le_top]
      rw [hEq]
      exact hView.Ap_boundedVariation omega
    · lift rho omega to NNReal using hRhoTop with r hr
      have hStoppedPath : (fun t => Aρ t omega) =
          FiniteVariationStoppedPath.stopAt (Ap · omega) r := by
        funext t
        dsimp [Aρ, FiniteVariationStoppedPath.stopAt,
          MeasureTheory.stoppedProcess]
        rw [← hr]
        have hcoe : (((min t r : NNReal) : WithTop NNReal)) =
            min (t : WithTop NNReal) (r : WithTop NNReal) :=
          WithTop.coe_min t r
        have hne : ((min t r : NNReal) : WithTop NNReal) ≠
            (⊤ : WithTop NNReal) := WithTop.coe_ne_top
        calc
          Ap (min (t : WithTop NNReal) (r : WithTop NNReal)).untopA omega =
              Ap (((min t r : NNReal) : WithTop NNReal)).untopA omega := by
            rw [hcoe]
          _ = Ap (min t r) omega := by
            rw [WithTop.untopA_eq_untop hne, WithTop.untop_coe]
      rw [hStoppedPath]
      exact FiniteVariationStoppedPath.boundedVariationOn_stopAt
        (hView.Ap_boundedVariation omega) r
  have hAρLocalVariation : ∀ omega,
      LocallyBoundedVariationOn (Aρ · omega) Set.univ := by
    intro omega
    exact (hAρVariation omega).locallyBoundedVariationOn
  have hAρZero : Aρ 0 = 0 := by
    funext omega
    change MeasureTheory.stoppedProcess Ap rho 0 omega = 0
    rw [MeasureTheory.stoppedProcess_eq_of_le (show
      (0 : WithTop NNReal) ≤ rho omega from bot_le)]
    exact congrFun hView.Ap_zero omega
  have hDoubleStop :
      MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess S alpha) rho =
        MeasureTheory.stoppedProcess S rho := by
    exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right hRhoLeAlpha
  have hDoubleStopIndistinguishable : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess S alpha) rho)
      (MeasureTheory.stoppedProcess S rho) := by
    rw [hDoubleStop]
    exact ProcessIndistinguishable.refl mu
      (MeasureTheory.stoppedProcess S rho)
  have hStoppedSource : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess S rho)
      (fun t omega => Mρ t omega + Aρ t omega) := by
    change ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess S rho)
      (fun t omega =>
        MeasureTheory.stoppedProcess Msource rho t omega +
          MeasureTheory.stoppedProcess Ap rho t omega)
    have hSumStop :
        MeasureTheory.stoppedProcess
            (fun t omega => Msource t omega + Ap t omega) rho =
          (fun t omega =>
            MeasureTheory.stoppedProcess Msource rho t omega +
              MeasureTheory.stoppedProcess Ap rho t omega) := by
      funext t omega
      simp [MeasureTheory.stoppedProcess]
    rw [← hDoubleStop, ← hSumStop]
    exact hView.source_indistinguishable.stoppedProcess rho
  let hRestopped : CommonStopUncenteredRestoppedComponentData
      hAlpha hView rho hRho hRhoLeAlpha Mρ Aρ := {
    Mρ_eq_stopped := by rfl
    Aρ_eq_stopped := by rfl
    source_doubleStop_eq := hDoubleStop
    source_doubleStop_indistinguishable := hDoubleStopIndistinguishable
    Mρ_martingale := hMρ
    Mρ_stronglyAdapted := hMρAdapted
    Mρ_rightContinuous := hMρRight
    Mρ_leftLimits := hMρLeft
    Mρ_initial := hMρInitial
    Aρ_isStronglyPredictable := hAρPredictable
    Aρ_isStronglyAdapted := hAρAdapted
    Aρ_rightContinuous := hAρRight
    Aρ_leftLimits := hAρLeft
    Aρ_boundedVariation := hAρVariation
    Aρ_locallyBoundedVariation := hAρLocalVariation
    Aρ_zero := hAρZero
    source_indistinguishable := hStoppedSource }
  exact ⟨Mρ, Aρ, hRestopped,
    ⟨hRestopped.toSpecialSemimartingaleDecomposition
      hAlpha hView rho hRho hRhoLeAlpha⟩⟩

end HorizonFactorialGrid

end FTAPTheorem42
