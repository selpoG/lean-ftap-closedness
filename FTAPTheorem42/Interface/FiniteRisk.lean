import FTAPTheorem42.Stochastic.Construction.GeneralAuxiliaryMarket
import FTAPTheorem42.Stochastic.DS.Lemma47.ActualVanishingRisk
import FTAPTheorem42.Stochastic.Integral.Local.Construction.UnitSourceRealization
import FTAPTheorem42.Foundations.EquivalentMeasureTransfer
import FTAPTheorem42.Stochastic.Construction.OriginalGainRealization

/-! # The finite-scale analytic input for DS Lemma 4.7

A single high-maximum event yields a terminal claim in the original market.
This construction assumes neither NFLVR nor maximality. The market
contradiction and the choice of an unbounded sequence belong to the main proof.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open LocalCompletedM2A PredictableElementaryEmery EquivalentMeasureTransfer

variable {Ω : Type*} [MeasurableSpace Ω]
  {S P : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]
  {D : SpecialSemimartingaleDecomposition P F Q}

/-- Finite-horizon vanishing risk, including the stopping jump and return to
an admissible terminal claim of the original price. -/
theorem originalMarket_finiteRisk
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (R : RealizedStrategy (ℱ := F) Q S) (G : LocallySIntegrableStrategy D)
    (hGain : G.stochasticIntegral = R.gain)
    (hUnit : G.integrand = PredictableProcess.unit)
    (hM0 : G.martingalePart 0 = 0) (hML : ProcessHasLeftLimits G.martingalePart)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 Q)
    (hBound : ∀ᵐ ω ∂Q, ∀ t, |G.stochasticIntegral t ω| ≤ ξ ω)
    (hLower : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ G.stochasticIntegral t ω)
    {B : Real} (hB : 0 ≤ B) (hNorm : eLpNorm ξ 2 Q ≤ ENNReal.ofReal B)
    (α : Real) (n : Nat) (T : NNReal)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hn : 0 < n)
    (hk : 0 < lemma47ExcursionCount α n)
    (hJump : 6 * B ≤ (n : Real) ^ 2) (hError : (B / (n : Real)) ^ 2 ≤ α)
    (hMass : 0 ≤ lemma47ExcursionMass α B n) (hT : 0 < T)
    (hHigh : 8 * α < Q.real {ω | (n : Real) ^ 3 <
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope G.martingalePart T ω}) :
    ∃ f : Ω → Real,
      f ∈ C0AsDifference Q ((generalMarket source).K0OfGainProcessModel Q) ∧
      AEStronglyMeasurable f Q ∧ AELowerBoundedBy Q (-lemma47Downside α n) f ∧
      lemma47TerminalMass α B n ≤ Q.real {ω | lemma47TerminalLevel α B n ≤ f ω} := by
  let _ := hUsual.rightContinuous
  let U := actualUnitSource (directScheduleOfL2Gain G hUsual hM0 hML ξ hξ hBound)
    hUnit (by rw [hGain]; exact R.gain_initial_eq_zero S source.rightContinuous)
  let H := U.deterministicallyStopped T hT
  have hM : H.val.martingalePart =
      stoppedProcess G.martingalePart (fun _ => (T : WithTop NNReal)) := by
    funext t ω
    simp only [H, U, ActualLocallySIntegrableStrategy.deterministicallyStopped,
      actualUnitSource, LocallySIntegrableStrategy.deterministicallyStopped,
      stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hX : H.val.stochasticIntegral =
      stoppedProcess G.stochasticIntegral (fun _ => (T : WithTop NNReal)) := by
    funext t ω
    simp only [H, U, ActualLocallySIntegrableStrategy.deterministicallyStopped,
      actualUnitSource, LocallySIntegrableStrategy.deterministicallyStopped,
      stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hEnv : FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope H.val.martingalePart T =
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope G.martingalePart T := by
    funext ω
    simp only [H, U, ActualLocallySIntegrableStrategy.deterministicallyStopped,
      actualUnitSource, LocallySIntegrableStrategy.deterministicallyStopped,
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope,
      FactorialChronologicalGrid.eFactorialRunningMaxSqEnvelope,
      FactorialChronologicalGrid.factorialRunningMax, finiteRunningMax,
      ChronologicalGrid.natSample, ChronologicalGrid.sampledTime,
      FactorialChronologicalGrid.stoppedGrid_time, min_assoc, min_self]
  let C := SIntegrableStrategy.processStoppingCalculus D
  let P := (C.lemma47RescaleAndStopUpTo H.val (lemma47FirstScale n)
    ((n : Real) ^ 3) (n : Real) T).predictablePathwiseHahnSeparator
  let V := actualLemma47VanishingRiskStrategy hML H α n T P
  have hV : (∀ᵐ ω ∂Q, ∀ t, -lemma47Downside α n ≤ V.val.stochasticIntegral t ω) ∧
      lemma47TerminalMass α B n ≤
        Q.real {ω | lemma47TerminalLevel α B n ≤ V.val.stochasticIntegral T ω} := by
    apply actualFirstLocalized_hahnPositive_stopDownside_of_originalHigh hML hUsual H
      (by rw [hM]; exact hML.stoppedProcess _)
      (by rw [hX, hGain]; exact R.gain_hasLeftLimits.stoppedProcess _)
      (by
        rw [hM]
        filter_upwards [] with ω
        rw [stoppedProcess_eq_of_le bot_le, hM0])
      (by
        filter_upwards [hLower] with ω hω
        intro t
        exact hω (min t T))
      hn hα hα4 hk ξ hξ
      (by
        filter_upwards [hBound] with ω hω
        intro t
        exact hω (min t T))
      hB hNorm hJump hT (by rwa [hEnv]) hError hMass P
  have hLowerV : ∀ t, AELowerBoundedBy Q (-(|lemma47Downside α n| + 1))
      (V.val.stochasticIntegral t) := by
    intro t
    filter_upwards [hV.1] with ω hω
    linarith [hω t, le_abs_self (lemma47Downside α n)]
  have hMem := auxiliary_actual_horizon_mem_original_terminalClaims source hQμ hμQ
    hUsual R G hGain hM0 hML ξ hξ hBound V T
    (by positivity : 0 < |lemma47Downside α n| + 1) hLowerV
    (actualLemma47VanishingRiskStrategy_stochasticIntegral_eq_terminal_of_le hML H α n T P)
  have hK0 : V.val.stochasticIntegral T ∈ (generalMarket source).K0OfGainProcessModel μ := by
    rw [← truncatedTerminalClaims_eq_generalMarket_K0]
    exact ⟨_, hMem⟩
  rw [K0OfGainProcessModel_eq_of_mutuallyAbsolutelyContinuous
    (generalMarket source) hμQ hQμ] at hK0
  refine ⟨V.val.stochasticIntegral T,
    C0FromTerminalGains_subset_C0AsDifference
      ⟨_, hK0, Eventually.of_forall (fun _ => le_rfl)⟩,
    ((V.val.stochasticIntegral_isStronglyAdapted T).mono (F.le T)).aestronglyMeasurable,
    ?_, hV.2⟩
  filter_upwards [hV.1] with ω hω
  exact hω T

/-- The finite-risk input in process-level vocabulary. Its statement exposes
neither an auxiliary integration source nor an elementary realization carrier. -/
theorem originalGain_finiteRisk
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (Y : OriginalGain source) (E : J1Decomposition Y.gain F Q)
    (hAP : IsStronglyPredictable F E.A)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 Q)
    (hBound : ∀ᵐ ω ∂Q, ∀ t, |Y.gain t ω| ≤ ξ ω)
    (hLower : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ Y.gain t ω)
    {B : Real} (hB : 0 ≤ B) (hNorm : eLpNorm ξ 2 Q ≤ ENNReal.ofReal B)
    (α : Real) (n : Nat) (T : NNReal)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hn : 0 < n)
    (hk : 0 < lemma47ExcursionCount α n)
    (hJump : 6 * B ≤ (n : Real) ^ 2) (hError : (B / (n : Real)) ^ 2 ≤ α)
    (hMass : 0 ≤ lemma47ExcursionMass α B n) (hT : 0 < T)
    (hHigh : 8 * α < Q.real {ω | (n : Real) ^ 3 <
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope E.N T ω}) :
    ∃ f : Ω → Real,
      f ∈ C0AsDifference Q ((generalMarket source).K0OfGainProcessModel Q) ∧
      AEStronglyMeasurable f Q ∧ AELowerBoundedBy Q (-lemma47Downside α n) f ∧
      lemma47TerminalMass α B n ≤ Q.real {ω | lemma47TerminalLevel α B n ≤ f ω} := by
  obtain ⟨R, hR⟩ := Y.exists_realized source hQμ hμQ
  let E' : J1Decomposition R.gain F Q :=
    { E with decomposition := by rw [hR]; exact E.decomposition }
  have hEN : E'.N = E.N := rfl
  have hEA : E'.A = E.A := rfl
  have hEP : IsStronglyPredictable F E'.A := hEA ▸ hAP
  let G := R.componentSource source.rightContinuous E' hEP
  have hM : G.martingalePart = E.N :=
    (R.componentSource_martingalePart source.rightContinuous E' hEP).trans hEN
  apply originalMarket_finiteRisk source hQμ hμQ hUsual R G rfl rfl
    (by rw [hM, E.zeroN]) (by rw [hM]; exact E.leftN)
    ξ hξ (by simpa only [G, RealizedStrategy.componentSource_gain, hR] using hBound)
    (by simpa only [G, RealizedStrategy.componentSource_gain, hR] using hLower)
    hB hNorm α n T hα hα4 hn hk hJump hError hMass hT
    (by rwa [hM])

end FTAPTheorem42.BoundedSourceIntegralMarket
