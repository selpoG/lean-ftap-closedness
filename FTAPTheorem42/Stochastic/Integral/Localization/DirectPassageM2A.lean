import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy
import FTAPTheorem42.Stochastic.DS.Lemma410.StoppedPrefixMartingale
import FTAPTheorem42.Stochastic.Stopping.CadlagPassageLocalizer

/-! # Passage M2 coordinates without a supplied stopping calculus -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42.SIntegrableStrategy

open SIntegrableProcessStoppingCalculus

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
  {S : Process Ω} {D : SpecialSemimartingaleDecomposition S F mu}

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem directPassage_stoppingTime (H : SIntegrableStrategy D) (n : Nat) :
    IsStoppingTime F (fun ω => (cadlagAbsolutePassageLocalizerFinite H.martingalePart n ω :
      WithTop NNReal)) := by
  simp only [coe_cadlagAbsolutePassageLocalizerFinite]
  exact (absoluteStrictHittingAfter_isStoppingTime H.martingalePart_isStronglyAdapted
    H.martingalePart_isRightContinuous (cadlagPassageLevel n)).min
    (isStoppingTime_const F (cadlagPassageHorizon n))

noncomputable def directPassage (H : SIntegrableStrategy D)
    (hZero : H.martingalePart 0 = 0) (n : Nat) : SIntegrableStrategy D :=
  H.toLocally.finiteClosedStop hZero (cadlagAbsolutePassageLocalizerFinite H.martingalePart n)
    (H.directPassage_stoppingTime n)

/-- The gain envelope supplies a jump envelope; closed-stop overshoot then
gives an L2 bound for the directly constructed martingale coordinate. -/
theorem directPassage_martingale_l2 (H : SIntegrableStrategy D)
    (hZero : H.martingalePart 0 = 0) (hLeft : ProcessHasLeftLimits H.martingalePart)
    (hUsual : Filtration.UsualConditions mu F) (ξ : Ω → Real) (hξ : MemLp ξ 2 mu)
    (hBound : ∀ᵐ ω ∂mu, ∀ t, |H.stochasticIntegral t ω| ≤ ξ ω) (n : Nat) :
    Martingale (H.directPassage hZero n).martingalePart F mu ∧
      MemLp ((H.directPassage hZero n).martingalePart (cadlagPassageHorizon n)) 2 mu := by
  obtain ⟨j, hj, hjPos, hjBound, _⟩ :=
    SIntegrableProcessStoppingCalculus.lemma47MartingaleJumpEnvelope_of_strategy
      hUsual H hLeft ξ hξ hBound
      (cadlagPassageHorizon_pos n)
  let P := H.directPassage hZero n
  let b : Ω → Real := fun ω => cadlagPassageLevel n + j ω
  have hb : MemLp b 2 mu := (memLp_const (cadlagPassageLevel n)).add hj
  have hP : ∀ᵐ ω ∂mu, ∀ t, |P.martingalePart t ω| ≤ b ω := by
    filter_upwards [hjPos, hjBound] with ω hp hjω
    intro t
    change |stoppedProcess H.martingalePart
      (fun ω => (cadlagAbsolutePassageLocalizerFinite H.martingalePart n ω : WithTop NNReal))
      t ω| ≤ cadlagPassageLevel n + j ω
    apply abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting_of_le_horizon
      (T := cadlagPassageHorizon n) H.martingalePart hLeft (cadlagPassageLevel n) (j ω) hp ω
    · rw [congrFun hZero ω, Pi.zero_apply, abs_zero]
      exact cadlagPassageLevel_nonnegative n
    · rw [coe_cadlagAbsolutePassageLocalizerFinite]
      exact min_le_left _ _
    · rw [coe_cadlagAbsolutePassageLocalizerFinite]
      exact min_le_right _ _
    · exact hjω
  have hPM : Martingale P.martingalePart F mu :=
    P.martingalePart_isMartingale_of_integrable_bound b (hb.integrable one_le_two) hP
  refine ⟨hPM, hb.of_le ?_ ?_⟩
  · exact ((hPM.stronglyMeasurable _).mono (F.le _)).aestronglyMeasurable
  · filter_upwards [hP, hjPos] with ω hp hjω
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (cadlagPassageLevel_nonnegative n) hjω)]
    exact hp _

end FTAPTheorem42.SIntegrableStrategy
