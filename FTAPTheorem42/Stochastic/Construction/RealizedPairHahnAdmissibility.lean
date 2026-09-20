import FTAPTheorem42.Stochastic.Construction.RealizedPairHahn
import FTAPTheorem42.Stochastic.Construction.GeneralFiniteEventPasting
import FTAPTheorem42.Stochastic.DS.Lemma411.LocalHahnStoppedSemantics
import FTAPTheorem42.Stochastic.DS.Lemma411.HahnDownsideProbability

/-! # The controlled Hahn pair returns an admissible finite terminal claim -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- The same pairwise Hahn gain, its component bounds, and the finite
terminal claim after closed downside stopping at level `1 + δ`. -/
def OriginalPairHahnAdmissibleControl
    (source : BoundedSemimartingaleSource S F μ)
    (hUsual : Filtration.UsualConditions Q F)
    (R V : RealizedStrategy (ℱ := F) Q S)
    (D : J1Decomposition R.gain F Q) (E : J1Decomposition V.gain F Q)
    (hDP : IsStronglyPredictable F D.A) (hEP : IsStronglyPredictable F E.A)
    (T : NNReal) (hT : 0 < T) (b δ : Real) : Prop :=
    letI := hUsual.rightContinuous
    let hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
      source.stronglyAdapted source.rightContinuous
    let W := R.sub hS V
    let B := R.subDecomposition hS V D E
    let hBP : IsStronglyPredictable F B.A := hDP.add hEP.neg
    let G := W.componentSource source.rightContinuous B hBP
    let hGL := W.componentSource_martingalePart_hasLeftLimits source.rightContinuous B hBP
    ∃ L : ActualLocallySIntegrableStrategy (realizationModel G), L.val = G ∧
      let X := actualHahnOfDeterministicStop hGL L T hT
      let τ := finiteHahnDownsideTime X.val.martingalePart (D.N - E.N) δ T
      (∃ K : Process Ω, IsTruncatedIntegralGraph (unitSource source) K X.val.stochasticIntegral) ∧
      (∀ᵐ ω ∂Q, ∀ a c : NNReal, a ≤ c →
        0 ≤ X.val.finiteVariationPart c ω - X.val.finiteVariationPart a ω ∧
        (D.A - E.A) (min c T) ω - (D.A - E.A) (min a T) ω ≤
          X.val.finiteVariationPart c ω - X.val.finiteVariationPart a ω) ∧
      (∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
        (∫ ω, elementaryEmeryTestError X.val.martingalePart 0 J T ω ∂Q) ≤ b) ∧
      (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        X.val.martingalePart T ω ∂Q) ≤ b ∧
      (0 < δ → δ ≤ 1 →
        Q.real {ω | lowerStrictHittingAfter
          (hahnMartingaleAdvantage X.val.martingalePart (D.N - E.N)) δ ω ≤
            (T : WithTop NNReal)} ≤ (b + b) / (δ / 4)) ∧
      (∀ᵐ ω ∂Q, ∀ t, -(1 + δ) ≤ (V.gain + X.val.stochasticIntegral) (min t (τ ω)) ω) ∧
      (fun ω => (V.gain + X.val.stochasticIntegral) (τ ω) ω) ∈
        truncatedTerminalClaimsBy (unitSource source) (1 + δ) ∧
      (∀ U : NNReal, T ≤ U →
        let Z := finiteHahnPastedGain V.gain X.val.stochasticIntegral
          X.val.martingalePart (D.N - E.N) δ T U
        (∃ J, IsTruncatedIntegralGraph (unitSource source) J Z) ∧
        (∀ᵐ ω ∂Q, ∀ t, -(1 + δ) ≤ Z t ω) ∧
        Z U ∈ truncatedTerminalClaimsBy (unitSource source) (1 + δ))

/-- Close the downside stop of the same controlled Hahn gain and return its
finite terminal to the original market. The bound includes the stopping jump. -/
theorem original_pair_hahn_finiteTerminal
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (R V : RealizedStrategy (ℱ := F) Q S)
    (D : J1Decomposition R.gain F Q) (E : J1Decomposition V.gain F Q)
    (hDP : IsStronglyPredictable F D.A) (hEP : IsStronglyPredictable F E.A)
    (hRLower : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ R.gain t ω)
    (hVLower : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ V.gain t ω)
    (T : NNReal) (hT : 0 < T) (b : Real)
    (hControl : OriginalPairHahnControl source hUsual R V D E hDP hEP T hT b)
    {δ : Real} (hδ : 0 ≤ δ) :
    OriginalPairHahnAdmissibleControl source hUsual R V D E hDP hEP T hT b δ := by
  unfold OriginalPairHahnAdmissibleControl
  let _ := hUsual.rightContinuous
  let hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  let W := R.sub hS V
  let B := R.subDecomposition hS V D E
  have hBP : IsStronglyPredictable F B.A := hDP.add hEP.neg
  let G := W.componentSource source.rightContinuous B hBP
  let hGL := W.componentSource_martingalePart_hasLeftLimits source.rightContinuous B hBP
  obtain ⟨L, hL, hGraph, hInc, hTest, hCap, hDiffCap⟩ := hControl
  change L.val = G at hL
  let X := actualHahnOfDeterministicStop hGL L T hT
  let τ := finiteHahnDownsideTime X.val.martingalePart (D.N - E.N) δ T
  have hGain : L.val.stochasticIntegral = R.gain - V.gain := by
    rw [hL]
    exact (W.componentSource_gain source.rightContinuous B hBP).trans (R.sub_gain hS V)
  have hA : L.val.finiteVariationPart = D.A - E.A := by
    rw [hL]
    exact (W.componentSource_finiteVariationPart source.rightContinuous B hBP).trans
      (R.subDecomposition_A hS V D E)
  have hLower := actualHahnBestOf_finiteStopped_lower_bound hGL L D E
    R.gain_hasLeftLimits V.gain_hasLeftLimits hGain hA hRLower hVLower T hT hδ
  have hτ := finiteHahnDownsideTime_isStoppingTime X.val.martingalePart_isStronglyAdapted
    (D.adaptedN.sub E.adaptedN) X.val.martingalePart_isRightContinuous
    (fun ω t => (D.rightN ω t).sub (E.rightN ω t)) δ T
  have hτT : ∀ ω, τ ω ≤ T := RightContinuousStoppedMartingale.boundedTime_le _ _
  obtain ⟨K, hK⟩ := hGraph
  have hVGraph : ∃ H, IsTruncatedIntegralGraph (unitSource source) H V.gain := by
    apply (exists_truncatedIntegralGraph_iff_exists_realizedStrategy source V.gain).mpr
    exact ⟨V.transferMeasure hQμ hμQ S hS, .refl μ _⟩
  obtain ⟨H, hH⟩ := hVGraph
  refine ⟨L, hL, ⟨K, hK⟩, hInc, hTest, hCap, ?_, hLower, ?_, ?_⟩
  · intro hδ0 hδ1
    exact hahnDownside_probability_le X.val.martingalePart_isStronglyAdapted
      (D.adaptedN.sub E.adaptedN) X.val.martingalePart_isRightContinuous
      (fun ω t => (D.rightN ω t).sub (E.rightN ω t)) T hδ0 hδ1 hCap hDiffCap
  · exact finiteStopped_sum_mem_original_terminalClaims source hH hK τ hτ T hτT
      (by linarith) (hμQ.ae_le hLower)
  · intro U hTU
    have hLL : ProcessHasLeftLimits L.val.stochasticIntegral := by
      rw [hGain]
      exact R.gain_hasLeftLimits.sub V.gain_hasLeftLimits
    obtain ⟨_hXL, hX0, hN0, _hJump⟩ := actualHahnOfDeterministicStop_semantics hGL L hLL T hT
    have hC : ∀ᵐ ω ∂Q, 0 ≤ X.val.finiteVariationPart T ω := by
      filter_upwards [hInc, hX0, hN0, X.val.integral_decomposition] with ω hi hx hn hd
      have h0 := hd 0
      have ht := (hi 0 T bot_le).1
      change X.val.stochasticIntegral 0 ω = 0 at hx
      change X.val.martingalePart 0 ω = 0 at hn
      linarith
    obtain ⟨hZGraph, hZLower, hZClaim⟩ := finiteHahnPastedGain_mem_original_terminalClaims
      source hH hK X.val.martingalePart_isStronglyAdapted (D.adaptedN.sub E.adaptedN)
      X.val.martingalePart_isRightContinuous (fun ω t => (D.rightN ω t).sub (E.rightN ω t))
      hTU hδ (hμQ.ae_le hVLower) (hμQ.ae_le hLower)
      (hμQ.ae_le (X.val.integral_decomposition.mono fun ω hω => hω T)) (hμQ.ae_le hC)
    exact ⟨hZGraph, hQμ.ae_le hZLower, hZClaim⟩

end FTAPTheorem42.BoundedSourceIntegralMarket
