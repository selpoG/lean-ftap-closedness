/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.RiskSchedules
import FTAPTheorem42.Trading.VanishingRisk
import FTAPTheorem42.Foundations.ProcessEnvelope
import FTAPTheorem42.Interface.FiniteRisk
import FTAPTheorem42.Foundations.MaximalProbability
import FTAPTheorem42.Foundations.EquivalentMeasureTransfer

/-! # DS Lemma 4.7: class boundedness in the original-price market

The finite-risk argument and its application to the original market are proved together.
-/

/-! ## The finite-risk contradiction -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- A finite-scale vanishing-risk construction bounds the entire martingale
maximal family under NFLVR. The input has no NFLVR or maximality premise. -/
theorem lemma47_boundedInProbability_of_finiteRisk
    {I : Type*} (M : I → Process Omega)
    (A : GainProcessModel Omega NNReal) (normBound : Real)
    (hRisk : ∀ (i : I) (alpha : Real) (n : Nat) (T : NNReal),
      0 < alpha → alpha ≤ 1 / 4 → 0 < n →
      0 < lemma47ExcursionCount alpha n →
      6 * normBound ≤ (n : Real) ^ 2 →
      (normBound / (n : Real)) ^ 2 ≤ alpha →
      0 ≤ lemma47ExcursionMass alpha normBound n → 0 < T →
      8 * alpha < mu.real {omega | (n : Real) ^ 3 <
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope (M i) T omega} →
      ∃ f : Omega → Real,
        f ∈ C0AsDifference mu (A.K0OfGainProcessModel mu) ∧
        AEStronglyMeasurable f mu ∧
        AELowerBoundedBy mu (-lemma47Downside alpha n) f ∧
        lemma47TerminalMass alpha normBound n ≤
          mu.real {omega | lemma47TerminalLevel alpha normBound n ≤ f omega})
    (hNFLVR : LinftyNFLVR mu (LinftyClaims mu
      (C0AsDifference mu (A.K0OfGainProcessModel mu)))) :
    ClaimSetBoundedInProbability mu
      {f | ∃ i, ∃ T : NNReal, 0 < T ∧
        f = FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope (M i) T} := by
  classical
  by_contra hNotBounded
  obtain ⟨epsilon, hEpsilon, f, hFClass, hFTail⟩ :=
    (ClaimSetUnboundedInProbabilityWitness.of_not_bounded hNotBounded)
      |>.exists_sequence_at (fun n : Nat => (n : Real) ^ 3)
        (fun n => by positivity)
  have hRepresent : ∀ n, ∃ i, ∃ T : NNReal, 0 < T ∧
      f n = FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (M i) T := by
    intro n
    exact hFClass n
  choose index hRest using hRepresent
  choose horizon hHorizonPositive hF using hRest
  let alpha : Real := min (epsilon / 16) (1 / 8)
  have hAlpha : 0 < alpha := by
    dsimp [alpha]
    exact lt_min (div_pos hEpsilon (by norm_num)) (by norm_num)
  have hAlphaQuarter : alpha <= 1 / 4 :=
    (min_le_right _ _).trans (by norm_num)
  have hEightAlpha : 8 * alpha < epsilon := by
    have hAlphaEpsilon : alpha <= epsilon / 16 := min_le_left _ _
    nlinarith
  have hHigh : ∀ n : Nat, 8 * alpha < mu.real {omega |
      (n : Real) ^ 3 <
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (M (index n)) (horizon n) omega} := by
    intro n
    have hTail := hFTail n
    rw [hF n] at hTail
    have hEvent :
        {omega | (n : Real) ^ 3 <
          |FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            (M (index n)) (horizon n) omega|} =
        {omega | (n : Real) ^ 3 <
          FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            (M (index n)) (horizon n) omega} := by
      ext omega
      have hEnvelopeNonnegative : 0 <=
          FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            (M (index n)) (horizon n) omega := by
        unfold FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        positivity
      change ((n : Real) ^ 3 <
        |FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (M (index n)) (horizon n) omega|) ↔
        ((n : Real) ^ 3 <
          FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            (M (index n)) (horizon n) omega)
      rw [abs_of_nonneg hEnvelopeNonnegative]
    rw [hEvent] at hTail
    have hTailReal : epsilon < mu.real {omega |
        (n : Real) ^ 3 <
          FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            (M (index n)) (horizon n) omega} := by
      have hToReal := (ENNReal.toReal_lt_toReal
        ENNReal.ofReal_ne_top (by finiteness)).2 hTail
      simpa only [Measure.real, ENNReal.toReal_ofReal hEpsilon.le] using
        hToReal
    exact hEightAlpha.trans hTailReal
  rcases eventually_atTop.1
      (eventually_lemma47ConstructionConditions hAlpha normBound) with
    ⟨N, hN⟩
  let m : Nat → Nat := fun n => n + N
  have hmStrict : StrictMono m := strictMono_id.add_const N
  have hConditions : ∀ n,
      0 < m n ∧
      0 < lemma47ExcursionCount alpha (m n) ∧
      6 * normBound <= (m n : Real) ^ 2 ∧
      (normBound / (m n : Real)) ^ 2 <= alpha ∧
      0 <= lemma47ExcursionMass alpha normBound (m n) ∧
      alpha ^ 3 / 8 < lemma47TerminalLevel alpha normBound (m n) ∧
      alpha ^ 2 / 4 < lemma47TerminalMass alpha normBound (m n) := by
    intro n
    exact hN (m n) (Nat.le_add_left N n)
  have hRiskData : ∀ k, ∃ f : Omega → Real,
      f ∈ C0AsDifference mu (A.K0OfGainProcessModel mu) ∧
      AEStronglyMeasurable f mu ∧
      AELowerBoundedBy mu (-lemma47Downside alpha (m k)) f ∧
      lemma47TerminalMass alpha normBound (m k) ≤
        mu.real {omega | lemma47TerminalLevel alpha normBound (m k) ≤ f omega} := by
    intro k
    rcases hConditions k with ⟨hm, hk, hj, he, hp, _hl, _ht⟩
    exact hRisk (index (m k)) alpha (m k) (horizon (m k)) hAlpha hAlphaQuarter
      hm hk hj he hp (hHorizonPositive (m k)) (hHigh (m k))
  choose terminal hTerminalC0 hTerminalMeas hTerminalLower hActual using hRiskData
  let downside : Nat → Real := fun n => lemma47Downside alpha (m n)
  have hDownsideZero : Tendsto downside atTop (𝓝 0) :=
    (tendsto_lemma47Downside_zero hAlpha).comp hmStrict.tendsto_atTop
  have hEpsilonMass : 0 < alpha ^ 2 / 4 := by positivity
  have hEta : 0 < alpha ^ 3 / 8 := by positivity
  have hTerminalMass : ∀ n,
      ENNReal.ofReal (alpha ^ 2 / 4) <
        mu {omega | alpha ^ 3 / 8 < terminal n omega} := by
    intro n
    have hCond := hConditions n
    have hEventSubset :
        {omega | lemma47TerminalLevel alpha normBound (m n) <=
          terminal n omega} ⊆
        {omega | alpha ^ 3 / 8 < terminal n omega} := by
      intro omega hOmega
      exact hCond.2.2.2.2.2.1.trans_le hOmega
    have hMassReal : alpha ^ 2 / 4 <
        mu.real {omega | alpha ^ 3 / 8 < terminal n omega} := by
      calc
        alpha ^ 2 / 4 < lemma47TerminalMass alpha normBound (m n) :=
          hCond.2.2.2.2.2.2
        _ <= mu.real {omega |
              lemma47TerminalLevel alpha normBound (m n) <=
                terminal n omega} := hActual n
        _ <= mu.real {omega | alpha ^ 3 / 8 < terminal n omega} :=
          measureReal_mono hEventSubset
    apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
      (by finiteness)).1
    simpa only [Measure.real, ENNReal.toReal_ofReal hEpsilonMass.le] using
      hMassReal
  exact not_vanishingRiskPositiveLevel_of_tendsto_linfyNFLVR
    (C0AsDifference_claimCone (μ := mu)
      (by simpa [A.K0OfGainProcessModel_eq_terminalGainModel mu] using
        A.K0_terminalGainModel_claimCone mu))
    (C0AsDifference_solid mu (A.K0OfGainProcessModel mu)) hNFLVR
      hEpsilonMass hEta hTerminalC0 hTerminalMeas hTerminalLower
      hDownsideZero hTerminalMass

end FTAPTheorem42

/-! ## Application to original gains -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open EquivalentMeasureTransfer SIntegrableMartingaleRestrictionL2Calculus

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- Original NFLVR bounds every family of normalized special gain components
with a common bound on the L² norms of their gain envelopes. -/
theorem originalGain_class_boundedInProbability
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    {I : Type*} (Y : I → OriginalGain source)
    (E : ∀ i, J1Decomposition (Y i).gain F Q)
    (hAP : ∀ i, IsStronglyPredictable F (E i).A)
    (ξ : I → Ω → Real) (hξ : ∀ i, MemLp (ξ i) 2 Q)
    (hBound : ∀ i, ∀ᵐ ω ∂Q, ∀ t, |(Y i).gain t ω| ≤ ξ i ω)
    (hLower : ∀ i, ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ (Y i).gain t ω)
    {B : Real} (hB : 0 ≤ B)
    (hNorm : ∀ i, eLpNorm (ξ i) 2 Q ≤ ENNReal.ofReal B) :
    ∀ ε : Real, 0 < ε → ∃ b : Real, 0 ≤ b ∧ ∀ i,
      Q {ω | ENNReal.ofReal b < ⨆ t : NNReal,
        ENNReal.ofReal |(E i).N t ω|} ≤ ENNReal.ofReal ε := by
  let A := generalMarket source
  have hNFLVRQ : LinftyNFLVR Q (LinftyClaims Q
      (C0AsDifference Q (A.K0OfGainProcessModel Q))) := by
    apply (linftyNFLVR_iff_of_mutuallyAbsolutelyContinuous_gainProcessModel A hμQ hQμ).mp
    simpa only [A, ← generalTerminalClaims_eq_generalMarket_K0] using hNFLVR
  have hBounded := lemma47_boundedInProbability_of_finiteRisk (fun i => (E i).N) A B
    (fun i α n T hα hα4 hn hk hj he hm hT hHigh =>
      originalGain_finiteRisk source hQμ hμQ hUsual (Y i) (E i) (hAP i)
        (ξ i) (hξ i) (hBound i) (hLower i) hB (hNorm i)
        α n T hα hα4 hn hk hj he hm hT hHigh) hNFLVRQ
  have hFinite : ClaimSetBoundedInProbability Q
      {f | ∃ M ∈ Set.range (fun i => (E i).N), ∃ T : NNReal, 0 < T ∧
        f = FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T} := by
    apply hBounded.mono
    rintro f ⟨M, ⟨i, rfl⟩, T, hT, rfl⟩
    exact ⟨i, T, hT, rfl⟩
  have hAll := processClass_allTimeMaximal_boundedInProbability_of_finiteHorizon
    (Set.range (fun i => (E i).N))
    (by rintro M ⟨i, rfl⟩; exact (E i).rightN)
    (by rintro M ⟨i, rfl⟩; exact (E i).leftN) hFinite
  intro ε hε
  obtain ⟨b, hb, hTail⟩ := hAll ε hε
  exact ⟨b, hb, fun i => hTail (E i).N ⟨i, rfl⟩⟩

end FTAPTheorem42.BoundedSourceIntegralMarket
