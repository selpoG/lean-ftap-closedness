/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Process
import FTAPTheorem42.Trading.Basic
import FTAPTheorem42.Interface.TailNormalization
import FTAPTheorem42.Proof.Components.ClassBoundedness

/-! # DS Lemma 4.8: uniform decay of martingale tails

Normalization turns persistent tail mass into a contradiction with the class bound.
The original-price application supplies this bound for each normalized family.
-/

/-! ## The normalized-tail contradiction -/

namespace FTAPTheorem42

open MeasureTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Finite normalization and a class bound force uniform decay of tail
passage probabilities. `P` describes the normalized class; its membership is
verified separately for every witness, not inferred from boundedness of the
original family or of its convex hull. -/
theorem lemma48_tail_small_of_normalization
    {I W : Type*} (M : I → Process Ω) (P : I → Prop)
    (admissibleWeight : W → Prop) (tailEvent : W → Real → Real → Set Ω)
    (hMaximal : ∀ V : Nat → I, (∀ k, P (V k)) →
      ∀ η : Real, 0 < η → ∃ R : Real, 0 ≤ R ∧ ∀ k,
        μ.real {ω | ENNReal.ofReal R < ⨆ t : NNReal,
          ENNReal.ofReal |M (V k) t ω|} ≤ η)
    (hFinite : ∀ ε : Real, 0 < ε → ∃ N : Real, 0 ≤ N ∧
      ∀ δ : Real, 0 < δ → δ ≤ ε / 4 → ∃ c₀ : Real, 0 ≤ c₀ ∧
        ∀ (w : W) (c : Real), c₀ ≤ c → admissibleWeight w →
          ε < μ.real (tailEvent w c ε) → ∃ V : I, P V ∧
            ε / 2 < μ.real {ω |
              ENNReal.ofReal (((1 + N) * δ)⁻¹ * (ε / 2)) <
                ⨆ t : NNReal, ENNReal.ofReal |M V t ω|}) :
    ∀ ε : Real, 0 < ε → ∃ c₀ : Real, 0 ≤ c₀ ∧
      ∀ (w : W) (c : Real), c₀ ≤ c → admissibleWeight w →
        μ.real (tailEvent w c ε) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN, hFinite⟩ := hFinite ε hε
  have haN : 0 < (1 : Real) + N := by linarith
  by_contra hConclusion
  have hBad : ∀ c₀ : Real, 0 ≤ c₀ → ∃ (w : W) (c : Real),
      c₀ ≤ c ∧ admissibleWeight w ∧ ε < μ.real (tailEvent w c ε) := by
    intro c₀ hc₀
    by_contra hWitness
    apply hConclusion
    refine ⟨c₀, hc₀, ?_⟩
    intro w c hc hw
    by_contra hTail
    exact hWitness ⟨w, c, hc, hw, lt_of_not_ge hTail⟩
  let δ : Nat → Real := fun k =>
    (ε / 4) * (1 + N)⁻¹ * (((k + 1 : Nat) : Real)⁻¹)
  have hδ k : 0 < δ k := by dsimp only [δ]; positivity
  have hδ_le k : δ k ≤ ε / 4 := by
    have hInvN : (1 + N)⁻¹ ≤ (1 : Real) :=
      (inv_le_one₀ haN).2 (by linarith)
    have hInvK : (((k + 1 : Nat) : Real)⁻¹) ≤ (1 : Real) :=
      (inv_le_one₀ (by positivity)).2 (by norm_num)
    dsimp only [δ]
    calc
      _ ≤ ε / 4 * 1 * (((k + 1 : Nat) : Real)⁻¹) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hInvN (by positivity)) (by positivity)
      _ ≤ ε / 4 * 1 * 1 :=
        mul_le_mul_of_nonneg_left hInvK (by positivity)
      _ = ε / 4 := by ring
  have hWitness k : ∃ V : I, P V ∧
      ε / 2 < μ.real {ω | ENNReal.ofReal (((1 + N) * δ k)⁻¹ * (ε / 2)) <
        ⨆ t : NNReal, ENNReal.ofReal |M V t ω|} := by
    obtain ⟨c₀, hc₀, hConstruct⟩ := hFinite (δ k) (hδ k) (hδ_le k)
    obtain ⟨w, c, hc, hw, hHigh⟩ := hBad c₀ hc₀
    exact hConstruct w c hc hw hHigh
  choose V hP hHigh using hWitness
  obtain ⟨R, hR, hBound⟩ := hMaximal V hP (ε / 4) (by positivity)
  obtain ⟨k, hk⟩ := exists_nat_gt R
  have hThreshold : (((1 : Real) + N) * δ k)⁻¹ * (ε / 2) =
      2 * ((k + 1 : Nat) : Real) := by
    dsimp only [δ]
    field_simp [haN.ne', hε.ne']; ring
  have hRThreshold : R ≤ (((1 : Real) + N) * δ k)⁻¹ * (ε / 2) := by
    rw [hThreshold]
    have hk' : R < (k : Real) := hk
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hSubset : {ω | ENNReal.ofReal (((1 + N) * δ k)⁻¹ * (ε / 2)) <
        ⨆ t : NNReal, ENNReal.ofReal |M (V k) t ω|} ⊆
      {ω | ENNReal.ofReal R < ⨆ t : NNReal, ENNReal.ofReal |M (V k) t ω|} :=
    fun _ hω => (ENNReal.ofReal_le_ofReal hRThreshold).trans_lt hω
  have hUpper := (measureReal_mono hSubset).trans (hBound k)
  linarith [hHigh k]

end FTAPTheorem42

/-! ## Application to original gains -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- Uniform decay for finite convex martingale tails of original gains. -/
theorem originalGain_finiteTail_tendsToZero
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (H : Nat → FiniteOriginalSpecialGain source Q)
    (q : Ω → Real) (hq : MemLp q 2 Q)
    (hLower : ∀ i, ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ (H i).original.gain t ω)
    (hBound : ∀ i, ∀ᵐ ω ∂Q, ∀ t, |(H i).original.gain t ω| ≤ ‖q ω‖) :
    ∀ ε : Real, 0 < ε → ∃ c₀ : Real, 0 ≤ c₀ ∧
      ∀ (w : TailConvexWeights 0) (c : Real), c₀ ≤ c →
        Q.real (convexTailPassageEvent (fun i => (H i).decomposition.N) w c ε) ≤ ε := by
  have hOriginal := originalGain_class_boundedInProbability source hNFLVR hQμ hμQ hUsual
    (fun i => (H i).original) (fun i => (H i).decomposition) (fun i => (H i).predictable)
    (fun _ ω => ‖q ω‖) (fun _ => hq.norm) hBound hLower
    ENNReal.toReal_nonneg (fun _ => by
      rw [eLpNorm_norm _ hq.aestronglyMeasurable, ENNReal.ofReal_toReal hq.eLpNorm_ne_top])
  have hMaximal : ∀ Y : Nat → OriginalSpecialGain source Q,
      (∀ k, (Y k).Normalized) → ∀ η : Real, 0 < η → ∃ R : Real, 0 ≤ R ∧ ∀ k,
        Q.real {ω | ENNReal.ofReal R < ⨆ t : NNReal,
          ENNReal.ofReal |(Y k).decomposition.N t ω|} ≤ η := by
    intro Y hY η hη
    choose ξ hξ hBound hNorm using fun k => (hY k).2
    have hBounded := originalGain_class_boundedInProbability source hNFLVR hQμ hμQ hUsual
      (fun k => (Y k).original) (fun k => (Y k).decomposition) (fun k => (Y k).predictable)
      ξ hξ hBound (fun k => (hY k).1) zero_le_one
      (fun k => by simpa only [ENNReal.ofReal_one] using hNorm k)
    obtain ⟨R, hR, hTail⟩ := hBounded η hη
    exact ⟨R, hR, fun k =>
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hTail k)).trans
        (by rw [ENNReal.toReal_ofReal hη.le])⟩
  have hFinite := originalGain_finiteTail_normalization source hQμ hμQ hUsual
    H q hq hLower hBound hOriginal
  have hResult := lemma48_tail_small_of_normalization
    (fun Y : OriginalSpecialGain source Q => Y.decomposition.N)
    OriginalSpecialGain.Normalized (fun _ : TailConvexWeights 0 => True)
    (convexTailPassageEvent (fun i => (H i).decomposition.N)) hMaximal
    (fun ε hε => by
      obtain ⟨N, hN, hFinite⟩ := hFinite ε hε
      exact ⟨N, hN, fun δ hδ hδε => by
        obtain ⟨c₀, hc₀, hFinite⟩ := hFinite δ hδ hδε
        exact ⟨c₀, hc₀, fun w c hc _ => hFinite w c hc⟩⟩)
  intro ε hε
  obtain ⟨c₀, hc₀, hResult⟩ := hResult ε hε
  exact ⟨c₀, hc₀, fun w c hc => hResult w c hc trivial⟩

end FTAPTheorem42.BoundedSourceIntegralMarket
