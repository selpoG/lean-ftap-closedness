/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import FTAPTheorem42.Stochastic.Topology.R1.CommonComponents

/-! # Assembling the three coordinates of r1 convergence -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu]

theorem J1Decomposition.tendsto_r1Cost_of_coordinates
    {Z : Nat → Process Ω} (D : ∀ n, J1Decomposition (Z n) F mu)
    (Q : ∀ n, LocalMartingaleQuadraticVariation (D n).N F mu)
    (hJump : Tendsto (fun n => boundedStoppingJumpCost (D n).N F mu) atTop (𝓝 0))
    (hRoot : ∀ T : NNReal, Tendsto (fun n => ∫⁻ w,
      min (ENNReal.ofReal (Real.sqrt ((Q n).variation T w))) 1 ∂mu) atTop (𝓝 0))
    (hVar : ∀ T : NNReal, Tendsto (fun n => ∫⁻ w,
      min (eVariationOn ((D n).A · w) (Icc 0 T)) 1 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n => (D n).r1Cost (Q n)) atTop (𝓝 0) := by
  have hClock (T : NNReal) : Tendsto
      (fun n => ∫⁻ w, min ((D n).clock (Q n) T w) 1 ∂mu) atTop (𝓝 0) := by
    have hUpper := (hRoot T).add (hVar T)
    simp only [add_zero] at hUpper
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _ => bot_le)
    intro n
    dsimp only
    have hMeas := (((Q n).stronglyAdapted T).mono (F.le T)).measurable.sqrt.ennreal_ofReal
    rw [← lintegral_add_left (hMeas.min measurable_const)]
    exact lintegral_mono (fun _ => min_add_one_le _ _)
  let a := fun j : Nat => (2 : ENNReal)⁻¹ ^ (j + 1)
  let f := fun n j => a j * ∫⁻ w, min ((D n).clock (Q n) (j : NNReal) w) 1 ∂mu
  have hFinite : (∫⁻ j, a j ∂Measure.count) ≠ ∞ := by
    rw [lintegral_count]
    have hOne : (∑' j, a j) = 1 := by
      dsimp only [a]
      rw [ENNReal.tsum_geometric_add_one]
      norm_num
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    rw [hOne]
    norm_num
  have hBound (n : Nat) : ∀ᵐ j ∂Measure.count, f n j ≤ a j := by
    apply Eventually.of_forall
    intro j
    apply (mul_le_mul' le_rfl (lintegral_mono (fun _ => min_le_right _ _))).trans_eq
    simp
  have hLimit : ∀ᵐ j ∂Measure.count, Tendsto (fun n => f n j) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro j
    have h := ENNReal.Tendsto.const_mul (hClock j) (Or.inr
      (show a j ≠ ∞ by simp [a]))
    simpa only [mul_zero] using h
  have hSeries := tendsto_lintegral_of_dominated_convergence' a
    (fun _ => (measurable_of_countable _).aemeasurable) hBound hFinite hLimit
  simp only [lintegral_count, tsum_zero] at hSeries
  have h := hJump.add hSeries
  simpa only [J1Decomposition.r1Cost, f, a, add_zero] using h

end FTAPTheorem42

namespace FTAPTheorem42.R1Process

/-! ## Completeness of the r1 space of decomposable processes -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [hUsual : Fact (Filtration.UsualConditions mu F)]

theorem exists_subsequence_tendsto_of_cauchy {Z : Nat → R1Process F mu}
    (h : CauchySeq (fun k => SeparationQuotient.mk (Z k))) :
    ∃ (f : Nat → Nat) (X : R1Process F mu), StrictMono f ∧
      Tendsto (fun k => SeparationQuotient.mk (Z (f k))) atTop
        (𝓝 (SeparationQuotient.mk X)) := by
  obtain ⟨f, hf, D, _, _, _, _, M, hMA, hMM, hMR, hML, hMZ, _, _, hJump,
      A, hAA, hAR, hAL, hAV, hAZ, _, hVar, P, hRoot, _⟩ :=
    exists_common_decomposition_components_of_cauchy h
  let E : J1Decomposition (fun t w => M t w + A t w) F mu := {
    N := M
    A := A
    decomposition := Eventually.of_forall (fun _ _ => rfl)
    localMartingale := hMM
    adaptedN := hMA
    rightN := hMR
    leftN := hML
    zeroN := hMZ
    adaptedA := hAA
    rightA := hAR
    leftA := hAL
    variationA := hAV
    zeroA := hAZ }
  obtain ⟨E0⟩ := (Z (f 0)).property
  let X : R1Process F mu :=
    ⟨(Z (f 0)).val + (fun t w => M t w + A t w), ⟨E0.add E⟩⟩
  let B : Nat → (Σ Y : Process Ω, J1Decomposition Y F mu) :=
    Nat.rec ⟨(fun t w => M t w + A t w), E⟩
      (fun n b => ⟨b.1 + -((Z (f (n + 1))).val - (Z (f n)).val), b.2.add (D n).neg⟩)
  have hBN : ∀ n, (B n).2.N = fun t w => M t w - ∑ k ∈ Finset.range n, (D k).N t w := by
    intro n
    induction n with
    | zero => funext t w; simp [B, E]
    | succ n ih =>
      funext t w
      change (B n).2.N t w + -(D n).N t w = _
      rw [ih, Finset.sum_range_succ]
      ring
  have hBA : ∀ n, (B n).2.A = fun t w => A t w - ∑ k ∈ Finset.range n, (D k).A t w := by
    intro n
    induction n with
    | zero => funext t w; simp [B, E]
    | succ n ih =>
      funext t w
      change (B n).2.A t w + -(D n).A t w = _
      rw [ih, Finset.sum_range_succ]
      ring
  have hSource : ∀ n, (B n).1 = X.val - (Z (f n)).val := by
    intro n
    induction n with
    | zero =>
      funext t w
      change M t w + A t w = (Z (f 0)).val t w + (M t w + A t w) - (Z (f 0)).val t w
      ring
    | succ n ih =>
      change (B n).1 + -((Z (f (n + 1))).val - (Z (f n)).val) = _
      rw [ih]
      abel
  let C : ∀ n, J1Decomposition (B n).1 F mu := fun n => {
    (B n).2 with
    N := fun t w => M t w - ∑ k ∈ Finset.range n, (D k).N t w
    decomposition := by simpa only [hBN n] using (B n).2.decomposition
    localMartingale := by simpa only [hBN n] using (B n).2.localMartingale
    adaptedN := by simpa only [hBN n] using (B n).2.adaptedN
    rightN := by simpa only [hBN n] using (B n).2.rightN
    leftN := by simpa only [hBN n] using (B n).2.leftN
    zeroN := by simpa only [hBN n] using (B n).2.zeroN }
  have hVarC : ∀ T : NNReal, Tendsto (fun n => ∫⁻ w,
      min (eVariationOn ((C n).A · w) (Icc 0 T)) 1 ∂mu) atTop (𝓝 0) := by
    intro T
    simpa only [C, hBA] using hVar T
  have hCost := J1Decomposition.tendsto_r1Cost_of_coordinates C P hJump hRoot hVarC
  have hR1 : Tendsto (fun n => semimartingaleR1 (X.val - (Z (f n)).val) F mu) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hCost (fun _ => bot_le)
    intro n
    dsimp only
    rw [← hSource n]
    exact iInf_le_of_le (C n) (iInf_le _ (P n))
  refine ⟨f, X, hf, quotient_tendsto_iff.mpr ?_⟩
  apply hR1.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [show X.val - (Z (f n)).val = -((Z (f n)).val - X.val) by abel,
    semimartingaleR1_neg]

instance : CompleteSpace (SeparationQuotient (R1Process F mu)) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  choose Z hZ using fun n => SeparationQuotient.surjective_mk (u n)
  have hC : CauchySeq (fun n => SeparationQuotient.mk (Z n)) := by
    simpa only [hZ] using hu
  obtain ⟨f, X, hf, hLimit⟩ := exists_subsequence_tendsto_of_cauchy hC
  refine ⟨SeparationQuotient.mk X, tendsto_nhds_of_cauchySeq_of_subseq hu hf.tendsto_atTop ?_⟩
  change Tendsto (fun k => u (f k)) atTop (𝓝 (SeparationQuotient.mk X))
  simpa only [hZ] using hLimit

end FTAPTheorem42.R1Process
