/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Trading.Basic

/-!
# Switching and no-arbitrage estimates

This module starts discharging the `K1` route input that terminal lower bounds
control running gains.  The key extra structure is the ability to switch on a
strategy after a time on an event.  Under no-arbitrage, a terminal lower bound
then rules out deeper interim losses: otherwise the post-time strategy would be
an arbitrage.
-/

namespace FTAPTheorem42

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable section

namespace GainProcessModel

/-- A raw arbitrage in a set of terminal claims. -/
def Arbitrage (μ : Measure Ω) (K0 : Set (Ω → ℝ)) : Prop :=
  ∃ g ∈ K0, AENonnegative μ g ∧ 0 < μ {ω | 0 < g ω}

/-- No terminal claim in `K0` is a nonzero nonnegative payoff. -/
def NoArbitrage (μ : Measure Ω) (K0 : Set (Ω → ℝ)) : Prop :=
  ¬ Arbitrage μ K0

theorem toLp_ne_zero_of_measure_pos_pos
    {μ : Measure Ω} {f : Ω → ℝ} (hfLp : MemLp f ⊤ μ)
    (hfpos : 0 < μ {ω | 0 < f ω}) :
    hfLp.toLp f ≠ (0 : Linfty (Ω := Ω) μ) := by
  intro hzero
  have hzero_toLp :
      hfLp.toLp f =
        (MemLp.zero (α := Ω) (ε := ℝ) (p := ⊤) (μ := μ)).toLp (0 : Ω → ℝ) := by
    rw [hzero]
    exact (MemLp.zero (α := Ω) (ε := ℝ) (p := ⊤) (μ := μ)).toLp_zero.symm
  have hf_zero : f =ᵐ[μ] (0 : Ω → ℝ) :=
    (MemLp.toLp_eq_toLp_iff hfLp
      (MemLp.zero (α := Ω) (ε := ℝ) (p := ⊤) (μ := μ))).mp hzero_toLp
  have hpos_zero : μ {ω | 0 < f ω} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hf_zero] with ω hωeq hωpos
    rw [hωeq] at hωpos
    exact (lt_irrefl (0 : ℝ)) hωpos
  exact (ne_of_gt hfpos) hpos_zero

/--
NFLVR rules out arbitrary raw arbitrages as soon as claims in `K0` have
a.e.-strongly-measurable representatives.  A nonnegative arbitrage `g` is
truncated to the bounded claim `g ⊓ 1`, which lies in `C0` by solidity.
-/
theorem noArbitrage_of_linfyNFLVR
    {μ : Measure Ω} [IsFiniteMeasure μ] {K0 : Set (Ω → ℝ)}
    (hKmeas : ClaimSetAEStronglyMeasurable μ K0)
    (hNFLVR :
      LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ K0))) :
    NoArbitrage μ K0 := by
  rintro ⟨g, hgK0, hgnonneg, hgpos⟩
  let f : Ω → ℝ := g ⊓ fun _ => (1 : ℝ)
  have hfmeas : AEStronglyMeasurable f μ := by
    exact (hKmeas g hgK0).inf aestronglyMeasurable_const
  have hfnonneg : AENonnegative μ f := by
    filter_upwards [hgnonneg] with ω hgω
    exact le_inf hgω zero_le_one
  have hfupper : ∀ ω, f ω ≤ 1 := by
    intro ω
    exact inf_le_right
  have hfLp : MemLp f ⊤ μ := by
    refine MemLp.of_bound hfmeas 1 ?_
    filter_upwards [hfnonneg] with ω hfω
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hfupper ω⟩
  have hfC0 : f ∈ C0AsDifference μ K0 := by
    apply (C0AsDifference_iff_measurable_residual hKmeas hfmeas).mpr
    refine ⟨g, hgK0, fun ω => g ω - f ω,
      (hKmeas g hgK0).sub hfmeas, ?_, ?_⟩
    · exact Filter.Eventually.of_forall (fun _ => sub_nonneg.mpr inf_le_left)
    · exact Filter.Eventually.of_forall (fun ω => by ring)
  have hfpos : 0 < μ {ω | 0 < f ω} := by
    have hsubset : {ω | 0 < g ω} ⊆ {ω | 0 < f ω} := by
      intro ω hω
      dsimp [f]
      exact lt_inf_iff.mpr ⟨hω, zero_lt_one⟩
    exact lt_of_lt_of_le hgpos (measure_mono hsubset)
  let F : Linfty (Ω := Ω) μ := hfLp.toLp f
  have hFmem : F ∈ LinftyClaims μ (C0AsDifference μ K0) :=
    ⟨f, hfC0, hfLp, rfl⟩
  have hFnonneg : F ∈ LinftyNonnegative μ := by
    filter_upwards [MemLp.coeFn_toLp hfLp, hfnonneg] with ω hFω hfω
    rw [hFω]
    exact hfω
  have hFzero : F = 0 :=
    hNFLVR ⟨subset_closure hFmem, hFnonneg⟩
  exact toLp_ne_zero_of_measure_pos_pos hfLp hfpos hFzero

theorem eventually_and_of_measure_pos_of_ae
    {μ : Measure Ω} {s : Set Ω} {p : Ω → Prop}
    (hs : 0 < μ s) (hp : ∀ᵐ ω ∂μ, p ω) :
    0 < μ {ω | ω ∈ s ∧ p ω} := by
  have hfreq_s : ∃ᵐ ω ∂μ, ω ∈ s :=
    frequently_ae_iff.mpr (ne_of_gt hs)
  have hfreq_sp : ∃ᵐ ω ∂μ, ω ∈ s ∧ p ω :=
    hfreq_s.and_eventually hp
  exact pos_iff_ne_zero.mpr (frequently_ae_iff.mp hfreq_sp)

end GainProcessModel

end

/-!
## K1 bridge wrappers for gain-process models

This section assembles K1 candidate, boundedness, and closedness assumptions
into concrete Theorem 4.2 statements for abstract gain-process models.
-/

namespace GainProcessModel

/--
Weak-star Theorem 4.2 assembly with the functional-analytic boundary fully
discharged.  The only realization input left here is the stochastic one.
-/
theorem theorem42ConcreteWeakStar_from_gainProcessModel_K1_maximalRealization
    {Time : Type*} (A : GainProcessModel Ω Time) (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (boundedSemimartingale NFLVR : Prop)
    (hKmeas :
      ClaimSetStronglyMeasurable
        (K0OfTerminalGainModel (A.terminalGainModel μ)))
    (hTerminal : A.TerminalGainRespectsAdmissibleLowerBound μ)
    (hControl : A.TerminalLowerBoundControlsGain μ)
    (hNFLVR :
      boundedSemimartingale →
        NFLVR →
          LinftyNFLVR μ
            (LinftyClaims μ
              (C0AsDifference μ
                (K0OfTerminalGainModel (A.terminalGainModel μ)))))
    (hRealize :
      boundedSemimartingale →
        NFLVR →
          MaximalInMeasureClosureAERealizableBetween μ
            (A.K1OfGainProcessModel μ)
            (K0OfTerminalGainModel (A.terminalGainModel μ))) :
    theorem42ConcreteWeakStarStatement μ
      (K0OfTerminalGainModel (A.terminalGainModel μ))
      boundedSemimartingale NFLVR := by
  apply theorem42ConcreteWeakStar_from_fatou
    μ (K0OfTerminalGainModel (A.terminalGainModel μ))
    boundedSemimartingale NFLVR
    (K0_terminalGainModel_claimCone A μ)
  intro hS hNFLVR'
  exact fatouClosed_C0AsDifference_of_terminalGainFatouStable
    (A.terminalGainFatouStable_K0_of_K1_maximalInMeasureClosureAERealizable
      μ hKmeas hTerminal hControl (hNFLVR hS hNFLVR')
      (hRealize hS hNFLVR'))

end GainProcessModel

end FTAPTheorem42
