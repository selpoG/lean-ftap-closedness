/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma48.CommonGainCap

/-!
# The tail-martingale cutoff in Lemma 4.8

After choosing a finite convex combination of post-passage tails, the proof
of Lemma 4.8 stops its martingale component at a fixed positive level.  This
module combines that passage with the common gain cap and active-weight
cutoff.  It proves both deterministic admissibility of the resulting actual
strategy and the probability estimate which preserves a large martingale
event outside the two localization errors.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- First strict passage of the martingale component of a finite convex
combination of post-passage tails. -/
noncomputable def lemma48TailMartingalePassage
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c ε : ℝ) : Ω → WithTop ℝ≥0 :=
  lemma48FirstPassage (C.lemma48TailConvexStrategy H weight n c) ε

theorem lemma48TailMartingalePassage_isStoppingTime
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c ε : ℝ) :
    IsStoppingTime ℱ
      (C.lemma48TailMartingalePassage H weight n c ε) :=
  lemma48FirstPassage_isStoppingTime
    (C.lemma48TailConvexStrategy H weight n c) ε

/-- Event that the convex tail martingale reaches its passage level. -/
def lemma48TailMartingalePassageFiniteEvent
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c ε : ℝ) : Set Ω :=
  {ω | C.lemma48TailMartingalePassage H weight n c ε ω ≠ ⊤}

/-- The earlier of the tail-martingale passage, common gain cap, and
active-weight cutoff. -/
noncomputable def lemma48FullCutoff
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ) : Ω → WithTop ℝ≥0 :=
  fun ω => min (C.lemma48TailMartingalePassage H weight n c ε ω)
    (lemma48GainActiveCutoff H weight n c N δ ω)

theorem lemma48FullCutoff_isStoppingTime
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ) :
    IsStoppingTime ℱ (C.lemma48FullCutoff H weight n c N δ ε) :=
  (C.lemma48TailMartingalePassage_isStoppingTime H weight n c ε).min
    (lemma48GainActiveCutoff_isStoppingTime H weight n c N δ)

/-- The actual convex tail strategy stopped at all three localization
times. -/
noncomputable def lemma48FullyLocalizedTailConvexStrategy
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ) : SIntegrableStrategy D :=
  C.stopAtTop (C.lemma48FullCutoff H weight n c N δ ε)
    (C.lemma48FullCutoff_isStoppingTime H weight n c N δ ε)
    (C.lemma48TailConvexStrategy H weight n c)

theorem lemma48FullyLocalizedTailConvexStrategy_stochasticIntegral
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ) :
    ProcessIndistinguishable μ
      (C.lemma48FullyLocalizedTailConvexStrategy
        H weight n c N δ ε).stochasticIntegral
      (MeasureTheory.stoppedProcess
        (C.lemma48TailConvexStrategy H weight n c).stochasticIntegral
        (C.lemma48FullCutoff H weight n c N δ ε)) :=
  C.stochasticIntegral_stopAtTop
    (C.lemma48FullCutoff H weight n c N δ ε)
    (C.lemma48FullCutoff_isStoppingTime H weight n c N δ ε)
    (C.lemma48TailConvexStrategy H weight n c)

theorem lemma48FullyLocalizedTailConvexStrategy_martingalePart
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ) :
    ProcessIndistinguishable μ
      (C.lemma48FullyLocalizedTailConvexStrategy
        H weight n c N δ ε).martingalePart
      (MeasureTheory.stoppedProcess
        (C.lemma48TailConvexStrategy H weight n c).martingalePart
        (C.lemma48FullCutoff H weight n c N δ ε)) :=
  C.martingalePart_stopAtTop
    (C.lemma48FullCutoff H weight n c N δ ε)
    (C.lemma48FullCutoff_isStoppingTime H weight n c N δ ε)
    (C.lemma48TailConvexStrategy H weight n c)

/-- The full three-way localization retains the deterministic admissibility
bound supplied by the common gain cap and active-weight cutoff. -/
theorem lemma48FullyLocalizedTailConvexStrategy_stochasticIntegral_lower_bound
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ)
    {a : ℝ}
    (hδ : 0 ≤ δ) (haN : 0 ≤ a + N)
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i)
    (hLower : ∀ i, ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      -a ≤ (H i).stochasticIntegral t ω) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      -(a + N) * δ ≤
        (C.lemma48FullyLocalizedTailConvexStrategy
          H weight n c N δ ε).stochasticIntegral t ω := by
  filter_upwards [C.lemma48FullyLocalizedTailConvexStrategy_stochasticIntegral
      H weight n c N δ ε,
    C.lemma48TailConvexStrategy_stochasticIntegral_lower_bound_before_commonGainCap
      H weight n c N hWeight hLower] with ω hStop hTail
  intro t
  rw [hStop t]
  let σ := C.lemma48FullCutoff H weight n c N δ ε
  let u := RightContinuousStoppedMartingale.boundedTime t σ ω
  have huCap : (u : WithTop ℝ≥0) ≤ lemma48CommonGainCap H N ω := by
    rw [RightContinuousStoppedMartingale.coe_boundedTime]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have huActive : (u : WithTop ℝ≥0) ≤
      lemma48ActiveMassCutoff H weight n c δ ω := by
    rw [RightContinuousStoppedMartingale.coe_boundedTime]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  have hMass := lemma48ActiveMass_stopped_le
    H weight n c δ hδ u ω
  rw [MeasureTheory.stoppedProcess_eq_of_le huActive] at hMass
  rw [← RightContinuousStoppedMartingale.sample_boundedTime_eq_stoppedProcess]
  change -(a + N) * δ ≤
    (C.lemma48TailConvexStrategy H weight n c).stochasticIntegral u ω
  exact (mul_le_mul_of_nonpos_left hMass (neg_nonpos.mpr haN)).trans
    (hTail u huCap)

/-- All-time martingale event of the fully localized tail, at half the raw
passage level.  The factor `1/2` avoids any strictness issue at a right-
continuous first passage. -/
def lemma48FullyLocalizedMartingaleHighEvent
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ) : Set Ω :=
  {ω | ENNReal.ofReal (ε / 2) <
    ⨆ t : ℝ≥0, ENNReal.ofReal
      |(C.lemma48FullyLocalizedTailConvexStrategy
        H weight n c N δ ε).martingalePart t ω|}

/-- A finite raw tail-martingale passage is preserved by the full cutoff
unless the common gain cap or active-weight cutoff is finite. -/
theorem measureReal_lemma48TailMartingalePassageFiniteEvent_le
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ) (hε : 0 < ε) :
    μ.real (C.lemma48TailMartingalePassageFiniteEvent H weight n c ε) ≤
      μ.real (C.lemma48FullyLocalizedMartingaleHighEvent
        H weight n c N δ ε) +
      μ.real {ω | lemma48CommonGainCap H N ω ≠ ⊤} +
      μ.real {ω | lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤} := by
  let A : Set Ω :=
    C.lemma48TailMartingalePassageFiniteEvent H weight n c ε
  let B : Set Ω := C.lemma48FullyLocalizedMartingaleHighEvent
    H weight n c N δ ε
  let G : Set Ω := {ω | lemma48CommonGainCap H N ω ≠ ⊤}
  let V : Set Ω :=
    {ω | lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤}
  have hSubset : A ≤ᵐ[μ] Set.union B (Set.union G V) := by
    filter_upwards [C.lemma48FullyLocalizedTailConvexStrategy_martingalePart
      H weight n c N δ ε] with ω hStopped
    intro hPassage
    by_cases hGainCap : lemma48CommonGainCap H N ω ≠ ⊤
    · exact Set.mem_union_right B (Set.mem_union_left V hGainCap)
    by_cases hActive : lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤
    · exact Set.mem_union_right B (Set.mem_union_right G hActive)
    apply Set.mem_union_left (G ∪ V)
    have hGainCapTop : lemma48CommonGainCap H N ω = ⊤ :=
      not_ne_iff.mp hGainCap
    have hActiveTop :
        lemma48ActiveMassCutoff H weight n c δ ω = ⊤ :=
      not_ne_iff.mp hActive
    have hFullCutoff : C.lemma48FullCutoff H weight n c N δ ε ω =
        C.lemma48TailMartingalePassage H weight n c ε ω := by
      simp [lemma48FullCutoff, lemma48GainActiveCutoff,
        hGainCapTop, hActiveTop]
    have hPassageNe :
        C.lemma48TailMartingalePassage H weight n c ε ω ≠ ⊤ :=
      hPassage
    let u := (C.lemma48TailMartingalePassage
      H weight n c ε ω).untopA
    have huCoe : (u : WithTop ℝ≥0) =
        C.lemma48TailMartingalePassage H weight n c ε ω := by
      dsimp only [u]
      rw [WithTop.untopA_eq_untop hPassageNe,
        WithTop.coe_untop _ hPassageNe]
    have hAt : ε ≤
        |(C.lemma48TailConvexStrategy H weight n c).martingalePart u ω| := by
      simpa only [u, lemma48TailMartingalePassage, lemma48FirstPassage] using
        (le_abs_untopA_absoluteStrictHittingAfter
          (C.lemma48TailConvexStrategy H weight n c).martingalePart
          (C.lemma48TailConvexStrategy H weight n c).martingalePart_isRightContinuous
          ε ω hPassageNe)
    have hStoppedAt :
        (C.lemma48FullyLocalizedTailConvexStrategy
          H weight n c N δ ε).martingalePart u ω =
          (C.lemma48TailConvexStrategy H weight n c).martingalePart u ω := by
      rw [hStopped u]
      apply MeasureTheory.stoppedProcess_eq_of_le
      rw [hFullCutoff, huCoe]
    change ENNReal.ofReal (ε / 2) <
      ⨆ t : ℝ≥0, ENNReal.ofReal
        |(C.lemma48FullyLocalizedTailConvexStrategy
          H weight n c N δ ε).martingalePart t ω|
    rw [lt_iSup_iff]
    refine ⟨u, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (by positivity : 0 ≤ ε / 2)).2 ?_⟩
    rw [hStoppedAt]
    linarith
  have hMeasure : μ.real A ≤ μ.real (B ∪ (G ∪ V)) :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hSubset)
  calc
    μ.real A ≤ μ.real (B ∪ (G ∪ V)) := hMeasure
    _ ≤ μ.real B + μ.real (G ∪ V) := measureReal_union_le B (G ∪ V)
    _ ≤ μ.real B + (μ.real G + μ.real V) := by
      gcongr
      exact measureReal_union_le G V
    _ = μ.real B + μ.real G + μ.real V := by ring

/-- Quantitative form of the preceding event inclusion: the raw high-event
mass survives after subtracting exactly the two localization errors. -/
theorem measureReal_lemma48FullyLocalizedMartingaleHighEvent_gt
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε rawMass gainError activeError : ℝ)
    (hε : 0 < ε)
    (hRaw : rawMass <
      μ.real (C.lemma48TailMartingalePassageFiniteEvent H weight n c ε))
    (hGain : μ.real {ω | lemma48CommonGainCap H N ω ≠ ⊤} ≤ gainError)
    (hActive : μ.real {ω |
      lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤} ≤ activeError) :
    rawMass - gainError - activeError <
      μ.real (C.lemma48FullyLocalizedMartingaleHighEvent
        H weight n c N δ ε) := by
  have hUpper := C.measureReal_lemma48TailMartingalePassageFiniteEvent_le
    H weight n c N δ ε hε
  linarith

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
