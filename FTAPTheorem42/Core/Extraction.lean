import FTAPTheorem42.Core.ForwardConvex
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Bounded-in-probability and extraction interfaces

This file contains the abstract Komlós-style extraction and boundedness
interfaces for terminal-gain sequences and claim sets.
-/

open Filter MeasureTheory Topology
open scoped BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Komlós-style extraction part without the terminal-gain closedness conclusion:
every terminal-gain sequence has forward convex combinations converging a.e. to
some raw claim.
-/
def TerminalGainHasAEForwardConvexCandidate
    (μ : Measure Ω) (K0 : Set (Ω → ℝ)) : Prop :=
  ∀ G : ℕ → Ω → ℝ,
    (∀ n, G n ∈ K0) →
      ∃ W : ForwardConvexWeights, ∃ G_lim, TendstoAE μ (W.apply G) G_lim

/--
A single sequence has a forward-convex a.e. limit.  This is the conclusion of
the Komlós extraction step, separated from any trading-model closedness.
-/
def HasForwardConvexAELimit
    (μ : Measure Ω) (G : ℕ → Ω → ℝ) : Prop :=
  ∃ W : ForwardConvexWeights, ∃ G_lim, TendstoAE μ (W.apply G) G_lim

theorem HasForwardConvexAELimit.shiftBack_const
    {μ : Measure Ω} {G : ℕ → Ω → ℝ} {c : ℝ}
    (hG : HasForwardConvexAELimit μ (fun n ω => G n ω + c)) :
    HasForwardConvexAELimit μ G := by
  rcases hG with ⟨W, G_lim, hlim⟩
  rw [W.apply_add_const G c] at hlim
  refine ⟨W, fun ω => G_lim ω - c, ?_⟩
  filter_upwards [hlim] with ω hω
  simpa using hω.sub_const c

/-- The class of sequences whose terms are terminal gains in `K₀`. -/
def TerminalGainSequenceClass (K0 : Set (Ω → ℝ)) :
    Set (ℕ → Ω → ℝ) :=
  { G | ∀ n, G n ∈ K0 }

/--
A sequence of real-valued claims is bounded in probability.  This is the
standard tightness-type input used before applying Komlós extraction.
-/
def BoundedInProbability
    (μ : Measure Ω) (G : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ n : ℕ, μ {ω | R < |G n ω|} ≤ ENNReal.ofReal ε

theorem BoundedInProbability.neg
    {μ : Measure Ω} {G : ℕ → Ω → ℝ}
    (hG : BoundedInProbability μ G) :
    BoundedInProbability μ (fun n ω => -G n ω) := by
  intro ε hε
  rcases hG ε hε with ⟨R, hR, htail⟩
  refine ⟨R, hR, ?_⟩
  intro n
  simpa only [abs_neg] using htail n

theorem BoundedInProbability.add
    {μ : Measure Ω} {F G : ℕ → Ω → ℝ}
    (hF : BoundedInProbability μ F)
    (hG : BoundedInProbability μ G) :
    BoundedInProbability μ (fun n ω => F n ω + G n ω) := by
  intro ε hε
  have hεhalf : 0 < ε / 2 := half_pos hε
  rcases hF (ε / 2) hεhalf with ⟨RF, hRF, hFtail⟩
  rcases hG (ε / 2) hεhalf with ⟨RG, hRG, hGtail⟩
  refine ⟨RF + RG, add_nonneg hRF hRG, ?_⟩
  intro n
  have hsubset :
      {ω | RF + RG < |F n ω + G n ω|} ⊆
        {ω | RF < |F n ω|} ∪ {ω | RG < |G n ω|} := by
    intro ω hω
    change RF < |F n ω| ∨ RG < |G n ω|
    by_cases hFlarge : RF < |F n ω|
    · exact Or.inl hFlarge
    · right
      by_contra hGnot
      have hFle : |F n ω| ≤ RF := le_of_not_gt hFlarge
      have hGle : |G n ω| ≤ RG := le_of_not_gt hGnot
      have htriangle : |F n ω + G n ω| ≤ |F n ω| + |G n ω| :=
        abs_add_le _ _
      have hω' : RF + RG < |F n ω| + |G n ω| :=
        lt_of_lt_of_le hω htriangle
      linarith
  calc
    μ {ω | RF + RG < |F n ω + G n ω|} ≤
        μ ({ω | RF < |F n ω|} ∪ {ω | RG < |G n ω|}) :=
      measure_mono hsubset
    _ ≤ μ {ω | RF < |F n ω|} + μ {ω | RG < |G n ω|} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hFtail n) (hGtail n)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hεhalf.le hεhalf.le]
      congr 1
      ring

theorem BoundedInProbability.sub
    {μ : Measure Ω} {F G : ℕ → Ω → ℝ}
    (hF : BoundedInProbability μ F)
    (hG : BoundedInProbability μ G) :
    BoundedInProbability μ (fun n ω => F n ω - G n ω) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem BoundedInProbability.add_const
    {μ : Measure Ω} {G : ℕ → Ω → ℝ} {c : ℝ}
    (hG : BoundedInProbability μ G) :
    BoundedInProbability μ (fun n ω => G n ω + c) := by
  intro ε hε
  rcases hG ε hε with ⟨R, hR, htail⟩
  refine ⟨R + |c|, add_nonneg hR (abs_nonneg c), ?_⟩
  intro n
  apply (measure_mono ?_).trans (htail n)
  intro ω hω
  change R < |G n ω|
  change R + |c| < |G n ω + c| at hω
  have htriangle : |G n ω + c| ≤ |G n ω| + |c| := abs_add_le _ _
  linarith

/-- A finite a.e.-measurable real function gives a bounded-in-probability
constant sequence on a finite measure space. -/
theorem BoundedInProbability.const_of_aemeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → ℝ}
    (hg : AEMeasurable g μ) :
    BoundedInProbability μ (fun _ : ℕ => g) := by
  let E : ℕ → Set Ω := fun n => {ω | (n : ℝ) < |g ω|}
  have hE_meas : ∀ n, NullMeasurableSet (E n) μ := by
    intro n
    exact (hg.norm.nullMeasurableSet_preimage measurableSet_Ioi)
  have hE_anti : Antitone E := by
    intro n m hnm ω hω
    change (m : ℝ) < |g ω| at hω
    change (n : ℝ) < |g ω|
    exact lt_of_le_of_lt (by exact_mod_cast hnm) hω
  have hE_empty : ⋂ n, E n = (∅ : Set Ω) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    obtain ⟨n, hn⟩ := exists_nat_gt |g ω|
    have hωn := Set.mem_iInter.1 hω n
    change (n : ℝ) < |g ω| at hωn
    exact (not_lt_of_ge hn.le) hωn
  have htail_tendsto : Tendsto (fun n => μ (E n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) hE_meas hE_anti
      ⟨0, measure_ne_top _ _⟩
    simpa [Function.comp_def, hE_empty] using h
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at htail_tendsto
  obtain ⟨N, hN⟩ := htail_tendsto (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨N, Nat.cast_nonneg N, ?_⟩
  intro n
  simpa [E] using hN N le_rfl

theorem BoundedInProbability.const_of_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ) :
    BoundedInProbability μ (fun _ : ℕ => g) :=
  BoundedInProbability.const_of_aemeasurable hg.aemeasurable

theorem BoundedInProbability.const_of_stronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → ℝ}
    (hg : StronglyMeasurable g) :
    BoundedInProbability μ (fun _ : ℕ => g) :=
  BoundedInProbability.const_of_aestronglyMeasurable hg.aestronglyMeasurable

/-!
### The diagonal truncation step

The full bounded-in-probability Komlós theorem needs a subsequent
forward-convex `L¹` extraction.  The following lemmas isolate the standard
first step without adding atomicity or a uniform `L∞` bound: choose truncation
levels whose errors are summable, then use the first Borel--Cantelli lemma.
-/

/-!
### Geometric thresholds from boundedness in probability

The next two lemmas isolate the countable localization input used by the
stochastic modules.  The first chooses one non-negative threshold for each
coordinate.  The second consumes the summable geometric tail estimate with
`ae_eventually_notMem` and records the resulting eventual pathwise envelope.
-/

/-- The class of sequences bounded in probability. -/
def BoundedInProbabilitySequenceClass
    (μ : Measure Ω) : Set (ℕ → Ω → ℝ) :=
  { G | BoundedInProbability μ G }

/--
The stochastic boundedness estimate needed before applying the abstract Komlós
theorem to terminal gains.
-/
def TerminalGainSequencesBoundedInProbability
    (μ : Measure Ω) (K0 : Set (Ω → ℝ)) : Prop :=
  TerminalGainSequenceClass K0 ⊆ BoundedInProbabilitySequenceClass μ

/-- A set of claims is bounded in probability, uniformly over all its members. -/
def ClaimSetBoundedInProbability
    (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ f ∈ D, μ {ω | R < |f ω|} ≤ ENNReal.ofReal ε

theorem ClaimSetBoundedInProbability.mono
    {μ : Measure Ω} {D E : Set (Ω → ℝ)}
    (hE : ClaimSetBoundedInProbability μ E) (hDE : D ⊆ E) :
    ClaimSetBoundedInProbability μ D := by
  intro ε hε
  rcases hE ε hε with ⟨R, hRnonneg, hR⟩
  exact ⟨R, hRnonneg, fun f hf => hR f (hDE hf)⟩

/-- A set of claims has a uniform a.e. lower bound. -/
def ClaimSetAELowerBoundedBy
    (μ : Measure Ω) (a : ℝ) (D : Set (Ω → ℝ)) : Prop :=
  ∀ f ∈ D, AELowerBoundedBy μ (-a) f

/--
The part of a claim set consisting of claims with a fixed a.e. lower bound.
For `a = 1` this is the abstract version of the uniformly `1`-admissible
terminal gains used in Proposition 3.1.
-/
def ClaimSetWithAELowerBound
    (μ : Measure Ω) (a : ℝ) (D : Set (Ω → ℝ)) : Set (Ω → ℝ) :=
  { f | f ∈ D ∧ AELowerBoundedBy μ (-a) f }

theorem ClaimSetWithAELowerBound_subset
    {μ : Measure Ω} {a : ℝ} {D : Set (Ω → ℝ)} :
    ClaimSetWithAELowerBound μ a D ⊆ D := by
  intro f hf
  exact hf.1

theorem ClaimSetWithAELowerBound_lowerBound
    {μ : Measure Ω} {a : ℝ} {D : Set (Ω → ℝ)} :
    ClaimSetAELowerBoundedBy μ a (ClaimSetWithAELowerBound μ a D) := by
  intro f hf
  exact hf.2

/-- Every claim in the set has an a.e. strongly measurable representative. -/
def ClaimSetAEStronglyMeasurable
    (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  ∀ f ∈ D, AEStronglyMeasurable f μ

/-- Every claim in the set is strongly measurable as a concrete representative. -/
def ClaimSetStronglyMeasurable
    (D : Set (Ω → ℝ)) : Prop :=
  ∀ f ∈ D, StronglyMeasurable f

theorem ClaimSetStronglyMeasurable.aestronglyMeasurable
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hD : ClaimSetStronglyMeasurable D) :
    ClaimSetAEStronglyMeasurable μ D := by
  intro f hf
  exact (hD f hf).aestronglyMeasurable

/--
Concrete witness form of failure of boundedness in probability: for some
fixed positive mass level `ε`, every nonnegative radius misses a claim in `D`.
-/
def ClaimSetUnboundedInProbabilityWitness
    (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ R : ℝ, 0 ≤ R →
      ∃ f ∈ D, ENNReal.ofReal ε < μ {ω | R < |f ω|}

/--
Negating boundedness in probability gives the usual fixed-`ε` family of
counterexamples at every radius.
-/
theorem ClaimSetUnboundedInProbabilityWitness.of_not_bounded
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hnot : ¬ ClaimSetBoundedInProbability μ D) :
    ClaimSetUnboundedInProbabilityWitness μ D := by
  classical
  rw [ClaimSetBoundedInProbability] at hnot
  push Not at hnot
  rcases hnot with ⟨ε, hεpos, hε⟩
  refine ⟨ε, hεpos, ?_⟩
  intro R hR
  rcases hε R hR with ⟨f, hfD, hfμ⟩
  exact ⟨f, hfD, hfμ⟩

/--
A witness to unboundedness in probability can be sampled at any prescribed
sequence of nonnegative thresholds.  The same positive mass level works at
every threshold.
-/
theorem ClaimSetUnboundedInProbabilityWitness.exists_sequence_at
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (h : ClaimSetUnboundedInProbabilityWitness μ D)
    (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ G : ℕ → Ω → ℝ,
        (∀ n, G n ∈ D) ∧
        ∀ n, ENNReal.ofReal ε < μ {ω | R n < |G n ω|} := by
  classical
  rcases h with ⟨ε, hεPositive, hε⟩
  have hseq :
      ∀ n, ∃ f ∈ D, ENNReal.ofReal ε < μ {ω | R n < |f ω|} := by
    intro n
    exact hε (R n) (hR n)
  choose G hGmem hGMeasure using hseq
  exact ⟨ε, hεPositive, G, hGmem, hGMeasure⟩

/--
Positive-tail witness form.  This is the form used in Proposition 3.1 after
admissibility rules out large negative tails.
-/
def ClaimSetUnboundedPositiveTailWitness
    (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ R : ℝ, 0 ≤ R →
      ∃ f ∈ D, ENNReal.ofReal ε < μ {ω | R < f ω}

/--
If all claims are a.e. bounded below by `-1`, then an absolute-tail witness can
be converted into a positive-tail witness.
-/
theorem ClaimSetUnboundedPositiveTailWitness.of_absWitness_of_aeLowerBound
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hLower : ClaimSetAELowerBoundedBy μ 1 D)
    (hAbs : ClaimSetUnboundedInProbabilityWitness μ D) :
    ClaimSetUnboundedPositiveTailWitness μ D := by
  classical
  rcases hAbs with ⟨ε, hεpos, hε⟩
  refine ⟨ε, hεpos, ?_⟩
  intro R hR
  let R' : ℝ := max R 1
  have hR'nonneg : 0 ≤ R' := le_trans hR (le_max_left R 1)
  rcases hε R' hR'nonneg with ⟨f, hfD, hfμ⟩
  refine ⟨f, hfD, ?_⟩
  have hsub : {ω | R' < |f ω|} ≤ᵐ[μ] {ω | R < f ω} := by
    filter_upwards [hLower f hfD] with ω hlow htail
    change R' < |f ω| at htail
    have hRle : R ≤ R' := le_max_left R 1
    have hOnele : 1 ≤ R' := le_max_right R 1
    by_cases hfneg : f ω < 0
    · have habs : |f ω| = -f ω := abs_of_neg hfneg
      have htail' : R' < -f ω := by simpa [habs] using htail
      have hlow' : -R' ≤ f ω := by linarith
      linarith
    · have hfnonneg : 0 ≤ f ω := le_of_not_gt hfneg
      have habs : |f ω| = f ω := abs_of_nonneg hfnonneg
      have htail' : R' < f ω := by simpa [habs] using htail
      linarith
  exact lt_of_lt_of_le hfμ (measure_mono_ae hsub)

/--
A positive-tail witness chooses a sequence whose positive tails stay above a
fixed mass level at thresholds `n`.
-/
theorem ClaimSetUnboundedPositiveTailWitness.exists_sequence
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (h : ClaimSetUnboundedPositiveTailWitness μ D) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ G : ℕ → Ω → ℝ,
        (∀ n, G n ∈ D) ∧
        ∀ n : ℕ, ENNReal.ofReal ε < μ {ω | (n : ℝ) < G n ω} := by
  classical
  rcases h with ⟨ε, hεpos, hε⟩
  have hseq :
      ∀ n : ℕ,
        ∃ f ∈ D, ENNReal.ofReal ε < μ {ω | (n : ℝ) < f ω} := by
    intro n
    exact hε (n : ℝ) (by exact_mod_cast Nat.zero_le n)
  choose G hGmem hGμ using hseq
  exact ⟨ε, hεpos, G, hGmem, hGμ⟩

/-- Boundedness in probability of `K₀` implies the sequence-level estimate. -/
theorem TerminalGainSequencesBoundedInProbability.of_setBounded
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)}
    (hBound : ClaimSetBoundedInProbability μ K0) :
    TerminalGainSequencesBoundedInProbability μ K0 := by
  intro G hG ε hε
  rcases hBound ε hε with ⟨R, hRnonneg, hR⟩
  exact ⟨R, hRnonneg, fun n => hR (G n) (hG n)⟩

end FTAPTheorem42
