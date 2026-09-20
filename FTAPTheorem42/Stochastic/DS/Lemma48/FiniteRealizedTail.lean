import FTAPTheorem42.Stochastic.DS.Lemma48.NormalizedTail
import FTAPTheorem42.Stochastic.Market.Transfer.FiniteRealizedGain

/-! # Realizing the normalized Lemma 4.8 tails in the original price

The component bookkeeping source may differ from the original price. Only
indistinguishability of the stored gains is used to transport the actual
original-price realizations through stopping and finite linear operations.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.SIntegrableProcessStoppingCalculus

open PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S P : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition P F μ}

omit [SigmaFiniteFiltration μ F] in
/-- The numeric stop agrees with the actual original-price stopped gain. -/
theorem stopAtTop_hasFiniteRealizedGain
    (C : SIntegrableProcessStoppingCalculus D)
    (hS : IsStronglyProgressive F S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (H : SIntegrableStrategy D) (hH : HasFiniteRealizedGain μ F S H.stochasticIntegral)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ) :
    HasFiniteRealizedGain μ F S (C.stopAtTop τ hτ H).stochasticIntegral :=
  (hH.stoppedProcess hS hSR τ hτ).congr (C.stochasticIntegral_stopAtTop τ hτ H)

/-- Subtraction of the stopped gain realizes the strict post-stopping tail. -/
theorem postStoppingTail_hasFiniteRealizedGain
    (C : SIntegrableProcessStoppingCalculus D)
    (hS : IsStronglyProgressive F S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (H : SIntegrableStrategy D) (hH : HasFiniteRealizedGain μ F S H.stochasticIntegral)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ) :
    HasFiniteRealizedGain μ F S (C.postStoppingTail τ hτ H).stochasticIntegral :=
  hH.add hS ((C.stopAtTop_hasFiniteRealizedGain hS hSR H hH τ hτ).neg hS)

/-- Finite linear combinations use the same original price. -/
theorem weightedPrefixSum_hasFiniteRealizedGain
    (hS : IsStronglyProgressive F S)
    (H : Nat → SIntegrableStrategy D)
    (hH : ∀ i, HasFiniteRealizedGain μ F S (H i).stochasticIntegral)
    (weight : Nat → Real) : ∀ n,
    HasFiniteRealizedGain μ F S
      (SIntegrableStrategy.weightedPrefixSum H weight n).stochasticIntegral := by
  intro n
  induction n with
  | zero => exact (hH 0).smul hS 0
  | succ n ih => exact ih.add hS ((hH n).smul hS (weight n))

/-- Every normalized convex tail appearing in the Lemma 4.8 contradiction
has a finite-horizon original-price realization. No sign restriction on the
weights is required for this realization statement. -/
theorem lemma48NormalizedTailConvexStrategy_hasFiniteRealizedGain
    [F.IsRightContinuous]
    (C : SIntegrableProcessStoppingCalculus D)
    (hS : IsStronglyProgressive F S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (H : Nat → SIntegrableStrategy D)
    (hH : ∀ i, HasFiniteRealizedGain μ F S (H i).stochasticIntegral)
    (weight : Nat → Real) (n : Nat) (c N δ ε a : Real) :
    HasFiniteRealizedGain μ F S
      (C.lemma48NormalizedTailConvexStrategy H weight n c N δ ε a).stochasticIntegral := by
  have hTail : ∀ i, HasFiniteRealizedGain μ F S (C.lemma48Tail (H i) c).stochasticIntegral :=
    fun i => C.postStoppingTail_hasFiniteRealizedGain hS hSR (H i) (hH i)
      (lemma48FirstPassage (H i) c) (lemma48FirstPassage_isStoppingTime (H i) c)
  have hSum := weightedPrefixSum_hasFiniteRealizedGain hS
    (fun i => C.lemma48Tail (H i) c) hTail weight n
  have hStop := C.stopAtTop_hasFiniteRealizedGain hS hSR
    (C.lemma48TailConvexStrategy H weight n c) hSum
    (C.lemma48FullCutoff H weight n c N δ ε)
    (C.lemma48FullCutoff_isStoppingTime H weight n c N δ ε)
  exact hStop.smul hS _

end FTAPTheorem42.SIntegrableProcessStoppingCalculus
