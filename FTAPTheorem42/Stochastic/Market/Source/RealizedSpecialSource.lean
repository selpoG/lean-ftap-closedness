import FTAPTheorem42.Stochastic.Market.Source.CenteredMarketUnitLocallySIntegrableStrategy
import FTAPTheorem42.Stochastic.Topology.Emery.RealizedComposition
import FTAPTheorem42.Stochastic.Topology.J1.Basic

/-! # Auxiliary unit sources retaining a realized gain's special components -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [SigmaFiniteFiltration μ F]

/-- A normalized regular decomposition with predictable finite variation
supplies a special certificate for this realized gain, not for the price. -/
def specialDecomposition (R : RealizedStrategy (ℱ := F) μ S)
    (D : J1Decomposition R.gain F μ) (hA : IsStronglyPredictable F D.A) :
    SpecialSemimartingaleDecomposition R.gain F μ where
  martingalePart := D.N
  finiteVariationPart := D.A
  martingalePart_isLocalMartingale := D.localMartingale
  finiteVariationPart_isPredictable := hA
  finiteVariationPart_isLocallyBoundedVariation := D.variationA
  decomposition := D.decomposition

/-- The gain itself is the auxiliary unit source. Its actual integrals must
still be returned to the original price by the general realization bridge. -/
noncomputable def componentSource (R : RealizedStrategy (ℱ := F) μ S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (D : J1Decomposition R.gain F μ) (hA : IsStronglyPredictable F D.A) :
    LocallySIntegrableStrategy (R.specialDecomposition D hA) :=
  (R.specialDecomposition D hA).zeroInitialUnitSource
    R.gain_stronglyAdapted R.gain_rightContinuous (R.gain_initial_eq_zero S hSR)
    D.adaptedN D.rightN D.rightA

@[simp]
theorem componentSource_martingalePart (R : RealizedStrategy (ℱ := F) μ S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (D : J1Decomposition R.gain F μ) (hA : IsStronglyPredictable F D.A) :
    (R.componentSource hSR D hA).martingalePart = D.N := by
  funext t ω
  change D.N t ω - D.N 0 ω = D.N t ω
  rw [D.zeroN]
  exact sub_zero _

@[simp]
theorem componentSource_finiteVariationPart (R : RealizedStrategy (ℱ := F) μ S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (D : J1Decomposition R.gain F μ) (hA : IsStronglyPredictable F D.A) :
    (R.componentSource hSR D hA).finiteVariationPart = D.A := by
  funext t ω
  change D.A t ω - D.A 0 ω = D.A t ω
  rw [D.zeroA]
  exact sub_zero _

@[simp]
theorem componentSource_gain (R : RealizedStrategy (ℱ := F) μ S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (D : J1Decomposition R.gain F μ) (hA : IsStronglyPredictable F D.A) :
    (R.componentSource hSR D hA).stochasticIntegral = R.gain := rfl

/-- Left limits are retained from the supplied normalized component. -/
theorem componentSource_martingalePart_hasLeftLimits
    (R : RealizedStrategy (ℱ := F) μ S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (D : J1Decomposition R.gain F μ) (hA : IsStronglyPredictable F D.A) :
    ProcessHasLeftLimits (R.componentSource hSR D hA).martingalePart := by
  rw [componentSource_martingalePart]
  exact D.leftN

end FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy
