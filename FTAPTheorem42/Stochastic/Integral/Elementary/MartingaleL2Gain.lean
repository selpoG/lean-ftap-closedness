/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryLeftStepMartingaleApproximation

/-! # Square-integrable elementary martingale gains

The coefficient absolute sum and the martingale maximal envelope bound the
elementary gain, proving its finite-horizon L² membership. -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace PredictableElementaryStrategy

/-- A uniformly bounded predictable elementary strategy has a square-integrable
finite-horizon martingale gain whenever the source martingale is square
integrable at that horizon. -/
theorem gain_memLp_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (C : NNReal)
    (hHBound : forall omega, H.coefficientAbsSum omega <= C) :
    MemLp (ElementaryStrategy.gain M H.toElementary T)
      (2 : ENNReal) mu := by
  let envelope : Omega -> Real :=
    FactorialChronologicalGrid.martingaleAbsoluteEnvelope M T
  let bound : Omega -> Real := fun omega =>
    2 * (C : Real) * envelope omega
  have hProgressive : IsStronglyProgressive F M :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      hM.stronglyAdapted hMRight
  have hGainMeas : AEStronglyMeasurable
      (ElementaryStrategy.gain M H.toElementary T) mu :=
    (((H.stronglyAdapted_gain M hProgressive) T).mono
      (F.le T)).aestronglyMeasurable
  have hEnvelopeMem : MemLp envelope (2 : ENNReal) mu :=
    FactorialChronologicalGrid.Martingale.martingaleAbsoluteEnvelope_memLp
      hM T hMT
  have hBoundMem : MemLp bound (2 : ENNReal) mu :=
    hEnvelopeMem.const_mul (2 * (C : Real))
  have hEnvelopeDominates : ∀ᵐ omega ∂mu, ∀ t, t <= T ->
      ‖M t omega‖ <= envelope omega :=
    FactorialChronologicalGrid.Martingale.norm_le_martingaleAbsoluteEnvelope_ae
      hM T hMT hMRight
  apply hBoundMem.mono' hGainMeas
  filter_upwards [hEnvelopeDominates] with omega homega
  have hGain := H.norm_gain_le_coefficientAbsSum_mul
    M T omega (envelope omega) homega
  have hEnvelopeNonnegative : 0 <= envelope omega := Real.sqrt_nonneg _
  have hRealCoefficient : H.coefficientAbsSum omega <= (C : Real) := by
    exact_mod_cast hHBound omega
  have hRaw :
      ‖ElementaryStrategy.gain M H.toElementary T omega‖ <=
        2 * (C : Real) * envelope omega := by
    calc
      ‖ElementaryStrategy.gain M H.toElementary T omega‖ <=
          2 * H.coefficientAbsSum omega * envelope omega := hGain
      _ <= 2 * (C : Real) * envelope omega := by
        nlinarith [H.coefficientAbsSum_nonneg omega]
  exact hRaw

end PredictableElementaryStrategy

end FTAPTheorem42
