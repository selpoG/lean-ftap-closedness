/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.PredictableIndicatorRing
import FTAPTheorem42.Stochastic.Integral.Elementary.MartingaleL2Gain

/-!
# Finite-horizon martingale energy on an elementary predictable ring

For a right-continuous square-integrable martingale `M` and a deterministic
horizon `T`, the refining factorial grids give finite predictable energy
measures for the stopped source `M^T`.  This module evaluates those measures
on the elementary predictable indicator ring and identifies their limit with
the squared `L²` norm of the corresponding actual elementary martingale gain.

The resulting set function is a finite additive content.  Its construction is
independent of a chosen elementary presentation: representation independence
of actual gains was proved before defining the content.  Extending this
content to the full predictable sigma algebra requires continuity at the empty
set; that countable-additivity boundary is intentionally not assumed here.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace FiniteHorizonMartingaleEnergyContent

/-- The refining finite-grid predictable energy control of the stopped
source. -/
noncomputable def gridControl
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (M : Process Omega) (T : NNReal) (r : Nat) :
    MeminPredictableControlMeasure F :=
  let G := LeftContinuousPredictable.finiteGrid r
    (LeftContinuousPredictable.horizonCellCount r T)
  G.martingaleEnergyControl F mu (deterministicallyStoppedProcess M T)

/-- The grid energy assigned to the positive finite-horizon part of a set. -/
noncomputable def gridValue
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (M : Process Omega) (T : NNReal)
    (s : Set (NNReal × Omega)) (r : Nat) : ENNReal :=
  gridControl F mu M T r
    (s ∩ FiniteHorizonPredictableIndicatorRing.horizonCarrier T)

/-- The limiting finite-horizon martingale energy set function. -/
noncomputable def value
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (M : Process Omega) (T : NNReal)
    (s : Set (NNReal × Omega)) : ENNReal :=
  limUnder atTop (gridValue F mu M T s)

/-- The squared extended-norm integral of an `L²` real function is the
nonnegative-real lift of the squared norm of its canonical `Lp` class. -/
theorem lintegral_enorm_sq_eq_ofReal_norm_toLp_sq
    {mu : Measure Omega} {f : Omega → Real}
    (hf : MemLp f (2 : ENNReal) mu) :
    (∫⁻ omega, ‖f omega‖ₑ ^ 2 ∂mu) =
      ENNReal.ofReal (‖hf.toLp f‖ ^ 2) := by
  rw [DiscretePredictableIntegral.lintegral_enorm_sq_eq_of_memLp_two hf,
    Lp.norm_toLp,
    eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hf]
  have hNonnegative : 0 ≤ ∫ omega, ‖f omega‖ ^ 2 ∂mu :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun omega => sq_nonneg ‖f omega‖)
  congr 1
  rw [Real.sq_sqrt hNonnegative]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun omega => by
    change f omega ^ 2 = ‖f omega‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs]

omit [MeasurableSpace Omega] in
/-- Integrating the deterministically stopped source to the last grid time
is the same pathwise process value as integrating the original source only
up to the stopping horizon. -/
theorem martingaleIntegralProcess_stoppedSource_last
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K M : Process Omega) (T : NNReal) :
    G.martingaleIntegralProcess K (deterministicallyStoppedProcess M T)
        (G.sampledTime N) =
      G.martingaleIntegralProcess K M T := by
  funext omega
  unfold ChronologicalGrid.martingaleIntegralProcess
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [deterministicIntervalMartingaleTransform_eq_of_le K
    (deterministicallyStoppedProcess M T)
    (G.sampledTime_mono (Nat.le_succ k))
    (G.sampledTime_mono (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))]
  simp only [deterministicIntervalMartingaleTransform,
    deterministicallyStoppedProcess_apply, stoppedProcess_const_apply]
  rw [min_comm T (G.sampledTime (k + 1)),
    min_comm T (G.sampledTime k)]

/-- The actual terminal gain represented by an elementary indicator. -/
noncomputable def representationGain
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {T : NNReal} {s : Set (NNReal × Omega)}
    (R : FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) T s)
    (M : Process Omega) : Omega → Real :=
  ElementaryStrategy.gain M R.strategy.toElementary T

/-- The canonical `L²` representative of an elementary indicator gain. -/
noncomputable def representationGainLp
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    {T : NNReal} (hMT : MemLp (M T) (2 : ENNReal) mu)
    {s : Set (NNReal × Omega)}
    (R : FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) T s) : Lp Real (2 : ENNReal) mu :=
  (R.strategy.gain_memLp_two M hM hMRight T hMT R.bound
    R.coefficientAbsSum_le).toLp (representationGain R M)

/-- Squared terminal `L²` energy of one represented predictable indicator. -/
noncomputable def representationEnergy
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    {T : NNReal} (hMT : MemLp (M T) (2 : ENNReal) mu)
    {s : Set (NNReal × Omega)}
    (R : FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) T s) : ENNReal :=
  ENNReal.ofReal (‖representationGainLp hM hMRight hMT R‖ ^ 2)

/-- On every refining grid, the energy of a represented set is exactly the
second moment of the corresponding chronological elementary gain. -/
theorem gridValue_eq_approximatingGain
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    {T : NNReal} (hMT : MemLp (M T) (2 : ENNReal) mu)
    {s : Set (NNReal × Omega)}
    (hs : MeasurableSet[F.predictable] s)
    (R : FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) T s)
    (r : Nat) :
    gridValue F mu M T s r =
      ∫⁻ omega, ‖ElementaryStrategy.gain M
        (R.strategy.horizonLeftStepStrategy r T).toElementary T omega‖ₑ ^ 2
        ∂mu := by
  let N : Nat := LeftContinuousPredictable.horizonCellCount r T
  let G : ChronologicalGrid NNReal N :=
    LeftContinuousPredictable.finiteGrid r N
  let MT : Process Omega := deterministicallyStoppedProcess M T
  have hCarrier : MeasurableSet[F.predictable]
      (FiniteHorizonPredictableIndicatorRing.horizonCarrier
        (Omega := Omega) T) :=
    FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier T
  have hsT : MeasurableSet[F.predictable]
      (s ∩ FiniteHorizonPredictableIndicatorRing.horizonCarrier T) :=
    hs.inter hCarrier
  have hIndicator :
      (fun p : NNReal × Omega =>
        ‖Function.uncurry R.strategy.integrand p‖ₑ ^ 2) =
      (s ∩ FiniteHorizonPredictableIndicatorRing.horizonCarrier T).indicator
        (fun _ => (1 : ENNReal)) := by
    funext p
    change ‖R.strategy.integrand p.1 p.2‖ₑ ^ 2 = _
    rw [congrFun (congrFun R.integrand_eq p.1) p.2]
    by_cases hp : p ∈
        s ∩ FiniteHorizonPredictableIndicatorRing.horizonCarrier T <;>
      simp [FiniteHorizonPredictableIndicatorRing.indicatorProcess, hp]
  have hSetIntegral :
      gridControl F mu M T r
          (s ∩ FiniteHorizonPredictableIndicatorRing.horizonCarrier T) =
        ∫⁻ p, ‖Function.uncurry R.strategy.integrand p‖ₑ ^ 2
          ∂gridControl F mu M T r := by
    rw [hIndicator]
    exact (lintegral_indicator_one
      (μ := gridControl F mu M T r) hsT).symm
  have hMTMartingale : Martingale MT F mu := by
    exact martingale_deterministicallyStopped hM hMRight T
  have hMTLp : ∀ t, MemLp (MT t) (2 : ENNReal) mu := by
    intro t
    exact stoppedProcess_const_memLp_two hM T hMT t
  have hIntegrandBound : ∀ t, ∀ᵐ omega ∂mu,
      |R.strategy.integrand t omega| ≤ (R.bound : Real) := by
    intro t
    exact Filter.Eventually.of_forall fun omega =>
      (R.strategy.abs_integrand_le_coefficientAbsSum t omega).trans
        (R.coefficientAbsSum_le omega)
  have hGridEnergy :
      (∫⁻ p, ‖Function.uncurry R.strategy.integrand p‖ₑ ^ 2
          ∂gridControl F mu M T r) =
        ∫⁻ omega, ‖discretePredictableIntegral
          (G.natSample R.strategy.integrand) (G.natSample MT) N omega‖ₑ ^ 2
          ∂mu := by
    change
      (∫⁻ p, ‖Function.uncurry R.strategy.integrand p‖ₑ ^ 2
          ∂G.martingaleEnergyControl F mu MT) = _
    exact G.lintegral_martingaleEnergyControl_eq_terminal
      hMTMartingale hMTLp R.strategy.integrand_isStronglyPredictable
        (fun t => hIntegrandBound t)
  have hTerminal :
      discretePredictableIntegral
          (G.natSample R.strategy.integrand) (G.natSample MT) N =
        ElementaryStrategy.gain M
          (R.strategy.horizonLeftStepStrategy r T).toElementary T := by
    rw [← G.martingaleIntegralProcess_last]
    rw [martingaleIntegralProcess_stoppedSource_last]
    funext omega
    exact (G.predictableElementaryStrategy_gain
      R.strategy.integrand R.strategy.integrand_isStronglyPredictable
        M T omega).symm
  rw [gridValue, hSetIntegral, hGridEnergy, hTerminal]

/-- The refining-grid set energies converge to the squared `L²` norm of the
actual elementary gain represented by the set indicator. -/
theorem gridValue_tendsto_representationEnergy
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    {T : NNReal} (hMT : MemLp (M T) (2 : ENNReal) mu)
    {s : Set (NNReal × Omega)}
    (hs : MeasurableSet[F.predictable] s)
    (R : FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) T s) :
    Tendsto (gridValue F mu M T s) atTop
      (nhds (representationEnergy hM hMRight hMT R)) := by
  let approximant : Nat → Omega → Real := fun r =>
    ElementaryStrategy.gain M
      (R.strategy.horizonLeftStepStrategy r T).toElementary T
  let target : Omega → Real := representationGain R M
  have hApproximantMem : ∀ r,
      MemLp (approximant r) (2 : ENNReal) mu := by
    intro r
    let C : NNReal :=
      (LeftContinuousPredictable.horizonCellCount r T : NNReal) * R.bound
    apply (R.strategy.horizonLeftStepStrategy r T).gain_memLp_two
      M hM hMRight T hMT C
    intro omega
    have hBound :=
      R.strategy.horizonLeftStepStrategy_coefficientAbsSum_le
        r T R.bound R.coefficientAbsSum_le omega
    simpa only [C, NNReal.coe_mul, Nat.cast_ofNat,
      NNReal.coe_natCast] using hBound
  have hTargetMem : MemLp target (2 : ENNReal) mu := by
    exact R.strategy.gain_memLp_two M hM hMRight T hMT R.bound
      R.coefficientAbsSum_le
  have hRaw : Tendsto
      (fun r => eLpNorm (approximant r - target) (2 : ENNReal) mu)
      atTop (nhds 0) := by
    simpa only [approximant, target, representationGain] using
      R.strategy.horizonLeftStepStrategy_gain_tendsto_eLpNorm_two
        M hM hMRight T hMT R.bound R.coefficientAbsSum_le
  have hLp : Tendsto
      (fun r => (hApproximantMem r).toLp (approximant r))
      atTop (nhds (hTargetMem.toLp target)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' approximant hApproximantMem
      target hTargetMem).mpr hRaw
  have hNormSq : Tendsto
      (fun r => ‖(hApproximantMem r).toLp (approximant r)‖ ^ 2)
      atTop (nhds (‖hTargetMem.toLp target‖ ^ 2)) :=
    hLp.norm.pow 2
  have hEnergy := ENNReal.tendsto_ofReal hNormSq
  apply hEnergy.congr'
  exact Filter.Eventually.of_forall fun r => by
    symm
    rw [gridValue_eq_approximatingGain hM hMRight hMT hs R r]
    exact lintegral_enorm_sq_eq_ofReal_norm_toLp_sq
      (hApproximantMem r)

/-- On the elementary predictable ring, the limiting set function is the
actual squared terminal `L²` energy of any bounded indicator
representation. -/
theorem value_eq_representationEnergy
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    {T : NNReal} (hMT : MemLp (M T) (2 : ENNReal) mu)
    {s : Set (NNReal × Omega)}
    (hs : MeasurableSet[F.predictable] s)
    (R : FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) T s) :
    value F mu M T s = representationEnergy hM hMRight hMT R := by
  exact (gridValue_tendsto_representationEnergy
    hM hMRight hMT hs R).limUnder_eq

/-- The limiting grid energy of the empty set is zero. -/
theorem value_empty
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (M : Process Omega) (T : NNReal) :
    value F mu M T ∅ = 0 := by
  have hGrid : gridValue F mu M T ∅ = fun _ => 0 := by
    funext r
    simp [gridValue]
  rw [value, hGrid, (tendsto_const_nhds (x := (0 : ENNReal))).limUnder_eq]

/-- The limiting grid energy is additive on disjoint members of the
elementary predictable indicator ring. -/
theorem value_union
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    {s u : Set (NNReal × Omega)}
    (hs : s ∈ FiniteHorizonPredictableIndicatorRing.sets (F := F) T)
    (hu : u ∈ FiniteHorizonPredictableIndicatorRing.sets (F := F) T)
    (hDisjoint : Disjoint s u) :
    value F mu M T (s ∪ u) =
      value F mu M T s + value F mu M T u := by
  let R := Classical.choice hs.2
  let Q := Classical.choice hu.2
  let U :=
    FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.union
      R Q
  have hCarrier : MeasurableSet[F.predictable]
      (FiniteHorizonPredictableIndicatorRing.horizonCarrier
        (Omega := Omega) T) :=
    FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier T
  have hGridAdd : ∀ r,
      gridValue F mu M T (s ∪ u) r =
        gridValue F mu M T s r + gridValue F mu M T u r := by
    intro r
    unfold gridValue
    rw [union_inter_distrib_right]
    exact measure_union
      (hDisjoint.mono inter_subset_left inter_subset_left)
      (hu.1.inter hCarrier)
  have hUnionTendsto :=
    gridValue_tendsto_representationEnergy hM hMRight hMT
      (hs.1.union hu.1) U
  have hSumTendsto :=
    (gridValue_tendsto_representationEnergy hM hMRight hMT hs.1 R).add
      (gridValue_tendsto_representationEnergy hM hMRight hMT hu.1 Q)
  have hUnionAsSum : Tendsto (gridValue F mu M T (s ∪ u)) atTop
      (nhds (representationEnergy hM hMRight hMT R +
        representationEnergy hM hMRight hMT Q)) := by
    apply hSumTendsto.congr'
    exact Filter.Eventually.of_forall fun r => (hGridAdd r).symm
  have hEnergyAdd : representationEnergy hM hMRight hMT U =
      representationEnergy hM hMRight hMT R +
        representationEnergy hM hMRight hMT Q :=
    tendsto_nhds_unique hUnionTendsto hUnionAsSum
  rw [value_eq_representationEnergy hM hMRight hMT (hs.1.union hu.1) U,
    value_eq_representationEnergy hM hMRight hMT hs.1 R,
    value_eq_representationEnergy hM hMRight hMT hu.1 Q]
  exact hEnergyAdd

/-- The finite additive martingale energy content on the elementary
predictable indicator ring. -/
noncomputable def addContent
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    (M : Process Omega) (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) :
    AddContent ENNReal
      (FiniteHorizonPredictableIndicatorRing.sets (F := F) T) :=
  (FiniteHorizonPredictableIndicatorRing.isSetRing_sets T).addContent_of_union
    (value F mu M T) (value_empty F mu M T)
      (fun hs hu => value_union hM hMRight T hMT hs hu)

@[simp]
theorem addContent_apply
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    (M : Process Omega) (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (s : Set (NNReal × Omega)) :
    addContent M hM hMRight T hMT s = value F mu M T s :=
  rfl

/-- The content value on a represented ring member is its actual terminal
gain energy. -/
theorem addContent_apply_eq_representationEnergy
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    {T : NNReal} (hMT : MemLp (M T) (2 : ENNReal) mu)
    {s : Set (NNReal × Omega)}
    (hs : MeasurableSet[F.predictable] s)
    (R : FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) T s) :
    addContent M hM hMRight T hMT s =
      representationEnergy hM hMRight hMT R := by
  rw [addContent_apply,
    value_eq_representationEnergy hM hMRight hMT hs R]

end FiniteHorizonMartingaleEnergyContent

end FTAPTheorem42
