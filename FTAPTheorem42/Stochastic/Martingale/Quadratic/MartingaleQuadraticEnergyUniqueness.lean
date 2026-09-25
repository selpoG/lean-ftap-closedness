/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticEnergy
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralStopping
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryStoppingIntegrand

/-!
# Uniqueness of the predictable martingale-energy measure

The forward-convex construction of quadratic-kernel data is noncanonical,
but its predictable energy measure is canonical.  Indeed, every resulting
measure agrees with the same elementary martingale-energy content on the
finite-horizon indicator ring, which generates the predictable sigma
algebra.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace FiniteHorizonPredictableIndicatorRing
namespace BoundedIndicatorRepresentation

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}

/-- Intersect an elementary predictable indicator representation with a
bounded stochastic interval, and repackage it at any deterministic horizon
which dominates that interval. -/
noncomputable def stopAtHorizon
    {U : NNReal} {s : Set (NNReal × Omega)}
    (R : BoundedIndicatorRepresentation (F := F) U s)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (T : NNReal) (hTauT : forall omega, tau omega <= T)
    (hTauU : forall omega, tau omega <= U) :
    BoundedIndicatorRepresentation (F := F) T
      (s ∩ stochasticIntervalIocZero tau) where
  strategy := R.strategy.stopAt tau hTau
  bound := 2 * R.bound
  coefficientAbsSum_le := by
    intro omega
    rw [PredictableElementaryStrategy.coefficientAbsSum_stopAt]
    exact mul_le_mul_of_nonneg_left (R.coefficientAbsSum_le omega) (by norm_num)
  integrand_eq := by
    funext t omega
    rw [PredictableElementaryStrategy.stopAt_integrand_apply,
      congrFun (congrFun R.integrand_eq t) omega]
    unfold indicatorProcess horizonCarrier
    by_cases hActive : 0 < t ∧ t <= tau omega
    · have htT : t <= T := hActive.2.trans (hTauT omega)
      have htU : t <= U := hActive.2.trans (hTauU omega)
      by_cases hs : (t, omega) ∈ s <;>
        simp [hActive, htT, htU, hs, mem_stochasticIntervalIocZero_iff]
    · simp [hActive, mem_stochasticIntervalIocZero_iff]

end BoundedIndicatorRepresentation
end FiniteHorizonPredictableIndicatorRing

namespace ElementaryStrategy

omit [MeasurableSpace Omega] in
/-- Integrating an elementary strategy against a stopped source is the same
as stopping its gain. -/
theorem gain_stoppedProcess
    (M : Process Omega) (H : ElementaryStrategy Omega NNReal)
    (tau : Omega -> NNReal) (t : NNReal) (omega : Omega) :
    gain (MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal))) H t omega =
      gain M H (min t (tau omega)) omega := by
  induction H with
  | nil => rfl
  | cons B H ih =>
      change B.gain (MeasureTheory.stoppedProcess M
          (fun omega => (tau omega : WithTop NNReal))) t omega +
          gain (MeasureTheory.stoppedProcess M
            (fun omega => (tau omega : WithTop NNReal))) H t omega =
        B.gain M (min t (tau omega)) omega +
          gain M H (min t (tau omega)) omega
      rw [ih]
      congr 1
      simp only [ElementaryInterval.gain, MeasureTheory.stoppedProcess,
        ← WithTop.coe_min]
      congr 2 <;> ac_rfl

end ElementaryStrategy

namespace BoundedMartingaleQuadraticKernel.Data

open BoundedMartingaleQuadraticEnergy.Data
open FiniteHorizonMartingaleEnergyContent

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {M : Process Omega} {T U : NNReal}

/-- The terminal energy of a represented predictable set is unchanged when
one either stops the source or intersects the coefficient with the same
bounded stochastic interval. -/
private theorem representationEnergy_stoppedProcess_eq_stopAt
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : forall omega, tau omega <= T)
    (hTauU : forall omega, tau omega <= U)
    (N : Process Omega)
    (hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal))))
    (hN : Martingale N F mu)
    (hNRight : forall omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNU : MemLp (N U) (2 : ENNReal) mu)
    {s : Set (NNReal × Omega)}
    (R : FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) U s) :
    FiniteHorizonMartingaleEnergyContent.representationEnergy
        hN hNRight hNU R =
      FiniteHorizonMartingaleEnergyContent.representationEnergy
        hM hMRight hMT (R.stopAtHorizon tau hTau T hTauT hTauU) := by
  have hGain :
      FiniteHorizonMartingaleEnergyContent.representationGain R N =ᵐ[mu]
        FiniteHorizonMartingaleEnergyContent.representationGain
          (R.stopAtHorizon tau hTau T hTauT hTauU) M := by
    filter_upwards [ae_iff.mp hNDef] with omega hPaths
    rw [FiniteHorizonMartingaleEnergyContent.representationGain,
      FiniteHorizonMartingaleEnergyContent.representationGain]
    calc
      ElementaryStrategy.gain N R.strategy.toElementary U omega =
          ElementaryStrategy.gain
            (MeasureTheory.stoppedProcess M
              (fun omega => (tau omega : WithTop NNReal)))
            R.strategy.toElementary U omega :=
        ElementaryStrategy.gain_congr_price R.strategy.toElementary
          U omega hPaths
      _ = ElementaryStrategy.gain M R.strategy.toElementary
          (min U (tau omega)) omega :=
        ElementaryStrategy.gain_stoppedProcess M R.strategy.toElementary
          tau U omega
      _ = ElementaryStrategy.gain M
          (R.strategy.stopAt tau hTau).toElementary T omega := by
        rw [PredictableElementaryStrategy.gain_stopAt,
          min_eq_right (hTauU omega), min_eq_right (hTauT omega)]
  unfold FiniteHorizonMartingaleEnergyContent.representationEnergy
  have hLp :
      FiniteHorizonMartingaleEnergyContent.representationGainLp
          hN hNRight hNU R =
        FiniteHorizonMartingaleEnergyContent.representationGainLp
          hM hMRight hMT (R.stopAtHorizon tau hTau T hTauT hTauU) := by
    unfold FiniteHorizonMartingaleEnergyContent.representationGainLp
    apply MemLp.toLp_congr
    exact hGain
  rw [hLp]

/-- Stopping a finite-horizon square-integrable martingale restricts its
canonical predictable energy measure to the stochastic interval `(0,tau]`.
The statement is independent of both noncanonical quadratic-kernel data. -/
theorem predictableEnergyMeasure_stoppedProcess_eq_restrict
    [SigmaFiniteFiltration mu F]
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : forall omega, tau omega <= T)
    (hTauU : forall omega, tau omega <= U)
    (N : Process Omega)
    (hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal))))
    (hN : Martingale N F mu)
    (hNRight : forall omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNU : MemLp (N U) (2 : ENNReal) mu)
    (R : BoundedMartingaleQuadraticKernel.Data F mu N U) :
    R.predictableEnergyMeasure =
      Q.predictableEnergyMeasure.restrict (stochasticIntervalIocZero tau) := by
  let _ : IsFiniteMeasure R.predictableEnergyMeasure :=
    R.predictableEnergyMeasure_isFinite
  let C := FiniteHorizonPredictableIndicatorRing.sets (F := F) U
  have hPi : IsPiSystem C := by
    intro s hs t ht _hNonempty
    exact (FiniteHorizonPredictableIndicatorRing.isSetRing_sets U).inter_mem
      hs ht
  have hEq (s : Set (NNReal × Omega)) (hs : s ∈ C) :
      R.predictableEnergyMeasure s =
        (Q.predictableEnergyMeasure.restrict
          (stochasticIntervalIocZero tau)) s := by
    let representation := Classical.choice hs.2
    let stoppedRepresentation :=
      representation.stopAtHorizon tau hTau T hTauT hTauU
    have hStoppedMem : s ∩ stochasticIntervalIocZero tau ∈
        FiniteHorizonPredictableIndicatorRing.sets (F := F) T :=
      ⟨hs.1.inter
          (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau),
        ⟨stoppedRepresentation⟩⟩
    rw [Measure.restrict_apply hs.1,
      predictableEnergyMeasure_apply_eq_addContent
        R hN hNRight hNU hs,
      predictableEnergyMeasure_apply_eq_addContent
        Q hM hMRight hMT hStoppedMem,
      addContent_apply_eq_representationEnergy
          hN hNRight hNU hs.1 representation,
      addContent_apply_eq_representationEnergy
          hM hMRight hMT hStoppedMem.1 stoppedRepresentation]
    exact representationEnergy_stoppedProcess_eq_stopAt
      hM hMRight hMT tau hTau hTauT hTauU N hNDef hN hNRight hNU
        representation
  apply MeasureTheory.ext_of_generate_finite C
    (FiniteHorizonPredictableIndicatorRing.generateFrom_sets U).symm hPi
    hEq
  let Urep :=
    FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.univ
      (F := F) U
  exact hEq Set.univ ⟨MeasurableSet.univ, ⟨Urep⟩⟩

/-- An energy-`L2` coefficient remains energy-`L2` after refining the source
by a bounded stopping time.  The witness is transported through the exact
restriction identity for the canonical energy measures. -/
theorem memLp_two_stoppedProcess_of_restrict
    [SigmaFiniteFiltration mu F]
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : forall omega, tau omega <= T)
    (hTauU : forall omega, tau omega <= U)
    (N : Process Omega)
    (hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal))))
    (hN : Martingale N F mu)
    (hNRight : forall omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNU : MemLp (N U) (2 : ENNReal) mu)
    (R : BoundedMartingaleQuadraticKernel.Data F mu N U)
    {f : NNReal × Omega -> Real}
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure) :
    MemLp f (2 : ENNReal) R.predictableEnergyMeasure := by
  have hRestricted : MemLp f (2 : ENNReal)
      (Q.predictableEnergyMeasure.restrict
        (stochasticIntervalIocZero tau)) :=
    hf.restrict (stochasticIntervalIocZero tau)
  rwa [predictableEnergyMeasure_stoppedProcess_eq_restrict
    Q hM hMRight hMT tau hTau hTauT hTauU N hNDef hN hNRight hNU R]

/-- The completed terminal integral against a stopped source is the old
terminal integral of the coefficient restricted to the same stochastic
interval. -/
theorem finiteHorizonMartingaleTerminalIntegralLp_stoppedProcess
    [SigmaFiniteFiltration mu F]
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : forall omega, tau omega <= T)
    (hTauU : forall omega, tau omega <= U)
    (N : Process Omega)
    (hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal))))
    (hN : Martingale N F mu)
    (hNRight : forall omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNU : MemLp (N U) (2 : ENNReal) mu)
    (R : BoundedMartingaleQuadraticKernel.Data F mu N U)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure) :
    let hfN := memLp_two_stoppedProcess_of_restrict
      Q hM hMRight hMT tau hTau hTauT hTauU N hNDef hN hNRight hNU R hf
    finiteHorizonMartingaleTerminalIntegralLp
        R hN hNRight hNU f hfMeas hfN =
      finiteHorizonMartingaleTerminalIntegralLp
        Q hM hMRight hMT
          ((stochasticIntervalIocZero tau).indicator f)
          (hfMeas.indicator
            (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau))
          (hf.indicator
            (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau)) := by
  classical
  let B := stochasticIntervalIocZero tau
  let hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau
  let g := B.indicator f
  let hgMeas : StronglyMeasurable[F.predictable] g := hfMeas.indicator hB
  let hg : MemLp g (2 : ENNReal) Q.predictableEnergyMeasure :=
    hf.indicator hB
  let hfN := memLp_two_stoppedProcess_of_restrict
    Q hM hMRight hMT tau hTau hTauT hTauU N hNDef hN hNRight hNU R hf
  let H : Nat -> PredictableElementaryStrategy F := fun n =>
    (elementaryApproximation R f hfMeas hfN n).strategy
  let K : Nat -> PredictableElementaryStrategy F := fun n =>
    (H n).stopAt tau hTau
  let C : Nat -> NNReal := fun n =>
    2 * (elementaryApproximation R f hfMeas hfN n).coefficientBound
  have hKBound : forall n omega,
      (K n).coefficientAbsSum omega <= C n := by
    intro n omega
    change ((H n).stopAt tau hTau).coefficientAbsSum omega <= C n
    rw [PredictableElementaryStrategy.coefficientAbsSum_stopAt]
    exact mul_le_mul_of_nonneg_left
      ((elementaryApproximation R f hfMeas hfN n).coefficientAbsSum_le omega)
      (by norm_num)
  have hKIntegrand (n : Nat) :
      Function.uncurry (K n).integrand =
        B.indicator (elementaryApproximationIntegrand
          R f hfMeas hfN n) := by
    funext point
    rcases point with ⟨t, omega⟩
    simp only [K, H, elementaryApproximationIntegrand,
      Function.uncurry_apply_pair,
      PredictableElementaryStrategy.stopAt_integrand_apply]
    rw [Set.indicator_apply]
    by_cases hActive : 0 < t ∧ t <= tau omega
    · rw [ite_eq_left hActive, ite_eq_left
        ((mem_stochasticIntervalIocZero_iff tau t omega).2 hActive)]
      rfl
    · rw [ite_eq_right hActive, ite_eq_right (fun hMem => hActive
        ((mem_stochasticIntervalIocZero_iff tau t omega).1 hMem))]
  let hKMem : forall n, MemLp
      (Function.uncurry (K n).integrand) (2 : ENNReal)
        Q.predictableEnergyMeasure := fun n =>
    elementaryIntegrand_memLp_two Q (K n) (C n) (hKBound n)
  let hKGain : forall n, MemLp
      (ElementaryStrategy.gain M (K n).toElementary T)
        (2 : ENNReal) mu := fun n =>
    (K n).gain_memLp_two M hM hMRight T hMT (C n) (hKBound n)
  let Z : Nat -> Lp Real 2 mu := fun n =>
    (hKGain n).toLp (ElementaryStrategy.gain M (K n).toElementary T)
  have hMeasure := predictableEnergyMeasure_stoppedProcess_eq_restrict
    Q hM hMRight hMT tau hTau hTauT hTauU N hNDef hN hNRight hNU R
  have hIntegrandDistance (n : Nat) :
      dist ((hKMem n).toLp (Function.uncurry (K n).integrand))
          (hg.toLp g) =
        dist ((elementaryApproximationIntegrand_memLp
            R f hfMeas hfN n).toLp
              (elementaryApproximationIntegrand R f hfMeas hfN n))
          (hfN.toLp f) := by
    rw [Lp.dist_edist, Lp.edist_toLp_toLp,
      Lp.dist_edist, Lp.edist_toLp_toLp]
    apply congrArg ENNReal.toReal
    rw [hKIntegrand n]
    have hIndicatorSub :
        B.indicator (elementaryApproximationIntegrand
            R f hfMeas hfN n) - g =
          B.indicator (elementaryApproximationIntegrand
            R f hfMeas hfN n - f) := by
      funext point
      by_cases hp : point ∈ B <;> simp [g, hp]
    rw [hIndicatorSub, eLpNorm_indicator_eq_eLpNorm_restrict hB,
      ← hMeasure]
  have hIntegrand : Tendsto (fun n =>
      (hKMem n).toLp (Function.uncurry (K n).integrand)) atTop
      (nhds (hg.toLp g)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hBase := tendsto_iff_dist_tendsto_zero.mp
      (elementaryApproximationIntegrand_tendsto R f hfMeas hfN)
    exact hBase.congr' (Filter.Eventually.of_forall fun n =>
      (hIntegrandDistance n).symm)
  have hZOld : Tendsto Z atTop
      (nhds (finiteHorizonMartingaleTerminalIntegralLp
        Q hM hMRight hMT g hgMeas hg)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hDistance := tendsto_iff_dist_tendsto_zero.mp hIntegrand
    exact hDistance.congr' (Filter.Eventually.of_forall fun n => by
      have hElementary :=
        finiteHorizonMartingaleTerminalIntegralLp_eq_elementary
          Q hM hMRight hMT (K n) (C n) (hKBound n)
      calc
        dist ((hKMem n).toLp (Function.uncurry (K n).integrand))
            (hg.toLp g) =
          dist (finiteHorizonMartingaleTerminalIntegralLp
              Q hM hMRight hMT (Function.uncurry (K n).integrand)
                (K n).integrand_isStronglyPredictable (hKMem n))
            (finiteHorizonMartingaleTerminalIntegralLp
              Q hM hMRight hMT g hgMeas hg) :=
          (dist_finiteHorizonMartingaleTerminalIntegralLp_eq
            Q hM hMRight hMT (Function.uncurry (K n).integrand)
              (K n).integrand_isStronglyPredictable (hKMem n)
                g hgMeas hg).symm
        _ = dist (Z n) (finiteHorizonMartingaleTerminalIntegralLp
            Q hM hMRight hMT g hgMeas hg) := by rw [hElementary])
  have hZNew : Tendsto Z atTop
      (nhds (finiteHorizonMartingaleTerminalIntegralLp
        R hN hNRight hNU f hfMeas hfN)) := by
    have hTerminal := terminalApproximation_tendsto
      R hN hNRight hNU f hfMeas hfN
    apply hTerminal.congr'
    exact Filter.Eventually.of_forall fun n => by
      apply MemLp.toLp_congr
      filter_upwards [ae_iff.mp hNDef] with omega hPaths
      calc
        ElementaryStrategy.gain N (H n).toElementary U omega =
            ElementaryStrategy.gain
              (MeasureTheory.stoppedProcess M
                (fun omega => (tau omega : WithTop NNReal)))
              (H n).toElementary U omega :=
          ElementaryStrategy.gain_congr_price (H n).toElementary U omega
            hPaths
        _ = ElementaryStrategy.gain M (H n).toElementary
            (min U (tau omega)) omega :=
          ElementaryStrategy.gain_stoppedProcess M (H n).toElementary
            tau U omega
        _ = ElementaryStrategy.gain M (K n).toElementary T omega := by
          rw [min_eq_right (hTauU omega),
            PredictableElementaryStrategy.gain_stopAt,
            min_eq_right (hTauT omega)]
  have hEq := tendsto_nhds_unique hZNew hZOld
  simpa only [B, g, hgMeas, hg, hB, hfN] using hEq

/-- Process-level form of stopped-source transport.  The completed integral
against the stopped source is indistinguishable from the old completed
integral of the coefficient restricted to `(0,tau]`. -/
theorem finiteHorizonMartingaleIntegralProcess_stoppedProcess
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : forall omega, tau omega <= T)
    (hTauU : forall omega, tau omega <= U)
    (N : Process Omega)
    (hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal))))
    (hN : Martingale N F mu)
    (hNRight : forall omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNU : MemLp (N U) (2 : ENNReal) mu)
    (R : BoundedMartingaleQuadraticKernel.Data F mu N U)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure) :
    let hfN := memLp_two_stoppedProcess_of_restrict
      Q hM hMRight hMT tau hTau hTauT hTauU N hNDef hN hNRight hNU R hf
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess
        hUsual R hN hNRight hNU f hfMeas hfN)
      (finiteHorizonMartingaleIntegralProcess
        hUsual Q hM hMRight hMT
          ((stochasticIntervalIocZero tau).indicator f)
          (hfMeas.indicator
            (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau))
          (hf.indicator
            (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau))) := by
  let B := stochasticIntervalIocZero tau
  let hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau
  let g := B.indicator f
  let hgMeas : StronglyMeasurable[F.predictable] g := hfMeas.indicator hB
  let hg : MemLp g (2 : ENNReal) Q.predictableEnergyMeasure :=
    hf.indicator hB
  let hfN := memLp_two_stoppedProcess_of_restrict
    Q hM hMRight hMT tau hTau hTauT hTauU N hNDef hN hNRight hNU R hf
  let I := finiteHorizonMartingaleIntegralProcess
    hUsual R hN hNRight hNU f hfMeas hfN
  let J := finiteHorizonMartingaleIntegralProcess
    hUsual Q hM hMRight hMT g hgMeas hg
  have hI : Martingale I F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual R hN hNRight hNU f hfMeas hfN
  have hJ : Martingale J F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hM hMRight hMT g hgMeas hg
  let hIU : MemLp (I U) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual R hN hNRight hNU f hfMeas hfN
  let hJT : MemLp (J T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT g hgMeas hg
  have hTerminalLp : hIU.toLp (I U) = hJT.toLp (J T) := by
    calc
      hIU.toLp (I U) = finiteHorizonMartingaleTerminalIntegralLp
          R hN hNRight hNU f hfMeas hfN :=
        finiteHorizonMartingaleIntegralProcess_terminal_toLp
          hUsual R hN hNRight hNU f hfMeas hfN
      _ = finiteHorizonMartingaleTerminalIntegralLp
          Q hM hMRight hMT g hgMeas hg := by
        simpa only [B, g, hgMeas, hg, hB, hfN] using
          finiteHorizonMartingaleTerminalIntegralLp_stoppedProcess
            Q hM hMRight hMT tau hTau hTauT hTauU N hNDef hN hNRight
              hNU R f hfMeas hf
      _ = hJT.toLp (J T) :=
        (finiteHorizonMartingaleIntegralProcess_terminal_toLp
          hUsual Q hM hMRight hMT g hgMeas hg).symm
  have hTerminalAE : I U =ᵐ[mu] J T :=
    (MemLp.toLp_eq_toLp_iff hIU hJT).mp hTerminalLp
  let V := max T U
  have hTV : T <= V := le_max_left T U
  have hUV : U <= V := le_max_right T U
  have hTerminalV : I V =ᵐ[mu] J V := by
    have hIConstant :=
      finiteHorizonMartingaleIntegralProcess_constantAfter
        hUsual R hN hNRight hNU f hfMeas hfN V hUV
    have hJConstant :=
      finiteHorizonMartingaleIntegralProcess_constantAfter
        hUsual Q hM hMRight hMT g hgMeas hg V hTV
    exact hIConstant.trans (hTerminalAE.trans hJConstant.symm)
  have hEqAt (t : NNReal) : I t =ᵐ[mu] J t := by
    by_cases ht : t <= V
    · exact (hI.condExp_ae_eq ht).symm.trans
        ((condExp_congr_ae hTerminalV).trans (hJ.condExp_ae_eq ht))
    · have hVt : V <= t := le_of_not_ge ht
      have hIConstant :=
        finiteHorizonMartingaleIntegralProcess_constantAfter
          hUsual R hN hNRight hNU f hfMeas hfN t (hUV.trans hVt)
      have hJConstant :=
        finiteHorizonMartingaleIntegralProcess_constantAfter
          hUsual Q hM hMRight hMT g hgMeas hg t (hTV.trans hVt)
      exact hIConstant.trans (hTerminalAE.trans hJConstant.symm)
  have hIRight : forall omega t,
      ContinuousWithinAt (I · omega) (Ici t) t :=
    finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual R hN hNRight hNU f hfMeas hfN
  have hJRight : forall omega t,
      ContinuousWithinAt (J · omega) (Ici t) t :=
    finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual Q hM hMRight hMT g hgMeas hg
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense
    I J NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
    (Filter.Eventually.of_forall hIRight)
    (Filter.Eventually.of_forall hJRight)
    (fun n => hEqAt _)

end BoundedMartingaleQuadraticKernel.Data

end FTAPTheorem42
