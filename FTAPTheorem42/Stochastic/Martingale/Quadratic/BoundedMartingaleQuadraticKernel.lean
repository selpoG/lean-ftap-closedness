/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticVariation
import FTAPTheorem42.Stochastic.FiniteVariation.IncreasingProcessStieltjesKernel
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization

/-!
# Predictable Stieltjes kernels from bounded-martingale quadratic variation

The forward-convex quadratic-variation limit is increasing only almost
surely.  The usual conditions allow all exceptional paths to be replaced by
zero on one time-zero event.  This module carries out that regularization,
retains convergence of the same quadratic approximations, and constructs the
resulting finite measure on the predictable sigma algebra.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticKernel

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticConvexification
open BoundedMartingaleQuadraticVariation

/-- The raw complementary process in the martingale square decomposition. -/
noncomputable def rawVariation
    (M : Process Omega) (T : NNReal) (Y : Process Omega) : Process Omega :=
  fun t omega => deterministicallyStoppedProcess M T t omega ^ 2 -
    deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega

omit [MeasurableSpace Omega] in
@[simp]
theorem rawVariation_apply
    (M : Process Omega) (T : NNReal) (Y : Process Omega)
    (t : NNReal) (omega : Omega) :
    rawVariation M T Y t omega = deterministicallyStoppedProcess M T t omega ^ 2 -
      deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega :=
  rfl

omit [MeasurableSpace Omega] in
/-- Every convexified squared-increment approximation starts from zero. -/
theorem convexSquaredIncrementPart_zero
    (M : Process Omega) (T : NNReal) {n : Nat}
    (w : TailConvexWeights n) :
    BoundedMartingaleQuadraticConvexification.squaredIncrementPart
      M T w 0 = 0 := by
  rw [BoundedMartingaleQuadraticConvexification.squaredIncrementPart]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [BoundedMartingaleQuadraticApproximation.squaredIncrementPart,
    ChronologicalGrid.squaredIncrementProcess_zero]
  simp

/-- Concrete data produced by the bounded-martingale quadratic construction.
The variation process has already been regularized on one null set, so its
path properties hold for every sample point. -/
structure Data
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (M : Process Omega) (T : NNReal) where
  weights : forall n, TailConvexWeights n
  cutoff : Nat -> Nat
  martingalePart : Process Omega
  variation : Process Omega
  cutoff_strictMono : StrictMono cutoff
  martingalePart_isMartingale : Martingale martingalePart F mu
  martingalePart_rightContinuous : forall omega t,
    ContinuousWithinAt (martingalePart · omega) (Ici t) t
  martingalePart_uniform : ∀ᵐ omega ∂mu, TendstoUniformly
    (fun k t => BoundedMartingaleQuadraticConvexification.martingalePart
      M T (weights (cutoff k)) t omega)
    (fun t => martingalePart t omega) atTop
  variation_uniform : ∀ᵐ omega ∂mu, TendstoUniformly
    (fun k t => squaredIncrementPart M T (weights (cutoff k)) t omega)
    (fun t => variation t omega) atTop
  variation_isStronglyAdapted : StronglyAdapted F variation
  variation_rightContinuous : forall omega t,
    ContinuousWithinAt (variation · omega) (Ici t) t
  variation_monotone : forall omega, Monotone (variation · omega)
  variation_constantAfter : forall omega t,
    T <= t -> variation t omega = variation T omega
  variation_zero : variation 0 = 0
  variation_indistinguishable_raw : ProcessIndistinguishable mu variation
    (rawVariation M T martingalePart)
  variation_terminal_integrable : Integrable (variation T) mu

namespace Data

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} {M : Process Omega} {T : NNReal}

/-- Every fixed-time value of the regularized variation process is measurable
in the ambient sample sigma algebra. -/
theorem variation_measurable (D : Data F mu M T) (t : NNReal) :
    Measurable (D.variation t) :=
  ((D.variation_isStronglyAdapted t).mono (F.le t)).measurable

/-- The pathwise Stieltjes kernel of the regularized quadratic variation. -/
noncomputable def stieltjesKernel (D : Data F mu M T) :
    Kernel Omega NNReal :=
  IncreasingProcessStieltjesKernel.kernel D.variation
    D.variation_monotone D.variation_rightContinuous T
    D.variation_constantAfter D.variation_measurable

@[simp]
theorem stieltjesKernel_apply (D : Data F mu M T) (omega : Omega) :
    D.stieltjesKernel omega =
      IncreasingProcessStieltjesKernel.pathMeasure D.variation
        D.variation_monotone D.variation_rightContinuous omega :=
  rfl

/-- The quadratic-variation measure on the predictable sigma algebra. -/
noncomputable def predictableEnergyMeasure (D : Data F mu M T) :
    MeminPredictableControlMeasure F :=
  IncreasingProcessStieltjesKernel.predictableMeasure F mu D.variation
    D.variation_monotone D.variation_rightContinuous T
    D.variation_constantAfter D.variation_measurable

/-- The quadratic-variation measure has finite total mass. -/
theorem predictableEnergyMeasure_isFinite
    [SFinite mu] (D : Data F mu M T) :
    IsFiniteMeasure D.predictableEnergyMeasure := by
  apply IncreasingProcessStieltjesKernel.predictableMeasure_isFinite
  simpa only [Pi.zero_apply, sub_zero, D.variation_zero] using
    D.variation_terminal_integrable

/-- The quadratic-variation measure does not charge time zero. -/
theorem predictableEnergyMeasure_timeZeroSlice
    [SFinite mu] (D : Data F mu M T) :
    D.predictableEnergyMeasure
        ({0} ×ˢ (Set.univ : Set Omega)) = 0 :=
  IncreasingProcessStieltjesKernel.predictableMeasure_timeZeroSlice
    D.variation D.variation_monotone D.variation_rightContinuous T
      D.variation_constantAfter D.variation_measurable

/-- Almost every point under the quadratic-variation measure has strictly
positive time coordinate. -/
theorem ae_time_pos [SFinite mu] (D : Data F mu M T) :
    ∀ᵐ p ∂D.predictableEnergyMeasure, 0 < p.1 := by
  rw [ae_iff]
  change D.predictableEnergyMeasure {p | ¬0 < p.1} = 0
  rw [show {p : NNReal × Omega | ¬0 < p.1} =
      ({0} ×ˢ (Set.univ : Set Omega)) by
    ext p
    simp]
  exact D.predictableEnergyMeasure_timeZeroSlice

/-- The quadratic-variation measure gives no mass to times strictly after
the deterministic horizon. -/
theorem predictableEnergyMeasure_afterHorizon
    [SFinite mu] (D : Data F mu M T) :
    D.predictableEnergyMeasure
        (Ioi T ×ˢ (Set.univ : Set Omega)) = 0 :=
  IncreasingProcessStieltjesKernel.predictableMeasure_afterHorizon
    D.variation D.variation_monotone D.variation_rightContinuous T
      D.variation_constantAfter D.variation_measurable

/-- Almost every point under the quadratic-variation measure lies at or
before the deterministic horizon. -/
theorem ae_time_le_horizon [SFinite mu] (D : Data F mu M T) :
    ∀ᵐ p ∂D.predictableEnergyMeasure, p.1 <= T := by
  rw [ae_iff]
  change D.predictableEnergyMeasure {p | ¬p.1 <= T} = 0
  rw [show {p : NNReal × Omega | ¬p.1 <= T} =
      Ioi T ×ˢ (Set.univ : Set Omega) by
    ext p
    simp]
  exact D.predictableEnergyMeasure_afterHorizon

/-- Evaluation of the quadratic-variation measure on a predictable set. -/
theorem predictableEnergyMeasure_apply
    [SFinite mu] (D : Data F mu M T)
    {s : Set (NNReal × Omega)} (hs : MeasurableSet[F.predictable] s) :
    D.predictableEnergyMeasure s =
      ∫⁻ omega, IncreasingProcessStieltjesKernel.pathMeasure D.variation
        D.variation_monotone D.variation_rightContinuous omega
          ((fun t => (t, omega)) ⁻¹' s) ∂mu :=
  IncreasingProcessStieltjesKernel.predictableMeasure_apply
    D.variation D.variation_monotone D.variation_rightContinuous T
      D.variation_constantAfter D.variation_measurable hs

end Data

/-- The raw quadratic limit is strongly adapted. -/
theorem rawVariation_isStronglyAdapted
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) {Y : Process Omega} (hY : Martingale Y F mu) :
    StronglyAdapted F (rawVariation M T Y) := by
  have hX := martingale_deterministicallyStopped hM hMRight T
  intro t
  exact (((hX.stronglyAdapted t).pow 2).sub
    (((hX.stronglyAdapted 0).mono (F.mono bot_le)).pow 2)).sub
      (hY.stronglyAdapted t)

omit [MeasurableSpace Omega] in
/-- Uniform convergence of the convexified squared increments forces the raw
limit to start from zero. -/
theorem rawVariation_zero_of_uniform
    (M : Process Omega) (T : NNReal)
    (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat)
    (Y : Process Omega) (omega : Omega)
    (hUniform : TendstoUniformly
      (fun k t => squaredIncrementPart M T (w (cutoff k)) t omega)
      (fun t => rawVariation M T Y t omega) atTop) :
    rawVariation M T Y 0 omega = 0 := by
  have hLimit := hUniform.tendsto_at 0
  have hZero : (fun k =>
      squaredIncrementPart M T (w (cutoff k)) 0 omega) = fun _ => 0 := by
    funext k
    exact congrFun (convexSquaredIncrementPart_zero
      M T (w (cutoff k))) omega
  rw [hZero] at hLimit
  exact tendsto_nhds_unique hLimit tendsto_const_nhds

omit [MeasurableSpace Omega] in
/-- The same uniform convergence forces the raw limit to be constant after
the deterministic horizon. -/
theorem rawVariation_constantAfter_of_uniform
    (M : Process Omega) (T : NNReal)
    (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat)
    (Y : Process Omega) (omega : Omega)
    (hUniform : TendstoUniformly
      (fun k t => squaredIncrementPart M T (w (cutoff k)) t omega)
      (fun t => rawVariation M T Y t omega) atTop) :
    forall t, T <= t ->
      rawVariation M T Y t omega = rawVariation M T Y T omega := by
  intro t ht
  have htLimit := hUniform.tendsto_at t
  have hTLimit := hUniform.tendsto_at T
  have hEq : (fun k =>
      squaredIncrementPart M T (w (cutoff k)) t omega) =
      fun k => squaredIncrementPart M T (w (cutoff k)) T omega := by
    funext k
    exact congrFun
      (Approximation.squaredIncrementPart_constantAfter
        M T (w (cutoff k)) ht) omega
  rw [hEq] at htLimit
  exact tendsto_nhds_unique htLimit hTLimit

/-- Regularize an almost-everywhere increasing quadratic limit on one null
set and package its finite predictable Stieltjes measure. -/
theorem exists_data_of_quadraticVariation
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat)
    (Y : Process Omega) (hCutoff : StrictMono cutoff)
    (hY : Martingale Y F mu)
    (hYRight : forall omega t,
      ContinuousWithinAt (Y · omega) (Ici t) t)
    (hMartingaleUniform : ∀ᵐ omega ∂mu, TendstoUniformly
      (fun k t => BoundedMartingaleQuadraticConvexification.martingalePart
        M T (w (cutoff k)) t omega)
      (fun t => Y t omega) atTop)
    (hSquaredUniform : ∀ᵐ omega ∂mu, TendstoUniformly
      (fun k t => squaredIncrementPart M T (w (cutoff k)) t omega)
      (fun t => rawVariation M T Y t omega) atTop)
    (hRawRight : forall omega t,
      ContinuousWithinAt (rawVariation M T Y · omega) (Ici t) t)
    (hRawMonotone : ∀ᵐ omega ∂mu,
      Monotone (rawVariation M T Y · omega))
    (hYTerminal : Integrable (Y T) mu) :
    Nonempty (Data F mu M T) := by
  let raw := rawVariation M T Y
  have hRawAdapted : StronglyAdapted F raw :=
    rawVariation_isStronglyAdapted hM hMRight T hY
  have hRawRegular : ∀ᵐ omega ∂mu,
      Monotone (raw · omega) ∧
        (forall t, T <= t -> raw t omega = raw T omega) ∧
        raw 0 omega = 0 := by
    filter_upwards [hRawMonotone, hSquaredUniform]
      with omega hMono hUniform
    exact ⟨hMono,
      rawVariation_constantAfter_of_uniform M T w cutoff Y omega hUniform,
      rawVariation_zero_of_uniform M T w cutoff Y omega hUniform⟩
  let bad : Set Omega := {omega | ¬(
    Monotone (raw · omega) ∧
      (forall t, T <= t -> raw t omega = raw T omega) ∧
      raw 0 omega = 0)}
  have hBadNull : mu bad = 0 := by
    simpa only [bad] using ae_iff.mp hRawRegular
  have hBadMeasurable : MeasurableSet[F 0] bad :=
    hUsual.containsNullSetsAtZero bad hBadNull
  let Q : Process Omega := ProcessNullSetRegularization.zeroOn bad raw
  have hQAdapted : StronglyAdapted F Q :=
    ProcessNullSetRegularization.stronglyAdapted_zeroOn
      hBadMeasurable hRawAdapted
  have hQRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t := by
    apply ProcessNullSetRegularization.zeroOn_isRightContinuous
    intro omega _ t
    exact hRawRight omega t
  have hQMono : forall omega, Monotone (Q · omega) := by
    intro omega s t hst
    by_cases homega : omega ∈ bad
    · simp [Q, homega]
    · have hRegular :
          Monotone (raw · omega) ∧
            (forall u, T <= u -> raw u omega = raw T omega) ∧
            raw 0 omega = 0 := by
        simpa only [bad, Set.mem_ofPred_eq, not_not] using homega
      simpa only [Q,
        ProcessNullSetRegularization.zeroOn_apply_of_notMem bad raw homega]
        using hRegular.1 hst
  have hQConstant : forall omega t, T <= t -> Q t omega = Q T omega := by
    intro omega t ht
    by_cases homega : omega ∈ bad
    · simp [Q, homega]
    · have hRegular :
          Monotone (raw · omega) ∧
            (forall u, T <= u -> raw u omega = raw T omega) ∧
            raw 0 omega = 0 := by
        simpa only [bad, Set.mem_ofPred_eq, not_not] using homega
      simpa only [Q,
        ProcessNullSetRegularization.zeroOn_apply_of_notMem bad raw homega]
        using hRegular.2.1 t ht
  have hQZero : Q 0 = 0 := by
    funext omega
    change Q 0 omega = 0
    by_cases homega : omega ∈ bad
    · simp [Q, homega]
    · have hRegular :
          Monotone (raw · omega) ∧
            (forall u, T <= u -> raw u omega = raw T omega) ∧
            raw 0 omega = 0 := by
        simpa only [bad, Set.mem_ofPred_eq, not_not] using homega
      simpa only [Q,
        ProcessNullSetRegularization.zeroOn_apply_of_notMem bad raw homega]
        using hRegular.2.2
  have hQIndistinguishable : ProcessIndistinguishable mu Q raw :=
    ProcessNullSetRegularization.zeroOn_indistinguishable hBadNull raw
  have hQEq : ∀ᵐ omega ∂mu, forall t, Q t omega = raw t omega :=
    ae_iff.mpr hQIndistinguishable
  have hQUniform : ∀ᵐ omega ∂mu, TendstoUniformly
      (fun k t => squaredIncrementPart M T (w (cutoff k)) t omega)
      (fun t => Q t omega) atTop := by
    filter_upwards [hSquaredUniform, hQEq] with omega hUniform hEq
    simpa only [raw, rawVariation, hEq] using hUniform
  have hXTerminal : MemLp (deterministicallyStoppedProcess M T T) (2 : ENNReal) mu :=
    stoppedProcess_const_memLp_two hM T hMT T
  have hXZero : MemLp (deterministicallyStoppedProcess M T 0) (2 : ENNReal) mu :=
    stoppedProcess_const_memLp_two hM T hMT 0
  have hRawTerminal : Integrable (raw T) mu := by
    exact (hXTerminal.integrable_sq.sub hXZero.integrable_sq).sub
      hYTerminal
  have hQTerminal : Integrable (Q T) mu :=
    hRawTerminal.congr (hQEq.mono fun _ hEq => (hEq T).symm)
  exact ⟨{
    weights := w
    cutoff := cutoff
    martingalePart := Y
    variation := Q
    cutoff_strictMono := hCutoff
    martingalePart_isMartingale := hY
    martingalePart_rightContinuous := hYRight
    martingalePart_uniform := hMartingaleUniform
    variation_uniform := hQUniform
    variation_isStronglyAdapted := hQAdapted
    variation_rightContinuous := hQRight
    variation_monotone := hQMono
    variation_constantAfter := hQConstant
    variation_zero := hQZero
    variation_indistinguishable_raw := hQIndistinguishable
    variation_terminal_integrable := hQTerminal }⟩

end BoundedMartingaleQuadraticKernel

end FTAPTheorem42
