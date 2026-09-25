/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationKernel
import FTAPTheorem42.Stochastic.Memin.ControlLIntegral

/-!
# Stieltjes kernels of increasing processes

An everywhere increasing right-continuous real process which is constant
after a deterministic horizon defines a finite Stieltjes measure on every
sample path.  Fixed-time measurability bundles these path measures into a
kernel.  Integrating the kernel over the sample space and trimming to the
predictable sigma algebra gives the measure used below for bounded-martingale
quadratic variation.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace IncreasingProcessStieltjesKernel

/-- The Stieltjes function carried by one increasing right-continuous path. -/
noncomputable def pathFunction
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (omega : Omega) : StieltjesFunction NNReal where
  toFun := fun t => Q t omega
  mono' := hMono omega
  right_continuous' := hRight omega

/-- The positive Stieltjes measure of one increasing path. -/
noncomputable def pathMeasure
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (omega : Omega) : Measure NNReal :=
  (pathFunction Q hMono hRight omega).measure

omit [MeasurableSpace Omega] in
@[simp]
theorem pathMeasure_Ioc
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (omega : Omega) (a b : NNReal) :
    pathMeasure Q hMono hRight omega (Ioc a b) =
      ENNReal.ofReal (Q b omega - Q a omega) := by
  exact StieltjesFunction.measure_Ioc
    (pathFunction Q hMono hRight omega) a b

omit [MeasurableSpace Omega] in
/-- Constancy after a finite horizon makes every path Stieltjes measure
finite. -/
theorem pathMeasure_isFinite
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (omega : Omega) :
    IsFiniteMeasure (pathMeasure Q hMono hRight omega) := by
  apply StieltjesFunction.isFiniteMeasure
      (f := pathFunction Q hMono hRight omega)
      (l := Q 0 omega) (u := Q T omega)
  · rw [atBot_eq_pure_of_isBot isBot_bot]
    exact tendsto_pure_nhds _ 0
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (hConstant omega t ht).symm

omit [MeasurableSpace Omega] in
/-- The total Stieltjes mass is the terminal increment of the increasing
path. -/
theorem pathMeasure_univ
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (omega : Omega) :
    pathMeasure Q hMono hRight omega Set.univ =
      ENNReal.ofReal (Q T omega - Q 0 omega) := by
  let f := pathFunction Q hMono hRight omega
  have hBot : Tendsto f atBot (nhds (Q 0 omega)) := by
    rw [atBot_eq_pure_of_isBot isBot_bot]
    exact tendsto_pure_nhds _ 0
  have hTop : Tendsto f atTop (nhds (Q T omega)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (hConstant omega t ht).symm
  exact StieltjesFunction.measure_univ f hBot hTop

omit [MeasurableSpace Omega] in
/-- Constancy after the horizon makes the open tail carry no Stieltjes
mass. -/
theorem pathMeasure_Ioi_horizon
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (omega : Omega) :
    pathMeasure Q hMono hRight omega (Ioi T) = 0 := by
  let f := pathFunction Q hMono hRight omega
  have hTop : Tendsto f atTop (nhds (Q T omega)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (hConstant omega t ht).symm
  rw [pathMeasure, f.measure_Ioi hTop T]
  simp [f, pathFunction]

/-- Interval masses of the random Stieltjes measures are measurable in the
sample parameter. -/
theorem measurable_pathMeasure_Ioc
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (hMeasurable : forall t, Measurable (Q t))
    (a b : NNReal) :
    Measurable fun omega =>
      pathMeasure Q hMono hRight omega (Ioc a b) := by
  simp_rw [pathMeasure_Ioc]
  exact ((hMeasurable b).sub (hMeasurable a)).ennreal_ofReal

/-- Total masses of the random Stieltjes measures are measurable in the
sample parameter. -/
theorem measurable_pathMeasure_univ
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t)) :
    Measurable fun omega =>
      pathMeasure Q hMono hRight omega Set.univ := by
  simp_rw [pathMeasure_univ Q hMono hRight T hConstant]
  exact ((hMeasurable T).sub (hMeasurable 0)).ennreal_ofReal

/-- Bundle the finite pathwise Stieltjes measures into a measurable kernel. -/
noncomputable def kernel
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t)) : Kernel Omega NNReal := by
  let : forall omega, IsFiniteMeasure
      (pathMeasure Q hMono hRight omega) := fun omega =>
    pathMeasure_isFinite Q hMono hRight T hConstant omega
  exact FiniteVariationKernel.ofFiniteMeasuresIoc
    (pathMeasure Q hMono hRight)
    (fun a b _ => measurable_pathMeasure_Ioc
      Q hMono hRight hMeasurable a b)
    (measurable_pathMeasure_univ
      Q hMono hRight T hConstant hMeasurable)

@[simp]
theorem kernel_apply
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t))
    (omega : Omega) :
    kernel Q hMono hRight T hConstant hMeasurable omega =
      pathMeasure Q hMono hRight omega :=
  rfl

/-- Every fibre of the increasing-process kernel is finite. -/
theorem kernel_isFiniteMeasure
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t))
    (omega : Omega) :
    IsFiniteMeasure
      (kernel Q hMono hRight T hConstant hMeasurable omega) := by
  rw [kernel_apply]
  exact pathMeasure_isFinite Q hMono hRight T hConstant omega

/-- A kernel with finite fibres is s-finite, even without a pathwise uniform
bound on its terminal mass. -/
theorem kernel_isSFinite
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t)) :
    IsSFiniteKernel
      (kernel Q hMono hRight T hConstant hMeasurable) := by
  let : forall omega, IsFiniteMeasure
      (kernel Q hMono hRight T hConstant hMeasurable omega) := fun omega =>
    kernel_isFiniteMeasure
      Q hMono hRight T hConstant hMeasurable omega
  exact FiniteVariationKernel.isSFiniteKernel_of_finiteMeasures _

/-- The integrated pathwise Stieltjes kernel, restricted to the predictable
sigma algebra. -/
noncomputable def predictableMeasure
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega)
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t)) :
    MeminPredictableControlMeasure F :=
  PredictableKernelMeasure.predictableMeasure F mu
    (kernel Q hMono hRight T hConstant hMeasurable)

/-- Evaluation of the integrated Stieltjes kernel on a predictable set. -/
theorem predictableMeasure_apply
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [SFinite mu]
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t))
    {s : Set (NNReal × Omega)} (hs : MeasurableSet[F.predictable] s) :
    predictableMeasure F mu Q hMono hRight T hConstant hMeasurable s =
      ∫⁻ omega, pathMeasure Q hMono hRight omega
        ((fun t => (t, omega)) ⁻¹' s) ∂mu := by
  let : IsSFiniteKernel
      (kernel Q hMono hRight T hConstant hMeasurable) :=
    kernel_isSFinite Q hMono hRight T hConstant hMeasurable
  exact PredictableKernelMeasure.predictableMeasure_apply hs

/-- The integrated Stieltjes measure gives zero mass to the predictable
time-zero slice. -/
theorem predictableMeasure_timeZeroSlice
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [SFinite mu]
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t)) :
    predictableMeasure F mu Q hMono hRight T hConstant hMeasurable
        ({0} ×ˢ (Set.univ : Set Omega)) = 0 := by
  have hSlice : MeasurableSet[F.predictable]
      ({0} ×ˢ (Set.univ : Set Omega)) :=
    measurableSet_predictable_singleton_bot_prod MeasurableSet.univ
  rw [predictableMeasure_apply Q hMono hRight T hConstant
    hMeasurable hSlice]
  have hSection (omega : Omega) :
      ((fun t : NNReal => (t, omega)) ⁻¹'
        ({0} ×ˢ (Set.univ : Set Omega))) = ({0} : Set NNReal) := by
    ext t
    simp
  simp_rw [hSection, pathMeasure]
  simp only [StieltjesFunction.measure_singleton]
  have hLeft (omega : Omega) :
      Function.leftLim
        (pathFunction Q hMono hRight omega : NNReal -> Real) 0 =
          pathFunction Q hMono hRight omega 0 :=
    leftLim_eq_of_eq_bot _ (by simp)
  simp_rw [hLeft, sub_self, ENNReal.ofReal_zero, lintegral_zero]

/-- The integrated predictable Stieltjes measure is supported at or before
the deterministic horizon. -/
theorem predictableMeasure_afterHorizon
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [SFinite mu]
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t)) :
    predictableMeasure F mu Q hMono hRight T hConstant hMeasurable
        (Ioi T ×ˢ (Set.univ : Set Omega)) = 0 := by
  have hTail : MeasurableSet[F.predictable]
      (Ioi T ×ˢ (Set.univ : Set Omega)) :=
    measurableSet_predictable_Ioi_prod MeasurableSet.univ
  rw [predictableMeasure_apply Q hMono hRight T hConstant
    hMeasurable hTail]
  have hSection (omega : Omega) :
      ((fun t : NNReal => (t, omega)) ⁻¹'
        (Ioi T ×ˢ (Set.univ : Set Omega))) = Ioi T := by
    ext t
    simp
  simp_rw [hSection,
    pathMeasure_Ioi_horizon Q hMono hRight T hConstant, lintegral_zero]

/-- Integrability of the terminal path mass makes the integrated predictable
Stieltjes measure finite. -/
theorem predictableMeasure_isFinite
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [SFinite mu]
    (Q : Process Omega)
    (hMono : forall omega, Monotone (Q · omega))
    (hRight : forall omega t,
      ContinuousWithinAt (Q · omega) (Ici t) t)
    (T : NNReal)
    (hConstant : forall omega t, T <= t -> Q t omega = Q T omega)
    (hMeasurable : forall t, Measurable (Q t))
    (hTerminal : Integrable (fun omega => Q T omega - Q 0 omega) mu) :
    IsFiniteMeasure
      (predictableMeasure F mu Q hMono hRight T hConstant hMeasurable) := by
  constructor
  rw [predictableMeasure_apply Q hMono hRight T hConstant
    hMeasurable MeasurableSet.univ]
  simp_rw [preimage_univ,
    pathMeasure_univ Q hMono hRight T hConstant]
  exact (lintegral_mono fun omega =>
    Real.ofReal_le_enorm (Q T omega - Q 0 omega)).trans_lt
      (hasFiniteIntegral_iff_enorm.mp hTerminal.2)

end IncreasingProcessStieltjesKernel

end FTAPTheorem42
