/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.ProjectionPackage
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The completed square-integrable dual predictable projection

The projection-ready package already fixes the rows, weights, cutoff,
candidate, regularized process, and predictable zero-on version.  This file
only consumes that data.  The terminal estimate is obtained by one Fatou
argument for the nonnegative squared terminal rows; no strong `L²` limit is
assumed.  The residual martingale is transported from the càdlàg candidate by
process indistinguishability.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

open SquareIntegrableIncreasingProcessData

/-! ## The terminal Fatou estimate -/

omit [IsProbabilityMeasure mu] in
private theorem integral_sq_le_of_tendstoAE_of_forall_integral_sq_le
    {f : Nat → Ω → Real} {g : Ω → Real} {K : Real}
    (hf : ∀ n, Integrable (fun omega => (f n omega) ^ 2) mu)
    (hg : Integrable (fun omega => (g omega) ^ 2) mu)
    (hfg : TendstoAE mu f g)
    (hbound : ∀ n, (∫ omega, (f n omega) ^ 2 ∂mu) ≤ K) :
    (∫ omega, (g omega) ^ 2 ∂mu) ≤ K := by
  have hSqTendsto : ∀ᵐ omega ∂mu, Tendsto
      (fun n => (f n omega) ^ 2) atTop (𝓝 ((g omega) ^ 2)) := by
    filter_upwards [hfg] with omega homega
    exact (continuousAt_pow (g omega) 2).tendsto.comp homega
  have hLiminfEq :
      (fun omega => liminf (fun n => (f n omega) ^ 2) atTop) =ᵐ[mu]
        (fun omega => (g omega) ^ 2) := by
    filter_upwards [hSqTendsto] with omega homega
    exact homega.liminf_eq
  have hLiminfIntegrable : Integrable
      (fun omega => liminf (fun n => (f n omega) ^ 2) atTop) mu :=
    hg.congr hLiminfEq.symm
  have hLiminfNonnegative : ∀ᵐ omega ∂mu,
      0 ≤ liminf (fun n => (f n omega) ^ 2) atTop := by
    filter_upwards [hLiminfEq] with omega homega
    rw [homega]
    exact sq_nonneg _
  have hFatou := MeasureTheory.lintegral_liminf_le'
    (μ := mu) (f := fun n omega => ENNReal.ofReal ((f n omega) ^ 2))
    (u := atTop)
    (fun n => (hf n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hLeft : ENNReal.ofReal
      (∫ omega, liminf (fun n => (f n omega) ^ 2) atTop ∂mu) =
      ∫⁻ omega, ENNReal.ofReal
        (liminf (fun n => (f n omega) ^ 2) atTop) ∂mu :=
    ofReal_integral_eq_lintegral_ofReal hLiminfIntegrable hLiminfNonnegative
  have hEach (n : Nat) : ENNReal.ofReal
      (∫ omega, (f n omega) ^ 2 ∂mu) =
      ∫⁻ omega, ENNReal.ofReal ((f n omega) ^ 2) ∂mu :=
    ofReal_integral_eq_lintegral_ofReal (hf n)
      (Filter.Eventually.of_forall (fun omega => sq_nonneg _))
  have hOfRealLiminf : ∀ᵐ omega ∂mu,
      ENNReal.ofReal (liminf (fun n => (f n omega) ^ 2) atTop) =
        liminf (fun n => ENNReal.ofReal ((f n omega) ^ 2)) atTop := by
    filter_upwards [hSqTendsto] with omega homega
    rw [homega.liminf_eq]
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp homega).liminf_eq.symm
  have hFatou' : ENNReal.ofReal
      (∫ omega, liminf (fun n => (f n omega) ^ 2) atTop ∂mu) ≤
      liminf (fun n => ENNReal.ofReal
        (∫ omega, (f n omega) ^ 2 ∂mu)) atTop := by
    calc
      ENNReal.ofReal
          (∫ omega, liminf (fun n => (f n omega) ^ 2) atTop ∂mu) =
          ∫⁻ omega, ENNReal.ofReal
            (liminf (fun n => (f n omega) ^ 2) atTop) ∂mu := hLeft
      _ = ∫⁻ omega, liminf
          (fun n => ENNReal.ofReal ((f n omega) ^ 2)) atTop ∂mu :=
        lintegral_congr_ae hOfRealLiminf
      _ ≤ liminf (fun n => ∫⁻ omega, ENNReal.ofReal
          ((f n omega) ^ 2) ∂mu) atTop := hFatou
      _ = liminf (fun n => ENNReal.ofReal
          (∫ omega, (f n omega) ^ 2 ∂mu)) atTop := by
        simp_rw [← hEach]
  have hUpper : ∀ n, ENNReal.ofReal
      (∫ omega, (f n omega) ^ 2 ∂mu) ≤ ENNReal.ofReal K := by
    intro n
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hLiminfBound : liminf (fun n => ENNReal.ofReal
      (∫ omega, (f n omega) ^ 2 ∂mu)) atTop ≤ ENNReal.ofReal K :=
    liminf_le_of_frequently_le (Filter.Frequently.of_forall hUpper)
  have hKNonnegative : 0 ≤ K := by
    exact le_trans (integral_nonneg (fun omega => sq_nonneg (f 0 omega)))
      (hbound 0)
  have hBoundENN : ENNReal.ofReal
      (∫ omega, liminf (fun n => (f n omega) ^ 2) atTop ∂mu) ≤ ENNReal.ofReal K :=
    hFatou'.trans hLiminfBound
  have hIntegralEq :
      (∫ omega, liminf (fun n => (f n omega) ^ 2) atTop ∂mu) =
        ∫ omega, (g omega) ^ 2 ∂mu :=
    integral_congr_ae hLiminfEq
  rw [← hIntegralEq]
  exact (ENNReal.ofReal_le_ofReal_iff hKNonnegative).mp hBoundENN

/-! ## The completed projection certificate -/

omit [SigmaFiniteFiltration mu F] in
structure SquareIntegrablePredictableCompensatorDualProjectionData
    {V : Process Ω} {T : NNReal}
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    (badPred : Set Ω) (Vp : Process Ω) : Prop where
  projection_ready :
    SquareIntegrablePredictableCompensatorProjectionReadyData pkg badPred Vp
  Vp_terminal_memLp_two : MemLp (Vp T) (2 : ENNReal) mu
  Vp_terminal_integrable : Integrable (Vp T) mu
  Vp_terminal_L2_bound :
    (∫ omega, (Vp T omega) ^ 2 ∂mu) ≤
      8 * ∫ omega, (V T omega) ^ 2 ∂mu
  residual_stronglyAdapted : StronglyAdapted F
    (fun t omega => V t omega - Vp t omega)
  residual_martingale : Martingale
    (fun t omega => V t omega - Vp t omega) F mu
  residual_integrable : ∀ t, Integrable
    (fun omega => V t omega - Vp t omega) mu
  residual_indistinguishable_martingale : ProcessIndistinguishable mu
    (fun t omega => V t omega - Vp t omega) pkg.M
  interval_testing_identity : ∀ {s t : NNReal}, s ≤ t →
    ∀ {B : Set Ω}, MeasurableSet[F s] B →
      (∫ omega in B,
        ((V t omega - Vp t omega) - (V s omega - Vp s omega)) ∂mu) = 0

/-! ## Construction from one fixed projection-ready package -/

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrablePredictableCompensatorDualProjection_producer
    {V : Process Ω} {T : NNReal}
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    {badPred : Set Ω} {Vp : Process Ω}
    (hReady : SquareIntegrablePredictableCompensatorProjectionReadyData
      pkg badPred Vp) :
    SquareIntegrablePredictableCompensatorDualProjectionData
      pkg badPred Vp := by
  have hVpMem : MemLp (Vp T) (2 : ENNReal) mu :=
    hReady.Vp_terminal_memLp_two
  have hVpIntegrable : Integrable (Vp T) mu :=
    hReady.Vp_terminal_integrable
  have hRowIntegrable : ∀ n, Integrable (fun omega =>
      (squareIntegrableCompensatorConvexRow
        pkg.hV pkg.hRows pkg.hControl pkg.hResidual
        (pkg.w (pkg.cutoff n)) T omega) ^ 2) mu := by
    intro n
    exact (squareIntegrableCompensatorConvexRow_terminal_memLp_two
      (F := F) (mu := mu) pkg.hV pkg.hRows pkg.hControl pkg.hResidual
      (pkg.w (pkg.cutoff n))).integrable_sq
  have hVpSqIntegrable : Integrable (fun omega => (Vp T omega) ^ 2) mu :=
    hVpMem.integrable_sq
  have hVpBound :
      (∫ omega, (Vp T omega) ^ 2 ∂mu) ≤
        8 * ∫ omega, (V T omega) ^ 2 ∂mu := by
    apply integral_sq_le_of_tendstoAE_of_forall_integral_sq_le
      hRowIntegrable hVpSqIntegrable
      hReady.terminal_row_tendstoAE
    exact hReady.terminal_row_L2_bound
  have hVPreg : ProcessIndistinguishable mu
      (fun t omega => V t omega - Vp t omega)
      (fun t omega => V t omega - pkg.Preg t omega) :=
    ProcessIndistinguishable.sub (ProcessIndistinguishable.refl mu V)
      hReady.Vp_indistinguishable_Preg
  have hPregPcad : ProcessIndistinguishable mu
      (fun t omega => V t omega - pkg.Preg t omega)
      (fun t omega => V t omega - pkg.Pcad t omega) :=
    ProcessIndistinguishable.sub (ProcessIndistinguishable.refl mu V)
      pkg.hReg.Preg_indistinguishable
  have hPcadM : ProcessIndistinguishable mu
      (fun t omega => V t omega - pkg.Pcad t omega) pkg.M := by
    filter_upwards [] with omega
    intro t
    have hDef := congrFun pkg.hCad.Pcad_definition t
    have hDefOmega := congrFun hDef omega
    rw [hDefOmega]
    ring
  have hResidualM : ProcessIndistinguishable mu
      (fun t omega => V t omega - Vp t omega) pkg.M :=
    hVPreg.trans (hPregPcad.trans hPcadM)
  have hResidualAdapted : StronglyAdapted F
      (fun t omega => V t omega - Vp t omega) :=
    pkg.hV.stronglyAdapted.sub
      hReady.predictable_version.Vp_isStronglyPredictable.stronglyAdapted
  have hResidualMartingale : Martingale
      (fun t omega => V t omega - Vp t omega) F mu :=
    pkg.hCad.M_martingale.congr hResidualAdapted
      (fun t => (hResidualM.eventuallyEq_at t).symm)
  have hResidualIntegrable : ∀ t, Integrable
      (fun omega => V t omega - Vp t omega) mu := by
    intro t
    exact hResidualMartingale.integrable t
  have hInterval : ∀ {s t : NNReal}, s ≤ t →
      ∀ {B : Set Ω}, MeasurableSet[F s] B →
        (∫ omega in B,
          ((V t omega - Vp t omega) - (V s omega - Vp s omega)) ∂mu) = 0 := by
    intro s t hst B hB
    have hSet := hResidualMartingale.setIntegral_eq hst hB
    calc
      (∫ omega in B,
          ((V t omega - Vp t omega) - (V s omega - Vp s omega)) ∂mu) =
          (∫ omega in B, V t omega - Vp t omega ∂mu) -
            ∫ omega in B, V s omega - Vp s omega ∂mu := by
        exact integral_sub (hResidualIntegrable t).restrict
          (hResidualIntegrable s).restrict
      _ = 0 := by
        rw [hSet]
        ring
  exact {
    projection_ready := hReady
    Vp_terminal_memLp_two := hVpMem
    Vp_terminal_integrable := hVpIntegrable
    Vp_terminal_L2_bound := hVpBound
    residual_stronglyAdapted := hResidualAdapted
    residual_martingale := hResidualMartingale
    residual_integrable := hResidualIntegrable
    residual_indistinguishable_martingale := hResidualM
    interval_testing_identity := hInterval }

namespace SquareIntegrablePredictableCompensatorComponentPackage

variable {V : Process Ω} {T : NNReal}

/-! The package method consumes exactly its existing projection-ready output. -/

omit [SigmaFiniteFiltration mu F] in
theorem dualProjection
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ badPred : Set Ω, ∃ Vp : Process Ω,
      SquareIntegrablePredictableCompensatorDualProjectionData
        pkg badPred Vp := by
  obtain ⟨badPred, Vp, hReady⟩ := pkg.projectionReady hUsual
  exact ⟨badPred, Vp,
    squareIntegrablePredictableCompensatorDualProjection_producer pkg hReady⟩

end SquareIntegrablePredictableCompensatorComponentPackage

end HorizonFactorialGrid

end FTAPTheorem42
