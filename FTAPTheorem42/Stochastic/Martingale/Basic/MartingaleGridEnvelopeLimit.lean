/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Davis.MartingaleConvexGridDavis
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisGeneric
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Foundations.CadlagEnvelope

/-!
# Limits of martingale grid envelopes

Identify the supremum over refining grids with the continuous-time supremum
and obtain integrability from uniform grid bounds.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticKernel

variable {mu : Measure Omega} [IsProbabilityMeasure mu]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [SigmaFiniteFiltration mu F]
  {M : Process Omega} {T : NNReal}

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticConvexification
open SIntegrableFiniteVariationBridge
open SquareIntegrableMartingaleQuadraticApproximation

omit [MeasurableSpace Omega] [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F] in
theorem eFactorialRunningMaxEnvelope_eq_iSup_Iic_of_rightContinuous
    (M : Process Omega) (T : NNReal)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (omega : Omega) :
    FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t omega => |M t omega|) T omega =
      ⨆ t : Set.Iic T, ENNReal.ofReal |M t.1 omega| := by
  apply le_antisymm
  · unfold FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
    apply iSup_le
    intro r
    obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.range (r * r.factorial + 1))
      Finset.nonempty_range_add_one
      (fun j => (FactorialChronologicalGrid.stoppedGrid T r).natSample
        (fun t omega => |M t omega|) j omega)
    rw [show FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T r omega =
        (FactorialChronologicalGrid.stoppedGrid T r).natSample
          (fun t omega => |M t omega|) k omega by
      exact hkEq]
    change ENNReal.ofReal
        |M ((FactorialChronologicalGrid.stoppedGrid T r).sampledTime k) omega| ≤ _
    exact le_iSup (fun t : Set.Iic T => ENNReal.ofReal |M t.1 omega|)
      ⟨(FactorialChronologicalGrid.stoppedGrid T r).sampledTime k, by
        change min ((FactorialChronologicalGrid.grid r).time
            ((FactorialChronologicalGrid.stoppedGrid T r).natIndex k)) T ≤ T
        exact min_le_right _ _⟩
  · apply iSup_le
    intro t
    exact FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
      (fun s omega => |M s omega|) T
      (fun omega s => (hMRight omega s).abs) omega t.2

omit [SigmaFiniteFiltration mu F] [IsProbabilityMeasure mu] in
theorem finiteHorizonAbsoluteEnvelope_integrable_of_grid_bound
    (M : Process Omega) (T : NNReal) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : forall omega t, Tendsto (M · omega) (𝓝[<] t)
      (𝓝 (Function.leftLim (M · omega) t)))
    {b : Real} (hb : 0 ≤ b)
    (hBound : ∀ r, (∫ omega, FactorialChronologicalGrid.factorialRunningMax
      (fun t omega => |M t omega|) T (level T r) omega ∂mu) ≤ b) :
    Integrable (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T) mu ∧
    (∫ omega, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T omega ∂mu) ≤ b := by
  let E := FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T
  have hENonneg : ∀ᵐ omega ∂mu, 0 ≤ E omega := by
    filter_upwards [] with omega
    exact Real.sqrt_nonneg _
  have hStarMeas : ∀ r, Measurable
      (fun omega => ENNReal.ofReal
        (FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |M t omega|) T (level T r) omega)) := by
    intro r
    apply Measurable.ennreal_ofReal
    exact FactorialChronologicalGrid.measurable_factorialRunningMax
      (fun t omega => |M t omega|) T (level T r)
      (fun t => ((hM.stronglyMeasurable t).mono (F.le t)).norm.measurable)
  have hStarMono : Monotone (fun r => fun omega => ENNReal.ofReal
      (FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T (level T r) omega)) := by
    intro r s hrs omega
    apply ENNReal.ofReal_le_ofReal
    exact (FactorialChronologicalGrid.factorialRunningMax_mono
      (fun t omega => |M t omega|) T)
      (BoundedMartingaleQuadraticApproximation.level_mono T hrs) omega
  have hLevelSup : (fun omega => ⨆ r, ENNReal.ofReal
        (FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |M t omega|) T r omega)) =
      (fun omega => ⨆ r, ENNReal.ofReal
        (FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |M t omega|) T (level T r) omega)) := by
    funext omega
    apply le_antisymm
    · apply iSup_le
      intro r
      exact le_iSup_of_le r (ENNReal.ofReal_le_ofReal
        ((FactorialChronologicalGrid.factorialRunningMax_mono
          (fun t omega => |M t omega|) T)
          (BoundedMartingaleQuadraticApproximation.self_le_level T r) omega))
    · apply iSup_le
      intro r
      exact le_iSup (fun s => ENNReal.ofReal
        (FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |M t omega|) T s omega)) (level T r)
  have hEnvelopeIntegral :
      (∫⁻ omega, FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t omega => |M t omega|) T omega ∂mu) =
        ⨆ r, ∫⁻ omega, ENNReal.ofReal
          (FactorialChronologicalGrid.factorialRunningMax
            (fun t omega => |M t omega|) T (level T r) omega) ∂mu := by
    unfold FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
    rw [hLevelSup]
    exact MeasureTheory.lintegral_iSup hStarMeas hStarMono
  have hEachBound : ∀ r, ∫⁻ omega, ENNReal.ofReal
      (FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T (level T r) omega) ∂mu ≤
      ENNReal.ofReal (b) := by
    intro r
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (factorialGridDavisStar_integrable M T hM r)
      (Filter.Eventually.of_forall fun omega => by
        exact finiteRunningMax_nonneg _ _
          ((FactorialChronologicalGrid.stoppedGrid T (level T r)).natSample_nonneg
            (fun _ _ => abs_nonneg _)) omega)]
    exact ENNReal.ofReal_le_ofReal
      (hBound r)
  have hEnvelopeBound :
      (∫⁻ omega, FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t omega => |M t omega|) T omega ∂mu) ≤
        ENNReal.ofReal (b) := by
    rw [hEnvelopeIntegral]
    exact iSup_le hEachBound
  have hEnvelopeOfReal : ∀ omega,
      ENNReal.ofReal (E omega) =
        FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
          (fun t omega => |M t omega|) T omega := by
    intro omega
    calc
      ENNReal.ofReal (E omega) =
          ⨆ t : Set.Iic T, ENNReal.ofReal |M t.1 omega| :=
        FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup
          hMRight hMLeft T
      _ = FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
          (fun t omega => |M t omega|) T omega :=
        (eFactorialRunningMaxEnvelope_eq_iSup_Iic_of_rightContinuous
          M T hMRight omega).symm
  have hEInt : Integrable E mu := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (((FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
        hM.stronglyAdapted T).mono (F.le T)).aestronglyMeasurable) hENonneg).mp
    rw [MeasureTheory.lintegral_congr hEnvelopeOfReal]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEnvelopeBound
  refine ⟨hEInt, ?_⟩
  have hEnvelopeOfRealIntegral :
      ENNReal.ofReal (∫ omega, E omega ∂mu) =
        ∫⁻ omega, FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
          (fun t omega => |M t omega|) T omega ∂mu := by
    calc
      ENNReal.ofReal (∫ omega, E omega ∂mu) =
          ∫⁻ omega, ENNReal.ofReal (E omega) ∂mu :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hEInt hENonneg
      _ = ∫⁻ omega, FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
          (fun t omega => |M t omega|) T omega ∂mu :=
        MeasureTheory.lintegral_congr hEnvelopeOfReal
  apply (ENNReal.ofReal_le_ofReal_iff
    hb).mp
  rw [hEnvelopeOfRealIntegral]
  exact hEnvelopeBound

end BoundedMartingaleQuadraticKernel

end FTAPTheorem42
