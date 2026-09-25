/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.CorrectedRegularization
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.CrossProductMartingale
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedJumpLocalMartingaleQuadraticSchedule
import FTAPTheorem42.Stochastic.Martingale.Quadratic.LocalMartingaleQuadraticVariation

/-!
# Quadratic variation and Davis control for the all-time DDY component

The variation belongs to the same bounded-jump component `L`. The original
source still requires the finite-variation correction involving `Q`.
-/

namespace FTAPTheorem42.HorizonFactorialGrid

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

open LocalMartingaleQuadratic SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

/-- Construct global DDY data from the original source and pass its same
bounded-jump component through quadratic gluing and the Davis estimate. -/
theorem exists_doleansDadeYen_quadratic_davis
    {X : Process Ω} (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    {c : Real} (hc : 0 < c) (hUsual : Filtration.UsualConditions mu F) :
    ∃ d : DoleansDadeYenData X F mu c,
      ∃ C : LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := d.L),
        ∃ QC : GluedQuadraticVariationCertificate C,
          (∀ n, localQuadraticRootAt QC.variation (C.localizer n) =ᵐ[mu]
            squareIntegrableMartingaleQuadraticRoot (C.coordinate n).quadraticData) ∧
          (∀ n, localQuadraticRootCostAt (mu := mu) QC.variation (C.localizer n) =
            squareIntegrableMartingaleQuadraticRootCost (C.coordinate n).quadraticData) ∧
          (∀ n, (∫ omega, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
              (stoppedProcess d.L (fun omega => (C.localizer n omega : WithTop NNReal)))
              (C.horizon n) omega ∂mu) ≤
            6 * ∫ omega, localQuadraticRootAt QC.variation (C.localizer n) omega ∂mu) ∧
          (∀ᵐ omega ∂mu, ∀ T : NNReal,
            Summable (fun t : Ioc (0 : NNReal) T =>
              (processLeftJump X t omega) ^ 2 - (processLeftJump d.L t omega) ^ 2) ∧
            (∑' t : Ioc (0 : NNReal) T,
              ((processLeftJump X t omega) ^ 2 - (processLeftJump d.L t omega) ^ 2)) =
              2 * (∑' t : Ioc (0 : NNReal) T,
                processLeftJump d.L t omega * processLeftJump d.Q t omega) +
                ∑' t : Ioc (0 : NNReal) T, (processLeftJump d.Q t omega) ^ 2 ∧
            |∑' t : Ioc (0 : NNReal) T,
              ((processLeftJump X t omega) ^ 2 - (processLeftJump d.L t omega) ^ 2)| ≤
              4 * c * variationOnFromTo (d.Q · omega) univ 0 T +
                (variationOnFromTo (d.Q · omega) univ 0 T) ^ 2) ∧
          (∀ (n : Nat) (G : ChronologicalGrid NNReal n) t omega,
            G.squaredIncrementProcess X t omega =
              G.squaredIncrementProcess d.L t omega +
                2 * G.crossIncrementProcess d.L d.Q t omega +
                G.squaredIncrementProcess d.Q t omega ∧
            |Real.sqrt (G.squaredIncrementProcess X t omega) -
              Real.sqrt (G.squaredIncrementProcess d.L t omega)| ≤
                variationOnFromTo (d.Q · omega) univ 0 t) ∧
          (∀ T omega,
            Tendsto (fun r =>
              (FactorialChronologicalGrid.grid (r + 1)).squaredIncrementProcess X T omega -
                (FactorialChronologicalGrid.grid (r + 1)).squaredIncrementProcess d.L T omega)
              atTop (𝓝 (2 * (∑' t : Ioc (0 : NNReal) T,
                processLeftJump d.L t omega * processLeftJump d.Q t omega) +
                  ∑' t : Ioc (0 : NNReal) T, (processLeftJump d.Q t omega) ^ 2))) ∧
          (∀ᵐ omega ∂mu, ∀ t,
            0 ≤ QC.variation t omega + d.quadraticCorrection t omega) ∧
          (StronglyAdapted F (fun t omega => QC.variation t omega + d.quadraticCorrection t omega) ∧
            ∀ᵐ omega ∂mu,
              (∀ t, ContinuousWithinAt
                (fun s => QC.variation s omega + d.quadraticCorrection s omega) (Ici t) t) ∧
              LocallyBoundedVariationOn
                (fun s => QC.variation s omega + d.quadraticCorrection s omega) univ) ∧
          (∀ᵐ omega ∂mu,
            Monotone (fun t => QC.variation t omega + d.quadraticCorrection t omega)) ∧
          (∃ V : Process Ω,
            ProcessIndistinguishable mu V
              (fun t omega => QC.variation t omega + d.quadraticCorrection t omega) ∧
            StronglyAdapted F V ∧
            (∀ omega t, ContinuousWithinAt (V · omega) (Ici t) t) ∧
            (∀ omega, Monotone (V · omega)) ∧ V 0 = 0 ∧
            (∀ omega, LocallyBoundedVariationOn (V · omega) univ) ∧ ProcessHasLeftLimits V ∧
            (∀ᵐ omega ∂mu, ∀ t,
              processLeftJump V t omega = (processLeftJump X t omega) ^ 2) ∧
            (∀ n, ProcessIndistinguishable mu
              (stoppedProcess V (fun w => (C.localizer n w : WithTop NNReal)))
              (fun t omega => stoppedProcess (C.coordinate n).quadraticData.variation
                (fun w => (C.localizer n w : WithTop NNReal)) t omega +
                  d.stoppedQuadraticCorrection (C.localizer n) t omega)) ∧
            (∀ᵐ omega ∂mu, ∀ t, X t omega ^ 2 - V t omega =
              (d.L t omega ^ 2 - QC.variation t omega) +
                2 * (d.L t omega * d.Q t omega -
                  (∑' s : Ioc (0 : NNReal) t,
                    processLeftJump d.L s omega * processLeftJump d.Q s omega) +
                  d.finiteVariationSquareIntegral t omega)) ∧
            LocalMartingale (fun t omega => X t omega ^ 2 - V t omega) F mu) ∧
          Nonempty (DoleansDadeYenL1Localization d) ∧
          LocalMartingale d.finiteVariationSquareIntegral F mu ∧
          LocalMartingale d.crossProductCorrection F mu := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨d⟩ := exists_doleansDadeYenData hX hXAdapted hXRight hXLeft hXZero hc hUsual
  obtain ⟨C⟩ := exists_boundedJumpLocalMartingaleQuadraticSchedule
    hUsual d.L_isLocalMartingale d.L_isStronglyAdapted d.L_rightContinuous d.L_leftLimits
    d.L_zero (fun _ => 2 * c) (fun _ => mul_nonneg (by norm_num) hc.le)
    (fun _ => by
      filter_upwards [d.L_jump_bound] with omega hOmega
      exact fun t _ => hOmega t)
  obtain ⟨QC⟩ := exists_gluedQuadraticVariationCertificate
    hUsual d.L_rightContinuous d.L_leftLimits C
  obtain ⟨V, hV, hVA, hVR, hVM, hVZ, hVB, hVL, hVJ, hVS, hVE⟩ :=
    d.exists_regularized_corrected C QC hUsual
  exact ⟨d, C, QC,
    fun n => localQuadraticRootAt_localizer_ae_eq_coordinate
      hUsual d.L_rightContinuous d.L_leftLimits C QC n,
    fun n => localQuadraticRootCostAt_localizer_eq_coordinate
      hUsual d.L_rightContinuous d.L_leftLimits C QC n,
    fun n => finiteHorizonAbsoluteEnvelope_integral_le_six_localQuadraticRoot
      hUsual d.L_rightContinuous d.L_leftLimits d.L_zero C QC n,
    d.jump_correction_identity, (fun _ G t omega => d.finiteGrid_control G t omega),
    d.finiteGrid_correction_tendsto_jumpSum, d.corrected_nonnegative C QC,
    d.corrected_regular C QC, d.corrected_monotone C QC,
    ⟨V, hV, hVA, hVR, hVM, hVZ, hVB, hVL, hVJ, hVS, hVE,
      d.corrected_squareResidual_isLocalMartingale hc.le C QC hVA hVR hV⟩,
    d.exists_common_localizer_integrableVariation hc.le,
    d.finiteVariationSquareIntegral_isLocalMartingale hc.le,
    d.crossProductCorrection_isLocalMartingale hc.le⟩

end FTAPTheorem42.HorizonFactorialGrid

namespace FTAPTheorem42

/-! ## Existence and uniqueness of quadratic variation for the original local martingale -/

open MeasureTheory Set Topology
open scoped NNReal

theorem exists_unique_localMartingaleQuadraticVariation
    {Ω : Type*} [MeasurableSpace Ω]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    {X : Process Ω} (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ Q : LocalMartingaleQuadraticVariation X F mu,
      ∀ R : LocalMartingaleQuadraticVariation X F mu,
        ProcessIndistinguishable mu Q.variation R.variation := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨d, C, QC, _, _, _, _, _, _, _, _, _, hV, _⟩ :=
    HorizonFactorialGrid.exists_doleansDadeYen_quadratic_davis
      hX hXAdapted hXRight hXLeft hXZero (c := 1) zero_lt_one hUsual
  obtain ⟨V, _, hAdapted, hRight, hMono, hZero, hBV, hLeft, hJump, _, _, hResidual⟩ := hV
  let Q : LocalMartingaleQuadraticVariation X F mu := {
    variation := V
    stronglyAdapted := hAdapted
    rightContinuous := hRight
    leftLimits := hLeft
    locallyBoundedVariation := hBV
    monotone := hMono
    zero := hZero
    jump_sq := hJump
    squareResidual := hResidual }
  exact ⟨Q, fun R => Q.unique hUsual hXRight R⟩

end FTAPTheorem42
