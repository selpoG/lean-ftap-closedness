import FTAPTheorem42.Stochastic.Topology.Emery.ProcessAlgebra
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAdditivity
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARestriction
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationPathIntegralControl
import FTAPTheorem42.Stochastic.Topology.Emery.FiniteVariationTestEstimate
import FTAPTheorem42.Stochastic.Topology.Emery.MartingaleTestEstimate

/-! # Uniform elementary-test convergence of coefficient truncation tails -/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data

variable {Omega : Type*} [MeasurableSpace Omega]
  {S : Process Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu} {G : SIntegrableStrategy D}
  {T : NNReal} {E : SIntegrableFiniteVariationBridge G}

omit [SigmaFiniteFiltration mu F] in
/-- Canonical variation L¹ convergence controls every elementary test of the
completed finite-variation processes under the original probability. -/
theorem finiteHorizonCompletedFiniteVariationPart_emery_zero
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T)
    (K : Nat → FiniteHorizonM2ACoefficient E Q)
    (hNorm : Tendsto (fun n => eLpNorm (K n).coefficient 1
      (canonicalVariationMeasure E)) atTop (𝓝 0)) :
    ElementaryEmeryConverges mu F
      (fun n => finiteHorizonCompletedFiniteVariationPart hUsual T Q E (K n)) 0 := by
  let A := fun n => finiteHorizonCompletedFiniteVariationPart hUsual T Q E (K n)
  have hBV n : ∀ w, BoundedVariationOn (A n · w) univ :=
    completedFiniteVariationProcess_isBoundedVariation hUsual E (K n).integrand
      (K n).integrand_isStronglyPredictable (K n).integrand_memLp_variation
  have hRight n : ∀ w t, ContinuousWithinAt (A n · w) (Ici t) t :=
    completedFiniteVariationProcess_rightContinuous hUsual E (K n).integrand
      (K n).integrand_isStronglyPredictable (K n).integrand_memLp_variation
  have hProg n : IsStronglyProgressive F (A n) :=
    (completedFiniteVariationProcess_isStronglyPredictable hUsual E (K n).integrand
      (K n).integrand_isStronglyPredictable (K n).integrand_memLp_variation).isStronglyProgressive
  let V : Nat → Omega → Real := fun n w =>
    (∫⁻ t, ‖(K n).integrand t w‖ₑ ∂(FiniteVariationPath.signedMeasure
      (G.finiteVariationPart_isBoundedVariation w)).totalVariation).toReal
  have hVStrong n : StronglyMeasurable (V n) := by
    simpa only [Pi.zero_apply, sub_zero] using
      finiteVariationPathIntegral_toReal_stronglyMeasurable E
        (K n).integrand_isStronglyPredictable
        (show IsStronglyPredictable F (0 : Process Omega) from stronglyMeasurable_zero)
  have hVNorm : Tendsto (fun n => eLpNorm (V n) 1 E.referenceMeasure) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hNorm
      (fun _ => zero_le) (fun n => ?_)
    have h : eLpNorm (V n) 1 E.referenceMeasure ≤
        eLpNorm (Function.uncurry (K n).integrand) 1 (canonicalVariationMeasure E) := by
      simpa only [show Function.uncurry (0 : Process Omega) = 0 from rfl,
        Pi.zero_apply, sub_zero] using
        finiteVariationPathIntegral_toReal_eLpNorm_le E
          (K n).integrand_isStronglyPredictable
          (show IsStronglyPredictable F (0 : Process Omega) from stronglyMeasurable_zero)
    exact h.trans (eLpNorm_indicator_le _ (measurableSet_finiteHorizonPredictableStrip T))
  let W : Nat → Omega → Real := fun n w => min (V n w) 1
  have hWStrong n : StronglyMeasurable (W n) :=
    ((hVStrong n).measurable.min measurable_const).stronglyMeasurable
  have hWBound n w : 0 ≤ W n w ∧ W n w ≤ 1 :=
    ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  have hWNorm : Tendsto (fun n => eLpNorm (W n) 1 E.referenceMeasure) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVNorm
      (fun _ => zero_le) (fun n => eLpNorm_mono (hWStrong n).aestronglyMeasurable fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hWBound n w).1,
      Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact min_le_left _ _
  have hWRef : TendstoInMeasure E.referenceMeasure W atTop (fun _ => (0 : Real)) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
    simpa only [← Pi.zero_def, sub_zero] using hWNorm
  have hRefAbs : E.referenceMeasure ≪ mu :=
    withDensity_absolutelyContinuous mu (fun w => (E.referenceDensity w : ENNReal))
  have hMuAbs : mu ≪ E.referenceMeasure :=
    withDensity_absolutelyContinuous'
      E.referenceDensity_measurable.coe_nnreal_ennreal.aemeasurable
      (Eventually.of_forall fun w => by exact_mod_cast (E.referenceDensity_pos w).ne')
  have hWMeasure : TendstoInMeasure mu W atTop (fun _ => (0 : Real)) :=
    (EquivalentMeasureTransfer.tendstoInMeasure_iff_of_mutuallyAbsolutelyContinuous
      hRefAbs hMuAbs (fun n => (hWStrong n).aestronglyMeasurable)).mp hWRef
  apply elementaryEmeryConverges_zero_of_boundedVariation hProg hBV hRight
    hWStrong hWBound _
    (PredictableElementaryEmery.integral_tendsto_zero_of_tendstoInMeasure_of_bounded
      hWStrong hWBound hWMeasure)
  intro n
  have hRaw := finiteHorizonCompletedFiniteVariationPart_indistinguishable hUsual E Q (K n)
  have hInt := integrable_section_ae_of_memLp_one_canonicalVariation E
    (K n).integrand (K n).integrand_isStronglyPredictable (K n).integrand_memLp_variation
  filter_upwards [hRaw, hInt] with w hw hi
  apply min_le_min_right 1
  apply ENNReal.toReal_mono hi.hasFiniteIntegral.ne
  apply totalVariation_cumulativeIntegral_le E (K n).integrand_isStronglyPredictable
    w hi (hBV n w) (hRight n w)
  intro t
  rw [show A n t w = _ from hw t, show A n 0 w = _ from hw 0]
  simp [finiteVariationIntegralProcess, pathVariationMeasureUpTo]

/-- Energy control convergence makes completed martingale integrals vanish
on every test horizon, including horizons after the completion horizon. -/
theorem finiteHorizonCompletedMartingalePart_emery_zero
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) 2 mu)
    (K : Nat → FiniteHorizonM2ACoefficient E Q)
    (hNorm : Tendsto (fun n => eLpNorm (K n).coefficient 2 Q.predictableEnergyMeasure)
      atTop (𝓝 0)) :
    ElementaryEmeryConverges mu F
      (fun n => finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale hGMTerminal
        (K n)) 0 := by
  let c := K
  let M := fun n => finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale hGMTerminal (c n)
  have hM n : Martingale (M n) F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale hUsual Q hGMartingale
      G.martingalePart_isRightContinuous hGMTerminal (Function.uncurry (c n).integrand)
      (c n).integrand_isStronglyPredictable (c n).integrand_memLp_energy
  have hMemT n : MemLp (M n T) 2 mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp hUsual Q hGMartingale
      G.martingalePart_isRightContinuous hGMTerminal (Function.uncurry (c n).integrand)
      (c n).integrand_isStronglyPredictable (c n).integrand_memLp_energy
  have hEarlier n U : MemLp (M n U) 2 mu ∧ eLpNorm (M n U) 2 mu ≤ eLpNorm (M n T) 2 mu := by
    rcases le_total U T with hUT | hTU
    · exact MartingaleL2Terminal.Martingale.memLp_two_of_le_and_eLpNorm_le (hM n) hUT (hMemT n)
    · have hEq : M n U =ᵐ[mu] M n T :=
        finiteHorizonMartingaleIntegralProcess_constantAfter hUsual Q hGMartingale
          G.martingalePart_isRightContinuous hGMTerminal (Function.uncurry (c n).integrand)
          (c n).integrand_isStronglyPredictable (c n).integrand_memLp_energy U hTU
      exact ⟨(hMemT n).ae_eq hEq.symm, (eLpNorm_congr_ae hEq).le⟩
  have hTerminal : Tendsto (fun n => eLpNorm (M n T) 2 mu) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hNorm
      (fun _ => zero_le) (fun n => ?_)
    have hEq := finiteHorizonMartingaleIntegralProcess_terminal_eLpNorm_eq
      hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
      (Function.uncurry (c n).integrand) (c n).integrand_isStronglyPredictable
      (c n).integrand_memLp_energy
    change eLpNorm (M n T) 2 mu =
      eLpNorm (Function.uncurry (c n).integrand) 2 Q.predictableEnergyMeasure at hEq
    rw [hEq]
    exact eLpNorm_indicator_le _ (measurableSet_finiteHorizonPredictableStrip T)
  apply elementaryEmeryConverges_zero_of_martingale_L2 hM _ _
    (fun n U => (hEarlier n U).1) _
  · intro n
    exact finiteHorizonMartingaleIntegralProcess_rightContinuous hUsual Q hGMartingale
      G.martingalePart_isRightContinuous hGMTerminal (Function.uncurry (c n).integrand)
      (c n).integrand_isStronglyPredictable (c n).integrand_memLp_energy
  · intro n
    exact finiteHorizonMartingaleIntegralProcess_zero hUsual Q hGMartingale
      G.martingalePart_isRightContinuous hGMTerminal (Function.uncurry (c n).integrand)
      (c n).integrand_isStronglyPredictable (c n).integrand_memLp_energy
  · intro U
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hTerminal (fun _ => zero_le) (fun n => (hEarlier n U).2)

/-- Simultaneous variation and energy control convergence gives uniform
elementary-test convergence of the completed integral. -/
theorem finiteHorizonCompletedM2AGain_emery_zero
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) 2 mu)
    (K : Nat → FiniteHorizonM2ACoefficient E Q)
    (hVariation : Tendsto (fun n => eLpNorm (K n).coefficient 1
      (canonicalVariationMeasure E)) atTop (𝓝 0))
    (hEnergy : Tendsto (fun n => eLpNorm (K n).coefficient 2
      Q.predictableEnergyMeasure) atTop (𝓝 0)) :
    ElementaryEmeryConverges mu F
      (fun n => finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal
        (K n)) 0 := by
  have hM := finiteHorizonCompletedMartingalePart_emery_zero
    hUsual Q hGMartingale hGMTerminal K hEnergy
  have hA := finiteHorizonCompletedFiniteVariationPart_emery_zero hUsual Q K hVariation
  have h := hM.add (fun n => ?_) (fun n => ?_)
    (show IsStronglyProgressive F (0 : Process Omega) from fun _ => stronglyMeasurable_zero)
    (show IsStronglyProgressive F (0 : Process Omega) from fun _ => stronglyMeasurable_zero) hA
  · unfold finiteHorizonCompletedM2AGain
    simpa only [Pi.add_def, add_zero] using h
  · exact StronglyAdapted.isStronglyProgressive_of_rightContinuous
      (finiteHorizonMartingaleIntegralProcess_isMartingale hUsual Q hGMartingale
        G.martingalePart_isRightContinuous hGMTerminal
        (Function.uncurry (K n).integrand)
        (K n).integrand_isStronglyPredictable
        (K n).integrand_memLp_energy).stronglyAdapted
      (finiteHorizonMartingaleIntegralProcess_rightContinuous hUsual Q hGMartingale
        G.martingalePart_isRightContinuous hGMTerminal
        (Function.uncurry (K n).integrand)
        (K n).integrand_isStronglyPredictable
        (K n).integrand_memLp_energy)
  · exact (completedFiniteVariationProcess_isStronglyPredictable hUsual E
      (K n).integrand (K n).integrand_isStronglyPredictable
      (K n).integrand_memLp_variation).isStronglyProgressive

/-- Both controls vanish for the same coefficient tail. -/
theorem finiteHorizonCompletedM2AGain_truncationTail_emery
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) 2 mu)
    (K : FiniteHorizonM2ACoefficient E Q) :
    ElementaryEmeryConverges mu F
      (fun n => finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal
        (K.truncationTail n)) 0 :=
  finiteHorizonCompletedM2AGain_emery_zero hUsual Q hGMartingale hGMTerminal _
    K.truncationTail_control_convergence.1 K.truncationTail_control_convergence.2

/-- Bounded coefficient truncations converge to the full completed integral. -/
theorem finiteHorizonCompletedM2AGain_truncationCut_emery
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) 2 mu)
    (K : FiniteHorizonM2ACoefficient E Q) :
    ElementaryEmeryConverges mu F
      (fun n => finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal
        (K.truncationCut n))
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal K) := by
  let X := fun c => finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal c
  have hTail := finiteHorizonCompletedM2AGain_truncationTail_emery
    hUsual Q hGMartingale hGMTerminal K
  change ElementaryEmeryConverges mu F (fun n => X (K.truncationTail n)) 0 at hTail
  have hDiff : ElementaryEmeryConverges mu F (fun n => X K - X (K.truncationCut n)) 0 := by
    apply hTail.congr_sequence
    intro n
    have h := finiteHorizonCompletedM2AGain_add hUsual Q E hGMartingale hGMTerminal
      (K.truncationCut n) (K.truncationTail n)
    rw [K.truncationCut_add_truncationTail n] at h
    filter_upwards [h] with w hw
    intro t
    have ht := hw t
    change X K t w = X (K.truncationCut n) t w + X (K.truncationTail n) t w at ht
    change X (K.truncationTail n) t w = X K t w - X (K.truncationCut n) t w
    linarith
  exact elementaryEmeryConverges_iff_reverse_sub_zero.mpr hDiff

end FTAPTheorem42.SIntegrableFiniteVariationBridge
