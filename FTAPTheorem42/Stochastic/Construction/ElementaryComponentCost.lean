import FTAPTheorem42.Stochastic.Construction.ElementaryGraph
import FTAPTheorem42.Stochastic.Topology.J1.ActualVariation

/-! # Actual component costs for stopped original-source elementary gains -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open LocalCompletedM2A SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Restopping a finite-stopped elementary graph at a deterministic horizon
supplies global FV component data in the original source's actual carrier. -/
noncomputable def elementaryClosedStop
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (T : NNReal) (hT : 0 < T) :
    ActualSIntegrableStrategy (realizationModel (unitSource source)) :=
  ActualLocallySIntegrableStrategy.deterministicallyStopped
    (elementaryActualLocal source (K.stopAt τ hτ) (2 * B) (fun ω => by
      rw [PredictableElementaryStrategy.coefficientAbsSum_stopAt]
      exact mul_le_mul_of_nonneg_left (hB ω) (by norm_num))) T hT

theorem elementaryClosedStop_martingaleZero
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (T : NNReal) (hT : 0 < T) :
    (elementaryClosedStop source K B hB τ hτ T hT).val.martingalePart 0 = 0 := by
  funext ω
  change _ - _ = (0 : Real)
  simp

theorem elementaryClosedStop_finiteVariationZero
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (T : NNReal) (hT : 0 < T) :
    (elementaryClosedStop source K B hB τ hτ T hT).val.finiteVariationPart 0 = 0 := by
  funext ω
  change _ - _ = (0 : Real)
  simp

theorem elementaryClosedStop_martingaleLeft
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (T : NNReal) (hT : 0 < T) :
    ProcessHasLeftLimits (elementaryClosedStop source K B hB τ hτ T hT).val.martingalePart := by
  have hBound : ∀ ω, (K.stopAt τ hτ).coefficientAbsSum ω ≤ (2 * B : NNReal) := by
    intro ω
    rw [PredictableElementaryStrategy.coefficientAbsSum_stopAt]
    exact mul_le_mul_of_nonneg_left (hB ω) (by norm_num)
  let data := sourceData (elementaryGainSource source (K.stopAt τ hτ) (2 * B) hBound)
  exact data.centeredUnitLocallySIntegrableStrategy_martingalePart_hasLeftLimits.stoppedProcess
      (fun _ : Ω => (T : WithTop NNReal))

theorem elementaryClosedStop_integrand
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (T : NNReal) (hT : 0 < T) (hτT : ∀ ω, τ ω ≤ T) :
    (elementaryClosedStop source K B hB τ hτ T hT).val.integrand =
      PredictableProcess.restrict (stochasticIntervalIocZero τ) K.integrand := by
  change PredictableProcess.restrict (stochasticIntervalIocZero (fun _ : Ω => T))
    (K.stopAt τ hτ).integrand = _
  have hK : (K.stopAt τ hτ).integrand =
      PredictableProcess.restrict (stochasticIntervalIocZero τ) K.integrand := by
    funext t ω
    rw [PredictableElementaryStrategy.stopAt_integrand_apply]
    by_cases ht : 0 < t ∧ t ≤ τ ω
    · rw [ite_eq_left ht, PredictableProcess.restrict_apply_of_mem
        ((mem_stochasticIntervalIocZero_iff τ t ω).2 ht)]
    · rw [ite_eq_right ht, PredictableProcess.restrict_apply_of_notMem
        (fun h => ht ((mem_stochasticIntervalIocZero_iff τ t ω).1 h))]
  rw [hK]
  funext t ω
  by_cases ht : (t, ω) ∈ stochasticIntervalIocZero (fun _ : Ω => T)
  · exact PredictableProcess.restrict_apply_of_mem ht
  · have hτ' : (t, ω) ∉ stochasticIntervalIocZero τ := by
      intro h
      have hh := (mem_stochasticIntervalIocZero_iff τ t ω).1 h
      exact ht ((mem_stochasticIntervalIocZero_iff _ t ω).2 ⟨hh.1, hh.2.trans (hτT ω)⟩)
    rw [PredictableProcess.restrict_apply_of_notMem ht,
      PredictableProcess.restrict_apply_of_notMem hτ']

theorem elementaryClosedStop_gain
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (T : NNReal) (hT : 0 < T) (hτT : ∀ ω, τ ω ≤ T) :
    ProcessIndistinguishable μ
      (stoppedProcess (ElementaryStrategy.gain S K.toElementary)
        (fun ω => (τ ω : WithTop NNReal)))
      (elementaryClosedStop source K B hB τ hτ T hT).val.stochasticIntegral := by
  apply Eventually.of_forall
  intro ω t
  change stoppedProcess (ElementaryStrategy.gain S K.toElementary) _ t ω =
    ElementaryStrategy.gain S (K.stopAt τ hτ).toElementary (min t T) ω
  rw [PredictableElementaryStrategy.gain_stopAt]
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [min_assoc, min_eq_right (hτT ω)]

/-- Summable prelocal and boundary-jump costs produce an actual component
row with global BV at a bounded coordinate of the original source. -/
theorem exists_elementary_component_row
    (source : BoundedSemimartingaleSource S F μ)
    (K : Nat → PredictableElementaryStrategy F) (B : Nat → NNReal)
    (hB : ∀ k ω, (K k).coefficientAbsSum ω ≤ B k)
    (Z : Nat → Process Ω) (hGain : ∀ k, ElementaryStrategy.gain S (K k).toElementary = Z k)
    {τ : Ω → NNReal} {T : NNReal} (hT : 0 < T)
    (W : ∀ k, EmeryPrelocalH1SupExactRepresentation (F := F) (mu := μ) (Z k) τ T)
    (hCost : (∑' k, prelocalH1SupWitnessCost (W k).witness) ≠ ∞)
    (hJump : (∑' k, ∫⁻ ω, ENNReal.ofReal |processLeftJump (Z k) (τ ω) ω| ∂μ) ≠ ∞) :
    ∃ A : Nat → ActualSIntegrableStrategy (realizationModel (unitSource source)),
      (∀ k, (A k).val.integrand =
        PredictableProcess.restrict (stochasticIntervalIocZero τ) (K k).integrand) ∧
      (∀ k, ProcessIndistinguishable μ
        (stoppedProcess (Z k) (fun ω => (τ ω : WithTop NNReal))) (A k).val.stochasticIntegral) ∧
      (∀ k, ProcessHasLeftLimits (A k).val.martingalePart) ∧
      (∀ k, (A k).val.martingalePart 0 = 0 ∧ (A k).val.finiteVariationPart 0 = 0) ∧
      (∀ k ω t, T ≤ t →
        (A k).val.martingalePart t ω = (A k).val.martingalePart T ω ∧
        (A k).val.finiteVariationPart t ω = (A k).val.finiteVariationPart T ω) ∧
      (∑' k, ((∫⁻ ω, ⨆ t : Icc (0 : NNReal) T,
        ENNReal.ofReal |(A k).val.centeredMartingalePart t.1 ω| ∂μ) +
        ∫⁻ ω, eVariationOn ((A k).val.finiteVariationPart · ω) (Icc 0 T) ∂μ)) ≠ ∞ := by
  let A := fun k => elementaryClosedStop source (K k) (B k) (hB k) τ
    (W k).witness.stoppingTime T hT
  have hIntegral : ∀ k, ProcessIndistinguishable μ
      (stoppedProcess (Z k) (fun ω => (τ ω : WithTop NNReal))) (A k).val.stochasticIntegral := by
    intro k
    simpa only [hGain k] using elementaryClosedStop_gain source (K k) (B k) (hB k) τ
      (W k).witness.stoppingTime T hT (W k).witness.stoppingTime_le_horizon
  refine ⟨A, fun k => elementaryClosedStop_integrand source (K k) (B k) (hB k) τ
    (W k).witness.stoppingTime T hT (W k).witness.stoppingTime_le_horizon, hIntegral,
    fun k => elementaryClosedStop_martingaleLeft source (K k) (B k) (hB k) τ
      (W k).witness.stoppingTime T hT,
    fun k => ⟨elementaryClosedStop_martingaleZero source (K k) (B k) (hB k) τ
      (W k).witness.stoppingTime T hT,
      elementaryClosedStop_finiteVariationZero source (K k) (B k) (hB k) τ
        (W k).witness.stoppingTime T hT⟩, ?_, ?_⟩
  · intro k ω t ht
    simp only [A, elementaryClosedStop, ActualLocallySIntegrableStrategy.deterministicallyStopped,
      LocallySIntegrableStrategy.deterministicallyStopped, min_eq_right ht, min_self, and_self]
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (a := (30 : ENNReal)) (by norm_num)
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (a := (32 : ENNReal)) (by norm_num) hCost, hJump⟩))
  calc
    _ ≤ ∑' k, 30 * (32 * prelocalH1SupWitnessCost (W k).witness +
        ∫⁻ ω, ENNReal.ofReal |processLeftJump (Z k) (τ ω) ω| ∂μ) := by
      apply ENNReal.tsum_le_tsum
      intro k
      have hSource := elementaryGainSource source (K k) (B k) (hB k)
      apply (A k).centered_component_cost_le_witness_of_stopped source.usualConditions _
        (hGain k ▸ hSource.stronglyAdapted) (hGain k ▸ hSource.rightContinuous)
        (hGain k ▸ hSource.hasLeftLimits) (W k) (hIntegral k)
      rw [← hGain k]
      funext ω
      simp [ElementaryStrategy.gain, ElementaryInterval.gain]
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left]

/-- Componentwise finite sums of the supplied increments are actual graphs:
their integrands and gains telescope to a directly constructed elementary
certificate. No actual addition or stopping calculus is required. -/
theorem exists_actual_telescoping_approximants
    (source : BoundedSemimartingaleSource S F μ)
    (K : Nat → PredictableElementaryStrategy F) (B : Nat → NNReal)
    (hB : ∀ k ω, (K k).coefficientAbsSum ω ≤ B k)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (T : NNReal) (hT : 0 < T) (hτT : ∀ ω, τ ω ≤ T)
    (A : Nat → ActualSIntegrableStrategy (realizationModel (unitSource source)))
    (hCoeff : ∀ k, (A k).val.integrand =
      PredictableProcess.restrict (stochasticIntervalIocZero τ)
        ((K (k + 1)).integrand - (K k).integrand))
    (hGain : ∀ k, ProcessIndistinguishable μ
      (stoppedProcess (ElementaryStrategy.gain S (K (k + 1)).toElementary -
        ElementaryStrategy.gain S (K k).toElementary) (fun ω => (τ ω : WithTop NNReal)))
      (A k).val.stochasticIntegral)
    (r : Nat) :
    ∃ P : Nat → ActualSIntegrableStrategy (realizationModel (unitSource source)),
      (P 0).val = (elementaryClosedStop source (K r) (B r) (hB r) τ hτ T hT).val ∧
      (∀ n, (P (n + 1)).val = (P n).val.add_of_rightContinuous (A (r + n)).val) ∧
      (∀ n, (P n).val.integrand =
        PredictableProcess.restrict (stochasticIntervalIocZero τ) (K (r + n)).integrand) ∧
      (∀ n, ProcessIndistinguishable μ
        (stoppedProcess (ElementaryStrategy.gain S (K (r + n)).toElementary)
          (fun ω => (τ ω : WithTop NNReal))) (P n).val.stochasticIntegral) := by
  let E := fun n => elementaryClosedStop source (K (r + n)) (B (r + n)) (hB (r + n))
    τ hτ T hT
  let R : Nat → SIntegrableStrategy (sourceData source).regularizedDecomposition :=
    Nat.rec (E 0).val (fun n p => p.add_of_rightContinuous (A (r + n)).val)
  have hRC : ∀ n, (R n).integrand =
      PredictableProcess.restrict (stochasticIntervalIocZero τ) (K (r + n)).integrand := by
    intro n
    induction n with
    | zero => exact elementaryClosedStop_integrand source _ _ _ τ hτ T hT hτT
    | succ n ih =>
      change (R n).integrand + (A (r + n)).val.integrand = _
      rw [ih, hCoeff]
      calc
        _ = PredictableProcess.restrict (stochasticIntervalIocZero τ)
            (fun t ω => (K (r + n)).integrand t ω +
              ((K (r + n + 1)).integrand t ω - (K (r + n)).integrand t ω)) :=
          (PredictableProcess.restrict_add _ _ _).symm
        _ = _ := by
          congr 1
          funext t ω
          simp only [Nat.add_succ]
          ring
  have hRG : ∀ n, ProcessIndistinguishable μ
      (stoppedProcess (ElementaryStrategy.gain S (K (r + n)).toElementary)
        (fun ω => (τ ω : WithTop NNReal))) (R n).stochasticIntegral := by
    intro n
    induction n with
    | zero => exact elementaryClosedStop_gain source _ _ _ τ hτ T hT hτT
    | succ n ih =>
      filter_upwards [ih, hGain (r + n)] with ω hω hAω
      intro t
      change _ = (R n).stochasticIntegral t ω + (A (r + n)).val.stochasticIntegral t ω
      rw [← hω t, ← hAω t]
      simp only [stoppedProcess, Pi.sub_apply, Nat.add_succ]
      ring
  let P := fun n => (E n).congr (R n)
    ((elementaryClosedStop_integrand source _ _ _ τ hτ T hT hτT).trans (hRC n).symm)
    ((elementaryClosedStop_gain source _ _ _ τ hτ T hT hτT).symm.trans (hRG n))
  exact ⟨P, rfl, fun _ => rfl, hRC, hRG⟩

end FTAPTheorem42.BoundedSourceIntegralMarket
