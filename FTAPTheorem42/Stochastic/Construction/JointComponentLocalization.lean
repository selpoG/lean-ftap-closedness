import FTAPTheorem42.Stochastic.Construction.ElementaryComponentCost
import FTAPTheorem42.Stochastic.Topology.R1.RealizedJointCostLocalization
import FTAPTheorem42.Stochastic.Memin.TelescopingSummability
import FTAPTheorem42.Stochastic.Memin.SummableComponentLimitData
import FTAPTheorem42.Stochastic.Memin.IntrinsicJointPassageLimitRealization

/-! # Original-source actual component rows under one equivalent measure -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open LocalCompletedM2A PredictableElementaryEmery
open BoundedMartingaleQuadraticEnergy.Data

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- A fixed coordinate uses the tail beginning at its horizon index. The
existing error envelope and one bounded elementary row give an L² envelope
under the already chosen measure; no integrability of the stored gain is assumed. -/
theorem stopped_representative_tail_gainBound
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (source : BoundedSemimartingaleSource S F Q)
    (H : RealizedStrategy (ℱ := F) μ S) (f : Nat → Nat)
    (η : Ω → Real) (hη : MemLp η 2 Q)
    (hDom : ∀ᵐ ω ∂Q, ∀ k,
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (elementaryGain S (H.representative (f k)) - H.gain)
        ((k + 1 : Nat) : NNReal) ω ≤ η ω)
    (r : Nat) (τ : Ω → NNReal) (hτ : ∀ ω, τ ω ≤ ((r + 1 : Nat) : NNReal)) :
    let ζ := fun ω => 2 * (H.representativeBound (f r) : Real) * max source.bound 0 + 2 * η ω
    MemLp ζ 2 Q ∧
      ∀ᵐ ω ∂Q, ∀ n t,
        |stoppedProcess (elementaryGain S (H.representative (f (r + n))))
          (fun ω => (τ ω : WithTop NNReal)) t ω| ≤ ζ ω := by
  have hConst : MemLp (fun _ : Ω =>
      2 * (H.representativeBound (f r) : Real) * max source.bound 0) 2 Q := memLp_const _
  have hTwice : MemLp (fun ω => 2 * η ω) 2 Q := hη.const_mul 2
  refine ⟨hConst.add hTwice, ?_⟩
  have hBase := (elementaryGainSource source (H.representative (f r))
    (H.representativeBound (f r)) (H.representative_coefficientAbsSum_le (f r))).uniformBound
  filter_upwards [hDom, hBase] with ω hω hBaseω
  have hErr : ∀ k t, t ≤ ((k + 1 : Nat) : NNReal) →
      |elementaryGain S (H.representative (f k)) t ω - H.gain t ω| ≤ η ω := by
    intro k t ht
    exact (FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
      (fun w s => (PredictableElementaryStrategy.rightContinuous_gain S source.rightContinuous
        (H.representative (f k)) w s).sub (H.gain_rightContinuous w s))
      ((ElementaryStrategy.gain_hasLeftLimits S source.hasLeftLimits
        (H.representative (f k)).toElementary).sub H.gain_hasLeftLimits)
      _ t ht).trans (hω k)
  intro n t
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have ht := (min_le_right t (τ ω)).trans (hτ ω)
  have ht' : min t (τ ω) ≤ ((r + n + 1 : Nat) : NNReal) :=
    ht.trans (by exact_mod_cast (Nat.le_add_right r n |> Nat.succ_le_succ))
  have h0 := hErr r _ ht
  have hn := hErr (r + n) _ ht'
  have hb := hBaseω (min t (τ ω))
  change |elementaryGain S (H.representative (f r)) (min t (τ ω)) ω| ≤
    2 * (H.representativeBound (f r) : Real) * max source.bound 0 at hb
  have htri := abs_add_le
    (elementaryGain S (H.representative (f (r + n))) (min t (τ ω)) ω - H.gain (min t (τ ω)) ω)
    (H.gain (min t (τ ω)) ω - elementaryGain S (H.representative (f r)) (min t (τ ω)) ω)
  rw [abs_sub_comm (H.gain _ ω)] at htri
  have hlast := abs_add_le
    (elementaryGain S (H.representative (f (r + n))) (min t (τ ω)) ω -
      elementaryGain S (H.representative (f r)) (min t (τ ω)) ω)
    (elementaryGain S (H.representative (f r)) (min t (τ ω)) ω)
  simp only [sub_add_sub_cancel] at htri
  simp only [sub_add_cancel] at hlast
  linarith

/-- Summable growing-horizon errors give simultaneous all-time convergence
on one full-measure set, which can be evaluated at a random stopping time. -/
theorem ae_representative_tendsto_of_error_sum
    (source : BoundedSemimartingaleSource S F μ)
    (H : RealizedStrategy (ℱ := F) μ S) (f : Nat → Nat)
    (hSum : (∑' k, ∫⁻ ω, ENNReal.ofReal
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (elementaryGain S (H.representative (f k)) - H.gain)
        ((k + 1 : Nat) : NNReal) ω) ∂μ) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ t, Tendsto (fun k => elementaryGain S (H.representative (f k)) t ω)
      atTop (𝓝 (H.gain t ω)) := by
  let e := fun k => FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
    (elementaryGain S (H.representative (f k)) - H.gain) ((k + 1 : Nat) : NNReal)
  have hMeas : ∀ k, Measurable (e k) := fun k =>
    ((FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      ((PredictableElementaryStrategy.stronglyAdapted_gain S
        (StronglyAdapted.isStronglyProgressive_of_rightContinuous
          source.stronglyAdapted source.rightContinuous)
        (H.representative (f k))).sub H.gain_stronglyAdapted) _).mono (F.le _)).measurable
  filter_upwards [ae_summable_of_summable_envelope_integrals e hMeas
    (fun _ _ => Real.sqrt_nonneg _) hSum] with ω hω
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    hω.tendsto_atTop_zero
  filter_upwards [eventually_ge_atTop (Nat.ceil t)] with k hk
  rw [Real.norm_eq_abs]
  exact FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
    (fun w s => (PredictableElementaryStrategy.rightContinuous_gain S source.rightContinuous
      (H.representative (f k)) w s).sub (H.gain_rightContinuous w s))
    ((ElementaryStrategy.gain_hasLeftLimits S source.hasLeftLimits
      (H.representative (f k)).toElementary).sub H.gain_hasLeftLimits)
    _ t ((Nat.le_ceil t).trans (by exact_mod_cast hk.trans (Nat.le_succ k)))

/-- The original bounded source and a realized elementary representative
sequence produce actual closed-stop difference graphs and summable component
costs under the same measure, subsequence, and exhaustive stopping family.
The envelope used in the measure choice is retained. No actual certificate,
raw calculus, or component convergence is supplied as an input. -/
theorem exists_joint_actual_component_localization
    (source : BoundedSemimartingaleSource S F μ)
    (H : RealizedStrategy (ℱ := F) μ S) :
    ∃ (f : Nat → Nat) (Q : Measure Ω), ∃ hQ : IsProbabilityMeasure Q, letI := hQ
    ∃ (sourceQ : BoundedSemimartingaleSource S F Q) (τ : Nat → Ω → NNReal),
      StrictMono f ∧ Q ≪ μ ∧ μ ≪ Q ∧
      IsLocalizingSequence F (fun r ω => (τ r ω : WithTop NNReal)) Q ∧
      (∀ r ω, τ r ω ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∃ η : Ω → Real, Measurable η ∧ (∀ ω, 0 ≤ η ω) ∧
      Q = CommonEnvelopeMeasure.tilted μ η ∧
      Q ≤ (CommonEnvelopeMeasure.normalizer μ η)⁻¹ • μ ∧ MemLp η 2 Q ∧
      (∀ ξ : Ω → Real, MemLp ξ 2 μ → MemLp (fun ω => ξ ω + η ω) 2 Q) ∧
      (∀ᵐ ω ∂Q, ∀ k,
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (elementaryGain S (H.representative (f k)) - H.gain)
          ((k + 1 : Nat) : NNReal) ω ≤ η ω) ∧
      (∀ r,
        let ζ := fun ω => 2 * (H.representativeBound (f r) : Real) * max sourceQ.bound 0 + 2 * η ω
        MemLp ζ 2 Q ∧ ∀ᵐ ω ∂Q, ∀ n t,
          |stoppedProcess (elementaryGain S (H.representative (f (r + n))))
            (fun ω => (τ r ω : WithTop NNReal)) t ω| ≤ ζ ω) ∧
      ∀ r, ∃ A : Nat → ActualSIntegrableStrategy (realizationModel (unitSource sourceQ)),
        (∀ k, (A k).val.integrand = PredictableProcess.restrict (stochasticIntervalIocZero (τ r))
          ((H.representative (f (k + 1))).integrand - (H.representative (f k)).integrand)) ∧
        (∀ k, ProcessIndistinguishable Q
          (stoppedProcess (elementaryGain S (H.representative (f (k + 1))) -
            elementaryGain S (H.representative (f k))) (fun ω => (τ r ω : WithTop NNReal)))
          (A k).val.stochasticIntegral) ∧
        (∀ k, ProcessHasLeftLimits (A k).val.martingalePart) ∧
        (∀ k, (A k).val.martingalePart 0 = 0 ∧ (A k).val.finiteVariationPart 0 = 0) ∧
        (∀ k ω t, ((r + 1 : Nat) : NNReal) ≤ t →
          (A k).val.martingalePart t ω = (A k).val.martingalePart ((r + 1 : Nat) : NNReal) ω ∧
          (A k).val.finiteVariationPart t ω =
            (A k).val.finiteVariationPart ((r + 1 : Nat) : NNReal) ω) ∧
        (∑' k, ((∫⁻ ω, ⨆ t : Icc (0 : NNReal) ((r + 1 : Nat) : NNReal),
          ENNReal.ofReal |(A k).val.centeredMartingalePart t.1 ω| ∂Q) +
          ∫⁻ ω, eVariationOn ((A k).val.finiteVariationPart · ω)
            (Icc 0 ((r + 1 : Nat) : NNReal)) ∂Q)) ≠ ∞ ∧
        (∃ P : Nat → ActualSIntegrableStrategy (realizationModel (unitSource sourceQ)),
          (P 0).val.martingalePart 0 = 0 ∧ (P 0).val.finiteVariationPart 0 = 0 ∧
          ProcessHasLeftLimits (P 0).val.martingalePart ∧
          (∀ n, (P (n + 1)).val = (P n).val.add_of_rightContinuous (A (r + n)).val) ∧
          (∀ n, (P n).val.integrand = PredictableProcess.restrict (stochasticIntervalIocZero (τ r))
            (H.representative (f (r + n))).integrand) ∧
          (∀ n, ProcessIndistinguishable Q
            (stoppedProcess (elementaryGain S (H.representative (f (r + n))))
              (fun ω => (τ r ω : WithTop NNReal))) (P n).val.stochasticIntegral) ∧
          (∀ᵐ ω ∂Q, ∀ n t, |(P n).val.stochasticIntegral t ω| ≤
            2 * (H.representativeBound (f r) : Real) * max sourceQ.bound 0 + 2 * η ω) ∧
          ∃ M V : Process Ω,
            StronglyAdapted F M ∧ LocalMartingale M F Q ∧ IsStronglyPredictable F V ∧
            (∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t) ∧ ProcessHasLeftLimits M ∧
            (∀ ω t, ContinuousWithinAt (V · ω) (Ici t) t) ∧
            (∀ ω, BoundedVariationOn (V · ω) univ) ∧ M 0 =ᵐ[Q] 0 ∧ V 0 =ᵐ[Q] 0 ∧
            ProcessIndistinguishable Q (fun t ω => M t ω + V t ω)
              (stoppedProcess H.gain (fun ω => (τ r ω : WithTop NNReal))) ∧
            (∀ᵐ ω ∂Q,
              TendstoUniformly (fun n t => (P n).val.martingalePart t ω) (M · ω) atTop ∧
              TendstoUniformly (fun n t => (P n).val.finiteVariationPart t ω) (V · ω) atTop ∧
              Tendsto (fun n => eVariationOn
                (fun t => V t ω - (P n).val.finiteVariationPart t ω) univ) atTop (𝓝 0) ∧
              ∀ t, Tendsto (fun n => (P n).val.stochasticIntegral t ω)
                atTop (𝓝 (M t ω + V t ω))) ∧
            ∃ data : MeminSummableComponentLimitData (realizationModel (unitSource sourceQ)),
              data.approximant = P ∧ data.martingaleLimit = M ∧ data.finiteVariationLimit = V) ∧
        let M := fun k => (A k).val.centeredMartingalePart
        let V := fun k t ω =>
          (A k).val.finiteVariationPart t ω - (A k).val.finiteVariationPart 0 ω
        Martingale (fun t ω => ∑' k, M k t ω) F Q ∧
          IsStronglyPredictable F (fun t ω => ∑' k, V k t ω) ∧
          ∀ᵐ ω ∂Q,
            TendstoUniformly (fun n t => ∑ k ∈ Finset.range n, M k t ω)
              (fun t => ∑' k, M k t ω) atTop ∧
            BoundedVariationOn (fun t => ∑' k, V k t ω) univ ∧
            TendstoUniformly (fun n t => ∑ k ∈ Finset.range n, V k t ω)
              (fun t => ∑' k, V k t ω) atTop ∧
            Tendsto (fun n => eVariationOn
              (fun t => (∑' k, V k t ω) - ∑ k ∈ Finset.range n, V k t ω) univ)
              atTop (𝓝 0) := by
  let B : NNReal := ⟨max source.bound 0, le_max_right _ _⟩
  have hB : ∀ᵐ ω ∂μ, ∀ t, |S t ω| ≤ B :=
    source.uniformBound.mono fun _ h t => (h t).trans (le_max_left _ _)
  obtain ⟨f, Q, HQ, τ, hf, hQ, hQμ, hμQ, _, _, hRep, hGain, hLoc, hτT,
    η, hηMeas, hηPos, hTilt, hDensity, hηL2, hSumL2, hDom, hError, hRows⟩ :=
    H.exists_joint_prelocal_jump_localization source.usualConditions
      (StronglyAdapted.isStronglyProgressive_of_rightContinuous
        source.stronglyAdapted source.rightContinuous)
      source.rightContinuous source.hasLeftLimits source.isSemimartingale B hB
  let : IsProbabilityMeasure Q := hQ
  let sourceQ := source.ofMutuallyAbsolutelyContinuous hμQ hQμ
  have hDomOriginal : ∀ᵐ ω ∂Q, ∀ k,
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (elementaryGain S (H.representative (f k)) - H.gain)
        ((k + 1 : Nat) : NNReal) ω ≤ η ω := by
    simpa only [hRep, hGain] using hDom
  refine ⟨f, Q, hQ, sourceQ, τ, hf, hQμ, hμQ, hLoc, hτT,
    η, hηMeas, hηPos, hTilt, hDensity, hηL2, hSumL2, hDomOriginal,
    fun r => stopped_representative_tail_gainBound sourceQ H f η hηL2 hDomOriginal r
      (τ r) (hτT r), fun r => ?_⟩
  obtain ⟨W, _, hCost, hJump, _, _⟩ := hRows r
  let K := fun k => elementaryDifference
    (HQ.representative (f (k + 1))) (HQ.representative (f k))
  let C := fun k => HQ.representativeBound (f (k + 1)) + HQ.representativeBound (f k)
  have hC : ∀ k ω, (K k).coefficientAbsSum ω ≤ C k := fun k =>
    elementaryDifference_coefficientAbsSum_le _ _ _ _
      (HQ.representative_coefficientAbsSum_le _) (HQ.representative_coefficientAbsSum_le _)
  have hKG : ∀ k, ElementaryStrategy.gain S (K k).toElementary =
      elementaryGain S (HQ.representative (f (k + 1))) -
        elementaryGain S (HQ.representative (f k)) := by
    intro k
    funext t
    exact elementaryDifference_gain _ _ S t
  obtain ⟨A, hCoeff, hActual, hLeft, hZero, hConst, hFinite⟩ :=
    exists_elementary_component_row sourceQ K C hC
    _ hKG (by positivity : (0 : NNReal) < ((r + 1 : Nat) : NNReal)) W hCost hJump
  have hCoeffOriginal : ∀ k, (A k).val.integrand =
      PredictableProcess.restrict (stochasticIntervalIocZero (τ r))
        ((H.representative (f (k + 1))).integrand - (H.representative (f k)).integrand) := by
    intro k
    simpa only [K, elementaryDifference_integrand, hRep] using hCoeff k
  have hActualOriginal : ∀ k, ProcessIndistinguishable Q
      (stoppedProcess (elementaryGain S (H.representative (f (k + 1))) -
        elementaryGain S (H.representative (f k))) (fun ω => (τ r ω : WithTop NNReal)))
      (A k).val.stochasticIntegral := by
    simpa only [hRep] using hActual
  refine ⟨A, hCoeffOriginal, hActualOriginal, hLeft, hZero, hConst, hFinite, ?_,
    ActualSIntegrableStrategy.component_series_of_summable_stopped_cost A _ hLeft hConst hFinite⟩
  obtain ⟨P, hP0, hPSucc, hPCoeff, hPGain⟩ := exists_actual_telescoping_approximants sourceQ
    (fun k => H.representative (f k)) (fun k => H.representativeBound (f k))
    (fun k => H.representative_coefficientAbsSum_le (f k))
    (τ r) (W 0).witness.stoppingTime _ (by positivity) (hτT r)
    A hCoeffOriginal hActualOriginal r
  have hPM0 : (P 0).val.martingalePart 0 = 0 := by
    rw [hP0]
    exact elementaryClosedStop_martingaleZero _ _ _ _ _ _ _ _
  have hPV0 : (P 0).val.finiteVariationPart 0 = 0 := by
    rw [hP0]
    exact elementaryClosedStop_finiteVariationZero _ _ _ _ _ _ _ _
  have hPMLeft : ProcessHasLeftLimits (P 0).val.martingalePart := by
    rw [hP0]
    exact elementaryClosedStop_martingaleLeft _ _ _ _ _ _ _ _
  refine ⟨P, hPM0, hPV0, hPMLeft, hPSucc, hPCoeff, hPGain, ?_, ?_⟩
  · have hBound := (stopped_representative_tail_gainBound sourceQ H f η hηL2
      hDomOriginal r (τ r) (hτT r)).2
    filter_upwards [hBound, ae_all_iff.mpr hPGain] with ω hω hPω
    intro n t
    rw [← hPω n t]
    exact hω n t
  · obtain ⟨M, V, hMA, hMLocal, hVP, hMR, hMLeft, hVR, hVBV, hM0, hV0, hCon⟩ :=
      ActualSIntegrableStrategy.exists_regular_telescoping_component_limit
        sourceQ.usualConditions (fun n => A (r + n)) P ((r + 1 : Nat) : NNReal)
        (fun n => hLeft (r + n)) (fun n => hConst (r + n))
        (ne_top_of_le_ne_top hFinite
          (ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective r) (fun k =>
            (∫⁻ ω, ⨆ t : Icc (0 : NNReal) ((r + 1 : Nat) : NNReal),
              ENNReal.ofReal |(A k).val.centeredMartingalePart t.1 ω| ∂Q) +
            ∫⁻ ω, eVariationOn ((A k).val.finiteVariationPart · ω)
              (Icc 0 ((r + 1 : Nat) : NNReal)) ∂Q)))
        (fun n => hZero (r + n)) hPSucc hPMLeft ⟨hPM0, hPV0⟩
    refine ⟨M, V, hMA, hMLocal, hVP, hMR, hMLeft, hVR, hVBV, hM0, hV0, ?_, hCon, ?_⟩
    · have hOriginal := ae_representative_tendsto_of_error_sum sourceQ HQ f
        (ne_top_of_le_ne_top (by norm_num) hError)
      filter_upwards [hCon, hOriginal, ae_all_iff.mpr hPGain] with ω hCω hOω hPω
      intro t
      have hStop : Tendsto
          (fun n => stoppedProcess (elementaryGain S (H.representative (f (r + n))))
            (fun ω => (τ r ω : WithTop NNReal)) t ω) atTop
          (𝓝 (stoppedProcess H.gain (fun ω => (τ r ω : WithTop NNReal)) t ω)) := by
        simpa only [hRep, hGain, Function.comp_def, Nat.add_comm, stoppedProcess, ← WithTop.coe_min,
          WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] using
          (hOω (min t (τ r ω))).comp (tendsto_add_atTop_nat r)
      exact tendsto_nhds_unique (hCω.2.2.2 t)
        (hStop.congr' (Eventually.of_forall fun n => hPω n t))
    · have hPLeftAll : ∀ n, ProcessHasLeftLimits (P n).val.martingalePart := by
        intro n
        induction n with
        | zero => exact hPMLeft
        | succ n ih =>
          rw [hPSucc]
          exact ih.add (hLeft (r + n))
      have hPZeroAll : ∀ n, (P n).val.martingalePart 0 = 0 ∧
          (P n).val.finiteVariationPart 0 = 0 := by
        intro n
        induction n with
        | zero => exact ⟨hPM0, hPV0⟩
        | succ n ih =>
          rw [hPSucc]
          change (P n).val.martingalePart 0 + (A (r + n)).val.martingalePart 0 = 0 ∧
            (P n).val.finiteVariationPart 0 + (A (r + n)).val.finiteVariationPart 0 = 0
          rw [ih.1, ih.2, (hZero (r + n)).1, (hZero (r + n)).2]
          simp
      have hTail := ne_top_of_le_ne_top hFinite
        (ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective r) _)
      let data : MeminSummableComponentLimitData (realizationModel (unitSource sourceQ)) := {
        approximant := P
        martingaleLimit := M
        finiteVariationLimit := V
        martingaleLimit_stronglyAdapted := hMA
        martingaleLimit_localMartingale := hMLocal
        finiteVariationLimit_isStronglyPredictable := hVP
        martingaleLimit_rightContinuous := hMR
        finiteVariationLimit_rightContinuous := hVR
        finiteVariationLimit_boundedVariation := hVBV
        finiteVariationLimit_zero := hV0
        gainEnvelope := fun ω =>
          2 * (H.representativeBound (f r) : Real) * max sourceQ.bound 0 + 2 * η ω
        gainEnvelope_memLp := (stopped_representative_tail_gainBound sourceQ H f η hηL2
          hDomOriginal r (τ r) (hτT r)).1
        approximant_martingaleLeft := hPLeftAll
        approximant_martingaleZero := fun n => Eventually.of_forall (congrFun (hPZeroAll n).1)
        approximant_finiteVariationZero := fun n =>
          Eventually.of_forall (congrFun (hPZeroAll n).2)
        approximant_gainBound := fun n => by
          filter_upwards [(stopped_representative_tail_gainBound sourceQ H f η hηL2
            hDomOriginal r (τ r) (hτT r)).2, hPGain n] with ω hBω hGω
          intro t
          rw [← hGω t]
          exact hBω n t
        variationSummable :=
          ActualSIntegrableStrategy.variation_summable_of_telescoping_stopped_cost
          (fun n => A (r + n)) P _ (fun n ω t ht => (hConst (r + n) ω t ht).2)
          (ne_top_of_le_ne_top hTail (ENNReal.tsum_le_tsum fun _ => le_add_left le_rfl)) hPSucc
        martingaleEnvelopeSummable :=
          ActualSIntegrableStrategy.martingaleEnvelope_summable_of_telescoping_stopped_cost
            (fun n => A (r + n)) P _ (fun n => hLeft (r + n))
            (fun n => (hZero (r + n)).1) (fun n ω t ht => (hConst (r + n) ω t ht).1)
            (ne_top_of_le_ne_top hTail (ENNReal.tsum_le_tsum fun _ => le_add_right le_rfl)) hPSucc
        martingaleTendsto := hCon.mono fun _ hω t => hω.1.tendsto_at t
        finiteVariationTendsto := hCon.mono fun _ hω t => hω.2.1.tendsto_at t
        gainTendsto := hCon.mono fun _ hω => hω.2.2.2
        martingaleTendstoUniformly := hCon.mono fun _ hω => hω.1
        finiteVariationTendstoUniformly := hCon.mono fun _ hω => hω.2.1
        finiteVariationVariationTendsto := hCon.mono fun _ hω => hω.2.2.1 }
      exact ⟨data, rfl, rfl, rfl⟩

/-- The stopped Mémín component record and its stored-gain identification
are generated from the original source and representative market alone. -/
theorem exists_stopped_meminComponentData
    (source : BoundedSemimartingaleSource S F μ)
    (H : RealizedStrategy (ℱ := F) μ S) :
    ∃ (f : Nat → Nat) (Q : Measure Ω), ∃ hQ : IsProbabilityMeasure Q, letI := hQ
    ∃ (sourceQ : BoundedSemimartingaleSource S F Q) (τ : Nat → Ω → NNReal)
      (data : Nat → MeminSummableComponentLimitData (realizationModel (unitSource sourceQ))),
      StrictMono f ∧ Q ≪ μ ∧ μ ≪ Q ∧
      IsLocalizingSequence F (fun r ω => (τ r ω : WithTop NNReal)) Q ∧
      (∀ r ω, τ r ω ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ r,
        ProcessIndistinguishable Q
          (fun t ω => (data r).martingaleLimit t ω + (data r).finiteVariationLimit t ω)
          (stoppedProcess H.gain (fun ω => (τ r ω : WithTop NNReal))) ∧
        (∀ n, ((data r).approximant n).val.integrand =
          PredictableProcess.restrict (stochasticIntervalIocZero (τ r))
            (H.representative (f (r + n))).integrand) ∧
        (∀ n, ProcessIndistinguishable Q
          (stoppedProcess (elementaryGain S (H.representative (f (r + n))))
            (fun ω => (τ r ω : WithTop NNReal)))
          ((data r).approximant n).val.stochasticIntegral) := by
  obtain ⟨f, Q, hQ, sourceQ, τ, hf, hQμ, hμQ, hLoc, hτT,
    η, _, _, _, _, _, _, _, _, hRows⟩ := exists_joint_actual_component_localization source H
  let : IsProbabilityMeasure Q := hQ
  have hData : ∀ r, ∃ data : MeminSummableComponentLimitData
      (realizationModel (unitSource sourceQ)),
      ProcessIndistinguishable Q
        (fun t ω => data.martingaleLimit t ω + data.finiteVariationLimit t ω)
        (stoppedProcess H.gain (fun ω => (τ r ω : WithTop NNReal))) ∧
      (∀ n, (data.approximant n).val.integrand =
        PredictableProcess.restrict (stochasticIntervalIocZero (τ r))
          (H.representative (f (r + n))).integrand) ∧
      (∀ n, ProcessIndistinguishable Q
        (stoppedProcess (elementaryGain S (H.representative (f (r + n))))
          (fun ω => (τ r ω : WithTop NNReal))) (data.approximant n).val.stochasticIntegral) := by
    intro r
    obtain ⟨A, _, _, _, _, _, _, hApprox, _⟩ := hRows r
    obtain ⟨P, _, _, _, _, hPCoeff, hPGain, _, hLimit⟩ := hApprox
    obtain ⟨M, V, _, _, _, _, _, _, _, _, _, hEq, _, data, hP, hM, hV⟩ := hLimit
    refine ⟨data, ?_, ?_, ?_⟩
    · simpa only [hM, hV] using hEq
    · simpa only [hP] using hPCoeff
    · simpa only [hP] using hPGain
  choose data hData using hData
  exact ⟨f, Q, hQ, sourceQ, τ, data, hf, hQμ, hμQ, hLoc, hτT, hData⟩

/-- On the same equivalent measure and exhaustive bounded stopping schedule,
the original representative gain is realized at every stopped stage by an
actual strategy of the original source. No stopping calculus is assumed. -/
theorem exists_stopped_actualRealization
    (source : BoundedSemimartingaleSource S F μ)
    (H : RealizedStrategy (ℱ := F) μ S) :
    ∃ (Q : Measure Ω), ∃ hQ : IsProbabilityMeasure Q, letI := hQ
    ∃ (sourceQ : BoundedSemimartingaleSource S F Q) (τ : Nat → Ω → NNReal)
      (V : Nat → ActualSIntegrableStrategy (realizationModel (unitSource sourceQ))),
      Q ≪ μ ∧ μ ≪ Q ∧
      IsLocalizingSequence F (fun r ω => (τ r ω : WithTop NNReal)) Q ∧
      (∀ r ω, τ r ω ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ r, ProcessIndistinguishable Q (V r).val.stochasticIntegral
        (stoppedProcess H.gain (fun ω => (τ r ω : WithTop NNReal))) := by
  obtain ⟨f, Q, hQ, sourceQ, τ, data, _hf, hQμ, hμQ, hLoc, hτT, hData⟩ :=
    exists_stopped_meminComponentData source H
  let : IsProbabilityMeasure Q := hQ
  let _ := sourceQ.usualConditions.rightContinuous
  have hRealized : ∀ r, ∃ V : ActualSIntegrableStrategy
      (realizationModel (unitSource sourceQ)),
      ProcessIndistinguishable Q V.val.stochasticIntegral
        (stoppedProcess H.gain (fun ω => (τ r ω : WithTop NNReal))) := by
    intro r
    obtain ⟨w, cutoff, _hCutoff, hRealized⟩ :=
      exists_intrinsicJointPassageLimitStrategyCandidate_isRealized_intrinsic
        (schedule sourceQ) (unitSource_integrand sourceQ) (unitSource_zero sourceQ) (data r)
    refine ⟨⟨intrinsicJointPassageLimitStrategyCandidate (data r) w cutoff, hRealized⟩, ?_⟩
    exact (hData r).1
  choose V hV using hRealized
  exact ⟨Q, hQ, sourceQ, τ, V, hQμ, hμQ, hLoc, hτT, hV⟩

end FTAPTheorem42.BoundedSourceIntegralMarket
