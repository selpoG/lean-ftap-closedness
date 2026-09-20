/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.ElementaryStrategy
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessAlgebra
import FTAPTheorem42.Stochastic.Integral.Elementary.LocalizedGoodIntegrator

/-! # Localization of elementary-test estimates

Compare stopped and unstopped errors outside the exceptional stopping event.
Finite stopping contracts the error, and uniform bounds on exhaustive
localizing coordinates pass to the original processes. -/

namespace FTAPTheorem42

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Before a closed stop, every sampled elementary-test increment agrees. -/
theorem elementaryEmeryTestError_stopped_eq_of_le
    (X Y : Process Ω) (τ : Ω → WithTop NNReal)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) (w : Ω)
    (hw : (T : WithTop NNReal) ≤ τ w) :
    elementaryEmeryTestError (stoppedProcess X τ) (stoppedProcess Y τ) J T w =
      elementaryEmeryTestError X Y J T w := by
  unfold elementaryEmeryTestError FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  congr 2
  apply iSup_congr
  intro r
  congr 1
  unfold FactorialChronologicalGrid.factorialRunningMax
  apply Finset.sup'_congr
  · rfl
  intro k hk
  simp only [ChronologicalGrid.natSample]
  have hTime : ((FactorialChronologicalGrid.stoppedGrid T r).sampledTime k : WithTop NNReal) ≤
      τ w := by
    apply le_trans _ hw
    exact_mod_cast (min_le_right
      ((FactorialChronologicalGrid.grid r).sampledTime k) T)
  rw [ElementaryStrategy.gain_stoppedProcess_eq_of_le X _ τ _ w hTime,
    ElementaryStrategy.gain_stoppedProcess_eq_of_le Y _ τ _ w hTime]

/-- Convergence on each common stopping coordinate gives global convergence.
The coordinate and row thresholds are both chosen before the test. -/
theorem ElementaryEmeryConverges.of_localizingSequence
    {X : Nat → Process Ω} {Y : Process Ω}
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    {τ : Nat → Ω → WithTop NNReal} (hτ : IsPreLocalizingSequence F τ μ)
    (hLocal : ∀ k, ElementaryEmeryConverges μ F
      (fun n => stoppedProcess (X n) (τ k)) (stoppedProcess Y (τ k))) :
    ElementaryEmeryConverges μ F X Y := by
  intro T ε hε
  have hBad : Tendsto (fun k => μ.real {w | τ k w ≤ T}) atTop (𝓝 0) := by
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal (by norm_num : (0 : ENNReal) ≠ ∞)).comp
        (FTAPTheorem42.IsPreLocalizingSequence.tendsto_measure_le hτ T)
  obtain ⟨k, hk⟩ := (hBad.eventually (gt_mem_nhds (half_pos hε))).exists
  let B : Set Ω := {w | τ k w ≤ T}
  have hB : MeasurableSet B := F.le T _ (hτ.isStoppingTime k T)
  let b : Ω → Real := B.indicator (fun _ => 1)
  have hbInt : Integrable b μ := (integrable_const (1 : Real)).indicator hB
  have hbIntegral : ∫ w, b w ∂μ = μ.real B := by
    rw [integral_indicator hB, setIntegral_const, smul_eq_mul, mul_one]
  filter_upwards [hLocal k T (ε / 2) (half_pos hε)] with n hn
  intro J
  have hStoppedInt := elementaryEmeryTestError_integrable (μ := μ)
    ((hX n).stoppedProcess (hτ.isStoppingTime k)) (hY.stoppedProcess (hτ.isStoppingTime k)) J T
  have hBound : ∀ w, elementaryEmeryTestError (X n) Y J T w ≤
      elementaryEmeryTestError (stoppedProcess (X n) (τ k)) (stoppedProcess Y (τ k)) J T w +
        b w := by
    intro w
    by_cases hw : w ∈ B
    · have hb : b w = 1 := Set.indicator_of_mem hw _
      rw [hb]
      exact (elementaryEmeryTestError_bounds (X n) Y J T w).2.trans
        (le_add_of_nonneg_left (elementaryEmeryTestError_bounds _ _ J T w).1)
    · have hb : b w = 0 := Set.indicator_of_notMem hw _
      rw [hb, add_zero, elementaryEmeryTestError_stopped_eq_of_le]
      exact (lt_of_not_ge hw).le
  have hi := integral_mono_ae (elementaryEmeryTestError_integrable (μ := μ) (hX n) hY J T)
    (hStoppedInt.add hbInt) (Eventually.of_forall hBound)
  simp only [Pi.add_apply] at hi
  rw [integral_add hStoppedInt hbInt, hbIntegral] at hi
  exact hi.trans ((add_le_add (hn J) hk.le).trans_eq (add_halves ε))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Stopping a right-continuous process contracts its capped maximal envelope
on the same test horizon; the stop need not have a deterministic bound. -/
theorem cappedEnvelope_finiteStopped_le (X : Process Ω) (τ : Ω → NNReal)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (T : NNReal) (w : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (stoppedProcess X (fun w => (τ w : WithTop NNReal))) T w ≤
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T w := by
  open FactorialChronologicalGrid in
  have hE : eFactorialRunningMaxEnvelope
      (fun t w => |stoppedProcess X (fun w => (τ w : WithTop NNReal)) t w|) T w ≤
      eFactorialRunningMaxEnvelope (fun t w => |X t w|) T w := by
    apply iSup_le
    intro r
    obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.range (r * r.factorial + 1)) Finset.nonempty_range_add_one
      (fun j => (stoppedGrid T r).natSample
        (fun t w => |stoppedProcess X (fun w => (τ w : WithTop NNReal)) t w|) j w)
    rw [show factorialRunningMax
      (fun t w => |stoppedProcess X (fun w => (τ w : WithTop NNReal)) t w|) T r w =
      (stoppedGrid T r).natSample
        (fun t w => |stoppedProcess X (fun w => (τ w : WithTop NNReal)) t w|) k w from heq]
    change ENNReal.ofReal |X (min ((stoppedGrid T r).sampledTime k) (τ w)) w| ≤ _
    apply ofReal_le_eFactorialRunningMaxEnvelope (fun t w => |X t w|) T
      (fun w t => (hRight w t).abs) w
    exact (min_le_left _ _).trans (min_le_right _ _)
  unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  apply ENNReal.toReal_mono
    (ne_top_of_le_ne_top (by finiteness) (min_le_right _ _))
  exact min_le_min hE le_rfl

/-- Uniform elementary-test convergence is preserved by a finite-valued
stopping time. The test threshold remains independent of the stop's range. -/
theorem ElementaryEmeryConverges.finiteStopped
    {X : Nat → Process Ω} {Y : Process Ω}
    (h : ElementaryEmeryConverges μ F X Y)
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hYR : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun w => (τ w : WithTop NNReal))) :
    ElementaryEmeryConverges μ F
      (fun n => stoppedProcess (X n) (fun w => (τ w : WithTop NNReal)))
      (stoppedProcess Y (fun w => (τ w : WithTop NNReal))) := by
  intro T ε hε
  filter_upwards [h T ε hε] with n hn
  intro J
  have hBound w : elementaryEmeryTestError
      (stoppedProcess (X n) (fun w => (τ w : WithTop NNReal)))
      (stoppedProcess Y (fun w => (τ w : WithTop NNReal))) J T w ≤
      elementaryEmeryTestError (X n) Y J T w := by
    unfold elementaryEmeryTestError
    rw [ElementaryStrategy.gain_finiteStoppedProcess, ElementaryStrategy.gain_finiteStoppedProcess]
    exact cappedEnvelope_finiteStopped_le
      (fun t w => ElementaryStrategy.gain (X n) J.strategy.toElementary t w -
        ElementaryStrategy.gain Y J.strategy.toElementary t w) τ
      (fun w t => (J.strategy.rightContinuous_gain _ (hXR n) w t).sub
        (J.strategy.rightContinuous_gain _ hYR w t)) T w
  exact (integral_mono_ae
    (elementaryEmeryTestError_integrable (μ := μ) ((hX n).stoppedProcess hτ)
      (hY.stoppedProcess hτ) J T)
    (elementaryEmeryTestError_integrable (hX n) hY J T)
    (Eventually.of_forall hBound)).trans (hn J)

/-- A finite stop contracts each elementary error on the same horizon. -/
theorem elementaryEmeryTestError_finiteStopped_le (X Y : Process Ω)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hYR : ∀ ω t, ContinuousWithinAt (Y · ω) (Ici t) t)
    (τ : Ω → NNReal) (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F)
    (T : NNReal) (ω : Ω) :
    elementaryEmeryTestError (stoppedProcess X (fun ω => (τ ω : WithTop NNReal)))
      (stoppedProcess Y (fun ω => (τ ω : WithTop NNReal))) J T ω ≤
        elementaryEmeryTestError X Y J T ω := by
  unfold elementaryEmeryTestError
  rw [ElementaryStrategy.gain_finiteStoppedProcess, ElementaryStrategy.gain_finiteStoppedProcess]
  exact cappedEnvelope_finiteStopped_le _ τ
    (fun ω t => (J.strategy.rightContinuous_gain X hXR ω t).sub
      (J.strategy.rightContinuous_gain Y hYR ω t)) T ω

/-- The integral contraction retains the same test and horizon. -/
theorem integral_elementaryEmeryTestError_finiteStopped_le (X Y : Process Ω)
    (hX : IsStronglyProgressive F X) (hY : IsStronglyProgressive F Y)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hYR : ∀ ω t, ContinuousWithinAt (Y · ω) (Ici t) t)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    (∫ ω, elementaryEmeryTestError (stoppedProcess X (fun ω => (τ ω : WithTop NNReal)))
      (stoppedProcess Y (fun ω => (τ ω : WithTop NNReal))) J T ω ∂μ) ≤
        ∫ ω, elementaryEmeryTestError X Y J T ω ∂μ :=
  integral_mono_ae
    (elementaryEmeryTestError_integrable (μ := μ) (hX.stoppedProcess hτ) (hY.stoppedProcess hτ) J T)
    (elementaryEmeryTestError_integrable hX hY J T)
    (Eventually.of_forall (elementaryEmeryTestError_finiteStopped_le X Y hXR hYR τ J T))

/-- A bound valid on every localizing coordinate passes to the unstopped
processes. The bound is unchanged and the horizon stays fixed. -/
theorem integral_elementaryEmeryTestError_bound_of_localizingSequence
    (X Y : Process Ω) (hX : IsStronglyProgressive F X) (hY : IsStronglyProgressive F Y)
    {τ : Nat → Ω → WithTop NNReal} (hτ : IsPreLocalizingSequence F τ μ)
    (T : NNReal) (b : Real)
    (hBound : ∀ n, ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError (stoppedProcess X (τ n))
        (stoppedProcess Y (τ n)) J T ω ∂μ) ≤ b) :
    ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError X Y J T ω ∂μ) ≤ b := by
  intro J
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hBad : Tendsto (fun k => μ.real {ω | τ k ω ≤ T}) atTop (𝓝 0) := by
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal (by norm_num : (0 : ENNReal) ≠ ∞)).comp
        (FTAPTheorem42.IsPreLocalizingSequence.tendsto_measure_le hτ T)
  obtain ⟨k, hk⟩ := (hBad.eventually (gt_mem_nhds hδ)).exists
  let B : Set Ω := {ω | τ k ω ≤ T}
  have hB : MeasurableSet B := F.le T _ (hτ.isStoppingTime k T)
  let e : Ω → Real := B.indicator (fun _ => 1)
  have heInt : Integrable e μ := (integrable_const (1 : Real)).indicator hB
  have heIntegral : ∫ ω, e ω ∂μ = μ.real B := by
    rw [integral_indicator hB, setIntegral_const, smul_eq_mul, mul_one]
  have hPoint ω : elementaryEmeryTestError X Y J T ω ≤
      elementaryEmeryTestError (stoppedProcess X (τ k)) (stoppedProcess Y (τ k)) J T ω + e ω := by
    by_cases hω : ω ∈ B
    · rw [show e ω = 1 from Set.indicator_of_mem hω _]
      exact (elementaryEmeryTestError_bounds X Y J T ω).2.trans
        (le_add_of_nonneg_left (elementaryEmeryTestError_bounds _ _ J T ω).1)
    · rw [show e ω = 0 from Set.indicator_of_notMem hω _, add_zero,
        elementaryEmeryTestError_stopped_eq_of_le X Y _ J T ω (lt_of_not_ge hω).le]
  have hInt := elementaryEmeryTestError_integrable (μ := μ)
    (hX.stoppedProcess (hτ.isStoppingTime k)) (hY.stoppedProcess (hτ.isStoppingTime k)) J T
  have hi := integral_mono_ae (elementaryEmeryTestError_integrable (μ := μ) hX hY J T)
    (hInt.add heInt) (Eventually.of_forall hPoint)
  simp only [Pi.add_apply] at hi
  rw [integral_add hInt heInt, heIntegral] at hi
  exact hi.trans (add_le_add (hBound k J) hk.le)

end FTAPTheorem42
