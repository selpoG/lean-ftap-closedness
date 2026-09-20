import FTAPTheorem42.Foundations.Passage
import FTAPTheorem42.Stochastic.DS.Lemma410.StoppedPrefixMartingale
import FTAPTheorem42.Stochastic.DS.Lemma48.TailHorizon

/-! # Finite passage prefixes of locally integrable components

The local component is first stopped at the finite horizon. The concrete
process stopping construction then supplies the existing prefix estimate.
The result refers to the original component and its own passage time.
-/

open Filter MeasureTheory Set
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem absolutePassagePrefix_deterministicallyStopped (M : Process Ω) (c : Real) (T : NNReal) :
    absolutePassagePrefix (fun t ω => M (min t T) ω) c T = absolutePassagePrefix M c T := by
  have hHit : (fun ω => min
      (absoluteStrictHittingAfter (fun t ω => M (min t T) ω) c ω) (T : WithTop NNReal)) =
      (fun ω => min (absoluteStrictHittingAfter M c ω) (T : WithTop NNReal)) := by
    funext ω
    exact min_absoluteStrictHittingAfter_deterministicallyStopped M c T ω
  have hStop : (fun t ω => M (min t T) ω) =
      stoppedProcess M (fun _ => (T : WithTop NNReal)) := by
    funext t ω
    simp only [stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  unfold absolutePassagePrefix
  rw [hHit, hStop, stoppedProcess_stoppedProcess']
  simp only [min_assoc, min_self]

namespace LocallySIntegrableStrategy

open SIntegrableProcessStoppingCalculus

variable {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [F.IsRightContinuous] {D : SpecialSemimartingaleDecomposition S F μ}

/-- The finite prefix of a local component is a true L² martingale, with the
same uniform bound as in Lemma 4.10. No global variation certificate is assumed. -/
theorem absolutePassagePrefix_martingale_l2
    (G : LocallySIntegrableStrategy D) (hUsual : Filtration.UsualConditions μ F)
    (hML : ProcessHasLeftLimits G.martingalePart) (hZero : G.martingalePart 0 =ᵐ[μ] 0)
    (q : Ω → Real) (hq : MemLp q 2 μ)
    (hBound : ∀ᵐ ω ∂μ, ∀ t, |G.stochasticIntegral t ω| ≤ q ω)
    (c : Real) (hc : 0 ≤ c) (T : NNReal) (hT : 0 < T) :
    Martingale (absolutePassagePrefix G.martingalePart c T) F μ ∧
      MemLp (absolutePassagePrefix G.martingalePart c T T) 2 μ ∧
      eLpNorm (absolutePassagePrefix G.martingalePart c T T) 2 μ ≤
        ENNReal.ofReal c + 6 * eLpNorm q 2 μ := by
  let H := G.deterministicallyStopped T hT
  let C := SIntegrableStrategy.processStoppingCalculus D
  have hMStop : H.martingalePart = stoppedProcess G.martingalePart
      (fun _ => (T : WithTop NNReal)) := by
    funext t ω
    simp only [H, deterministicallyStopped, stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hHL : ProcessHasLeftLimits H.martingalePart := by
    rw [hMStop]
    exact hML.stoppedProcess _
  have hHZero : H.martingalePart 0 =ᵐ[μ] 0 := by
    rw [hMStop]
    filter_upwards [hZero] with ω hω
    rw [stoppedProcess_eq_of_le bot_le]
    exact hω
  have hHB : ∀ᵐ ω ∂μ, ∀ t, |H.stochasticIntegral t ω| ≤ q ω := by
    filter_upwards [hBound] with ω hω
    exact fun t => hω (min t T)
  have hResult := C.lemma410StoppedPrefixStrategy_martingale_l2_of_strategy
    hUsual H hHL hHZero q hq hHB c hc hT
  have hR : (C.lemma410StoppedPrefixStrategy H c T).martingalePart =
      absolutePassagePrefix G.martingalePart c T := by
    change absolutePassagePrefix (fun t ω => G.martingalePart (min t T) ω) c T = _
    exact absolutePassagePrefix_deterministicallyStopped G.martingalePart c T
  change Martingale _ F μ ∧ MemLp _ 2 μ ∧ eLpNorm _ 2 μ ≤ _ at hResult
  rwa [hR] at hResult

end LocallySIntegrableStrategy

end FTAPTheorem42
