/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ValueTruncationL1Limit
import FTAPTheorem42.Stochastic.Martingale.Regularization.TerminalL1MartingaleProcessCompletion

/-!
# Càdlàg process limit of value-truncated projections

The terminal `L¹` residual certificate is consumed here by the existing
terminal-`L¹` martingale completion theorem.  It supplies a strict cutoff and
a right-continuous true martingale whose selected residual paths converge
uniformly almost everywhere.  The adapted càdlàg candidate is the difference
between the original increasing source and that residual martingale.

No predictability assertion is made for the candidate.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-- A process-level certificate obtained from the terminal `L¹` value-truncation
residual limit.  The candidate `Pcad` is adapted and càdlàg; predictability is
deliberately not included. -/
structure ValueTruncationProjectionCadlagLimit
    {U : Process Ω} {T : NNReal}
    (family : ValueTruncationProjectionFamily
      (F := F) (mu := mu) U T)
    (terminal : ValueTruncationProjectionTerminalL1Limit
      (F := F) (mu := mu) family) where
  cutoff : ℕ → ℕ
  cutoff_strictMono : StrictMono cutoff
  M : Process Ω
  M_stronglyAdapted : StronglyAdapted F M
  M_martingale : Martingale M F mu
  M_rightContinuous : ∀ omega t,
    ContinuousWithinAt (M · omega) (Ici t) t
  M_leftLimits : ProcessHasLeftLimits M
  M_constant_after : ∀ t, T ≤ t → M t =ᵐ[mu] M T
  M_terminal_ae_eq_residual : M T =ᵐ[mu]
    (fun omega => U T omega - terminal.limit omega)
  residual_uniform_ae : ∀ᵐ omega ∂mu, TendstoUniformly
    (fun n t => valueTruncation U (cutoff n) t omega -
      (family.data (cutoff n)).Vp t omega)
    (fun t => M t omega) atTop
  Pcad : Process Ω
  Pcad_definition : Pcad = fun t omega => U t omega - M t omega
  projection_uniform_ae : ∀ᵐ omega ∂mu, TendstoUniformly
    (fun n t => (family.data (cutoff n)).Vp t omega)
    (fun t => Pcad t omega) atTop
  Pcad_stronglyAdapted : StronglyAdapted F Pcad
  Pcad_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Pcad · omega) (Ici t) t
  Pcad_leftLimits : ProcessHasLeftLimits Pcad
  Pcad_zero_ae : Pcad 0 =ᵐ[mu] 0
  Pcad_constant_after : ∀ t, T ≤ t → Pcad t =ᵐ[mu] Pcad T
  Pcad_terminal_ae_eq_limit : Pcad T =ᵐ[mu] terminal.limit

omit [SigmaFiniteFiltration mu F] in
theorem ValueTruncationProjectionFamily.exists_cadlagLimit
    [F.IsRightContinuous]
    {U : Process Ω} {T : NNReal}
    (family : ValueTruncationProjectionFamily
      (F := F) (mu := mu) U T)
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (hUsual : Filtration.UsualConditions mu F)
    (terminal : ValueTruncationProjectionTerminalL1Limit
      (F := F) (mu := mu) family) :
    Nonempty (ValueTruncationProjectionCadlagLimit
      (F := F) (mu := mu) family terminal) := by
  let R : ℕ → Process Ω := fun n => fun t omega =>
    valueTruncation U n t omega - (family.data n).Vp t omega
  have hRMartingale : ∀ n, Martingale (R n) F mu := by
    intro n
    simpa [R] using (family.data n).projection.residual_martingale
  have hRRight : ∀ n omega t,
      ContinuousWithinAt (R n · omega) (Ici t) t := by
    intro n omega t
    dsimp [R]
    exact (hU.valueTruncation_rightContinuous n omega t).sub
      ((family.data n).projection.projection_ready.predictable_version.Vp_rightContinuous
        omega t)
  have hRLeft : ∀ n omega t, Tendsto
      (fun s => R n s omega) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun s => R n s omega) t)) := by
    intro n omega t
    dsimp [R]
    have hsub := (hU.valueTruncation_hasLeftLimits n omega t).sub
      ((family.data n).projection.projection_ready.predictable_version.Vp_leftLimits
        omega t)
    exact tendsto_leftLim_of_tendsto ⟨_, hsub⟩
  have hRConstant : ∀ n t, T ≤ t → R n t = R n T := by
    intro n t ht
    funext omega
    dsimp [R]
    rw [hU.valueTruncation_constant_after n omega t ht,
      (family.data n).projection.projection_ready.predictable_version.Vp_constant_after
        omega t ht]
  have hRTerminalIntegrable : ∀ n, Integrable (R n T) mu := by
    intro n
    simpa [R] using terminal.residual_terminal_integrable n
  have hRTerminal : ∀ n, MemLp (R n T) 1 mu := by
    intro n
    exact memLp_one_iff_integrable.mpr (hRTerminalIntegrable n)
  let residualLimit : Ω → Real := fun omega => U T omega - terminal.limit omega
  have hResidualLimitIntegrable : Integrable residualLimit mu := by
    simpa [residualLimit] using terminal.residual_terminal_limit_integrable
  have hResidualLimit : MemLp residualLimit 1 mu :=
    memLp_one_iff_integrable.mpr hResidualLimitIntegrable
  have hRTerminalLpTendsto : Tendsto
      (fun n => (hRTerminal n).toLp (R n T)) atTop
        (𝓝 (hResidualLimit.toLp residualLimit)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => R n T) hRTerminal residualLimit hResidualLimit).mpr
    change Tendsto
      (fun n => eLpNorm (fun omega =>
        (valueTruncation U n T omega - (family.data n).Vp T omega) -
          (U T omega - terminal.limit omega)) 1 mu) atTop (𝓝 0)
    simpa [R, residualLimit] using terminal.residual_terminal_l1_tendsto
  have hRTerminalCauchy : CauchySeq
      (fun n => (hRTerminal n).toLp (R n T)) :=
    hRTerminalLpTendsto.cauchySeq
  obtain ⟨cutoff, hCutoff, M0, hM0Martingale, hM0Right, hM0Constant,
      hRUniform0, hM0Terminal, hM0TerminalLpEq⟩ :=
    ChronologicalGrid.exists_rightContinuous_martingale_of_terminalL1_cauchy
      hUsual R T hRMartingale hRRight hRConstant hRTerminal hRTerminalCauchy
  have hM0LeftAE : ∀ᵐ omega ∂mu, ∀ t, Tendsto
      (fun s => M0 s omega) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun s => M0 s omega) t)) := by
    filter_upwards [hRUniform0] with omega hUniform
    intro t
    exact leftLimits_of_tendstoUniformly
      (fun n s => R (cutoff n) s omega) (fun s => M0 s omega)
      hUniform (fun n s => hRLeft (cutoff n) omega s) t
  have hM0RegularAE : ∀ᵐ omega ∂mu,
      (∀ t, ContinuousWithinAt (M0 · omega) (Ici t) t) ∧
        ∀ t, Tendsto (fun s => M0 s omega) (𝓝[<] t)
          (𝓝 (Function.leftLim (fun s => M0 s omega) t)) := by
    filter_upwards [hM0LeftAE] with omega hLeft
    exact ⟨hM0Right omega, hLeft⟩
  obtain ⟨M, hMStrong, hMRight, hMLeft, hMIndist⟩ :=
    ProcessNullSetRegularization.exists_stronglyAdapted_rightContinuous_leftLimits_version
      hUsual hM0Martingale.stronglyAdapted hM0RegularAE
  have hMMartingale : Martingale M F mu :=
    hM0Martingale.congr hMStrong
      (fun t => (hMIndist.eventuallyEq_at t).symm)
  have hMConstant : ∀ t, T ≤ t → M t =ᵐ[mu] M T := by
    intro t ht
    filter_upwards [hMIndist.eventuallyEq_at t,
      hMIndist.eventuallyEq_at T, hM0Constant t ht] with omega hMt hMT hM0
    rw [hMt, hMT, hM0]
  have hResidualUniform : ∀ᵐ omega ∂mu, TendstoUniformly
      (fun n t => R (cutoff n) t omega) (fun t => M t omega) atTop := by
    filter_upwards [hRUniform0, hMIndist] with omega hUniform hEq
    have hPathEq : (fun t => M t omega) = fun t => M0 t omega := by
      funext t
      exact hEq t
    rw [hPathEq]
    exact hUniform
  have hResidualLimitLpEq :
      limUnder atTop (fun n => (hRTerminal n).toLp (R n T)) =
        hResidualLimit.toLp residualLimit := by
    exact tendsto_nhds_unique hRTerminalCauchy.tendsto_limUnder
      hRTerminalLpTendsto
  have hM0TerminalLp : hM0Terminal.toLp (M0 T) =
      hResidualLimit.toLp residualLimit :=
    hM0TerminalLpEq.trans hResidualLimitLpEq
  have hM0TerminalAE : M0 T =ᵐ[mu] residualLimit :=
    (MemLp.toLp_eq_toLp_iff hM0Terminal hResidualLimit).mp hM0TerminalLp
  have hMTerminalAE : M T =ᵐ[mu] residualLimit :=
    (hMIndist.eventuallyEq_at T).trans hM0TerminalAE
  have hCapTendsto : Tendsto (fun n : ℕ => valueTruncationCap n)
      atTop atTop := by
    dsimp [valueTruncationCap]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hCapSelected : Tendsto (fun n : ℕ => valueTruncationCap (cutoff n))
      atTop atTop := hCapTendsto.comp hCutoff.tendsto_atTop
  have hSourceSelectedEventuallyEq : ∀ᵐ omega ∂mu, ∀ᶠ n in atTop,
      ∀ t, valueTruncation U (cutoff n) t omega = U t omega := by
    filter_upwards [] with omega
    have hCap := hCapSelected.eventually_ge_atTop (U T omega)
    filter_upwards [hCap] with n hn t
    have hUt : U t omega ≤ U T omega := by
      rcases le_total t T with ht | ht
      · exact hU.monotone omega ht
      · rw [hU.constant_after omega t ht]
    change min (U t omega) (valueTruncationCap (cutoff n)) = U t omega
    exact min_eq_left (hUt.trans hn)
  let Pcad : Process Ω := fun t omega => U t omega - M t omega
  have hProjectionUniform : ∀ᵐ omega ∂mu, TendstoUniformly
      (fun n t => (family.data (cutoff n)).Vp t omega)
      (fun t => Pcad t omega) atTop := by
    filter_upwards [hResidualUniform, hSourceSelectedEventuallyEq] with omega
      hUniform hSource
    apply Metric.tendstoUniformly_iff.mpr
    intro epsilon hepsilon
    have hNEvent : ∀ᶠ n in atTop, ∀ t,
        dist (M t omega) (R (cutoff n) t omega) < epsilon :=
      (Metric.tendstoUniformly_iff.mp hUniform) epsilon hepsilon
    obtain ⟨N, hN⟩ := eventually_atTop.mp hNEvent
    have hSource' : ∀ᶠ n in atTop, ∀ t,
        valueTruncation U (cutoff n) t omega = U t omega := hSource
    obtain ⟨K, hK⟩ := eventually_atTop.mp hSource'
    refine eventually_atTop.2 ⟨max N K, fun n hn t => ?_⟩
    have hnN : N ≤ n := (le_max_left N K).trans hn
    have hnK : K ≤ n := (le_max_right N K).trans hn
    have hResidual := hN n hnN t
    have hResidual' : |M t omega -
        (valueTruncation U (cutoff n) t omega -
          (family.data (cutoff n)).Vp t omega)| < epsilon := by
      simpa only [R, Real.dist_eq] using hResidual
    have hSourceEq := hK n hnK t
    rw [Real.dist_eq]
    change |(U t omega - M t omega) -
      (family.data (cutoff n)).Vp t omega| < epsilon
    rw [← hSourceEq]
    calc
      |(valueTruncation U (cutoff n) t omega - M t omega) -
          (family.data (cutoff n)).Vp t omega| =
          |M t omega - (valueTruncation U (cutoff n) t omega -
            (family.data (cutoff n)).Vp t omega)| := by
        rw [show (valueTruncation U (cutoff n) t omega - M t omega) -
            (family.data (cutoff n)).Vp t omega =
              -(M t omega - (valueTruncation U (cutoff n) t omega -
                (family.data (cutoff n)).Vp t omega)) by ring,
          abs_neg]
      _ < epsilon := hResidual'
  have hRZero : ∀ n omega, R n 0 omega = 0 := by
    intro n omega
    dsimp [R]
    rw [congrFun (hU.valueTruncation_zero n) omega,
      congrFun
        (family.data n).projection.projection_ready.predictable_version.Vp_zero omega]
    simp
  have hMZero : M 0 =ᵐ[mu] 0 := by
    filter_upwards [hResidualUniform] with omega hUniform
    have hPoint := hUniform.tendsto_at 0
    have hEqFun : (fun n => R (cutoff n) 0 omega) =
        (fun _ : ℕ => (0 : Real)) := by
      funext n
      exact hRZero (cutoff n) omega
    rw [hEqFun] at hPoint
    have hEq : (0 : Real) = M 0 omega :=
      tendsto_nhds_unique tendsto_const_nhds hPoint
    exact hEq.symm
  have hPcadStrong : StronglyAdapted F Pcad := by
    dsimp [Pcad]
    exact hU.stronglyAdapted.sub hMStrong
  have hPcadRight : ∀ omega t,
      ContinuousWithinAt (Pcad · omega) (Ici t) t := by
    intro omega t
    dsimp [Pcad]
    exact (hU.rightContinuous omega t).sub (hMRight omega t)
  have hPcadLeft : ProcessHasLeftLimits Pcad := by
    dsimp [Pcad]
    exact hU.hasLeftLimits.sub hMLeft
  have hPcadZero : Pcad 0 =ᵐ[mu] 0 := by
    filter_upwards [hMZero] with omega hM
    change U 0 omega - M 0 omega = 0
    rw [congrFun hU.zero omega, hM]
    simp
  have hPcadConstant : ∀ t, T ≤ t → Pcad t =ᵐ[mu] Pcad T := by
    intro t ht
    filter_upwards [hMConstant t ht] with omega hM
    change U t omega - M t omega = U T omega - M T omega
    rw [hU.constant_after omega t ht, hM]
  have hPcadTerminal : Pcad T =ᵐ[mu] terminal.limit := by
    filter_upwards [hMTerminalAE] with omega hM
    change U T omega - M T omega = terminal.limit omega
    dsimp [residualLimit] at hM
    rw [hM]
    ring
  exact ⟨{
    cutoff := cutoff
    cutoff_strictMono := hCutoff
    M := M
    M_stronglyAdapted := hMStrong
    M_martingale := hMMartingale
    M_rightContinuous := hMRight
    M_leftLimits := hMLeft
    M_constant_after := hMConstant
    M_terminal_ae_eq_residual := hMTerminalAE
    residual_uniform_ae := hResidualUniform
    Pcad := Pcad
    Pcad_definition := rfl
    projection_uniform_ae := hProjectionUniform
    Pcad_stronglyAdapted := hPcadStrong
    Pcad_rightContinuous := hPcadRight
    Pcad_leftLimits := hPcadLeft
    Pcad_zero_ae := hPcadZero
    Pcad_constant_after := hPcadConstant
    Pcad_terminal_ae_eq_limit := hPcadTerminal }⟩

end HorizonFactorialGrid

end FTAPTheorem42
