/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Stochastic.FiniteVariation.PredictableFiniteVariationLocalMartingale
import FTAPTheorem42.Stochastic.Market.Source.CenteredMarketUnitLocallySIntegrableStrategy

/-!
# Regular versions of special semimartingale decompositions

Construct càdlàg predictable finite-variation representatives and the corresponding
martingale components without changing the processes up to indistinguishability.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SpecialSemimartingaleDecomposition

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega}

omit [MeasurableSpace Omega] in
/-- A locally bounded-variation path has a left limit at every time. -/
theorem finiteVariationPart_hasLeftLimits_of_localBoundedVariation
    {A : Process Omega}
    (hA : ∀ omega, LocallyBoundedVariationOn
      (fun t => A t omega) Set.univ) :
    ProcessHasLeftLimits A := by
  intro omega t
  let hBV : BoundedVariationOn (fun u => A u omega)
      (Set.univ ∩ Set.Icc (0 : NNReal) t) :=
    hA omega 0 t (Set.mem_univ _) (Set.mem_univ _)
  obtain ⟨l, hl⟩ := hBV.exists_tendsto_left t
  apply tendsto_leftLim_of_tendsto
  refine ⟨l, ?_⟩
  have hset : Set.Icc (0 : NNReal) t ∩ Set.Iio t = Set.Iio t := by
    ext s
    constructor
    · intro hs
      exact hs.2
    · intro hs
      exact ⟨⟨bot_le, hs.le⟩, hs⟩
  simpa only [univ_inter, hset] using hl

/-- The supplied source and finite-variation paths give the raw martingale
left limits on one common full-measure set. -/
theorem martingalePart_hasLeftLimits_ae
    (D : SpecialSemimartingaleDecomposition S F mu)
    (hSLeft : ProcessHasLeftLimits S) :
    ∀ᵐ omega ∂mu, ∀ t,
      Tendsto (fun s => D.martingalePart s omega) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun s => D.martingalePart s omega) t)) := by
  have hALeft : ProcessHasLeftLimits D.finiteVariationPart :=
    finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      D.finiteVariationPart_isLocallyBoundedVariation
  filter_upwards [D.decomposition] with omega homega
  intro t
  have hDifference : Tendsto
      (fun s => S s omega - D.finiteVariationPart s omega)
      (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s => S s omega) t -
        Function.leftLim (fun s => D.finiteVariationPart s omega) t)) :=
    (hSLeft omega t).sub (hALeft omega t)
  have hPath : ∀ s,
      S s omega - D.finiteVariationPart s omega =
        D.martingalePart s omega := by
    intro s
    rw [homega s]
    ring
  have hMartingale : Tendsto
      (fun s => D.martingalePart s omega) (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s => S s omega) t -
        Function.leftLim (fun s => D.finiteVariationPart s omega) t)) :=
    hDifference.congr' (Filter.Eventually.of_forall hPath)
  exact tendsto_leftLim_of_tendsto ⟨_, hMartingale⟩

/-- The decomposition and pathwise right-continuity of the source and
martingale components force the finite-variation component to be
right-continuous on the same full-measure set. -/
theorem finiteVariationPart_isRightContinuous_ae
    (D : SpecialSemimartingaleDecomposition S F mu)
    (hSRight : ∀ omega t,
      ContinuousWithinAt (S · omega) (Set.Ici t) t)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (D.martingalePart · omega) (Set.Ici t) t) :
    ∀ᵐ omega ∂mu, ∀ t,
      ContinuousWithinAt (D.finiteVariationPart · omega) (Set.Ici t) t := by
  filter_upwards [D.decomposition] with omega homega
  intro t
  have hPath : (D.finiteVariationPart · omega) =
      (S · omega) - (D.martingalePart · omega) := by
    funext s
    have hs := homega s
    change D.finiteVariationPart s omega =
      S s omega - D.martingalePart s omega
    rw [hs]
    ring
  rw [hPath]
  exact (hSRight omega t).sub (hMRight omega t)

/-- A special-semimartingale decomposition admits a pathwise-left-limit
martingale representative whenever the source itself has pathwise left
limits.  The finite-variation representative is kept unchanged. -/
theorem exists_pathwiseLeftLimit_representative
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (D : SpecialSemimartingaleDecomposition S F mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hSLeft : ProcessHasLeftLimits S)
    (hMAdapted : StronglyAdapted F D.martingalePart)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (D.martingalePart · omega) (Set.Ici t) t) :
    ∃ M' : Process Omega,
      StronglyAdapted F M' ∧
        LocalMartingale M' F mu ∧
        (∀ omega t,
          ContinuousWithinAt (M' · omega) (Set.Ici t) t) ∧
        ProcessHasLeftLimits M' ∧
        ProcessIndistinguishable mu M' D.martingalePart := by
  have hMLeftAE := martingalePart_hasLeftLimits_ae D hSLeft
  have hMRegular : ∀ᵐ omega ∂mu,
      (∀ t, ContinuousWithinAt
        (D.martingalePart · omega) (Set.Ici t) t) ∧
        ∀ t, Tendsto (fun s => D.martingalePart s omega) (𝓝[<] t)
          (𝓝 (Function.leftLim (fun s => D.martingalePart s omega) t)) := by
    filter_upwards [hMLeftAE] with omega hLeft
    exact ⟨fun t => hMRight omega t, hLeft⟩
  obtain ⟨M', hM'Adapted, hM'Right, hM'Left, hM'M⟩ :=
    ProcessNullSetRegularization.exists_stronglyAdapted_rightContinuous_leftLimits_version
      hUsual hMAdapted hMRegular
  have hM'Local : LocalMartingale M' F mu :=
    LocalMartingale.congr_indistinguishable
      D.martingalePart_isLocalMartingale hM'Adapted hM'Right hM'M.symm
  exact ⟨M', hM'Adapted, hM'Local, hM'Right, hM'Left, hM'M⟩

/-- Replace both components by pathwise regular representatives while
preserving the source decomposition.  The finite-variation component is
regularized on the exceptional set where the decomposition does not force
right-continuity. -/
theorem exists_regularizedDecomposition
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (D : SpecialSemimartingaleDecomposition S F mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hSLeft : ProcessHasLeftLimits S)
    (hSAdapted : StronglyAdapted F S)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (D.martingalePart · omega) (Set.Ici t) t)
    (hSRight : ∀ omega t,
      ContinuousWithinAt (S · omega) (Set.Ici t) t) :
    ∃ D' : SpecialSemimartingaleDecomposition S F mu,
      ProcessIndistinguishable mu D'.martingalePart D.martingalePart ∧
        ProcessIndistinguishable mu D'.finiteVariationPart
          D.finiteVariationPart ∧
        StronglyAdapted F D'.martingalePart ∧
        (∀ omega t,
          ContinuousWithinAt (D'.martingalePart · omega) (Set.Ici t) t) ∧
        ProcessHasLeftLimits D'.martingalePart ∧
        (∀ omega t,
          ContinuousWithinAt (D'.finiteVariationPart · omega) (Set.Ici t) t) := by
  have hARightAE := finiteVariationPart_isRightContinuous_ae D hSRight hMRight
  let badA : Set Omega := {omega | ¬∀ t,
    ContinuousWithinAt (D.finiteVariationPart · omega) (Set.Ici t) t}
  have hbadANull : mu badA = 0 := by
    simpa only [badA] using ae_iff.mp hARightAE
  have hbadAMeasurable : MeasurableSet[F 0] badA :=
    hUsual.containsNullSetsAtZero badA hbadANull
  have hARightOff : ∀ omega, omega ∉ badA → ∀ t,
      ContinuousWithinAt (D.finiteVariationPart · omega) (Set.Ici t) t := by
    intro omega hω
    simpa only [badA, Set.mem_ofPred_eq, not_not] using hω
  have hALocalOff : ∀ omega, omega ∉ badA →
      LocallyBoundedVariationOn
        (D.finiteVariationPart · omega) Set.univ := by
    intro omega hω
    exact D.finiteVariationPart_isLocallyBoundedVariation omega
  let A' : Process Omega :=
    ProcessNullSetRegularization.zeroOn badA D.finiteVariationPart
  have hA'Predictable : IsStronglyPredictable F A' := by
    simpa only [A'] using
      ProcessNullSetRegularization.isStronglyPredictable_zeroOn
        hbadAMeasurable D.finiteVariationPart_isPredictable
  have hA'Local : ∀ omega,
      LocallyBoundedVariationOn (A' · omega) Set.univ := by
    simpa only [A'] using
      ProcessNullSetRegularization.zeroOn_isLocallyBoundedVariation hALocalOff
  have hA'Right : ∀ omega t,
      ContinuousWithinAt (A' · omega) (Set.Ici t) t := by
    simpa only [A'] using
      ProcessNullSetRegularization.zeroOn_isRightContinuous hARightOff
  have hA'A : ProcessIndistinguishable mu A' D.finiteVariationPart := by
    simpa only [A'] using
      ProcessNullSetRegularization.zeroOn_indistinguishable hbadANull
        D.finiteVariationPart
  let M0 : Process Omega := S - A'
  have hM0Adapted : StronglyAdapted F M0 := by
    simpa only [M0] using hSAdapted.sub hA'Predictable.stronglyAdapted
  have hM0Right : ∀ omega t,
      ContinuousWithinAt (M0 · omega) (Set.Ici t) t := by
    intro omega t
    change ContinuousWithinAt (fun u => S u omega - A' u omega)
      (Set.Ici t) t
    exact (hSRight omega t).sub (hA'Right omega t)
  have hM0M : ProcessIndistinguishable mu M0 D.martingalePart := by
    filter_upwards [D.decomposition, hA'A] with omega hD hA
    intro t
    change S t omega - A' t omega = D.martingalePart t omega
    rw [hA t, hD t]
    ring
  let D0 : SpecialSemimartingaleDecomposition S F mu := {
    martingalePart := M0
    finiteVariationPart := A'
    martingalePart_isLocalMartingale :=
      LocalMartingale.congr_indistinguishable
        D.martingalePart_isLocalMartingale hM0Adapted hM0Right hM0M.symm
    finiteVariationPart_isPredictable := hA'Predictable
    finiteVariationPart_isLocallyBoundedVariation := hA'Local
    decomposition := by
      filter_upwards [] with omega
      intro t
      change S t omega = (S t omega - A' t omega) + A' t omega
      ring
  }
  obtain ⟨M', hM'Adapted, hM'Local, hM'Right, hM'Left, hM'0⟩ :=
    exists_pathwiseLeftLimit_representative D0 hUsual hSLeft
      hM0Adapted hM0Right
  have hM'M : ProcessIndistinguishable mu M' D.martingalePart :=
    hM'0.trans hM0M
  let D' : SpecialSemimartingaleDecomposition S F mu := {
    martingalePart := M'
    finiteVariationPart := A'
    martingalePart_isLocalMartingale := hM'Local
    finiteVariationPart_isPredictable := hA'Predictable
    finiteVariationPart_isLocallyBoundedVariation :=
      hA'Local
    decomposition := by
      exact D.decomposition.trans
        (hM'M.add hA'A).symm
  }
  exact ⟨D', by simpa only [D'] using hM'M,
    by simpa only [D'] using hA'A,
    by simpa only [D'] using hM'Adapted,
    by simpa only [D'] using hM'Right,
    by simpa only [D'] using hM'Left,
    by simpa only [D'] using hA'Right⟩

/-- The pathwise-regular representative selected by
`exists_regularizedDecomposition`. -/
noncomputable def regularizedDecomposition
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (D : SpecialSemimartingaleDecomposition S F mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hSLeft : ProcessHasLeftLimits S)
    (hSAdapted : StronglyAdapted F S)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (D.martingalePart · omega) (Set.Ici t) t)
    (hSRight : ∀ omega t,
      ContinuousWithinAt (S · omega) (Set.Ici t) t) :
    SpecialSemimartingaleDecomposition S F mu :=
  Classical.choose (exists_regularizedDecomposition D hUsual hSLeft
    hSAdapted hMRight hSRight)

theorem regularizedDecomposition_spec
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (D : SpecialSemimartingaleDecomposition S F mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hSLeft : ProcessHasLeftLimits S)
    (hSAdapted : StronglyAdapted F S)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (D.martingalePart · omega) (Set.Ici t) t)
    (hSRight : ∀ omega t,
      ContinuousWithinAt (S · omega) (Set.Ici t) t) :
    ProcessIndistinguishable mu
        (regularizedDecomposition D hUsual hSLeft hSAdapted hMRight hSRight).martingalePart
        D.martingalePart ∧
      ProcessIndistinguishable mu
        (regularizedDecomposition D hUsual hSLeft hSAdapted hMRight hSRight).finiteVariationPart
        D.finiteVariationPart ∧
      StronglyAdapted F
        (regularizedDecomposition D hUsual hSLeft hSAdapted hMRight hSRight).martingalePart ∧
      (∀ omega t, ContinuousWithinAt
        ((regularizedDecomposition D hUsual hSLeft hSAdapted
          hMRight hSRight).martingalePart · omega)
        (Set.Ici t) t) ∧
      ProcessHasLeftLimits
        (regularizedDecomposition D hUsual hSLeft hSAdapted hMRight hSRight).martingalePart ∧
      (∀ omega t, ContinuousWithinAt
        ((regularizedDecomposition D hUsual hSLeft hSAdapted
          hMRight hSRight).finiteVariationPart · omega)
        (Set.Ici t) t) := by
  exact Classical.choose_spec (exists_regularizedDecomposition D hUsual hSLeft
    hSAdapted hMRight hSRight)

/-- The centered unit graph built from the regularized decomposition.  The
finite-variation right-continuity input is supplied by the null-set
regularization of the decomposition itself. -/
noncomputable def regularizedCenteredUnitLocallySIntegrableStrategy
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (D : SpecialSemimartingaleDecomposition S F mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hSLeft : ProcessHasLeftLimits S)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t,
      ContinuousWithinAt (S · omega) (Set.Ici t) t)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (D.martingalePart · omega) (Set.Ici t) t) :
    LocallySIntegrableStrategy
      (regularizedDecomposition D hUsual hSLeft hSAdapted hMRight hSRight) := by
  let D' := regularizedDecomposition D hUsual hSLeft hSAdapted hMRight hSRight
  have hD' := regularizedDecomposition_spec D hUsual hSLeft hSAdapted hMRight hSRight
  have hM'Adapted : StronglyAdapted F D'.martingalePart := by
    simpa only [D'] using hD'.2.2.1
  have hM'Right : ∀ omega t,
      ContinuousWithinAt (D'.martingalePart · omega) (Set.Ici t) t := by
    simpa only [D'] using hD'.2.2.2.1
  have hARight' : ∀ omega t,
      ContinuousWithinAt (D'.finiteVariationPart · omega) (Set.Ici t) t := by
    simpa only [D'] using hD'.2.2.2.2.2
  exact D'.centeredUnitLocallySIntegrableStrategy hSAdapted hSRight
    hM'Adapted hM'Right hARight'

end SpecialSemimartingaleDecomposition

end FTAPTheorem42
