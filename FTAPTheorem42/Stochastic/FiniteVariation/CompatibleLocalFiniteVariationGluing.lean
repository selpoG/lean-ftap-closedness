/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.CompatibleLocalMartingaleGluing
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization

/-!
# Gluing compatible local finite-variation coordinates

This module glues a family of globally bounded-variation coordinates along an
exhaustive localizing sequence.  The stopped-overlap identity makes the
pointwise `limUnder` eventually equal to one coordinate on every bounded time
interval, so the limit is locally of bounded variation.  Usual conditions are
used only to replace the almost-surely regular raw limit by a predictable,
pathwise right-continuous version.

The result is deliberately a local finite-variation process.  No global
bounded-variation conclusion is asserted for the infinite-horizon limit.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace CompatibleLocalFiniteVariationGluing

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega}

/-! ## The local variation of the raw limit -/

theorem rawLimit_locallyBoundedVariation_ae
    {tau : Nat -> Omega -> WithTop NNReal}
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    {A : Nat -> Process Omega}
    (hAVariation : forall n omega,
      BoundedVariationOn (A n · omega) Set.univ)
    (hCompat : forall n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (A n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (A m) (min (tau n) (tau m)))) :
    ∀ᵐ omega ∂mu,
      LocallyBoundedVariationOn
        (CompatibleLocalMartingaleGluing.rawLimit A · omega) Set.univ := by
  have hCompatAll : ∀ᵐ omega ∂mu, ∀ n m t,
      MeasureTheory.stoppedProcess (A n) (min (tau n) (tau m)) t omega =
        MeasureTheory.stoppedProcess (A m) (min (tau n) (tau m)) t omega := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    exact hCompat n
  filter_upwards [hTau.mono, hTau.tendsto_top, hCompatAll]
      with omega hMono hTop hCompatOmega
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  intro a b ha hb
  obtain ⟨n, hn⟩ := (hTop b).exists
  have hEq : ∀ s, s ∈ Set.Icc a b →
      CompatibleLocalMartingaleGluing.rawLimit A s omega = A n s omega := by
    intro s hs
    apply CompatibleLocalMartingaleGluing.rawLimit_eq_of_le hMono
      (fun m t => hCompatOmega n m t)
    exact (WithTop.coe_le_coe.mpr hs.2).trans hn.le
  have hVariationA : BoundedVariationOn
      (A n · omega) (Set.univ ∩ Set.Icc a b) :=
    (hAVariation n omega).mono inter_subset_left
  unfold BoundedVariationOn at hVariationA ⊢
  rw [eVariationOn.eq_of_eqOn (fun s hs => hEq s hs.2)]
  exact hVariationA

/-!
## Main gluing theorem

The coordinate variation hypothesis is global because each coordinate is a
finite-horizon object.  The conclusion is only local: an infinite-horizon
localization need not have finite total variation on all of `Set.univ`.
-/

theorem exists_predictable_rightContinuous_locallyBoundedVariation
    (hUsual : Filtration.UsualConditions mu F)
    {tau : Nat -> Omega -> WithTop NNReal}
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    {A : Nat -> Process Omega}
    (hAPredictable : forall n, IsStronglyPredictable F (A n))
    (hARight : forall n omega t,
      ContinuousWithinAt (A n · omega) (Set.Ici t) t)
    (hAVariation : forall n omega,
      BoundedVariationOn (A n · omega) Set.univ)
    (hCompat : forall n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (A n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (A m) (min (tau n) (tau m)))) :
    exists A' : Process Omega,
      IsStronglyPredictable F A' /\
        (forall omega t,
          ContinuousWithinAt (A' · omega) (Set.Ici t) t) /\
        (forall omega,
          LocallyBoundedVariationOn (A' · omega) Set.univ) /\
        forall n, ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess A' (tau n))
          (MeasureTheory.stoppedProcess (A n) (tau n)) := by
  let raw : Process Omega := CompatibleLocalMartingaleGluing.rawLimit A
  have hRawPredictable : IsStronglyPredictable F raw := by
    change StronglyMeasurable[F.predictable]
      (fun p : NNReal × Omega => limUnder atTop
        (fun n => A n p.1 p.2))
    exact @MeasureTheory.StronglyMeasurable.limUnder
      Nat (NNReal × Omega) Real F.predictable _ _ atTop _
      (fun n p => A n p.1 p.2) _ _
      (fun n => hAPredictable n)
  have hRawRight : ∀ᵐ omega ∂mu, ∀ t,
      ContinuousWithinAt (raw · omega) (Set.Ici t) t := by
    simpa only [raw] using
      (CompatibleLocalMartingaleGluing.rawLimit_rightContinuous_ae
        hTau hARight hCompat)
  have hRawVariation : ∀ᵐ omega ∂mu,
      LocallyBoundedVariationOn (raw · omega) Set.univ := by
    simpa only [raw] using
      (rawLimit_locallyBoundedVariation_ae hTau hAVariation hCompat)
  have hRawRegular : ∀ᵐ omega ∂mu,
      (∀ t, ContinuousWithinAt (raw · omega) (Set.Ici t) t) ∧
        LocallyBoundedVariationOn (raw · omega) Set.univ := by
    filter_upwards [hRawRight, hRawVariation] with omega hRight hVariation
    exact ⟨hRight, hVariation⟩
  let bad : Set Omega := {omega |
    ¬((∀ t, ContinuousWithinAt (raw · omega) (Set.Ici t) t) ∧
      LocallyBoundedVariationOn (raw · omega) Set.univ)}
  have hbadNull : mu bad = 0 := by
    simpa only [bad] using ae_iff.mp hRawRegular
  have hbadMeasurable : MeasurableSet[F 0] bad :=
    hUsual.containsNullSetsAtZero bad hbadNull
  have hRightOff : ∀ omega, omega ∉ bad → ∀ t,
      ContinuousWithinAt (raw · omega) (Set.Ici t) t := by
    intro omega homega
    have hRegular :
        (∀ t, ContinuousWithinAt (raw · omega) (Set.Ici t) t) ∧
          LocallyBoundedVariationOn (raw · omega) Set.univ := by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using homega
    exact hRegular.1
  have hVariationOff : ∀ omega, omega ∉ bad →
      LocallyBoundedVariationOn (raw · omega) Set.univ := by
    intro omega homega
    have hRegular :
        (∀ t, ContinuousWithinAt (raw · omega) (Set.Ici t) t) ∧
          LocallyBoundedVariationOn (raw · omega) Set.univ := by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using homega
    exact hRegular.2
  refine ⟨ProcessNullSetRegularization.zeroOn bad raw,
    ProcessNullSetRegularization.isStronglyPredictable_zeroOn
      hbadMeasurable hRawPredictable,
    ProcessNullSetRegularization.zeroOn_isRightContinuous hRightOff,
    ProcessNullSetRegularization.zeroOn_isLocallyBoundedVariation
      hVariationOff, ?_⟩
  intro n
  exact (ProcessNullSetRegularization.zeroOn_indistinguishable
      hbadNull raw).stoppedProcess (tau n) |>.trans
    (by
      simpa only [raw] using
        (CompatibleLocalMartingaleGluing.rawLimit_stoppedProcess
          hTau hCompat n))

end CompatibleLocalFiniteVariationGluing

end FTAPTheorem42
