/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.R1.Metric
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessAlgebra
import FTAPTheorem42.Stochastic.Topology.J1.Decomposition

/-! # Regular representatives of decomposable processes

The raw value of an R1 process need not itself be adapted or regular on its
exceptional set. The sum of the decomposition components is a regular version.
-/

namespace FTAPTheorem42.R1Process

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}

theorem exists_regular_representative (X : R1Process F μ) :
    ∃ Y : R1Process F μ, ProcessIndistinguishable μ X.val Y.val ∧
      IsStronglyProgressive F Y.val ∧
      (∀ w t, ContinuousWithinAt (Y.val · w) (Ici t) t) ∧
      ProcessHasLeftLimits Y.val ∧ Y.val 0 = 0 := by
  obtain ⟨D⟩ := X.property
  let Z : Process Ω := fun t w => D.N t w + D.A t w
  have hD : Nonempty (J1Decomposition Z F μ) :=
    ⟨{ D with decomposition := ProcessIndistinguishable.refl μ Z }⟩
  have hR : ∀ w t, ContinuousWithinAt (Z · w) (Ici t) t :=
    fun w t => (D.rightN w t).add (D.rightA w t)
  refine ⟨⟨Z, hD⟩, D.decomposition,
    StronglyAdapted.isStronglyProgressive_of_rightContinuous (D.adaptedN.add D.adaptedA) hR,
    hR, D.leftN.add D.leftA, ?_⟩
  funext w
  change D.N 0 w + D.A 0 w = 0
  simp [D.zeroN, D.zeroA]

end FTAPTheorem42.R1Process

namespace FTAPTheorem42.R1Process

/-! ## Elementary-test Cauchy limits on the full R1 process domain -/

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- The raw decomposable carrier is closed under elementary-test Cauchy
limits. Regularity of the input values is not assumed: it is supplied by
indistinguishable decomposition representatives. -/
theorem exists_elementaryEmery_limit (hUsual : Filtration.UsualConditions μ F)
    (X : Nat → R1Process F μ)
    (hC : ElementaryEmeryCauchy μ F (fun n => (X n).val)) :
    ∃ Y : R1Process F μ, IsStronglyProgressive F Y.val ∧
      (∀ w t, ContinuousWithinAt (Y.val · w) (Ici t) t) ∧
      ProcessHasLeftLimits Y.val ∧ Y.val 0 = 0 ∧
      ElementaryEmeryConverges μ F (fun n => (X n).val) Y.val := by
  choose R hXR hRP hRR hRL hR0 using fun n => (X n).exists_regular_representative
  have hRC := hC.congr hXR
  have hRGI : ∀ n, IsSemimartingale (R n).val F μ := by
    intro n
    obtain ⟨D⟩ := (R n).property
    exact D.isSemimartingale hUsual
  obtain ⟨Y, hYP, hYR, hYL, hY0, hYD, hConv⟩ :=
    hRC.exists_j1_limit hUsual hRP hRR hRL hR0 hRGI
  exact ⟨⟨Y, hYD⟩, hYP, hYR, hYL, hY0,
    hConv.congr_sequence (fun n => (hXR n).symm)⟩

omit [SigmaFiniteFiltration μ F] in
/-- Elementary-test limits in the decomposable domain are unique up to
indistinguishability, even for raw nonregular representatives. -/
theorem elementaryEmery_limit_unique (X : Nat → R1Process F μ) (Y Z : R1Process F μ)
    (hY : ElementaryEmeryConverges μ F (fun n => (X n).val) Y.val)
    (hZ : ElementaryEmeryConverges μ F (fun n => (X n).val) Z.val) :
    ProcessIndistinguishable μ Y.val Z.val := by
  choose R hXR hRP hRR hRL hR0 using fun n => (X n).exists_regular_representative
  obtain ⟨Y', hYY', hYP, hYR, _, hY0⟩ := Y.exists_regular_representative
  obtain ⟨Z', hZZ', hZP, hZR, _, hZ0⟩ := Z.exists_regular_representative
  have hY' := (hY.congr_sequence hXR).congr_limit hYY'
  have hZ' := (hZ.congr_sequence hXR).congr_limit hZZ'
  have hInitial : Y'.val 0 =ᵐ[μ] Z'.val 0 :=
    Eventually.of_forall fun w => by rw [hY0, hZ0]
  exact hYY'.trans ((ElementaryEmeryConverges.limit_indistinguishable
    hRP hYP hZP hYR hZR hInitial hY' hZ').trans hZZ'.symm)

end FTAPTheorem42.R1Process

namespace FTAPTheorem42.R1Process

/-! ## Elementary-test gauges on the same indistinguishability quotient

These gauges are defined on the existing R1 separation quotient. Their
sequential completeness is independent of the R1 topology: only the
identification of inseparability with indistinguishability is used.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [hUsual : Fact (Filtration.UsualConditions μ F)]

/-- Supremum over all unit elementary tests, at a fixed finite horizon.
No topology comparison is part of this definition. -/
noncomputable def elementaryGauge (T : NNReal) :
    SeparationQuotient (R1Process F μ) → SeparationQuotient (R1Process F μ) → ENNReal :=
  SeparationQuotient.lift₂
    (fun X Y : R1Process F μ => ⨆ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      ENNReal.ofReal (∫ w, elementaryEmeryTestError X.val Y.val J T w ∂μ))
    (by
      intro X Y X' Y' hX hY
      have hXX' := (quotient_eq_iff X X').mp (SeparationQuotient.mk_eq_mk.mpr hX)
      have hYY' := (quotient_eq_iff Y Y').mp (SeparationQuotient.mk_eq_mk.mpr hY)
      apply iSup_congr
      intro J
      rw [integral_congr_ae (elementaryEmeryTestError_congr hXX' hYY' J T)])

@[simp] theorem elementaryGauge_mk (T : NNReal) (X Y : R1Process F μ) :
    elementaryGauge T (SeparationQuotient.mk X) (SeparationQuotient.mk Y) =
      ⨆ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
        ENNReal.ofReal (∫ w, elementaryEmeryTestError X.val Y.val J T w ∂μ) := rfl

theorem elementaryGauge_mk_le_iff (T : NNReal) (X Y : R1Process F μ)
    {ε : Real} (hε : 0 ≤ ε) :
    elementaryGauge T (SeparationQuotient.mk X) (SeparationQuotient.mk Y) ≤ ENNReal.ofReal ε ↔
      ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
        ∫ w, elementaryEmeryTestError X.val Y.val J T w ∂μ ≤ ε := by
  simp only [elementaryGauge_mk, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hε]

/-- A Cauchy sequence for the elementary gauge family has a limit in the
same quotient. This does not use completeness or continuity of the R1 metric. -/
theorem exists_elementaryGauge_limit
    (X : Nat → SeparationQuotient (R1Process F μ))
    (hC : ∀ T : NNReal, ∀ ε > (0 : Real), ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      elementaryGauge T (X m) (X n) ≤ ENNReal.ofReal ε) :
    ∃ Y : SeparationQuotient (R1Process F μ),
      ∀ T : NNReal, ∀ ε > (0 : Real), ∀ᶠ n in atTop,
        elementaryGauge T (X n) Y ≤ ENNReal.ofReal ε := by
  choose R hR using fun n => SeparationQuotient.surjective_mk (X n)
  have hRaw : ElementaryEmeryCauchy μ F (fun n => (R n).val) := by
    intro T ε hε
    obtain ⟨N, hN⟩ := hC T ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    apply (elementaryGauge_mk_le_iff T (R m) (R n) hε.le).mp
    rw [hR m, hR n]
    exact hN m hm n hn
  obtain ⟨Y, _, _, _, _, hConv⟩ := exists_elementaryEmery_limit hUsual.out R hRaw
  refine ⟨SeparationQuotient.mk Y, fun T ε hε => ?_⟩
  filter_upwards [hConv T ε hε] with n hn
  rw [← hR n]
  exact (elementaryGauge_mk_le_iff T (R n) Y hε.le).mpr hn

/-- Gauge limits are unique on the existing indistinguishability quotient. -/
theorem elementaryGauge_limit_unique
    (X : Nat → SeparationQuotient (R1Process F μ))
    (Y Z : SeparationQuotient (R1Process F μ))
    (hY : ∀ T : NNReal, ∀ ε > (0 : Real), ∀ᶠ n in atTop,
      elementaryGauge T (X n) Y ≤ ENNReal.ofReal ε)
    (hZ : ∀ T : NNReal, ∀ ε > (0 : Real), ∀ᶠ n in atTop,
      elementaryGauge T (X n) Z ≤ ENNReal.ofReal ε) : Y = Z := by
  choose R hR using fun n => SeparationQuotient.surjective_mk (X n)
  obtain ⟨Y, rfl⟩ := SeparationQuotient.surjective_mk Y
  obtain ⟨Z, rfl⟩ := SeparationQuotient.surjective_mk Z
  have hRaw (W : R1Process F μ)
      (hW : ∀ T : NNReal, ∀ ε > (0 : Real), ∀ᶠ n in atTop,
        elementaryGauge T (X n) (SeparationQuotient.mk W) ≤ ENNReal.ofReal ε) :
      ElementaryEmeryConverges μ F (fun n => (R n).val) W.val := by
    intro T ε hε
    filter_upwards [hW T ε hε] with n hn
    rw [← hR n] at hn
    exact (elementaryGauge_mk_le_iff T (R n) W hε.le).mp hn
  exact (quotient_eq_iff Y Z).mpr
    (elementaryEmery_limit_unique R Y Z (hRaw Y hY) (hRaw Z hZ))

end FTAPTheorem42.R1Process
