import FTAPTheorem42

/-! Check the public theorem's logical assumptions and the principal links in its proof. -/
open Lean Elab Command

private partial def dependencies (env : Environment) (n : Name) (seen : NameSet := {}) : NameSet := Id.run do
  if seen.contains n then return seen
  let mut seen := seen.insert n
  if let some info := env.find? n then
    for e in #[info.type] ++ (info.value? true).toArray do
      for child in e.getUsedConstants do
        seen := dependencies env child seen
  return seen

#print axioms FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket
#check FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket

run_cmd do
  let target := ``FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket
  for ax in ← collectAxioms target do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom: {ax}"
  let env ← getEnv
  let deps := dependencies env target
  let mut projectCount : Nat := 0
  let mut projectModules : NameSet := {}
  for name in deps.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if (`FTAPTheorem42).isPrefixOf mod then
      projectCount := projectCount + 1
      projectModules := projectModules.insert mod
  logInfo m!"Main proof: {projectCount} project declarations from {projectModules.toList.length} modules"
  for n in [``FTAPTheorem42.BoundedSourceIntegralMarket.generalMarket_forwardConvexCandidates,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.exists_uniform_terminal_limit_of_maximal,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.originalGain_class_boundedInProbability,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.originalGain_finiteTail_tendsToZero,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.originalGain_tail_tests,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.exists_original_martingale_convexification,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.exists_original_oriented_sequence,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.exists_selected_original_componentCauchy,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.maximal_mem_general_K1,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.exists_truncatedIntegralGraph_of_emeryConverges,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.generalMarket_terminalLowerBoundControlsGain,
      ``FTAPTheorem42.GainProcessModel.theorem42ConcreteWeakStar_from_gainProcessModel_K1_maximalRealization] do
    unless deps.contains n do throwError "Missing proof dependency: {n}"
    logInfo m!"Verified: {n}"
  for n in [``FTAPTheorem42.BoundedSourceIntegralMarket.generalMarket_terminalLowerBoundControlsGain,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.exists_truncatedIntegralGraph_of_emeryConverges,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.exists_original_oriented_sequence,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.exists_selected_original_componentCauchy,
      ``FTAPTheorem42.BoundedSourceIntegralMarket.truncatedTerminalClaims_one_of_component_estimates] do
    let some info := env.find? n | throwError "Missing interface theorem: {n}"
    for child in info.type.getUsedConstants do
      let some idx := env.getModuleIdxFor? child | continue
      let mod := env.header.moduleNames[idx.toNat]!
      if (`FTAPTheorem42.Stochastic.Construction).isPrefixOf mod ||
          (``FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy).isPrefixOf child ||
          child == ``FTAPTheorem42.LocallySIntegrableStrategy ||
          child == ``FTAPTheorem42.SpecialSemimartingaleDecomposition then
        throwError "Internal construction data in interface type: {n} -> {child}"
  logInfo "Interface types: no schedules or realization carriers"
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == `FTAPTheorem42.Main || (`FTAPTheorem42.Closedness).isPrefixOf mod ||
        (`FTAPTheorem42.Proof).isPrefixOf mod do continue
    checked := checked + 1
    for e in #[info.type] ++ (info.value? true).toArray do
      for child in e.getUsedConstants do
        let some childIdx := env.getModuleIdxFor? child | continue
        let childMod := env.header.moduleNames[childIdx.toNat]!
        if (`FTAPTheorem42.Stochastic).isPrefixOf childMod then
          throwError "Closedness bypasses analytic interface: {name} -> {child} ({childMod})"
  if checked == 0 then throwError "No closedness declarations were inspected"
  logInfo m!"Analytic boundary: {checked} declarations checked; no direct Stochastic dependencies"
  if let some output ← IO.getEnv "FTAP_DECLARATION_AUDIT_OUTPUT" then
    let mut declarations : Array Json := #[]
    for (name, _) in env.constants.toList do
      let some idx := env.getModuleIdxFor? name | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless (`FTAPTheorem42).isPrefixOf mod do continue
      declarations := declarations.push <| Json.mkObj
        [("name", toJson name.toString), ("module", toJson mod.toString),
         ("used", toJson (deps.contains name))]
    IO.FS.writeFile output (toJson declarations).compress

-- The public result still has exactly the original truncated-market specification.
-- Definitional equality, rather than a new mathematical assumption, bridges the names.
open MeasureTheory in
open scoped NNReal in
example {Ω : Type*} [MeasurableSpace Ω] {S : FTAPTheorem42.Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
    (source : FTAPTheorem42.BoundedSemimartingaleSource S F μ) :
    let K := FTAPTheorem42.LocalCompletedM2A.truncatedTerminalClaims
      (FTAPTheorem42.BoundedSourceIntegralMarket.unitSource source)
    FTAPTheorem42.LinftyNFLVR μ (FTAPTheorem42.LinftyClaims μ
      (FTAPTheorem42.C0AsDifference μ K)) →
    FTAPTheorem42.FatouClosed μ (FTAPTheorem42.C0AsDifference μ K) ∧
      FTAPTheorem42.LinftyWeakStarClosed μ (FTAPTheorem42.C0AsDifference μ K) :=
  FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket source
