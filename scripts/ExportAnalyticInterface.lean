import FTAPTheorem42

/-! Export exact elaborated interface signatures for the isolated consumer test.
The generated assumptions are confined to a temporary build, never the library. -/

open Lean Elab Command

/-- An unused binder has no proof body to refer to it in an axiom signature.
Underscore-prefixed binders preserve the kernel type without spurious unused-name warnings. -/
private partial def markUnusedBinders (e : Expr) : Expr :=
  e.replace fun part => match part with
    | .forallE n a b bi => some <| .forallE
        (if b.hasLooseBVar 0 then n else `_unused)
        (markUnusedBinders a) (markUnusedBinders b) bi
    | .lam n a b bi => some <| .lam
        (if b.hasLooseBVar 0 then n else `_unused)
        (markUnusedBinders a) (markUnusedBinders b) bi
    | _ => none

/-- Inline generated proof constants before printing signatures, so the exported
source uses the proof term rather than an unstable elaborator-generated name. -/
private partial def inlineGeneratedProofs (env : Environment) (e : Expr) : Expr :=
  e.replace fun part => match part.getAppFn with
    | .const n levels =>
      if n.toString.splitOn "." |>.any (·.startsWith "_proof_") then
        (env.find? n).bind fun info => (info.value? true).map fun value =>
          inlineGeneratedProofs env
            ((value.instantiateLevelParams info.levelParams levels).beta part.getAppArgs)
      else none
    | _ => none

private def contracts : List (String × String × List String) :=
  [("IntegralClosure", "BoundedSourceIntegralMarket", ["GeneralIntegralGraph", "generalAdmissibleClaims",
    "generalTerminalClaims", "generalMarket", "truncatedTerminalClaims_one_of_component_estimates",
    "generalAdmissibleClaims_eq_generalMarket", "generalTerminalClaims_eq_generalMarket_K0",
    "generalAdmissibleClaims_one_eq_generalMarket_K1"]),
   ("TerminalMarket", "BoundedSourceIntegralMarket", ["generalMarket_terminal_properties"]),
   ("MarketOperations", "BoundedSourceIntegralMarket", ["generalMarket_operations"]),
   ("FiniteRisk", "BoundedSourceIntegralMarket", ["originalGain_finiteRisk"]),
   ("TailNormalization", "BoundedSourceIntegralMarket", ["originalGain_finiteTail_normalization"]),
   ("TailTests", "BoundedSourceIntegralMarket", ["originalGain_finiteTail_test_estimate"]),
   ("GainStopping", "BoundedSourceIntegralMarket", ["originalSpecialGain_finiteStop"]),
   ("MartingaleApproximation", "AnalyticInterface",
    ["emeryCauchy_of_uniform_approximations", "martingaleTestsCauchy_of_terminalL2"]),
   ("PathLimits", "AnalyticInterface", ["regular_uniform_limit"]),
   ("PrefixEnergy", "BoundedSourceIntegralMarket", ["originalGain_prefix_energy", "originalGain_prefix_regular"]),
   ("GainDecomposition", "BoundedSourceIntegralMarket", ["originalGain_specialDecomposition"]),
   ("GainConvexity", "BoundedSourceIntegralMarket", ["originalGain_convexCombination"]),
   ("FiniteHahn", "BoundedSourceIntegralMarket", ["originalGain_finiteHahn"]),
   ("Envelope", "AnalyticInterface", ["regular_common_envelope", "equivalent_envelope_measure"])]

namespace FTAPTheorem42.BoundedSourceIntegralMarket

run_cmd liftTermElabM do
  let some output ← IO.getEnv "FTAP_INTERFACE_EXPORT" |
    throwError "Set FTAP_INTERFACE_EXPORT to an empty export directory"
  let env ← getEnv
  let shared := "import FTAPTheorem42.Foundations.BoundedSource\n" ++
    "import FTAPTheorem42.Foundations.CadlagEnvelope\n" ++
    "import FTAPTheorem42.Foundations.ChronologicalGrid\n" ++
    "import FTAPTheorem42.Foundations.ChronologicalGridOrientation\n" ++
    "import FTAPTheorem42.Foundations.CommonHilbertConvexification\n" ++
    "import FTAPTheorem42.Foundations.ConvexProcesses\n" ++
    "import FTAPTheorem42.Foundations.Decomposition\n" ++
    "import FTAPTheorem42.Foundations.ElementaryIntegral\n" ++
    "import FTAPTheorem42.Foundations.ElementaryIntegrand\n" ++
    "import FTAPTheorem42.Foundations.ElementaryPredictable\n" ++
    "import FTAPTheorem42.Foundations.ElementaryPredictableProcess\n" ++
    "import FTAPTheorem42.Foundations.ElementaryStrategy\n" ++
    "import FTAPTheorem42.Foundations.Emery\n" ++
    "import FTAPTheorem42.Foundations.Envelope\n" ++
    "import FTAPTheorem42.Foundations.EquivalentMeasureTransfer\n" ++
    "import FTAPTheorem42.Foundations.FactorialChronologicalGrid\n" ++
    "import FTAPTheorem42.Foundations.FiniteVariationCanonicalMeasure\n" ++
    "import FTAPTheorem42.Foundations.FiniteVariationPathMeasure\n" ++
    "import FTAPTheorem42.Foundations.FiniteVariationStoppedPath\n" ++
    "import FTAPTheorem42.Foundations.GridEnvelope\n" ++
    "import FTAPTheorem42.Foundations.HahnStopping\n" ++
    "import FTAPTheorem42.Foundations.HilbertConvexification\n" ++
    "import FTAPTheorem42.Foundations.MaximalProbability\n" ++
    "import FTAPTheorem42.Foundations.Passage\n" ++
    "import FTAPTheorem42.Foundations.Paths\n" ++
    "import FTAPTheorem42.Foundations.Process\n" ++
    "import FTAPTheorem42.Foundations.ProcessEnvelope\n" ++
    "import FTAPTheorem42.Foundations.ProcessIndistinguishable\n" ++
    "import FTAPTheorem42.Foundations.RightContinuousHittingTime\n" ++
    "import FTAPTheorem42.Foundations.RightContinuousProgressive\n" ++
    "import FTAPTheorem42.Foundations.RiskSchedules\n" ++
    "import FTAPTheorem42.Foundations.Semimartingale\n" ++
    "import FTAPTheorem42.Foundations.SignedMeasureVariation\n" ++
    "import FTAPTheorem42.Foundations.Skeleton\n" ++
    "import FTAPTheorem42.Foundations.TerminalLimit\n" ++
    "import FTAPTheorem42.Foundations.UsualConditions\n" ++
    "import FTAPTheorem42.Foundations.Variation\n" ++
    "import FTAPTheorem42.Trading.TerminalImprovement\n" ++
    "import FTAPTheorem42.Trading.FatouCriterion\n"
  let path := System.FilePath.mk output
  IO.FS.createDirAll path
  let mut axioms : Array String := #[]
  for (file, ns, names) in contracts do
    let imports := if file == "IntegralClosure" then shared else
      "import FTAPTheorem42.Interface.HahnData\n" ++
      "import FTAPTheorem42.Interface.MarketData\n" ++ shared
    let mut text := imports ++ "\n/-! # Generated contracts for the isolated interface test -/\n\n" ++
      s!"namespace FTAPTheorem42.{ns}\n\n"
    for short in names do
      let n := `FTAPTheorem42 ++ ns.toName ++ short.toName
      let info ← getConstInfo n
      let universes := if info.levelParams.isEmpty then "" else
        ".{" ++ String.intercalate ", " (info.levelParams.map Name.toString) ++ "}"
      let concrete := ["generalAdmissibleClaims", "generalTerminalClaims"].contains short
      unless concrete do axioms := axioms.push n.toString
      let expressions := #[info.type] ++ if concrete then (info.value? true).toArray else #[]
      for e in expressions do
        for child in e.getUsedConstants do
          if let some idx := env.getModuleIdxFor? child then
            if (`FTAPTheorem42.Stochastic).isPrefixOf env.header.moduleNames[idx.toNat]! then
              throwError "Implementation leaked into exported signature: {n} -> {child}"
      text := text ++ (← withTheReader Core.Context
        (fun ctx => { ctx with currNamespace := `FTAPTheorem42 ++ ns.toName }) <|
        withOptions (fun opts => ((opts.setBool `pp.all true).setBool `pp.fullNames false)
          |>.set `format.indent (1 : Nat)) do
        let typeExpr := markUnusedBinders (inlineGeneratedProofs env info.type)
        unless ← Meta.isDefEq info.type typeExpr do
          throwError "Export changed the interface type: {n}"
        let type := (← Meta.ppExpr typeExpr).pretty 90 2 2
        if concrete then
          let some value := info.value? true | throwError "Missing concrete definition {n}"
          let valueExpr := markUnusedBinders (inlineGeneratedProofs env value)
          unless ← Meta.isDefEq value valueExpr do
            throwError "Export changed the concrete definition: {n}"
          return s!"noncomputable def {short}{universes} :\n  {type} :=\n  {(← Meta.ppExpr valueExpr).pretty 90 2 2}\n\n"
        else
          return s!"axiom {short}{universes} :\n  {type}\n\n")
    IO.FS.writeFile (path / s!"{file}.lean") (text ++ s!"end FTAPTheorem42.{ns}\n")
  IO.FS.writeFile (path / "boundary.json") (toJson axioms).compress
  logInfo m!"Exported {axioms.size} analytic assumptions; concrete terminal sets and gain records retained"

end FTAPTheorem42.BoundedSourceIntegralMarket
