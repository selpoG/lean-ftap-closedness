# Module guide

[日本語](architecture.ja.md)

The public entry point is `import FTAPTheorem42`. Its theorem is
`FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket` in
[Main.lean](../FTAPTheorem42/Main.lean). Internal paths organize the proof;
they are not a separate compatibility API.

## The main proof and the analytic appendix

| Layer | Mathematical responsibility |
| --- | --- |
| `PositiveTail/`, `Trading/`, `Core/` | Forward-convex compactness (DS A1.1 and Proposition 3.1), maximal elements (4.3), the Fatou criterion, and weak-star closedness. |
| `Proof/Selection/` | Terminal lower-bound control, chronological first-gap pasting and the maximal candidate's uniform path limit (4.5). |
| `Proof/Components/` | The NFLVR contradiction for indexed gain families (4.7), normalized-tail contradiction (4.8), uniform test cutoff (4.9), and common Hilbert convexification (4.10). |
| `Proof/OrientedSequence.lean` | Preserve the same original gains, component weights, uniform limit and terminal while assembling finite Hahn improvements. |
| `Closedness/`, `Main.lean` | Use Hahn improvements to contradict maximality (4.11), obtain FV Cauchy estimates, realize the maximal claim, and conclude both closure statements. |
| `Interface/` | The precise process-level analytic contracts used by the main proof. All are proved in the normal library. |
| `Stochastic/` | Decomposition, compensation, integral construction, localization, topology comparison, and finite quantitative risk/tail/Hahn estimates. |
| `Foundations/` | Concrete shared vocabulary and elementary probability, process, stopping, variation and convexity facts. No stochastic implementation or interface import. |

The main proof chooses the sequence and convex weights and proves the Cauchy
properties. These conclusions are not supplied as analytic assumptions.
The analytic implementation does not import `Proof/`, `Closedness/`, or `Main.lean`.
Some implementation modules import concrete interface records to construct
values of those records; the dependency graph is acyclic.

`Proof/Components/ClassBoundedness`, `TailBoundedness`, and `TailTests` each contain
both the general argument for DS Lemma 4.7, 4.8, or 4.9 and its application to
the original-price market. Shared types and analytic inputs retain separate
modules where they define a dependency boundary, even when those modules are short.

## Mathematical contracts

The Japanese and English proof texts state the same mathematical boundary.
Their declaration tables locate the corresponding main arguments and analytic inputs.

| Mathematical input | Interface modules |
| --- | --- |
| Regular-path completeness, measurable envelopes and exponential change of measure | `PathLimits`, `Envelope` |
| Special decomposition under an L² gain envelope | `GainDecomposition` |
| Original-market identification, finite switching, stopping, finite convex sums, terminal limits | `IntegralClosure`, `MarketOperations`, `GainStopping`, `GainConvexity`, `TerminalMarket` |
| Finite vanishing-risk, normalized-tail and test estimates, prefix L² energy | `FiniteRisk`, `TailNormalization`, `TailTests`, `PrefixEnergy` |
| Martingale L² test estimate and uniform-approximation criterion | `MartingaleApproximation` |
| Finite Hahn improvements with closed-stop lower bounds and original terminal claims | `FiniteHahn` |
| Realization of the common limit from component estimates | `IntegralClosure` |

These inputs contain no NFLVR or maximality hypothesis. The finite bounds do
not assert convergence of the market's selected sequence. For example, the tail
normalization input constructs a normalized gain at one scale; the main proof
chooses the scales and applies Lemma 4.7 to the resulting family.

`GainData`, `MarketData`, and `HahnData` are concrete records. Their fields describe
processes, original integral graphs, regular components, finite operations and
quantitative inequalities. Neither localization schedules nor internal integral
carriers occur in the main proof's types. `generalAdmissibleClaims` and
`generalTerminalClaims` remain explicit sets defined by a graph, a running lower
bound, and the candidate's own continuous-time terminal limit.

Section 2 of the mathematical account states the seven groups above as seven propositions with twenty explicit clauses.
Together with the integral-graph and market data definitions, each identifier maps to one declaration in the actual isolated boundary.
Appendices A–C contain internal constructions, D proves the seven inputs, and E gives the declaration correspondence.
`check_structure.py` compares both language tables with the input lists and rejects direct references from the main proof to appendix internals.
The isolation check compares that list with declarations exported by Lean. Reference checking does not automatically verify the meaning of the prose.

## Checking the separation

[AuditMainTheorem.lean](../scripts/AuditMainTheorem.lean) checks direct constants
in the types and proof values of **every** declaration in `Proof/`, `Closedness/`
and `Main.lean`, including generated auxiliaries. Any direct dependency on
`Stochastic/` is rejected. Positive checks require the main selection, indexed
class bound, tail bound, common convexification, maximality and closure arguments
to occur in the final proof. The theorem may use only `propext`, `Classical.choice`
and `Quot.sound`.

[check_analytic_isolation.py](../scripts/check_analytic_isolation.py) removes the
entire stochastic tree in a temporary project. It exports exact elaborated types
for 20 analytic theorems and two data primitives (`GeneralIntegralGraph` and
`generalMarket`), replaces only these by temporary assumptions, and recompiles
the unchanged main proof. Concrete gain, market-operation, Hahn and terminal-set
definitions are retained. Only third-party package caches are shared; project
artifacts are rebuilt. A final audit requires exactly the listed assumptions
and the standard axioms, with no other axioms. These temporary assumptions are
never part of the normal library or public export.
Signature export, the isolated build, and the final audit all fail on warnings.

The public theorem still has the original truncated-market specification;
an elaboration check verifies its definitional equality with the public names.

## Maintaining the library

Keep an object's definitions and direct consequences together. File length and
declaration count are review aids, not fixed limits. Preserve explicit bridges
between integral representations and measures; special decomposition is not
transferred unconditionally between equivalent measures.

`task verify` checks structure, build, declaration closure, documented names,
axioms and analytic isolation. Every source declaration must contribute to the
main theorem, possibly through its generated declarations. Elaboration commands,
notations and instance attributes must also remain sufficient to rebuild it.
After mathematical text changes, run `task docs` and update both PDFs. The
standard mathlib linters are enabled; fix warnings at their source.
