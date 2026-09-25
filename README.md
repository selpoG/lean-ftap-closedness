# The Delbaen–Schachermayer Closedness Theorem in Lean

[日本語](README.ja.md)

This repository formalizes Theorem 4.2 of Delbaen and Schachermayer's
*A General Version of the Fundamental Theorem of Asset Pricing* for bounded,
real-valued semimartingales. FTAP abbreviates the Fundamental Theorem of Asset
Pricing; the result formalized here is its closedness theorem.

Let `K₀` be the terminal gains of admissible general predictable integrals
against the original price process, and put `C₀ = K₀ − L⁰₊` and
`C = C₀ ∩ L∞`. Under NFLVR, the theorem proves Fatou closedness of `C₀`
and closedness of `C` for the actual `σ(L∞, L¹)` topology.

The Lean implementation uses the downward hull on raw functions, without a
measurability requirement on the subtracted residual. On a.e. measurable
claims this agrees with `K₀ − L⁰₊`: if `f ≤ g` almost surely with `g ∈ K₀`,
then `g − f` is an a.e. measurable nonnegative residual. This equivalence is
proved by `C0AsDifference_iff_measurable_residual` in
[Core/Basic.lean](FTAPTheorem42/Core/Basic.lean). Passing to almost-sure
classes gives the usual `L⁰` formulation; the `L∞` cone and NFLVR are unchanged.

```lean
import FTAPTheorem42

#check FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket
```

The public theorem is in [Main.lean](FTAPTheorem42/Main.lean). Its inputs are a
bounded semimartingale source and NFLVR for that source's general integral
market. The source records the usual filtration conditions, adapted càdlàg
paths, a uniform bound, and the elementary good-integrator property. Terminal
claims carry their own almost-sure continuous-time limits.

The explicit Lean context also includes a probability measure and
`SigmaFiniteFiltration`; the latter holds for a probability measure.
The source chooses an everywhere càdlàg representative and requires one
deterministic bound almost surely, uniformly over all nonnegative times.
The definition of Fatou closedness normalizes the common lower bound to
`−1`; positive scaling of the cone gives the usual arbitrary constant bound.

The supported result is
`FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket`.
Its first and second projections give Fatou and weak-star closedness,
respectively. The construction of maximal claims is available in the same
module as `maximal_mem_general_K1`. The `FTAPTheorem42` Lean namespace records
the theorem's number in the original paper; it is independent of the repository name.

The scope is the bounded, real-valued version of Theorem 4.2. Multidimensional
prices, the locally bounded extension, and existence of an equivalent
martingale measure are separate results and are not claimed here.

## Build and verify

The project pins Lean 4.34.0 and mathlib v4.34.0. Install Git and Lean's `elan`
toolchain manager; Python 3 is also needed for the audit scripts. Then run:

```sh
git clone https://github.com/selpoG/lean-ftap-closedness.git
cd lean-ftap-closedness
lake exe cache get
lake build
```

`lake exe cache get` downloads mathlib's compiled dependency cache; the project
itself is built from source. To use the result from another Lake project, add
this Git repository as a dependency, pin a commit, and import `FTAPTheorem42`.

Run the complete verification with [Task](https://taskfile.dev/):

```sh
task verify
```

The equivalent individual commands are:

```sh
python3 scripts/check_structure.py
lake build
lake exe lint-style FTAPTheorem42
python3 scripts/check_declaration_closure.py
lake env lean scripts/AuditProject.lean
python3 scripts/check_analytic_isolation.py
```

The dependency audit traverses declaration types and opaque proof values. It
checks that the main theorem uses only `propext`, `Classical.choice`, and
`Quot.sound`, and that every source declaration in the public library
contributes to the main proof. Automatically generated projections, recursors,
and auxiliary declarations are grouped with their originating declaration.
The audit also checks that the declarations cited in the mathematical proof
exist and belong to the main theorem's dependency closure. It also rejects direct
uses of internal stochastic constructions from the main proof; the exact
mathematical boundary is described in the [module guide](docs/architecture.md).
The isolation check rebuilds the unchanged main proof without `Stochastic/`,
using the exact interface signatures as temporary assumptions. The normal build
proves these contracts and retains its three-axiom audit.

## Proof and module map

The proof constructs a maximal claim's uniform process limit, obtains common
martingale and finite-variation Cauchy estimates, realizes the limit in the
original integral market, and applies the Fatou and weak-star closure arguments.

| Location | Responsibility |
| --- | --- |
| [Main.lean](FTAPTheorem42/Main.lean) | Maximal-claim realization and the public theorem. |
| `Core/`, `PositiveTail/`, `Trading/` | Functional analysis, terminal convex compactness, and closure. |
| `Stochastic/Process/`, `Stopping/`, `Predictable/` | Path regularity, stopping times, and predictability. |
| `Stochastic/Martingale/`, `FiniteVariation/`, `Decomposition/` | Component estimates and semimartingale decomposition. |
| `Stochastic/Integral/`, `Topology/`, `Memin/` | Integral construction, topology comparison, and closedness of the integral domain. |
| `Stochastic/Compactness/`, `DS/`, `Market/`, `Construction/` | Analytic localization, finite risk/tail/Hahn estimates, and realization of trades. |
| `Proof/Selection/`, `Proof/Components/` | DS Lemmas 4.5 and 4.7–4.10: maximality, NFLVR contradictions, and common convexification. |
| `Foundations/` | Concrete shared definitions and elementary process, stopping, and variation facts; independent of `Stochastic/`. |
| `Interface/` | Process-level analytic inputs, hiding localization schedules and integral carriers. |
| `Closedness/` | Maximality, FV Cauchy estimates, maximal-claim realization, and the two closure conclusions. |

Use `import FTAPTheorem42` as the stable entry point. Internal module paths
organize the proof and may change as the implementation is maintained.

The mathematical proof is available in [English](docs/proof.pdf) and
[Japanese](docs/proof.ja.pdf). Both cover the full argument, its stochastic
constructions, and a Lean declaration correspondence table. The text explicitly
cites the bounded Bichteler–Dellacherie and compensator existence theorems as
foundations; Lean constructs these too. See also
the [module guide](docs/architecture.md) and [documentation guide](docs/README.md).

To rebuild both PDFs with upLaTeX, dvipdfmx, and pdfLaTeX installed:

```sh
task docs
```

Without Task, run `python3 scripts/build_docs.py`. On Debian/Ubuntu, the TeX
packages are `texlive-lang-japanese`, `texlive-latex-extra`,
`texlive-fonts-recommended`, and `lmodern`. The build checks the final log for unresolved
references and overfull/underfull boxes before replacing each PDF. CI runs both
the Lean verification and this documentation build.

## License and citation

Author: **Mocho Go** ([selpoG](https://github.com/selpoG)).

Please cite the software using [CITATION.cff](CITATION.cff), and identify the
release or commit you used so that the cited formalization is reproducible.

Released under the [Apache License 2.0](LICENSE).
