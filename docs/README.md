# Documentation

[日本語](README.ja.md)

Start with the [English README](../README.md) or [日本語 README](../README.ja.md).

- [Mathematical proof in English](proof.pdf).
- [数学的証明（日本語）](proof.ja.pdf).

Both versions cover the proof from the integral domain to Fatou and weak-star
closedness, followed by the stochastic constructions and a Lean declaration
correspondence table.
Section 2 lists all analytic inputs as seven propositions (twenty clauses) and two data definitions.
Accepting them suffices to follow the market proof without consulting internal appendix lemmas.
Each clause corresponds to one declaration assumed in the Lean isolation check, which also compares both language mappings with the actual 22 declarations.

- Appendix A: decomposition, compensation and component norms.
- Appendix B: common localization and component series.
- Appendix C: the Emery topology and realization by one integrand.
- Appendix D: proofs of the seven analytic inputs.
- Appendix E: mathematical stages and Lean declarations.

To check an input, follow the proof-location table in Section 2 to Appendix D, then consult only the required internal constructions in A–C.
The isolation build verifies the formal dependency separation; agreement in mathematical meaning between prose and types is checked separately.

The text states the bounded Bichteler–Dellacherie characterization and the
dual predictable projection theorem as cited foundational results. Their
application hypotheses and norm estimates are explicit; the two-control
coefficient selection and original-market component estimates are proved in
the text. Lean also constructs the foundational decomposition and compensator.

- [Module guide](architecture.md): responsibilities, principal proof boundaries,
  and checks to run when maintaining the library.

The Japanese sources are `proof.ja.tex` and `proof.ja/`; the English sources are
`proof.tex` and `proof/`. Both use the bibliography in `proof/`. The mathematical text uses ordinary
mathematical notation; Lean names are collected in the final correspondence table.

Run `task docs` or `python3 scripts/build_docs.py` to build both PDFs. The required
TeX packages are listed in the [README](../README.md#proof-and-module-map).
The build rejects unresolved references and typesetting warnings before updating
each PDF. The Lean dependency audit checks that the declarations cited by the text
exist and contribute to the main theorem.
