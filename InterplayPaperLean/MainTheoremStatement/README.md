# Main theorem statement dependencies

This directory is the minimal specification layer required to state the main
theorem from `interplay_paper.tex`.

Files in this directory define the mathematical meaning of the theorem's
hypotheses and conclusion. Changes here can change what `MainTheorem.lean`
claims and therefore require explicit review.

Substantive lemmas and proof machinery belong in the subject-based directories
outside this specification layer. They may use these definitions, but should
not replace them with alternate versions.

`WeakContractivity.lean` currently marks an intentionally opaque specification
boundary. The theorem statement is not fully locked down until that predicate
is expanded using the paper's definitions of admissible kinetics, trajectories,
stoichiometric compatibility classes, relative interiors, and norms.
