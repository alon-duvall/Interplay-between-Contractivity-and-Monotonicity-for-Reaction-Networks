# Main theorem statement dependencies

This directory is the minimal specification layer required to state the main
theorem from `interplay_paper.tex`.

Files in this directory define the mathematical meaning of the theorem's
hypotheses and conclusion. Changes here can change what `MainTheorem.lean`
claims and therefore require explicit review.

Substantive lemmas and proof machinery belong in the subject-based directories
outside this specification layer. They may use these definitions, but should
not replace them with alternate versions.

The conclusion in `WeakContractivity.lean` is explicit. It depends on
`Kinetics.lean` and `Trajectories.lean`, and quantifies over every admissible
kinetics, every stoichiometric compatibility class, a norm, every pair of
distinct trajectories in the relative interior, and every pair of common
forward times.
