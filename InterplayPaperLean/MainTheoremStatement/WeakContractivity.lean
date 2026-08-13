import InterplayPaperLean.MainTheoremStatement.ReactionNetwork

namespace InterplayPaperLean

/-- The dynamical conclusion called weak contractivity in the paper.

This is kept as a named specification boundary while the paper's admissible
kinetics, maximal flows, relative interiors of stoichiometric compatibility
classes, and class-dependent norms are formalized. It must be replaced by the
expanded definition before the main theorem is considered fully formalized. -/
opaque IsWeaklyContractive {species reactions : ℕ}
    (network : ReactionNetwork species reactions) : Prop

end InterplayPaperLean
