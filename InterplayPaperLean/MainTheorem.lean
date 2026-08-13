import InterplayPaperLean.MainTheoremStatement.MatrixClasses
import InterplayPaperLean.MainTheoremStatement.RIGraph
import InterplayPaperLean.MainTheoremStatement.WeakContractivity

/-! # Main theorem

This is the canonical statement of Theorem 1 from `interplay_paper.tex`.
-/

namespace InterplayPaperLean

/-- **Main theorem (paper, Theorem 1).**

If a non-catalytic reaction network has a strongly connected RI graph and its
stoichiometric matrix factors as `P * N * D`, with `P ∈ 𝒫`, `N ∈ 𝒩`, and
`D ∈ 𝒟`, then the network is weakly contractive.
-/
theorem mainTheorem
    {species reactions intermediate : ℕ}
    (network : ReactionNetwork species reactions)
    (P : Matrix (Fin species) (Fin intermediate) ℝ)
    (N : Matrix (Fin intermediate) (Fin reactions) ℝ)
    (D : Matrix (Fin reactions) (Fin reactions) ℝ)
    (hNonCatalytic : network.IsNonCatalytic)
    (hFactorization : network.stoichiometricMatrix = P * N * D)
    (hP : InP P)
    (hN : InN N)
    (hD : InD D)
    (hRI : network.IsRIGraphStronglyConnected) :
    IsWeaklyContractive network := by
  sorry

end InterplayPaperLean
