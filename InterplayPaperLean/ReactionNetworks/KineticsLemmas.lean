import InterplayPaperLean.MainTheoremStatement.Kinetics
import InterplayPaperLean.ReactionNetworks.Stoichiometry

namespace InterplayPaperLean.Kinetics

theorem vectorField_apply {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions) (x : Fin species → ℝ) (i) :
    kinetics.vectorField network x i =
      ∑ j, network.stoichiometricMatrix i j * kinetics.rate x j := rfl

theorem vectorField_mem_stoichiometricSubspace {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions) (x : Fin species → ℝ) :
    kinetics.vectorField network x ∈ network.StoichiometricSubspace := by
  exact network.mulVec_mem_stoichiometricSubspace (kinetics.rate x)

end InterplayPaperLean.Kinetics
