import InterplayPaperLean.MainTheoremStatement.ReactionNetwork
import Mathlib.Logic.Relation

namespace InterplayPaperLean.ReactionNetwork

/-- A directed edge in the paper's reaction-interaction (`RI`) graph. -/
def RIEdge {species reactions : ℕ} (network : ReactionNetwork species reactions)
    (source target : Fin reactions) : Prop :=
  if network.reversible target then
    network.SharesSpecies source target
  else
    ∃ s, network.stoichiometricMatrix s source ≠ 0 ∧
      network.stoichiometricMatrix s target < 0

/-- Strong connectivity of the directed `RI` graph. Reflexive-transitive
reachability handles the path from a reaction to itself. -/
def IsRIGraphStronglyConnected {species reactions : ℕ}
    (network : ReactionNetwork species reactions) : Prop :=
  ∀ i j, Relation.ReflTransGen network.RIEdge i j

end InterplayPaperLean.ReactionNetwork
