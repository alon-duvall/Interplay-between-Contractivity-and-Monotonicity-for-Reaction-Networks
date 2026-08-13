import InterplayPaperLean.MainTheoremStatement.Kinetics
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace InterplayPaperLean

/-- A forward solution of `x' = Γ R(x)` on an interval containing time zero. -/
structure Trajectory {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions) where
  timeDomain : Set ℝ
  state : ℝ → (Fin species → ℝ)
  zero_mem : 0 ∈ timeDomain
  nonnegative_time : ∀ t ∈ timeDomain, 0 ≤ t
  interval_timeDomain : Set.OrdConnected timeDomain
  solves : ∀ t ∈ timeDomain,
    HasDerivWithinAt state (kinetics.vectorField network (state t)) timeDomain t

namespace Trajectory

def initial {species reactions : ℕ} {network : ReactionNetwork species reactions}
    {kinetics : Kinetics species reactions}
    (trajectory : Trajectory network kinetics) : Fin species → ℝ :=
  trajectory.state 0

def StaysIn {species reactions : ℕ} {network : ReactionNetwork species reactions}
    {kinetics : Kinetics species reactions}
    (trajectory : Trajectory network kinetics) (domain : Set (Fin species → ℝ)) : Prop :=
  ∀ t ∈ trajectory.timeDomain, trajectory.state t ∈ domain

end Trajectory

end InterplayPaperLean
