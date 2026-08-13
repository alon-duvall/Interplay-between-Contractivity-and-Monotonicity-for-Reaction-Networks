import InterplayPaperLean.MainTheoremStatement.WeakContractivity
import InterplayPaperLean.MonotonicityContractivity.Cones

namespace InterplayPaperLean

def ConeLE {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (K : ClosedConvexCone V) (x y : V) : Prop :=
  y - x ∈ K

/-- Strict order improvement, stated directly between any two common times.
This incorporates the ordinary monotonicity needed by the paper's proof and
also supports the time-shift step required by weak contractivity. -/
def StrictlyOrderImprovingOn {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions)
    (domain : Set (Fin species → ℝ))
    (K : ClosedConvexCone (Fin species → ℝ)) : Prop :=
  ∀ (x y : Trajectory network kinetics),
    x.StaysIn domain → y.StaysIn domain →
    ∀ t₁, t₁ ∈ x.timeDomain → t₁ ∈ y.timeDomain →
    ∀ t₂, t₂ ∈ x.timeDomain → t₂ ∈ y.timeDomain → t₁ < t₂ →
      ConeLE K (x.state t₁) (y.state t₁) → x.state t₁ ≠ y.state t₁ →
      y.state t₂ - x.state t₂ ∈ intrinsicInterior ℝ (K : Set (Fin species → ℝ))

def MonotoneOn {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions)
    (domain : Set (Fin species → ℝ))
    (K : ClosedConvexCone (Fin species → ℝ)) : Prop :=
  ∀ (x y : Trajectory network kinetics),
    x.StaysIn domain → y.StaysIn domain →
    ∀ t₁, t₁ ∈ x.timeDomain → t₁ ∈ y.timeDomain →
    ∀ t₂, t₂ ∈ x.timeDomain → t₂ ∈ y.timeDomain → t₁ ≤ t₂ →
      ConeLE K (x.state t₁) (y.state t₁) → ConeLE K (x.state t₂) (y.state t₂)

end InterplayPaperLean
