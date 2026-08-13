import InterplayPaperLean.MainTheoremStatement.Trajectories
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Seminorm

namespace InterplayPaperLean

/-- A norm represented without changing the ambient type's global norm
instance. `toSeminorm` supplies homogeneity and the triangle inequality, while
`definite` says that only zero has norm zero. -/
structure PaperNorm (V : Type*) [AddCommGroup V] [Module ℝ V] where
  toSeminorm : Seminorm ℝ V
  definite : ∀ v, toSeminorm v = 0 → v = 0

namespace PaperNorm

instance {V : Type*} [AddCommGroup V] [Module ℝ V] : CoeFun (PaperNorm V) (fun _ => V → ℝ) :=
  ⟨fun norm => norm.toSeminorm⟩

end PaperNorm

/-- A system is weakly contractive on `domain` if one norm makes the distance
between every pair of distinct forward solutions strictly decrease at every
two common times. -/
def WeaklyContractiveOn {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions)
    (domain : Set (Fin species → ℝ)) : Prop :=
  ∃ norm : PaperNorm (Fin species → ℝ),
    ∀ (x y : Trajectory network kinetics),
      x.StaysIn domain → y.StaysIn domain → x.initial ≠ y.initial →
      ∀ t₁, t₁ ∈ x.timeDomain → t₁ ∈ y.timeDomain →
      ∀ t₂, t₂ ∈ x.timeDomain → t₂ ∈ y.timeDomain →
        t₁ < t₂ → norm (x.state t₂ - y.state t₂) < norm (x.state t₁ - y.state t₁)

/-- The paper's definition: for every admissible kinetics, the dynamics on the
relative interior of every stoichiometric compatibility class are weakly
contractive with respect to some norm. -/
def IsWeaklyContractive {species reactions : ℕ}
    (network : ReactionNetwork species reactions) : Prop :=
  ∀ kinetics : Kinetics species reactions,
    kinetics.IsAdmissible network →
    ∀ x₀ ∈ ReactionNetwork.NonnegativeOrthant species,
      WeaklyContractiveOn network kinetics
        (intrinsicInterior ℝ (network.StoichiometricClass x₀))

end InterplayPaperLean
