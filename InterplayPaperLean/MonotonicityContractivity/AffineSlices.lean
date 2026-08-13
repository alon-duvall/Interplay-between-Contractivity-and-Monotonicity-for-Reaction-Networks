import InterplayPaperLean.MonotonicityContractivity.MonotoneSystems

namespace InterplayPaperLean

def AffineSlice {species : ℕ} (S : Submodule ℝ (Fin species → ℝ))
    (a : Fin species → ℝ) : Set (Fin species → ℝ) :=
  ReactionNetwork.NonnegativeOrthant species ∩ {x | x - a ∈ S}

def ForwardInvariantOnSlices {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions)
    (S : Submodule ℝ (Fin species → ℝ)) : Prop :=
  ∀ (trajectory : Trajectory network kinetics) (a),
    trajectory.initial ∈ AffineSlice S a → trajectory.StaysIn (AffineSlice S a)

end InterplayPaperLean
