import InterplayPaperLean.MainTheoremStatement.Trajectories
import InterplayPaperLean.ReactionNetworks.KineticsLemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace InterplayPaperLean.Trajectory

/-- Every velocity of a reaction-network trajectory is tangent to the
stoichiometric subspace. This is the local ingredient for compatibility-class
invariance. -/
theorem derivative_mem_stoichiometricSubspace {species reactions : ℕ}
    {network : ReactionNetwork species reactions}
    {kinetics : Kinetics species reactions}
    (trajectory : Trajectory network kinetics) {t : ℝ} (_ht : t ∈ trajectory.timeDomain) :
    kinetics.vectorField network (trajectory.state t) ∈ network.StoichiometricSubspace :=
  kinetics.vectorField_mem_stoichiometricSubspace network (trajectory.state t)

theorem initial_state {species reactions : ℕ}
    {network : ReactionNetwork species reactions}
    {kinetics : Kinetics species reactions}
    (trajectory : Trajectory network kinetics) : trajectory.state 0 = trajectory.initial := rfl

/-- A trajectory remains in the affine translate of the stoichiometric
subspace determined by its initial state. -/
theorem state_sub_initial_mem_stoichiometricSubspace {species reactions : ℕ}
    {network : ReactionNetwork species reactions}
    {kinetics : Kinetics species reactions}
    (trajectory : Trajectory network kinetics) {t : ℝ} (ht : t ∈ trajectory.timeDomain) :
    trajectory.state t - trajectory.initial ∈ network.StoichiometricSubspace := by
  let S := network.StoichiometricSubspace
  change trajectory.state t - trajectory.state 0 ∈ S
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
  intro φ hφ
  let cφ : (Fin species → ℝ) →L[ℝ] ℝ :=
    ⟨φ, φ.continuous_of_finiteDimensional⟩
  let scalarTrajectory : ℝ → ℝ := cφ ∘ trajectory.state
  have hle := trajectory.interval_timeDomain.convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) (f := scalarTrajectory) (fun u hu => by
      have hc : HasFDerivAt cφ cφ (trajectory.state u) := cφ.hasFDerivAt
      have hcomp := hc.comp_hasDerivWithinAt u (trajectory.solves u hu)
      have hv : kinetics.vectorField network (trajectory.state u) ∈ S :=
        kinetics.vectorField_mem_stoichiometricSubspace network (trajectory.state u)
      have hzero : cφ (kinetics.vectorField network (trajectory.state u)) = 0 :=
        (S.mem_dualAnnihilator φ).mp hφ _ hv
      rw [hzero] at hcomp
      exact hcomp) (fun _ _ => by simp) ht trajectory.zero_mem
  have hzero : ‖scalarTrajectory 0 - scalarTrajectory t‖ = 0 :=
    le_antisymm (by simpa using hle) (norm_nonneg _)
  have hconst : scalarTrajectory t = scalarTrajectory 0 := by
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  change φ (trajectory.state t - trajectory.state 0) = 0
  rw [map_sub]
  change scalarTrajectory t - scalarTrajectory 0 = 0
  rw [hconst, sub_self]

/-- A nonnegative trajectory stays in the stoichiometric compatibility class
of its initial state. -/
theorem staysIn_stoichiometricClass {species reactions : ℕ}
    {network : ReactionNetwork species reactions}
    {kinetics : Kinetics species reactions}
    (trajectory : Trajectory network kinetics)
    (hnonnegative : trajectory.StaysIn (ReactionNetwork.NonnegativeOrthant species)) :
    trajectory.StaysIn (network.StoichiometricClass trajectory.initial) := by
  intro t ht
  rw [network.mem_stoichiometricClass_iff]
  exact ⟨hnonnegative t ht, trajectory.state_sub_initial_mem_stoichiometricSubspace ht⟩

end InterplayPaperLean.Trajectory
