import InterplayPaperLean.MonotonicityContractivity.AffineSlices

namespace InterplayPaperLean

/-- The autonomous evolution interface used by the paper's argument. It makes
existence, uniqueness, time shifting, and preservation of affine slices
explicit instead of appealing to them informally. -/
structure LocalEvolution {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions) where
  existsAt : (Fin species → ℝ) → ℝ → Prop
  evolve : ℝ → (Fin species → ℝ) → (Fin species → ℝ)
  isOpen_existsAt : IsOpen {p : (Fin species → ℝ) × ℝ | existsAt p.1 p.2}
  continuousOn_evolve : ContinuousOn (fun p : (Fin species → ℝ) × ℝ => evolve p.2 p.1)
    {p | existsAt p.1 p.2}
  exists_zero : ∀ x, existsAt x 0
  evolve_zero : ∀ x, evolve 0 x = x
  nonnegative_exists : ∀ {x t}, existsAt x t → 0 ≤ t
  interval_exists : ∀ x, Set.OrdConnected {t | existsAt x t}
  solves : ∀ x t, existsAt x t →
    HasDerivWithinAt (fun u => evolve u x)
      (kinetics.vectorField network (evolve t x)) {u | existsAt x u} t
  semigroup_exists : ∀ {x s t}, existsAt x s → existsAt x (s + t) →
    existsAt (evolve s x) t
  semigroup : ∀ {x s t}, existsAt x s → existsAt x (s + t) →
    evolve t (evolve s x) = evolve (s + t) x
  unique : ∀ (trajectory : Trajectory network kinetics) t,
    t ∈ trajectory.timeDomain → evolve t trajectory.initial = trajectory.state t

namespace LocalEvolution

theorem isOpen_initialsAt {species reactions : ℕ}
    {network : ReactionNetwork species reactions} {kinetics : Kinetics species reactions}
    (evolution : LocalEvolution network kinetics) (t : ℝ) :
    IsOpen {x | evolution.existsAt x t} := by
  have hcontinuous : Continuous (fun x : Fin species → ℝ => (x, t)) :=
    continuous_id.prodMk continuous_const
  exact evolution.isOpen_existsAt.preimage hcontinuous

theorem continuousOn_evolveAt {species reactions : ℕ}
    {network : ReactionNetwork species reactions} {kinetics : Kinetics species reactions}
    (evolution : LocalEvolution network kinetics) (t : ℝ) :
    ContinuousOn (evolution.evolve t) {x | evolution.existsAt x t} := by
  intro x hx
  have hg : ContinuousAt (fun z : Fin species → ℝ => (z, t)) x :=
    continuousAt_id.prodMk continuousAt_const
  have hg' : ContinuousWithinAt (fun z : Fin species → ℝ => (z, t))
      {z | evolution.existsAt z t} x := hg.continuousWithinAt
  have hm : Set.MapsTo (fun z : Fin species → ℝ => (z, t))
      {z | evolution.existsAt z t} {p | evolution.existsAt p.1 p.2} := by
    intro z hz
    exact hz
  simpa [Function.comp_def] using
    (ContinuousWithinAt.comp (f := fun z : Fin species → ℝ => (z, t))
      (evolution.continuousOn_evolve (x, t) hx) hg' hm)

def orbit {species reactions : ℕ} {network : ReactionNetwork species reactions}
    {kinetics : Kinetics species reactions} (evolution : LocalEvolution network kinetics)
    (x : Fin species → ℝ) : Trajectory network kinetics where
  timeDomain := {t | evolution.existsAt x t}
  state t := evolution.evolve t x
  zero_mem := evolution.exists_zero x
  nonnegative_time _ ht := evolution.nonnegative_exists ht
  interval_timeDomain := evolution.interval_exists x
  solves t ht := evolution.solves x t ht

@[simp] theorem orbit_initial {species reactions : ℕ}
    {network : ReactionNetwork species reactions} {kinetics : Kinetics species reactions}
    (evolution : LocalEvolution network kinetics) (x : Fin species → ℝ) :
    (evolution.orbit x).initial = x := evolution.evolve_zero x

theorem trajectory_eq_evolve {species reactions : ℕ}
    {network : ReactionNetwork species reactions} {kinetics : Kinetics species reactions}
    (evolution : LocalEvolution network kinetics) (trajectory : Trajectory network kinetics)
    {t : ℝ} (ht : t ∈ trajectory.timeDomain) :
    evolution.evolve t trajectory.initial = trajectory.state t :=
  evolution.unique trajectory t ht

end LocalEvolution

end InterplayPaperLean
