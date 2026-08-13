import InterplayPaperLean.MonotonicityContractivity.Theorem36
import InterplayPaperLean.MonotonicityContractivity.Evolution

namespace InterplayPaperLean

open Set

/-- Flow form of Theorem 3.6.  Strong order improvement for every positive
elapsed-time map yields weak contractivity between every two common times on
each affine compatibility class. -/
theorem stronglyMonotoneEvolution_weaklyContractiveOn
    {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions)
    (evolution : LocalEvolution network kinetics)
    (phaseDomain classDomain : Set (Fin species → ℝ))
    (hphaseOpen : IsOpen phaseDomain) (hphaseConvex : Convex ℝ phaseDomain)
    (hclassPhase : classDomain ⊆ phaseDomain)
    (S : Submodule ℝ (Fin species → ℝ))
    (hclassS : ∀ ⦃x⦄, x ∈ classDomain → ∀ ⦃y⦄, y ∈ classDomain → y - x ∈ S)
    (K : ClosedConvexCone (Fin species → ℝ)) (b : Fin species → ℝ)
    (hb : K.StrictlyPositive b) (hb0 : b ≠ 0) (hS : S ≤ K.span)
    (hpointed : K.PointedAlong S)
    (hstrict : ∀ τ, 0 < τ →
      StrictlyOrderImprovingMapOn (evolution.evolve τ) phaseDomain K)
    (hslices : ∀ τ, 0 < τ →
      PreservesAffineSlices (evolution.evolve τ) phaseDomain S) :
    WeaklyContractiveOn network kinetics classDomain := by
  let normS := subspaceSectionNormOfCone K S b hb hS hpointed
  let norm := extendSubspacePaperNorm S normS
  refine ⟨norm, ?_⟩
  intro x y hxstay hystay hinitial t₁ hxt₁ hyt₁ t₂ hxt₂ hyt₂ ht
  let Δ := t₂ - t₁
  have hΔ : 0 < Δ := sub_pos.mpr ht
  have hxt₁phase : x.state t₁ ∈ phaseDomain :=
    hclassPhase (hxstay t₁ hxt₁)
  have hyt₁phase : y.state t₁ ∈ phaseDomain :=
    hclassPhase (hystay t₁ hyt₁)
  have hdiffS : y.state t₁ - x.state t₁ ∈ S :=
    hclassS (hxstay t₁ hxt₁) (hystay t₁ hyt₁)
  have hdistinct : x.state t₁ ≠ y.state t₁ := by
    intro heq
    have hxExists := evolution.trajectory_exists x t₁ hxt₁
    have hyExists := evolution.trajectory_exists y t₁ hyt₁
    apply hinitial
    apply evolution.injective hxExists hyExists
    rw [evolution.trajectory_eq_evolve x hxt₁,
      evolution.trajectory_eq_evolve y hyt₁]
    exact heq
  have hfixed := stronglyMonotoneMap_strictlyContractsOnClass
    hphaseOpen hphaseConvex K S b hb hb0 hS hpointed
    (hstrict Δ hΔ) (hslices Δ hΔ)
    hyt₁phase hxt₁phase (by simpa only [neg_sub] using S.neg_mem hdiffS) hdistinct.symm
  have hxShift : evolution.evolve Δ (x.state t₁) = x.state t₂ := by
    have ht₁Exists := evolution.trajectory_exists x t₁ hxt₁
    have ht₂Exists := evolution.trajectory_exists x t₂ hxt₂
    calc
      evolution.evolve Δ (x.state t₁) =
          evolution.evolve Δ (evolution.evolve t₁ x.initial) := by
            rw [evolution.trajectory_eq_evolve x hxt₁]
      _ = evolution.evolve (t₁ + Δ) x.initial :=
        evolution.semigroup ht₁Exists (by simpa [Δ] using ht₂Exists)
      _ = evolution.evolve t₂ x.initial := by congr 2 <;> simp [Δ]
      _ = x.state t₂ := evolution.trajectory_eq_evolve x hxt₂
  have hyShift : evolution.evolve Δ (y.state t₁) = y.state t₂ := by
    have ht₁Exists := evolution.trajectory_exists y t₁ hyt₁
    have ht₂Exists := evolution.trajectory_exists y t₂ hyt₂
    calc
      evolution.evolve Δ (y.state t₁) =
          evolution.evolve Δ (evolution.evolve t₁ y.initial) := by
            rw [evolution.trajectory_eq_evolve y hyt₁]
      _ = evolution.evolve (t₁ + Δ) y.initial :=
        evolution.semigroup ht₁Exists (by simpa [Δ] using ht₂Exists)
      _ = evolution.evolve t₂ y.initial := by congr 2 <;> simp [Δ]
      _ = y.state t₂ := evolution.trajectory_eq_evolve y hyt₂
  simpa only [norm, normS, hxShift, hyShift] using hfixed

end InterplayPaperLean
