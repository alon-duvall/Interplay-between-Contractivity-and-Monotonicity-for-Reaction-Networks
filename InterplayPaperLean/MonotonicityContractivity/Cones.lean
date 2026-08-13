import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Geometry.Convex.Cone.Basic

namespace InterplayPaperLean

/-- The paper uses closed convex cones. Nonemptiness is recorded explicitly
because `ConvexCone` itself permits the empty cone. -/
structure ClosedConvexCone (V : Type*) [AddCommMonoid V] [Module ℝ V]
    [TopologicalSpace V] where
  toConvexCone : ConvexCone ℝ V
  zero_mem : (0 : V) ∈ toConvexCone
  isClosed : IsClosed (toConvexCone : Set V)

namespace ClosedConvexCone

instance {V : Type*} [AddCommMonoid V] [Module ℝ V] [TopologicalSpace V] :
    SetLike (ClosedConvexCone V) V where
  coe K := K.toConvexCone
  coe_injective K L h := by
    cases K
    cases L
    simp_all

theorem convex {V : Type*} [AddCommMonoid V] [Module ℝ V] [TopologicalSpace V]
    (K : ClosedConvexCone V) : Convex ℝ (K : Set V) :=
  K.toConvexCone.convex

def span {V : Type*} [AddCommMonoid V] [Module ℝ V] [TopologicalSpace V]
    (K : ClosedConvexCone V) : Submodule ℝ V :=
  Submodule.span ℝ (K : Set V)

theorem affineSpan_eq_span {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) :
    (affineSpan ℝ (K : Set V) : Set V) = K.span := by
  change (affineSpan ℝ (K : Set V) : Set V) = Submodule.span ℝ (K : Set V)
  have hins : Set.insert (0 : V) (K : Set V) = (K : Set V) :=
    Set.insert_eq_of_mem K.zero_mem
  calc
    (affineSpan ℝ (K : Set V) : Set V) =
        (affineSpan ℝ (Set.insert 0 (K : Set V)) : Set V) := by
      rw [hins]
    _ = Submodule.span ℝ (K : Set V) := affineSpan_insert_zero _

def PointedAlong {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) : Prop :=
  (K : Set V) ∩ S = {0}

def StrictlyPositive {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (v : V) : Prop :=
  v ∈ intrinsicInterior ℝ (K : Set V)

end ClosedConvexCone

end InterplayPaperLean
