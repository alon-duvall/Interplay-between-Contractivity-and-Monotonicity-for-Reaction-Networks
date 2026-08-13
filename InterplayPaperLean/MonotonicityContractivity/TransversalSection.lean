import InterplayPaperLean.MonotonicityContractivity.AffineSlices
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

namespace InterplayPaperLean

open Set Pointwise

def TransversalSection {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V) : Set V :=
  (K : Set V) ∩ {x | x - b ∈ S}

def DifferenceBody {V : Type*} [AddCommGroup V]
    (P : Set V) : Set V := P - P

namespace TransversalSection

theorem base_mem {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) {b : V} (hb : b ∈ K) :
    b ∈ TransversalSection K S b := by
  exact ⟨hb, by simp⟩

theorem nonempty {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) {b : V} (hb : b ∈ K) :
    (TransversalSection K S b).Nonempty :=
  ⟨b, base_mem K S hb⟩

theorem subset_affineTranslate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V) :
    TransversalSection K S b ⊆ {x | x - b ∈ S} :=
  inter_subset_right

theorem convex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V) :
    Convex ℝ (TransversalSection K S b) := by
  apply K.convex.inter
  intro x hx y hy a c ha hc hac
  change a • x + c • y - b ∈ S
  have hcalc : a • x + c • y - b = a • (x - b) + c • (y - b) := by
    calc
      a • x + c • y - b = a • x + c • y - (a + c) • b := by rw [hac, one_smul]
      _ = a • (x - b) + c • (y - b) := by module
  rw [hcalc]
  exact S.add_mem (S.smul_mem a hx) (S.smul_mem c hy)

theorem isClosed {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) [FiniteDimensional ℝ V] (b : V) :
    IsClosed (TransversalSection K S b) := by
  apply K.isClosed.inter
  exact S.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)

end TransversalSection

namespace DifferenceBody

theorem zero_mem {V : Type*} [AddCommGroup V] {P : Set V} (hP : P.Nonempty) :
    (0 : V) ∈ DifferenceBody P := by
  obtain ⟨p, hp⟩ := hP
  exact ⟨p, hp, p, hp, sub_self p⟩

theorem neg_mem {V : Type*} [AddCommGroup V] {P : Set V} {x : V}
    (hx : x ∈ DifferenceBody P) : -x ∈ DifferenceBody P := by
  rcases hx with ⟨p, hp, q, hq, rfl⟩
  exact ⟨q, hq, p, hp, (neg_sub p q).symm⟩

theorem symmetric {V : Type*} [AddCommGroup V] (P : Set V) :
    (DifferenceBody P : Set V) = -DifferenceBody P := by
  ext x
  constructor
  · intro hx
    simpa only [mem_neg] using neg_mem hx
  · intro hx
    simpa only [mem_neg, neg_neg] using neg_mem hx

theorem convex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P : Set V} (hP : Convex ℝ P) : Convex ℝ (DifferenceBody P) :=
  hP.sub hP

theorem sub_mem_interior {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P : Set V} {p q : V} (hp : p ∈ interior P) (hq : q ∈ P) :
    p - q ∈ interior (DifferenceBody P) := by
  apply subset_interior_sub_left
  exact ⟨p, hp, q, hq, rfl⟩

theorem isCompact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P : Set V} (hP : IsCompact P) : IsCompact (DifferenceBody P) := by
  have hc : IsCompact ((fun z : V × V => z.1 - z.2) '' (P ×ˢ P)) :=
    (hP.prod hP).image (continuous_fst.sub continuous_snd)
  convert hc using 1
  ext x
  simp [DifferenceBody]

end DifferenceBody

end InterplayPaperLean
