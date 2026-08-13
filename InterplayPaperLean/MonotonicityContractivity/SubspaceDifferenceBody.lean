import InterplayPaperLean.MonotonicityContractivity.DifferenceBodyNorm
import Mathlib.Analysis.Normed.Affine.AsymptoticCone
import Mathlib.Analysis.SpecificLimits.Basic

namespace InterplayPaperLean

open Set Topology
open scoped Topology

def sectionInSubspace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V) : Set S :=
  {s | b + (s : V) ∈ K}

def subspaceDifferenceBody {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V) : Set S :=
  DifferenceBody (sectionInSubspace K S b)

theorem sectionInSubspace_zero_mem {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) {b : V} (hb : b ∈ K) :
    (0 : S) ∈ sectionInSubspace K S b := by
  simpa [sectionInSubspace] using hb

theorem sectionInSubspace_convex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V) :
    Convex ℝ (sectionInSubspace K S b) := by
  intro x hx y hy a c ha hc hac
  change b + (a • x + c • y : S) ∈ K
  have heq : b + (a • x + c • y : S) =
      a • (b + (x : V)) + c • (b + (y : V)) := by
    simp only [Submodule.coe_add, Submodule.coe_smul]
    have hb : b = a • b + c • b := by
      calc
        b = (1 : ℝ) • b := by rw [one_smul]
        _ = (a + c) • b := by rw [hac]
        _ = a • b + c • b := add_smul a c b
    calc
      b + (a • (x : V) + c • (y : V)) =
          (a • b + c • b) + (a • (x : V) + c • (y : V)) :=
        congrArg (fun z => z + (a • (x : V) + c • (y : V))) hb
      _ = a • (b + (x : V)) + c • (b + (y : V)) := by module
  rw [heq]
  exact K.convex hx hy ha hc hac

theorem sectionInSubspace_isClosed {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V) :
    IsClosed (sectionInSubspace K S b) := by
  exact K.isClosed.preimage (continuous_const.add continuous_subtype_val)

theorem sectionInSubspace_isCompact_of_isBounded {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V)
    (hbounded : Bornology.IsBounded (sectionInSubspace K S b)) :
    IsCompact (sectionInSubspace K S b) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨sectionInSubspace_isClosed K S b, hbounded⟩

theorem sectionInSubspace_subset_differenceBody {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) {b : V} (hb : b ∈ K) :
    sectionInSubspace K S b ⊆ subspaceDifferenceBody K S b := by
  intro s hs
  exact ⟨s, hs, 0, sectionInSubspace_zero_mem K S hb, sub_zero s⟩

theorem subspaceDifferenceBody_mem_nhds_zero_of_section
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) {b : V} (hb : b ∈ K)
    (hsection : sectionInSubspace K S b ∈ nhds (0 : S)) :
    subspaceDifferenceBody K S b ∈ nhds (0 : S) :=
  Filter.mem_of_superset hsection (sectionInSubspace_subset_differenceBody K S hb)

theorem subspaceDifferenceBody_absorbent_of_section
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) {b : V} (hb : b ∈ K)
    (hsection : sectionInSubspace K S b ∈ nhds (0 : S)) :
    Absorbent ℝ (subspaceDifferenceBody K S b) :=
  absorbent_nhds_zero
    (subspaceDifferenceBody_mem_nhds_zero_of_section K S hb hsection)

/-- A point in the relative interior of the cone makes every linear slice
through that point, in a direction contained in the cone's span, a
neighborhood of the base point. -/
theorem sectionInSubspace_mem_nhds_zero_of_strictlyPositive
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) {b : V}
    (hb : K.StrictlyPositive b) (hS : S ≤ K.span) :
    sectionInSubspace K S b ∈ nhds (0 : S) := by
  obtain ⟨y, hy, hyb⟩ := (mem_intrinsicInterior.mp hb)
  let f : S → affineSpan ℝ (K : Set V) := fun s =>
    ⟨b + (s : V), by
      change b + (s : V) ∈ (affineSpan ℝ (K : Set V) : Set V)
      rw [K.affineSpan_eq_span]
      have hbspan : b ∈ K.span := Submodule.subset_span (intrinsicInterior_subset hb)
      exact K.span.add_mem hbspan (hS s.property)⟩
  have hf : Continuous f := by
    exact Continuous.subtype_mk (continuous_const.add continuous_subtype_val) _
  have hf0 : f 0 = y := by
    apply Subtype.ext
    simpa [f] using hyb.symm
  have hpre : ((↑) ⁻¹' (K : Set V) : Set (affineSpan ℝ (K : Set V))) ∈ nhds y :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
  have hpull : f ⁻¹' ((↑) ⁻¹' (K : Set V) :
      Set (affineSpan ℝ (K : Set V))) ∈ nhds (0 : S) := by
    have hmap : Filter.Tendsto f (nhds (0 : S)) (nhds (f 0)) := hf.continuousAt
    apply hmap
    rw [hf0]
    exact hpre
  have heq : f ⁻¹' ((↑) ⁻¹' (K : Set V) :
      Set (affineSpan ℝ (K : Set V))) = sectionInSubspace K S b := by
    ext s
    rfl
  rw [← heq]
  exact hpull

theorem subspaceDifferenceBody_absorbent_of_strictlyPositive
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) {b : V}
    (hb : K.StrictlyPositive b) (hS : S ≤ K.span) :
    Absorbent ℝ (subspaceDifferenceBody K S b) := by
  exact subspaceDifferenceBody_absorbent_of_section K S
    (intrinsicInterior_subset hb)
    (sectionInSubspace_mem_nhds_zero_of_strictlyPositive K S hb hS)

theorem sectionInSubspace_isBounded_of_pointedAlong
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) {b : V} (hb : b ∈ K)
    (hpointed : K.PointedAlong S) :
    Bornology.IsBounded (sectionInSubspace K S b) := by
  rw [isBounded_iff_asymptoticCone_subset_singleton]
  intro v hv
  have hzero : (0 : S) ∈ sectionInSubspace K S b :=
    sectionInSubspace_zero_mem K S hb
  have hray : ∀ c : ℝ, 0 ≤ c → c • v + (0 : S) ∈ sectionInSubspace K S b := by
    intro c hc
    exact (sectionInSubspace_convex K S b).smul_vadd_mem_of_isClosed_of_mem_asymptoticCone
      (sectionInSubspace_isClosed K S b) hc hv hzero
  have hseqK : ∀ n : ℕ, ((n + 1 : ℝ)⁻¹ • b + (v : V)) ∈ K := by
    intro n
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    have hs := hray (n + 1 : ℝ) hnpos.le
    simp only [add_zero] at hs
    change b + (((n + 1 : ℝ) • v : S) : V) ∈ K at hs
    have hscaled := K.toConvexCone.smul_mem (inv_pos.mpr hnpos) hs
    change ((n + 1 : ℝ)⁻¹ • b + (v : V)) ∈ K.toConvexCone
    simpa [smul_add, smul_smul, hnpos.ne'] using hscaled
  have hinv : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℝ)⁻¹))
      Filter.atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)
  have hlim : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℝ)⁻¹ • b + (v : V)))
      Filter.atTop (nhds (v : V)) := by
    simpa using (hinv.smul_const b).add tendsto_const_nhds
  have hvK : (v : V) ∈ K := K.isClosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hseqK)
  have hvinter : (v : V) ∈ (K : Set V) ∩ S := ⟨hvK, v.property⟩
  have hvzero : (v : V) = 0 := by
    rw [hpointed] at hvinter
    exact Set.mem_singleton_iff.mp hvinter
  exact Set.mem_singleton_iff.mpr (Subtype.ext hvzero)

theorem subspaceDifferenceBody_balanced {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V) :
    Balanced ℝ (subspaceDifferenceBody K S b) :=
  differenceBody_balanced (sectionInSubspace_convex K S b)

theorem subspaceDifferenceBody_convex {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V) :
    Convex ℝ (subspaceDifferenceBody K S b) :=
  DifferenceBody.convex (sectionInSubspace_convex K S b)

theorem subspaceDifferenceBody_isCompact_of_section_isBounded {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V)
    (hbounded : Bornology.IsBounded (sectionInSubspace K S b)) :
    IsCompact (subspaceDifferenceBody K S b) :=
  DifferenceBody.isCompact
    (sectionInSubspace_isCompact_of_isBounded K S b hbounded)

theorem subspaceDifferenceBody_isVonNBounded_of_section_isBounded {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V)
    (hbounded : Bornology.IsBounded (sectionInSubspace K S b)) :
    Bornology.IsVonNBounded ℝ (subspaceDifferenceBody K S b) :=
  (subspaceDifferenceBody_isCompact_of_section_isBounded K S b hbounded).isVonNBounded ℝ

/-- Once the section is known to be absorbent and bounded in `S`, its
difference body gives the canonical norm used in the bridge theorem. -/
noncomputable def subspaceSectionNorm {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V)
    (habsorbent : Absorbent ℝ (subspaceDifferenceBody K S b))
    (hbounded : Bornology.IsVonNBounded ℝ (subspaceDifferenceBody K S b)) :
    PaperNorm S :=
  paperNormOfGoodSet _ (subspaceDifferenceBody_balanced K S b)
    (subspaceDifferenceBody_convex K S b) habsorbent hbounded

/-- The section norm with all geometric side conditions discharged from the
paper's hypotheses. -/
noncomputable def subspaceSectionNormOfCone {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V)
    (hb : K.StrictlyPositive b) (hS : S ≤ K.span) (hpointed : K.PointedAlong S) :
    PaperNorm S :=
  subspaceSectionNorm K S b
    (subspaceDifferenceBody_absorbent_of_strictlyPositive K S hb hS)
    (subspaceDifferenceBody_isVonNBounded_of_section_isBounded K S b
      (sectionInSubspace_isBounded_of_pointedAlong K S
        (intrinsicInterior_subset hb) hpointed))

end InterplayPaperLean
