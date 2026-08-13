import InterplayPaperLean.MonotonicityContractivity.LocalToGlobal

namespace InterplayPaperLean

open Set

/-- Fixed-time form of the paper's strong-monotonicity-to-contractivity
theorem.  One cone-derived norm works simultaneously on every affine
`S`-class contained in the open convex phase domain. -/
theorem stronglyMonotoneMap_strictlyContractsOnClass {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {F : V → V} {domain : Set V} (hdomainOpen : IsOpen domain)
    (hdomainConvex : Convex ℝ domain)
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V)
    (hb : K.StrictlyPositive b) (hb0 : b ≠ 0) (hS : S ≤ K.span)
    (hpointed : K.PointedAlong S)
    (hstrict : StrictlyOrderImprovingMapOn F domain K)
    (hFslice : PreservesAffineSlices F domain S)
    {x y : V} (hx : x ∈ domain) (hy : y ∈ domain)
    (hxyS : y - x ∈ S) (hxy : x ≠ y) :
    let norm := extendSubspacePaperNorm S
      (subspaceSectionNormOfCone K S b hb hS hpointed)
    norm (F y - F x) < norm (y - x) := by
  let normS := subspaceSectionNormOfCone K S b hb hS hpointed
  let norm := extendSubspacePaperNorm S normS
  let d : S := ⟨y - x, hxyS⟩
  have hd : d ≠ 0 := by
    intro hd0
    have : y - x = 0 := congrArg Subtype.val hd0
    exact hxy (sub_eq_zero.mp this).symm
  let G : S → V := fun u => F (x + (u : V))
  have hsegmentDomain : ∀ w ∈ segment ℝ (0 : S) d,
      x + (w : V) ∈ domain := by
    intro w hw
    rcases hw with ⟨a, c, ha, hc, hac, hw⟩
    have hxd : x + (d : V) = y := by
      change x + (y - x) = y
      module
    simp only [smul_zero, zero_add] at hw
    have hwV := congrArg Subtype.val hw
    change c • (d : V) = (w : V) at hwV
    have heq : x + (w : V) = a • x + c • y := by
      calc
        x + (w : V) = x + c • (d : V) := by rw [hwV]
        _ = (a + c) • x + c • (d : V) := by rw [hac, one_smul]
        _ = a • x + c • (x + (d : V)) := by module
        _ = a • x + c • y := by rw [hxd]
    rw [heq]
    exact hdomainConvex hx hy ha hc hac
  have hlocal : ∀ w ∈ segment ℝ (0 : S) d,
      ∃ U : Set S, IsOpen U ∧ w ∈ U ∧
        ∀ a ∈ U, ∀ c ∈ U, a ≠ c →
          norm (G c - G a) < norm (S.subtype (c - a)) := by
    intro w hw
    have hxw : x + (w : V) ∈ domain := hsegmentDomain w hw
    obtain ⟨U₀, hU₀open, h0U₀, hU₀strict⟩ :=
      exists_pairwise_strict_neighborhood hdomainOpen K S b hb hb0 hS
        hpointed hstrict hFslice hxw
    let U : Set S := {a | a - w ∈ U₀}
    have hUopen : IsOpen U := hU₀open.preimage (continuous_id.sub continuous_const)
    have hwU : w ∈ U := by simpa [U] using h0U₀
    refine ⟨U, hUopen, hwU, ?_⟩
    intro a ha c hc hac
    have haw : a - w ∈ U₀ := ha
    have hcw : c - w ∈ U₀ := hc
    have hne : a - w ≠ c - w := by
      intro heq
      exact hac (sub_left_injective heq)
    have hloc := hU₀strict (a - w) haw (c - w) hcw hne
    change norm (F (x + (c : V)) - F (x + (a : V))) <
      norm (S.subtype (c - a))
    have hbaseA : (x + (w : V)) + ((a - w : S) : V) = x + (a : V) := by
      simp
    have hbaseC : (x + (w : V)) + ((c - w : S) : V) = x + (c : V) := by
      simp
    have hdiff : (((c - w : S) : V) - ((a - w : S) : V)) =
        (S.subtype (c - a) : V) := by simp
    simpa only [hbaseA, hbaseC, hdiff] using hloc
  have hglobal := local_strict_contraction_on_segment norm S.subtype G hd hlocal
  change norm (F y - F x) < norm (y - x)
  have hGd : G d = F y := by
    change F (x + (d : V)) = F y
    congr 1
    change x + (y - x) = y
    module
  have hG0 : G 0 = F x := by simp [G]
  have hιd : S.subtype d = y - x := rfl
  simpa only [hGd, hG0, hιd] using hglobal

end InterplayPaperLean
