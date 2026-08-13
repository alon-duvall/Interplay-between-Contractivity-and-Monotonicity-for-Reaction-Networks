import InterplayPaperLean.MonotonicityContractivity.ExtendSubspaceNorm

namespace InterplayPaperLean

open Set

/-- A fixed-time map strictly improves every nontrivial order relation whose
endpoints lie in its domain. -/
def StrictlyOrderImprovingMapOn {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V → V) (domain : Set V) (K : ClosedConvexCone V) : Prop :=
  ∀ ⦃x z⦄, x ∈ domain → z ∈ domain → z - x ∈ K → x ≠ z →
    F z - F x ∈ intrinsicInterior ℝ (K : Set V)

/-- A fixed-time flow map preserves every affine translate of `S`. -/
def PreservesAffineSlices {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V → V) (domain : Set V) (S : Submodule ℝ V) : Prop :=
  ∀ ⦃x⦄, x ∈ domain → F x - x ∈ S

theorem ClosedConvexCone.smul_mem_intrinsicInterior {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ClosedConvexCone V) {c : ℝ} (hc : 0 < c) {v : V}
    (hv : v ∈ intrinsicInterior ℝ (K : Set V)) :
    c • v ∈ intrinsicInterior ℝ (K : Set V) := by
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
  have himage : e '' (K : Set V) = (K : Set V) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact K.toConvexCone.smul_mem hc hy
    · intro hx
      refine ⟨c⁻¹ • x, K.toConvexCone.smul_mem (inv_pos.mpr hc) hx, ?_⟩
      simp [e, hc.ne']
  change e.toContinuousAffineEquiv v ∈ intrinsicInterior ℝ (K : Set V)
  rw [← himage]
  change e.toContinuousAffineEquiv v ∈
    intrinsicInterior ℝ (e.toContinuousAffineEquiv '' (K : Set V))
  rw [e.toContinuousAffineEquiv.intrinsicInterior_image]
  exact ⟨v, hv, by simp [e]⟩

theorem PreservesAffineSlices.map_sub_sub_mem {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → V} {domain : Set V} {S : Submodule ℝ V}
    (hF : PreservesAffineSlices F domain S) {x y : V}
    (hx : x ∈ domain) (hy : y ∈ domain) :
    (F y - F x) - (y - x) ∈ S := by
  have hxS := hF hx
  have hyS := hF hy
  have heq : (F y - F x) - (y - x) = (F y - y) - (F x - x) := by module
  rw [heq]
  exact S.sub_mem hyS hxS

theorem PreservesAffineSlices.map_sub_mem {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → V} {domain : Set V} {S : Submodule ℝ V}
    (hF : PreservesAffineSlices F domain S) {x y : V}
    (hx : x ∈ domain) (hy : y ∈ domain) (hxy : y - x ∈ S) :
    F y - F x ∈ S := by
  have hchange := hF.map_sub_sub_mem hx hy
  have heq : F y - F x = ((F y - F x) - (y - x)) + (y - x) := by module
  rw [heq]
  exact S.add_mem hchange hxy

theorem normalized_difference_submodule_mem {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → V} {domain : Set V} {S : Submodule ℝ V}
    {b x z : V} {ε : ℝ} (hε : 0 < ε)
    (hx : x ∈ domain) (hz : z ∈ domain)
    (hFslice : PreservesAffineSlices F domain S)
    (hinitial : z - x - ε • b ∈ S) :
    ε⁻¹ • (F z - F x) - b ∈ S := by
  have hchange := hFslice.map_sub_sub_mem hx hz
  have hsum : (F z - F x) - ε • b ∈ S := by
    have heq : (F z - F x) - ε • b =
        ((F z - F x) - (z - x)) + ((z - x) - ε • b) := by module
    rw [heq]
    exact S.add_mem hchange hinitial
  have heq : ε⁻¹ • (F z - F x) - b = ε⁻¹ • ((F z - F x) - ε • b) := by
    calc
      ε⁻¹ • (F z - F x) - b =
          ε⁻¹ • (F z - F x) - (ε⁻¹ * ε) • b := by
            rw [inv_mul_cancel₀ hε.ne', one_smul]
      _ = ε⁻¹ • ((F z - F x) - ε • b) := by module
  rw [heq]
  exact S.smul_mem ε⁻¹ hsum

theorem section_normalization_after_map {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → V} {domain : Set V} {K : ClosedConvexCone V}
    {S : Submodule ℝ V} {b x z : V} {ε : ℝ}
    (hε : 0 < ε) (hx : x ∈ domain) (hz : z ∈ domain)
    (hFslice : PreservesAffineSlices F domain S)
    (hstrict : F z - F x ∈ intrinsicInterior ℝ (K : Set V))
    (hinitial : z - x - ε • b ∈ S) :
    ⟨ε⁻¹ • (F z - F x) - b,
      normalized_difference_submodule_mem hε hx hz hFslice hinitial⟩ ∈
      sectionInSubspace K S b := by
  change b + (ε⁻¹ • (F z - F x) - b) ∈ K
  have heq : b + (ε⁻¹ • (F z - F x) - b) = ε⁻¹ • (F z - F x) := by module
  rw [heq]
  exact K.toConvexCone.smul_mem (inv_pos.mpr hε)
    (intrinsicInterior_subset hstrict)

/-- The auxiliary-point step in the paper.  It isolates the only local-domain
obligation: the point `z = x + r(b+p)` must remain in the domain. -/
theorem strict_contraction_of_auxiliary_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {F : V → V} {domain : Set V} (K : ClosedConvexCone V)
    (S : Submodule ℝ V) (b : V)
    (hb : K.StrictlyPositive b) (hb0 : b ≠ 0) (hS : S ≤ K.span)
    (hpointed : K.PointedAlong S)
    (hstrict : StrictlyOrderImprovingMapOn F domain K)
    (hFslice : PreservesAffineSlices F domain S)
    {x y : V} (hx : x ∈ domain) (hy : y ∈ domain)
    (hxyS : y - x ∈ S) (hxy : x ≠ y)
    (haux : ∀ (p q : S),
      p ∈ sectionInSubspace K S b → q ∈ sectionInSubspace K S b →
      p - q = (subspaceSectionNormOfCone K S b hb hS hpointed
        ⟨y - x, hxyS⟩)⁻¹ • (⟨y - x, hxyS⟩ : S) →
      x + (subspaceSectionNormOfCone K S b hb hS hpointed
        ⟨y - x, hxyS⟩) • (b + (p : V)) ∈ domain) :
    subspaceSectionNormOfCone K S b hb hS hpointed
        ⟨F y - F x, by
          exact hFslice.map_sub_mem hx hy hxyS⟩ <
      subspaceSectionNormOfCone K S b hb hS hpointed ⟨y - x, hxyS⟩ := by
  let normS := subspaceSectionNormOfCone K S b hb hS hpointed
  let d : S := ⟨y - x, hxyS⟩
  have hd0 : d ≠ 0 := by
    intro hd
    have : y - x = 0 := congrArg Subtype.val hd
    exact hxy (sub_eq_zero.mp this).symm
  have hr0 : normS d ≠ 0 := fun hr => hd0 (normS.definite d hr)
  have hr : 0 < normS d := lt_of_le_of_ne (by positivity) hr0.symm
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    normalized_mem_subspaceDifferenceBody K S b hb hS hpointed hd0
  let z : V := x + normS d • (b + (p : V))
  have hz : z ∈ domain := haux p q hp hq hpq
  have hbK : b ∈ K := intrinsicInterior_subset hb
  have hpk : b + (p : V) ∈ K := hp
  have hqk : b + (q : V) ∈ K := hq
  have hpk0 : b + (p : V) ≠ 0 := by
    intro heq
    have hbS : b ∈ S := by
      have : b = -(p : V) := eq_neg_of_add_eq_zero_left heq
      rw [this]
      exact S.neg_mem p.property
    have hb_inter : b ∈ (K : Set V) ∩ S := ⟨hbK, hbS⟩
    rw [hpointed] at hb_inter
    exact hb0 (Set.mem_singleton_iff.mp hb_inter)
  have hqk0 : b + (q : V) ≠ 0 := by
    intro heq
    have hbS : b ∈ S := by
      have : b = -(q : V) := eq_neg_of_add_eq_zero_left heq
      rw [this]
      exact S.neg_mem q.property
    have hb_inter : b ∈ (K : Set V) ∩ S := ⟨hbK, hbS⟩
    rw [hpointed] at hb_inter
    exact hb0 (Set.mem_singleton_iff.mp hb_inter)
  have hzx : z - x = normS d • (b + (p : V)) := by
    simp [z]
  have hzy_eq : z = y + normS d • (b + (q : V)) := by
    have hpqV : (p : V) - (q : V) = (normS d)⁻¹ • (y - x) :=
      congrArg Subtype.val hpq
    have hdscale : y - x = normS d • ((p : V) - (q : V)) := by
      have h := congrArg (fun v : V => normS d • v) hpqV.symm
      simpa [smul_smul, hr0] using h
    have hyform : y = x + normS d • ((p : V) - (q : V)) := by
      simpa [add_comm] using eq_add_of_sub_eq hdscale
    rw [hyform]
    simp only [z]
    module
  have hzy : z - y = normS d • (b + (q : V)) := by
    rw [hzy_eq]
    simp
  have hzxK : z - x ∈ K := by
    rw [hzx]
    exact K.toConvexCone.smul_mem hr hpk
  have hzyK : z - y ∈ K := by
    rw [hzy]
    exact K.toConvexCone.smul_mem hr hqk
  have hxz : x ≠ z := by
    intro heq
    have hz0 : z - x = 0 := sub_eq_zero.mpr heq.symm
    rw [hzx] at hz0
    exact hpk0 (smul_eq_zero.mp hz0 |>.resolve_left hr0)
  have hyz : y ≠ z := by
    intro heq
    have hz0 : z - y = 0 := sub_eq_zero.mpr heq.symm
    rw [hzy] at hz0
    exact hqk0 (smul_eq_zero.mp hz0 |>.resolve_left hr0)
  have hFx := hstrict hx hz hzxK hxz
  have hFy := hstrict hy hz hzyK hyz
  let px : S := ⟨(normS d)⁻¹ • (F z - F x) - b,
    normalized_difference_submodule_mem hr hx hz hFslice (by
      rw [hzx]
      have hi : normS d • (b + (p : V)) - normS d • b = normS d • (p : V) := by module
      rw [hi]
      exact S.smul_mem (normS d) p.property)⟩
  let py : S := ⟨(normS d)⁻¹ • (F z - F y) - b,
    normalized_difference_submodule_mem hr hy hz hFslice (by
      rw [hzy]
      have hi : normS d • (b + (q : V)) - normS d • b = normS d • (q : V) := by module
      rw [hi]
      exact S.smul_mem (normS d) q.property)⟩
  have hpx : px ∈ interior (sectionInSubspace K S b) := by
    apply sectionInSubspace_mem_interior_of_add_strictlyPositive K S
      (Submodule.subset_span hbK) hS
    change b + ((normS d)⁻¹ • (F z - F x) - b) ∈ intrinsicInterior ℝ (K : Set V)
    have heq : b + ((normS d)⁻¹ • (F z - F x) - b) =
        (normS d)⁻¹ • (F z - F x) := by module
    rw [heq]
    exact K.smul_mem_intrinsicInterior (inv_pos.mpr hr) hFx
  have hpy : py ∈ sectionInSubspace K S b := by
    exact section_normalization_after_map hr hy hz hFslice hFy (by
      rw [hzy]
      have hi : normS d • (b + (q : V)) - normS d • b = normS d • (q : V) := by module
      rw [hi]
      exact S.smul_mem (normS d) q.property)
  have hdiffInterior : px - py ∈ interior (subspaceDifferenceBody K S b) :=
    DifferenceBody.sub_mem_interior hpx hpy
  have hlt : normS (px - py) < 1 := by
    exact paperNormOfGoodSet_lt_one_of_mem_interior
      (subspaceDifferenceBody K S b)
      (subspaceDifferenceBody_balanced K S b)
      (subspaceDifferenceBody_convex K S b)
      (subspaceDifferenceBody_absorbent_of_strictlyPositive K S hb hS)
      (subspaceDifferenceBody_isVonNBounded_of_section_isBounded K S b
        (sectionInSubspace_isBounded_of_pointedAlong K S hbK hpointed))
      hdiffInterior
  have hout : (⟨F y - F x, by
      exact hFslice.map_sub_mem hx hy hxyS⟩ : S) = normS d • (px - py) := by
    apply Subtype.ext
    have hcoord : ((px - py : S) : V) = (normS d)⁻¹ • (F y - F x) := by
      simp only [px, py, Submodule.coe_sub]
      module
    rw [Submodule.coe_smul, hcoord, smul_smul, mul_inv_cancel₀ hr0, one_smul]
  rw [hout]
  change normS.toSeminorm (normS d • (px - py)) < normS d
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
  simpa using (mul_lt_mul_of_pos_left hlt hr)

end InterplayPaperLean
