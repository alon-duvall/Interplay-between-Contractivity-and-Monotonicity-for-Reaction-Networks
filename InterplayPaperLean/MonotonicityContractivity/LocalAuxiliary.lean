import InterplayPaperLean.MonotonicityContractivity.StrongMonotoneMap
import Mathlib.Topology.Compactness.Compact

namespace InterplayPaperLean

open Set Topology

/-- Openness of the phase domain and compactness of the transversal section
give a single scalar neighborhood on which every auxiliary point used by the
paper remains in the domain. -/
theorem exists_scalar_nhds_auxiliary {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {domain : Set V} (hdomain : IsOpen domain)
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V)
    (hb : b ∈ K) (hpointed : K.PointedAlong S) {x : V} (hx : x ∈ domain) :
    ∃ R : Set ℝ, IsOpen R ∧ 0 ∈ R ∧
      ∀ r ∈ R, ∀ p ∈ sectionInSubspace K S b,
        x + r • (b + (p : V)) ∈ domain := by
  let n : Set (ℝ × S) :=
    {(rp : ℝ × S) | x + rp.1 • (b + (rp.2 : V)) ∈ domain}
  have hn : IsOpen n := by
    exact hdomain.preimage (by fun_prop)
  have hsectionClosed := sectionInSubspace_isClosed K S b
  have hsectionBounded := sectionInSubspace_isBounded_of_pointedAlong K S
    hb hpointed
  have hsectionCompact : IsCompact (sectionInSubspace K S b) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hsectionClosed, hsectionBounded⟩
  have hprod : ({(0 : ℝ)} ×ˢ sectionInSubspace K S b) ⊆ n := by
    rintro ⟨r, p⟩ ⟨hr, hp⟩
    simp only [mem_singleton_iff] at hr
    subst r
    simpa [n] using hx
  obtain ⟨R, Q, hRopen, hQopen, h0R, hsectionQ, hRQ⟩ :=
    generalized_tube_lemma (isCompact_singleton : IsCompact ({(0 : ℝ)} : Set ℝ))
      hsectionCompact hn hprod
  refine ⟨R, hRopen, h0R (mem_singleton 0), ?_⟩
  intro r hr p hp
  have hpQ : p ∈ Q := hsectionQ hp
  have hrp : (r, p) ∈ R ×ˢ Q := ⟨hr, hpQ⟩
  exact hRQ hrp

theorem exists_base_scalar_nhds_auxiliary {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {domain : Set V} (hdomain : IsOpen domain)
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V)
    (hb : b ∈ K) (hpointed : K.PointedAlong S) {x : V} (hx : x ∈ domain) :
    ∃ A : Set V, ∃ R : Set ℝ, IsOpen A ∧ IsOpen R ∧ x ∈ A ∧ 0 ∈ R ∧
      ∀ a ∈ A, ∀ r ∈ R, ∀ p ∈ sectionInSubspace K S b,
        a + r • (b + (p : V)) ∈ domain := by
  let n : Set ((V × ℝ) × S) :=
    {arp | arp.1.1 + arp.1.2 • (b + (arp.2 : V)) ∈ domain}
  have hn : IsOpen n := hdomain.preimage (by fun_prop)
  have hP : IsCompact (sectionInSubspace K S b) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨sectionInSubspace_isClosed K S b,
       sectionInSubspace_isBounded_of_pointedAlong K S hb hpointed⟩
  have hprod : ({(x, (0 : ℝ))} ×ˢ sectionInSubspace K S b) ⊆ n := by
    rintro ⟨ar, p⟩ ⟨har, hp⟩
    simp only [mem_singleton_iff] at har
    subst ar
    simpa [n] using hx
  obtain ⟨W, Q, hWopen, hQopen, hx0W, hPQ, hWQ⟩ :=
    generalized_tube_lemma
      (isCompact_singleton : IsCompact ({(x, (0 : ℝ))} : Set (V × ℝ)))
      hP hn hprod
  have hx0 : ({x} ×ˢ {(0 : ℝ)}) ⊆ W := by
    rintro ⟨a, r⟩ ⟨ha, hr⟩
    simp only [mem_singleton_iff] at ha hr
    subst a
    subst r
    exact hx0W (mem_singleton (x, (0 : ℝ)))
  obtain ⟨A, R, hAopen, hRopen, hxA, h0R, hAR⟩ :=
    generalized_tube_lemma
      (isCompact_singleton : IsCompact ({x} : Set V))
      (isCompact_singleton : IsCompact ({(0 : ℝ)} : Set ℝ))
      hWopen hx0
  refine ⟨A, R, hAopen, hRopen, hxA (mem_singleton x),
    h0R (mem_singleton 0), ?_⟩
  intro a ha r hr p hp
  have har : (a, r) ∈ W := hAR ⟨ha, hr⟩
  have hpQ : p ∈ Q := hPQ hp
  have harp : ((a, r), p) ∈ W ×ˢ Q := ⟨har, hpQ⟩
  exact hWQ harp

/-- Around every point of an open phase domain there is a relative
neighborhood in the affine `S`-slice on which the fixed-time map strictly
contracts every pair. -/
theorem exists_pairwise_strict_neighborhood {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {F : V → V} {domain : Set V} (hdomain : IsOpen domain)
    (K : ClosedConvexCone V) (S : Submodule ℝ V) (b : V)
    (hb : K.StrictlyPositive b) (hb0 : b ≠ 0) (hS : S ≤ K.span)
    (hpointed : K.PointedAlong S)
    (hstrict : StrictlyOrderImprovingMapOn F domain K)
    (hFslice : PreservesAffineSlices F domain S)
    {x : V} (hx : x ∈ domain) :
    ∃ U : Set S, IsOpen U ∧ 0 ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
        extendSubspacePaperNorm S
            (subspaceSectionNormOfCone K S b hb hS hpointed)
            (F (x + (v : V)) - F (x + (u : V))) <
          extendSubspacePaperNorm S
            (subspaceSectionNormOfCone K S b hb hS hpointed)
            ((v : V) - (u : V)) := by
  obtain ⟨A, R, hAopen, hRopen, hxA, h0R, hauxUniform⟩ :=
    exists_base_scalar_nhds_auxiliary hdomain K S b
      (intrinsicInterior_subset hb) hpointed hx
  let A' : Set V := A ∩ domain
  have hA'open : IsOpen A' := hAopen.inter hdomain
  have hxA' : x ∈ A' := ⟨hxA, hx⟩
  let W : Set (S × S) := {(uv : S × S) |
    subspaceSectionNormOfCone K S b hb hS hpointed (uv.2 - uv.1) ∈ R}
  have hWopen : IsOpen W := hRopen.preimage (by
    exact (continuous_subspaceSectionNormOfCone K S b hb hS hpointed).comp
      (continuous_snd.sub continuous_fst))
  have h00W : ((0 : S), (0 : S)) ∈ W := by
    simpa [W] using h0R
  obtain ⟨U₁, U₂, hU₁open, hU₂open, h0U₁, h0U₂, hprodW⟩ :=
    generalized_tube_lemma
      (isCompact_singleton : IsCompact ({(0 : S)} : Set S))
      (isCompact_singleton : IsCompact ({(0 : S)} : Set S))
      hWopen (by
        rintro ⟨u, v⟩ ⟨hu, hv⟩
        simp only [mem_singleton_iff] at hu hv
        subst u
        subst v
        exact h00W)
  let Ubase : Set S := (fun u : S => x + (u : V)) ⁻¹' A'
  have hUbaseOpen : IsOpen Ubase := hA'open.preimage
    (continuous_const.add continuous_subtype_val)
  have h0Ubase : (0 : S) ∈ Ubase := by simpa [Ubase] using hxA'
  let U := U₁ ∩ U₂ ∩ Ubase
  refine ⟨U, (hU₁open.inter hU₂open).inter hUbaseOpen,
    ⟨⟨h0U₁ (mem_singleton 0), h0U₂ (mem_singleton 0)⟩, h0Ubase⟩, ?_⟩
  intro u hu v hv huv
  have hu₁ : u ∈ U₁ := hu.1.1
  have hu₂ : u ∈ U₂ := hu.1.2
  have hv₁ : v ∈ U₁ := hv.1.1
  have hv₂ : v ∈ U₂ := hv.1.2
  have huBase : x + (u : V) ∈ A' := hu.2
  have hvBase : x + (v : V) ∈ A' := hv.2
  have hnormR : subspaceSectionNormOfCone K S b hb hS hpointed (v - u) ∈ R := by
    have huvProd : (u, v) ∈ U₁ ×ˢ U₂ := ⟨hu₁, hv₂⟩
    exact hprodW huvProd
  have hxy : x + (u : V) ≠ x + (v : V) := by
    intro heq
    apply huv
    apply Subtype.ext
    exact add_left_cancel heq
  have hdiff : (x + (v : V)) - (x + (u : V)) ∈ S := by
    have heq : (x + (v : V)) - (x + (u : V)) = (v : V) - (u : V) := by module
    rw [heq]
    exact S.sub_mem v.property u.property
  have hdEq : (⟨(x + (v : V)) - (x + (u : V)), hdiff⟩ : S) = v - u := by
    apply Subtype.ext
    simp
  have hlocal := strict_contraction_of_auxiliary_point K S b hb hb0 hS hpointed
    hstrict hFslice huBase.2 hvBase.2 hdiff hxy
    (by
      intro p q hp hq hpq
      apply hauxUniform (x + (u : V)) huBase.1
        (subspaceSectionNormOfCone K S b hb hS hpointed
          ⟨(x + (v : V)) - (x + (u : V)), hdiff⟩)
      · simpa only [hdEq] using hnormR
      · exact hp)
  have houtS : F (x + (v : V)) - F (x + (u : V)) ∈ S :=
    hFslice.map_sub_mem huBase.2 hvBase.2 hdiff
  have hinS : (v : V) - (u : V) ∈ S := S.sub_mem v.property u.property
  change extendSubspacePaperNorm S
      (subspaceSectionNormOfCone K S b hb hS hpointed)
      ((⟨F (x + (v : V)) - F (x + (u : V)), houtS⟩ : S) : V) <
    extendSubspacePaperNorm S
      (subspaceSectionNormOfCone K S b hb hS hpointed)
      ((⟨(v : V) - (u : V), hinS⟩ : S) : V)
  rw [extendSubspacePaperNorm_agrees, extendSubspacePaperNorm_agrees]
  rw [hdEq] at hlocal
  exact hlocal

end InterplayPaperLean
