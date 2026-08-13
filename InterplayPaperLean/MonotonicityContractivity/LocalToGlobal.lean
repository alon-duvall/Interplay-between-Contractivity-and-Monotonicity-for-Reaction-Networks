import InterplayPaperLean.MonotonicityContractivity.LocalAuxiliary
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace InterplayPaperLean

open Set BigOperators

private theorem seminorm_sum_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : Seminorm ℝ V) {ι : Type*} (s : Finset ι) (f : ι → V) :
    p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (map_add_le_add p (f a) (∑ i ∈ s, f i)).trans
        (add_le_add (le_refl _) ih)

/-- A locally strictly distance-decreasing map is strictly decreasing between
the endpoints of a line segment, provided every point of the segment has a
pairwise contraction neighborhood.  This is the finite-subdivision argument
used in the paper. -/
theorem local_strict_contraction_on_segment {S V : Type*}
    [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : PaperNorm V) (ι : S →ₗ[ℝ] V) (G : S → V) {d : S} (hd : d ≠ 0)
    (hlocal : ∀ w ∈ segment ℝ (0 : S) d,
      ∃ U : Set S, IsOpen U ∧ w ∈ U ∧
        ∀ a ∈ U, ∀ b ∈ U, a ≠ b → p (G b - G a) < p (ι (b - a))) :
    p (G d - G 0) < p (ι d) := by
  classical
  let cover : S → Set S := fun w =>
    if hw : w ∈ segment ℝ (0 : S) d then (hlocal w hw).choose else ∅
  have hcoverOpen : ∀ w, IsOpen (cover w) := by
    intro w
    by_cases hw : w ∈ segment ℝ (0 : S) d
    · simp only [cover, dif_pos hw]
      exact (hlocal w hw).choose_spec.1
    · simp [cover, hw]
  have hcover : segment ℝ (0 : S) d ⊆ ⋃ w, cover w := by
    intro w hw
    apply mem_iUnion.mpr
    refine ⟨w, ?_⟩
    simp only [cover, dif_pos hw]
    exact (hlocal w hw).choose_spec.2.1
  have hsegmentCompact : IsCompact (segment ℝ (0 : S) d) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    hsegmentCompact hcoverOpen hcover
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hδ (by positivity : 0 < ‖d‖ + 1))
  let N := n + 1
  have hN : (1 : ℝ) / N < δ / (‖d‖ + 1) := by simpa [N] using hn
  have hN0 : N ≠ 0 := by
    simp [N]
  let point : ℕ → S := fun k => ((k : ℝ) / N) • d
  have point_zero : point 0 = 0 := by simp [point]
  have point_N : point N = d := by simp [point, hN0]
  have hpoint_segment : ∀ k ≤ N, point k ∈ segment ℝ (0 : S) d := by
    intro k hk
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN0)
    refine ⟨1 - (k : ℝ) / N, (k : ℝ) / N, ?_, ?_, by ring, ?_⟩
    · exact sub_nonneg.mpr ((div_le_one hNpos).2 (by exact_mod_cast hk))
    · positivity
    · simp [point]
  have hstep_dist : ∀ k < N, dist (point (k + 1)) (point k) < δ := by
    intro k hk
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN0)
    have hδbound : (1 : ℝ) / N * ‖d‖ < δ := by
      calc
        (1 : ℝ) / N * ‖d‖ < (δ / (‖d‖ + 1)) * ‖d‖ :=
          mul_lt_mul_of_pos_right hN (norm_pos_iff.mpr hd)
        _ < δ := by
          rw [div_mul_eq_mul_div]
          exact (div_lt_iff₀ (by positivity : 0 < ‖d‖ + 1)).2 (by nlinarith [norm_nonneg d])
    rw [dist_eq_norm]
    have heq : point (k + 1) - point k = ((1 : ℝ) / N) • d := by
      simp only [point]
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hNpos)]
    exact hδbound
  have hstep : ∀ k < N, p (G (point (k + 1)) - G (point k)) <
      p (ι (point (k + 1) - point k)) := by
    intro k hk
    have hpk : point k ∈ segment ℝ (0 : S) d := hpoint_segment k (Nat.le_of_lt hk)
    obtain ⟨w, hw⟩ := hball (point k) hpk
    have hpkU : point k ∈ cover w := hw (Metric.mem_ball_self hδ)
    have hsuccU : point (k + 1) ∈ cover w := hw (by
      rw [Metric.mem_ball]
      exact hstep_dist k hk)
    have hwseg : w ∈ segment ℝ (0 : S) d := by
      by_contra hn
      simp [cover, hn] at hpkU
    have hpair := (hlocal w hwseg).choose_spec.2.2
    have hpkU' : point k ∈ (hlocal w hwseg).choose := by
      simpa only [cover, dif_pos hwseg] using hpkU
    have hsuccU' : point (k + 1) ∈ (hlocal w hwseg).choose := by
      simpa only [cover, dif_pos hwseg] using hsuccU
    apply hpair (point k) hpkU' (point (k + 1)) hsuccU'
    intro heq
    have : ((1 : ℝ) / N) • d = 0 := by
      rw [← show point (k + 1) - point k = ((1 : ℝ) / N) • d by
        simp only [point]
        module]
      rw [heq, sub_self]
    exact hd (smul_eq_zero.mp this |>.resolve_left (by positivity))
  have htel : G d - G 0 = ∑ k ∈ Finset.range N,
      (G (point (k + 1)) - G (point k)) := by
    simpa [Function.comp_def, point_zero, point_N] using
      (Finset.sum_range_sub (G ∘ point) N).symm
  have htriangle : p (G d - G 0) ≤ ∑ k ∈ Finset.range N,
      p (G (point (k + 1)) - G (point k)) := by
    rw [htel]
    exact seminorm_sum_le p.toSeminorm (Finset.range N)
      (fun k => G (point (k + 1)) - G (point k))
  have hsumlt : (∑ k ∈ Finset.range N,
      p (G (point (k + 1)) - G (point k))) <
      ∑ k ∈ Finset.range N, p (ι (point (k + 1) - point k)) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hN0)⟩
    · intro k hk
      exact hstep k (Finset.mem_range.mp hk)
  have hinputsum : (∑ k ∈ Finset.range N,
      p (ι (point (k + 1) - point k))) = p (ι d) := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN0)
    simp_rw [show ∀ k, point (k + 1) - point k = ((1 : ℝ) / N) • d by
      intro k
      simp only [point]
      module]
    change (∑ _k ∈ Finset.range N,
      p.toSeminorm (ι (((1 : ℝ) / N) • d))) = p.toSeminorm (ι d)
    rw [map_smul]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hNpos)]
    simp [hN0]
  exact htriangle.trans_lt (hsumlt.trans_eq hinputsum)

end InterplayPaperLean
