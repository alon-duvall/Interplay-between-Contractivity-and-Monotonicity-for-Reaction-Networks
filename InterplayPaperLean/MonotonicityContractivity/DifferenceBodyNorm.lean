import InterplayPaperLean.MonotonicityContractivity.TransversalSection

namespace InterplayPaperLean

open Set

/-- The Minkowski functional of a balanced, convex, absorbent, bounded set is
a genuine norm. This packages Mathlib's `gaugeSeminorm` as the `PaperNorm`
used by the main theorem statement. -/
noncomputable def paperNormOfGoodSet {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (H : Set V) (hbalanced : Balanced ℝ H) (hconvex : Convex ℝ H)
    (habsorbent : Absorbent ℝ H) (hbounded : Bornology.IsVonNBounded ℝ H) :
    PaperNorm V where
  toSeminorm := gaugeSeminorm hbalanced hconvex habsorbent
  definite := by
    intro v hv
    apply (gauge_eq_zero habsorbent hbounded).mp
    exact hv

@[simp] theorem paperNormOfGoodSet_apply {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (H : Set V) (hbalanced : Balanced ℝ H) (hconvex : Convex ℝ H)
    (habsorbent : Absorbent ℝ H) (hbounded : Bornology.IsVonNBounded ℝ H)
    (v : V) :
    paperNormOfGoodSet H hbalanced hconvex habsorbent hbounded v = gauge H v :=
  rfl

/-- Membership in the interior of the chosen unit body is exactly the strict
estimate needed in the contraction argument. -/
theorem paperNormOfGoodSet_lt_one_of_mem_interior {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (H : Set V) (hbalanced : Balanced ℝ H) (hconvex : Convex ℝ H)
    (habsorbent : Absorbent ℝ H) (hbounded : Bornology.IsVonNBounded ℝ H)
    {v : V} (hv : v ∈ interior H) :
    paperNormOfGoodSet H hbalanced hconvex habsorbent hbounded v < 1 := by
  rw [paperNormOfGoodSet_apply]
  exact interior_subset_gauge_lt_one H hv

theorem differenceBody_balanced {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P : Set V} (hconvex : Convex ℝ P) : Balanced ℝ (DifferenceBody P) := by
  rw [balanced_iff_neg_mem (DifferenceBody.convex hconvex)]
  intro x hx
  exact DifferenceBody.neg_mem hx

end InterplayPaperLean
