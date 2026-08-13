import InterplayPaperLean.MainTheoremStatement.ReactionNetwork
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace InterplayPaperLean.ReactionNetwork

theorem stoichiometricMatrix_apply {species reactions : ℕ}
    (network : ReactionNetwork species reactions) (i j) :
    network.stoichiometricMatrix i j =
      network.productComplex i j - network.reactantComplex i j := rfl

theorem reactant_eq_zero_of_stoichiometricMatrix_pos {species reactions : ℕ}
    (network : ReactionNetwork species reactions) (h : network.IsNonCatalytic)
    {i j} (hpos : 0 < network.stoichiometricMatrix i j) :
    network.reactantComplex i j = 0 := by
  rcases h i j with hr | hp
  · exact hr
  · exact False.elim ((not_lt_of_ge (network.reactant_nonnegative i j)) (by
      simpa [stoichiometricMatrix, hp] using hpos))

theorem product_eq_zero_of_stoichiometricMatrix_neg {species reactions : ℕ}
    (network : ReactionNetwork species reactions) (h : network.IsNonCatalytic)
    {i j} (hneg : network.stoichiometricMatrix i j < 0) :
    network.productComplex i j = 0 := by
  rcases h i j with hr | hp
  · exact False.elim ((not_lt_of_ge (network.product_nonnegative i j)) (by
      simpa [stoichiometricMatrix, hr] using hneg))
  · exact hp

theorem stoichiometricMatrix_pos_iff_product_pos {species reactions : ℕ}
    (network : ReactionNetwork species reactions) (h : network.IsNonCatalytic)
    (i j) :
    0 < network.stoichiometricMatrix i j ↔ 0 < network.productComplex i j := by
  constructor
  · intro hpos
    have hr := reactant_eq_zero_of_stoichiometricMatrix_pos network h hpos
    simpa [stoichiometricMatrix, hr] using hpos
  · intro hp
    have hr : network.reactantComplex i j = 0 := (h i j).resolve_right (ne_of_gt hp)
    simp [stoichiometricMatrix_apply, hr, hp]

theorem stoichiometricMatrix_neg_iff_reactant_pos {species reactions : ℕ}
    (network : ReactionNetwork species reactions) (h : network.IsNonCatalytic)
    (i j) :
    network.stoichiometricMatrix i j < 0 ↔ 0 < network.reactantComplex i j := by
  constructor
  · intro hneg
    have hp := product_eq_zero_of_stoichiometricMatrix_neg network h hneg
    simpa [stoichiometricMatrix, hp] using hneg
  · intro hr
    have hp : network.productComplex i j = 0 := (h i j).resolve_left (ne_of_gt hr)
    simp [stoichiometricMatrix_apply, hp, hr]

def StoichiometricSubspace {species reactions : ℕ}
    (network : ReactionNetwork species reactions) : Submodule ℝ (Fin species → ℝ) :=
  LinearMap.range network.stoichiometricMatrix.mulVecLin

theorem mulVec_mem_stoichiometricSubspace {species reactions : ℕ}
    (network : ReactionNetwork species reactions) (c : Fin reactions → ℝ) :
    network.stoichiometricMatrix.mulVec c ∈ network.StoichiometricSubspace := by
  exact ⟨c, Matrix.mulVecLin_apply _ _⟩

theorem mem_stoichiometricClass_iff {species reactions : ℕ}
    (network : ReactionNetwork species reactions) (x₀ x : Fin species → ℝ) :
    x ∈ network.StoichiometricClass x₀ ↔
      x ∈ NonnegativeOrthant species ∧ x - x₀ ∈ network.StoichiometricSubspace := by
  constructor
  · rintro ⟨hx, c, rfl⟩
    refine ⟨hx, ?_⟩
    simpa only [add_sub_cancel_left] using network.mulVec_mem_stoichiometricSubspace c
  · rintro ⟨hx, c, hc⟩
    refine ⟨hx, c, ?_⟩
    rw [Matrix.mulVecLin_apply] at hc
    calc
      x = x₀ + (x - x₀) := by abel
      _ = x₀ + network.stoichiometricMatrix.mulVec c := congrArg (x₀ + ·) hc.symm

end InterplayPaperLean.ReactionNetwork
