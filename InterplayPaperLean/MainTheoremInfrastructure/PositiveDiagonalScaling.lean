import InterplayPaperLean.MainTheoremStatement.MatrixClasses
import Mathlib.Data.Matrix.Mul

namespace InterplayPaperLean

open Matrix

noncomputable section

theorem inD_eq_diagonal {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ} (hD : InD D) :
    D = Matrix.diagonal (fun i => D i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, hD.1 i j hij]

theorem inD_diagonal_pos {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ} (hD : InD D) (i) :
    0 < D i i := hD.2 i

theorem inD_diagonal_ne_zero {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : InD D) (i) : D i i ≠ 0 := ne_of_gt (hD.2 i)

def inverseDiagonalVector {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun i => (D i i)⁻¹

theorem diagonal_mulVec_inverseDiagonalVector {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : InD D) (v : Fin n → ℝ) :
    D *ᵥ (fun i => inverseDiagonalVector D i * v i) = v := by
  rw [inD_eq_diagonal hD]
  ext i
  rw [Matrix.mulVec_diagonal]
  simp only [inverseDiagonalVector, Matrix.diagonal_apply_eq]
  rw [← mul_assoc, mul_inv_cancel₀ (inD_diagonal_ne_zero hD i), one_mul]

theorem mul_mulVec_inverseDiagonalVector {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : InD D) (v : Fin n → ℝ) :
    (A * D) *ᵥ (fun i => inverseDiagonalVector D i * v i) = A *ᵥ v := by
  rw [← Matrix.mulVec_mulVec, diagonal_mulVec_inverseDiagonalVector hD]

theorem positiveDiagonal_rescaling_preserves_vectorField {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : InD D) (rate : Fin n → ℝ) :
    (A * D) *ᵥ (fun i => inverseDiagonalVector D i * rate i) = A *ᵥ rate :=
  mul_mulVec_inverseDiagonalVector A hD rate

end

end InterplayPaperLean
