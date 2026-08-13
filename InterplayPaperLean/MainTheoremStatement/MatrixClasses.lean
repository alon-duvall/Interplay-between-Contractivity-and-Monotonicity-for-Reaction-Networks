import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

namespace InterplayPaperLean

open Matrix

noncomputable section

def HasSignEntries {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1

def AtMostTwoNonzeroPerColumn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ j, (Finset.univ.filter fun i => A i j ≠ 0).card ≤ 2

def AtMostTwoNonzeroPerRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i, (Finset.univ.filter fun j => A i j ≠ 0).card ≤ 2

/-- The paper's matrix class `S`. -/
def InS {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  HasSignEntries A ∧ AtMostTwoNonzeroPerColumn A

/-- Membership in `Sᵗ`: the transpose belongs to `S`. -/
def InSTranspose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  InS A.transpose

/-- The paper's matrix class `𝒩 = S ∪ Sᵗ`. -/
def InN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  InS A ∨ InSTranspose A

/-- The paper's matrix class `𝒫`. -/
def InP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i, (Finset.univ.filter fun j => A i j ≠ 0).card ≤ 1) ∧
    (∀ j, ∃ i, A i j ≠ 0)

/-- The paper's matrix class `𝒟`. -/
def InD {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, i ≠ j → A i j = 0) ∧ ∀ i, 0 < A i i

end

end InterplayPaperLean
