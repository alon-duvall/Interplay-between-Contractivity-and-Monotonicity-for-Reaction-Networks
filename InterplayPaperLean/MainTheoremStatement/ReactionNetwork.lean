import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace InterplayPaperLean

/-- A finite reaction network, including the reactant/product data that a net
stoichiometric matrix alone cannot retain. -/
structure ReactionNetwork (species reactions : ℕ) where
  reactantComplex : Matrix (Fin species) (Fin reactions) ℝ
  productComplex : Matrix (Fin species) (Fin reactions) ℝ
  reactant_nonnegative : ∀ i j, 0 ≤ reactantComplex i j
  product_nonnegative : ∀ i j, 0 ≤ productComplex i j
  reversible : Fin reactions → Bool
  species_participates : ∀ i, ∃ j,
    if reversible j then
      reactantComplex i j > 0 ∨ productComplex i j > 0
    else
      reactantComplex i j > 0

namespace ReactionNetwork

def stoichiometricMatrix {species reactions : ℕ}
    (network : ReactionNetwork species reactions) :
    Matrix (Fin species) (Fin reactions) ℝ :=
  fun i j => network.productComplex i j - network.reactantComplex i j

/-- No species appears on both sides of any reaction. -/
def IsNonCatalytic {species reactions : ℕ}
    (network : ReactionNetwork species reactions) : Prop :=
  ∀ i j, network.reactantComplex i j = 0 ∨ network.productComplex i j = 0

def SharesSpecies {species reactions : ℕ}
    (network : ReactionNetwork species reactions) (i j : Fin reactions) : Prop :=
  ∃ s, network.stoichiometricMatrix s i ≠ 0 ∧
    network.stoichiometricMatrix s j ≠ 0

def NonnegativeOrthant (species : ℕ) : Set (Fin species → ℝ) :=
  {x | ∀ i, 0 ≤ x i}

def StoichiometricClass {species reactions : ℕ}
    (network : ReactionNetwork species reactions) (x₀ : Fin species → ℝ) :
    Set (Fin species → ℝ) :=
  {x | x ∈ NonnegativeOrthant species ∧
    ∃ c : Fin reactions → ℝ,
      x = x₀ + network.stoichiometricMatrix.mulVec c}

end ReactionNetwork

end InterplayPaperLean
