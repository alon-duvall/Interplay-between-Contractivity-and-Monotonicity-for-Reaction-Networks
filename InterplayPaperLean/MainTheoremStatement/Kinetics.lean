import InterplayPaperLean.MainTheoremStatement.ReactionNetwork
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace InterplayPaperLean

open ReactionNetwork

noncomputable section

def AllPresent {species reactions : ℕ}
    (complex : Matrix (Fin species) (Fin reactions) ℝ)
    (x : Fin species → ℝ) (r : Fin reactions) : Prop :=
  ∀ s, complex s r > 0 → x s > 0

/-- A global `C¹` extension of a vector of reaction-rate functions. The paper
assumes precisely that rates on the closed nonnegative orthant admit such an
extension to an open neighborhood; using a global extension is an equivalent
choice of representative after a standard extension step. -/
structure Kinetics (species reactions : ℕ) where
  rate : (Fin species → ℝ) → (Fin reactions → ℝ)
  contDiff_rate : ContDiff ℝ 1 rate

namespace Kinetics

def partialRate {species reactions : ℕ} (kinetics : Kinetics species reactions)
    (x : Fin species → ℝ) (r : Fin reactions) (s : Fin species) : ℝ :=
  fderiv ℝ kinetics.rate x (Pi.single s 1) r

def IsAdmissible {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions) : Prop :=
  ∀ x ∈ NonnegativeOrthant species, ∀ r,
    if network.reversible r then
      (¬ AllPresent network.productComplex x r → 0 ≤ kinetics.rate x r) ∧
      (¬ AllPresent network.reactantComplex x r → kinetics.rate x r ≤ 0) ∧
      (∀ s, network.reactantComplex s r > 0 → 0 ≤ kinetics.partialRate x r s) ∧
      (∀ s, network.productComplex s r > 0 → kinetics.partialRate x r s ≤ 0) ∧
      (∀ s, network.reactantComplex s r = 0 → network.productComplex s r = 0 →
        kinetics.partialRate x r s = 0) ∧
      (AllPresent network.reactantComplex x r →
        ∀ s, network.reactantComplex s r > 0 → 0 < kinetics.partialRate x r s) ∧
      (AllPresent network.productComplex x r →
        ∀ s, network.productComplex s r > 0 → kinetics.partialRate x r s < 0)
    else
      (¬ AllPresent network.reactantComplex x r → kinetics.rate x r = 0) ∧
      (∀ s, network.reactantComplex s r > 0 → 0 ≤ kinetics.partialRate x r s) ∧
      (∀ s, network.reactantComplex s r = 0 → kinetics.partialRate x r s = 0) ∧
      (AllPresent network.reactantComplex x r →
        ∀ s, network.reactantComplex s r > 0 → 0 < kinetics.partialRate x r s)

def vectorField {species reactions : ℕ}
    (network : ReactionNetwork species reactions)
    (kinetics : Kinetics species reactions) (x : Fin species → ℝ) :
    Fin species → ℝ :=
  network.stoichiometricMatrix.mulVec (kinetics.rate x)

end Kinetics

end

end InterplayPaperLean
