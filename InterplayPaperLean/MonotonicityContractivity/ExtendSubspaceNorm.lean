import InterplayPaperLean.MonotonicityContractivity.SubspaceDifferenceBody
import Mathlib.LinearAlgebra.Projection

namespace InterplayPaperLean

open LinearMap

/-- Extend a norm on a finite-dimensional subspace to the ambient space by
adding the original ambient norm on a chosen complementary component. -/
noncomputable def extendSubspacePaperNorm {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : Submodule ℝ V) (p : PaperNorm S) : PaperNorm V := by
  let T := S.exists_isCompl.choose
  let h : IsCompl S T := S.exists_isCompl.choose_spec
  let projS : V →ₗ[ℝ] S := S.projectionOnto T h
  let residual : V →ₗ[ℝ] V := LinearMap.id - S.subtype.comp projS
  let pS : Seminorm ℝ V := p.toSeminorm.comp projS
  let pT : Seminorm ℝ V := (normSeminorm ℝ V).comp residual
  refine
    { toSeminorm := pS + pT
      definite := ?_ }
  intro v hv
  have hnonnegS : 0 ≤ pS v := by positivity
  have hnonnegT : 0 ≤ pT v := by positivity
  have hsum : pS v + pT v = 0 := hv
  have hpS : pS v = 0 := by linarith
  have hpT : pT v = 0 := by linarith
  have hproj : projS v = 0 := p.definite _ hpS
  have hres : residual v = 0 := by
    exact norm_eq_zero.mp hpT
  change v - S.subtype (projS v) = 0 at hres
  rw [hproj, map_zero, sub_zero] at hres
  exact hres

theorem extendSubspacePaperNorm_agrees {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : Submodule ℝ V) (p : PaperNorm S) (v : S) :
    extendSubspacePaperNorm S p (v : V) = p v := by
  simp [extendSubspacePaperNorm, Submodule.projectionOnto_apply_left]

end InterplayPaperLean
