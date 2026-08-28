import SchemeFact51
import PreClosReindex
import ClosInterSch

/-!
# An affine cover of a center, with charts `A_γ ⧸ M_i`

To build the paper's restricted datum `(D_J, X_J)|_{X_i}` as a `PreMultiCenter` on the
center `X_i` one first needs an affine covering of `X_i`.  The natural one -- `pull_cov`
along `X_i ↪ X` -- has *opaque* charts (Mathlib's `Scheme.affineOpenCover` of
`X_i ×_X U_γ`, indexed by pairs), which no ring-level result can talk about.

This file assembles the pieces of `SchemeFact51` into the *bespoke* cover whose charts are
literally `Spec (A_γ ⧸ M.Yideal i γ)` and whose index set is `M.cov.J`, one chart per chart
of `X`.  That is what makes every later comparison a chart-for-chart comparison with the
ring-level theory (`quotCenter`, `quotHom`, `panelHom`).
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (i₀ : M.indnumb)

/-- `chartOfCenter_to` is an open immersion.  (This was only a `haveI` buried inside
`chartOfCenter_to_flat`.) -/
instance chartOfCenter_to_isOpenImmersion (γ : M.cov.J) :
    IsOpenImmersion (M.chartOfCenter_to i₀ γ) := by
  haveI := M.cov.map_prop γ
  haveI h1 : IsOpenImmersion (pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ)) :=
    inferInstance
  show IsOpenImmersion ((M.YcondIso i₀ γ).hom ≫
    pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ))
  infer_instance

/-- **An affine cover of the center `X_{i₀}` with charts `A_γ ⧸ M_{i₀}`**, indexed by the
charts of `X` themselves. -/
def centerCover : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) (M.Ysub i₀) where
  J := M.cov.J
  obj γ := CommRingCat.of ((M.cov.obj γ) ⧸ M.Yideal i₀ γ)
  map γ := M.chartOfCenter_to i₀ γ
  f y := M.cov.f ((M.Ysub i₀ ↘ X).base y)
  covers y := by
    set γ₀ := M.cov.f ((M.Ysub i₀ ↘ X).base y) with hγ₀
    have h1 : y ∈ (M.Ysub i₀ ↘ X).base ⁻¹' Set.range (M.cov.map γ₀).base :=
      M.cov.covers _
    rw [← Scheme.Pullback.range_fst (f := M.Ysub i₀ ↘ X) (g := M.cov.map γ₀)] at h1
    obtain ⟨z, hz⟩ := h1
    refine ⟨(M.YcondIso i₀ γ₀).inv.base z, ?_⟩
    show (M.chartOfCenter_to i₀ γ₀).base _ = y
    rw [chartOfCenter_to, Scheme.comp_base_apply, ← hz]
    congr 1
    erw [← Scheme.comp_base_apply, Iso.inv_hom_id]
    rfl
  map_prop γ := inferInstance

@[simp] theorem centerCover_J : (M.centerCover i₀).J = M.cov.J := rfl

@[simp] theorem centerCover_obj (γ : M.cov.J) :
    (M.centerCover i₀).obj γ = CommRingCat.of ((M.cov.obj γ) ⧸ M.Yideal i₀ γ) := rfl

@[simp] theorem centerCover_map (γ : M.cov.J) :
    (M.centerCover i₀).map γ = M.chartOfCenter_to i₀ γ := rfl

/-- The chart map of `centerCover` sits over the quotient map on `X`. -/
theorem centerCover_map_overX (γ : M.cov.J) :
    (M.centerCover i₀).map γ ≫ (M.Ysub i₀ ↘ X) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γ))) ≫
        M.cov.map γ :=
  M.chartOfCenter_to_overX i₀ γ

end PreMultiCenter

end SchemeDilatation
