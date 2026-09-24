import SchemeFact51
import PreClosReindex
import ClosInterSch

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (i₀ : M.indnumb)

instance chartOfCenter_to_isOpenImmersion (γ : M.cov.J) :
    IsOpenImmersion (M.chartOfCenter_to i₀ γ) := by
  haveI := M.cov.map_prop γ
  haveI h1 : IsOpenImmersion (pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ)) :=
    inferInstance
  show IsOpenImmersion ((M.YcondIso i₀ γ).hom ≫
    pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ))
  infer_instance

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

theorem centerCover_map_overX (γ : M.cov.J) :
    (M.centerCover i₀).map γ ≫ (M.Ysub i₀ ↘ X) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γ))) ≫
        M.cov.map γ :=
  M.chartOfCenter_to_overX i₀ γ

end PreMultiCenter

end SchemeDilatation
