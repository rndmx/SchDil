import GlobalDilProperties

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (N : PreMultiCenter X)

noncomputable def dilatationCover :
    Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) N.dilatation where
  J := N.cov.J
  obj γ := CommRingCat.of (Multicenter.Dilatation (N.localMulticenter γ))
  map γ := N.chartTo γ
  f x := (N.glueData.ι_jointly_surjective x).choose
  covers x := by
    obtain ⟨y, hy⟩ := (N.glueData.ι_jointly_surjective x).choose_spec
    exact ⟨y, hy⟩
  map_prop γ := N.chartTo_isOpenImmersion γ

@[simp] theorem dilatationCover_J : (N.dilatationCover).J = N.cov.J := rfl
@[simp] theorem dilatationCover_obj (γ : N.cov.J) :
    (N.dilatationCover).obj γ =
      CommRingCat.of (Multicenter.Dilatation (N.localMulticenter γ)) := rfl
@[simp] theorem dilatationCover_map (γ : N.cov.J) :
    (N.dilatationCover).map γ = N.chartTo γ := rfl

end PreMultiCenter

end SchemeDilatation

section Present
open SchemeDilatation
variable {B V : Scheme.{u+1}} (c : V ⟶ B) [IsClosedImmersion c]
  (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) B)

instance present_pullback_snd_isClosedImmersion (γ : cov.J) :
    IsClosedImmersion (pullback.snd c (cov.map γ)) :=
  MorphismProperty.pullback_snd _ _ inferInstance

noncomputable def presentIdeal (γ : cov.J) : Ideal (cov.obj γ) :=
  (IsClosedImmersion.Spec_iff.mp
    (present_pullback_snd_isClosedImmersion c cov γ)).choose

noncomputable def presentIso (γ : cov.J) :
    pullback c (cov.map γ) ≅
      Spec (CommRingCat.of (cov.obj γ ⧸ presentIdeal c cov γ)) :=
  (IsClosedImmersion.Spec_iff.mp
    (present_pullback_snd_isClosedImmersion c cov γ)).choose_spec.choose

theorem presentIso_eq (γ : cov.J) :
    pullback.snd c (cov.map γ) =
      (presentIso c cov γ).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (presentIdeal c cov γ))) :=
  (IsClosedImmersion.Spec_iff.mp
    (present_pullback_snd_isClosedImmersion c cov γ)).choose_spec.choose_spec

noncomputable def presentPreClos : PreClos B where
  indnumb := PUnit
  subscheme _ := V
  over _ := ⟨c⟩
  cov := cov
  ideal _ γ := presentIdeal c cov γ
  condiso _ γ := (presentIso c cov γ).symm
  condover _ γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (presentIso c cov γ).inv ≫ pullback.snd c (cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (presentIdeal c cov γ)))
    rw [presentIso_eq c cov γ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[simp] theorem presentPreClos_ideal (u : PUnit) (γ : cov.J) :
    (presentPreClos c cov).ideal u γ = presentIdeal c cov γ := rfl

end Present
