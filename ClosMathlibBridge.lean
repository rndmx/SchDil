import ClosEquiv
import Remark37
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SchemeDilatation

variable {X Z W : Scheme.{u+1}}

noncomputable def closSubschemeIso (f : Z ⟶ X) [IsClosedImmersion f] :
    Z ≅ f.ker.subscheme :=
  asIso f.toImage

@[reassoc (attr := simp)]
theorem closSubschemeIso_hom_subschemeι (f : Z ⟶ X) [IsClosedImmersion f] :
    (closSubschemeIso f).hom ≫ f.ker.subschemeι = f :=
  f.toImage_imageι

theorem ker_pullback_snd (f : Z ⟶ X) [IsClosedImmersion f] (j : W ⟶ X) :
    (pullback.snd f j).ker = f.ker.comap j := by
  rw [Scheme.IdealSheafData.comap,
    ← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry f.ker.subschemeι j).hom,
    pullbackSymmetry_hom_comp_fst,
    ← Scheme.Hom.ker_comp_of_isIso
      (pullback.map f j f.ker.subschemeι j f.toImage (𝟙 _) (𝟙 _) (by simp) (by simp))]
  simp

theorem ker_pullback_snd_app_top (f : Z ⟶ X) [IsClosedImmersion f]
    (j : W ⟶ X) [IsOpenImmersion j] [IsAffine W] :
    RingHom.ker ((pullback.snd f j).app ⊤).hom =
      Ideal.comap (j.appIso (⊤ : W.Opens)).inv.hom
        (RingHom.ker (f.app (j ''ᵁ (⊤ : W.Opens))).hom) := by
  rw [← Scheme.Hom.ker_apply (pullback.snd f j) (⟨⊤, isAffineOpen_top W⟩ : W.affineOpens),
    ker_pullback_snd, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.Hom.ker_apply]

theorem ker_app_top_Spec_map {R S : CommRingCat.{u+1}} (φ : R ⟶ S) :
    RingHom.ker ((Spec.map φ).app ⊤).hom =
      Ideal.comap (Scheme.ΓSpecIso R).hom.hom (RingHom.ker φ.hom) := by
  have hφ : (Spec.map φ).app ⊤ =
      (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [hφ]
  rw [show ((Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv).hom =
      ((Scheme.ΓSpecIso S).inv.hom.comp φ.hom).comp (Scheme.ΓSpecIso R).hom.hom from rfl,
    ← RingHom.comap_ker]
  congr 1
  exact RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).1

theorem ker_app_top_of_spec_presentation {R : CommRingCat.{u+1}} {P : Scheme.{u+1}}
    (g : P ⟶ Spec R) (I : Ideal R) (e : P ≅ Spec (CommRingCat.of (R ⧸ I)))
    (he : g = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    RingHom.ker (g.app ⊤).hom = Ideal.comap (Scheme.ΓSpecIso R).hom.hom I := by
  haveI : IsClosedImmersion g := by rw [he]; infer_instance
  rw [← Scheme.Hom.ker_apply g (⟨⊤, isAffineOpen_top _⟩ : (Spec R).affineOpens), he,
    Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_apply, ker_app_top_Spec_map]
  simp

theorem isPrincipal_comap_of_isIso {A B : CommRingCat.{u+1}} (φ : A ⟶ B) [IsIso φ]
    {J : Ideal B} (hJ : J.IsPrincipal) : (Ideal.comap φ.hom J).IsPrincipal := by
  obtain ⟨a, ha⟩ := hJ.principal
  refine ⟨⟨(inv φ).hom a, ?_⟩⟩
  have he : Ideal.comap φ.hom J =
      Ideal.map (asIso φ).commRingCatIsoToRingEquiv.symm J :=
    (Ideal.map_symm (I := J) (asIso φ).commRingCatIsoToRingEquiv).symm
  rw [he]
  show Ideal.map _ J = Ideal.span {(inv φ).hom a}
  rw [show J = Ideal.span {a} from ha, Ideal.map_span, Set.image_singleton]
  rfl

section Family

variable {ι : Type} (Y : ι → Scheme.{u+1}) [∀ i, Scheme.Over (Y i) X]
  (hY : ∀ i, IsClosedImmersion (Y i ↘ X))
  (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X)

theorem famIdeal_comap_eq (i : ι) (γ : cov.J) :
    Ideal.comap (Scheme.ΓSpecIso (cov.obj γ)).hom.hom
      (famIdeal Y hY cov i γ) =
      Ideal.comap
        ((cov.map γ).appIso (⊤ : (Spec (cov.obj γ)).Opens)).inv.hom
        (RingHom.ker
          ((Y i ↘ X).app ((cov.map γ) ''ᵁ (⊤ : (Spec (cov.obj γ)).Opens))).hom) :=
  haveI := hY i
  ((ker_app_top_of_spec_presentation _ _ (famIso Y hY cov i γ)
      (famIso_eq Y hY cov i γ)).symm).trans
    (ker_pullback_snd_app_top (Y i ↘ X) (cov.map γ))

theorem famIdeal_isPrincipal (i : ι) (γ : cov.J)
    (hp : (RingHom.ker
      ((Y i ↘ X).app ((cov.map γ) ''ᵁ (⊤ : (Spec (cov.obj γ)).Opens))).hom).IsPrincipal) :
    (famIdeal Y hY cov i γ).IsPrincipal := by
  have h1 : (Ideal.comap (Scheme.ΓSpecIso (cov.obj γ)).hom.hom
      (famIdeal Y hY cov i γ)).IsPrincipal := by
    rw [famIdeal_comap_eq Y hY cov i γ]
    exact isPrincipal_comap_of_isIso _ hp
  have h2 := isPrincipal_comap_of_isIso (Scheme.ΓSpecIso (cov.obj γ)).inv h1
  rwa [Ideal.comap_comap,
    show (Scheme.ΓSpecIso (cov.obj γ)).hom.hom.comp (Scheme.ΓSpecIso (cov.obj γ)).inv.hom =
      RingHom.id _ from congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (cov.obj γ)).inv_hom_id,
    Ideal.comap_id] at h2

end Family

end SchemeDilatation
