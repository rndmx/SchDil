import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import PreClosAndClos

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

variable {X : Scheme.{u+1}}

theorem PreClos.subscheme_isClosedImmersion (Z : PreClos X) (i : Z.indnumb) :
    IsClosedImmersion (Z.subscheme i ↘ X) := by
  rw [IsLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Z.cov.cover]
  intro γ
  have hiso : IsClosedImmersion
      (pullback.snd (Z.subscheme i ↘ X) (Z.cov.cover.map γ)) := by
    have hspec : IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal i γ)))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hover := Z.condover i γ
    rw [Scheme.Hom.isOver_iff] at hover
    change (Z.condiso i γ).hom ≫ pullback.snd (Z.subscheme i ↘ X) (Z.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal i γ))) at hover
    have hcomp : IsClosedImmersion
        ((Z.condiso i γ).hom ≫ pullback.snd (Z.subscheme i ↘ X) (Z.cov.map γ)) := by
      rw [hover]; exact hspec
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsClosedImmersion) (Z.condiso i γ).hom _).mp hcomp
  exact hiso

instance PreClos.pullback_snd_isClosedImmersion (Z : PreClos X)
    (cov' : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) (i : Z.indnumb) (γ : cov'.J) :
    IsClosedImmersion (pullback.snd (Z.subscheme i ↘ X) (cov'.map γ)) :=
  MorphismProperty.pullback_snd _ _ (Z.subscheme_isClosedImmersion i)

noncomputable def PreClos.reindexIdeal (Z : PreClos X)
    (cov' : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) (i : Z.indnumb) (γ : cov'.J) :
    Ideal (cov'.obj γ) :=
  (IsClosedImmersion.Spec_iff.mp (Z.pullback_snd_isClosedImmersion cov' i γ)).choose

noncomputable def PreClos.reindexIso (Z : PreClos X)
    (cov' : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) (i : Z.indnumb) (γ : cov'.J) :
    pullback (Z.subscheme i ↘ X) (cov'.map γ) ≅
      Spec (CommRingCat.of (cov'.obj γ ⧸ Z.reindexIdeal cov' i γ)) :=
  (IsClosedImmersion.Spec_iff.mp (Z.pullback_snd_isClosedImmersion cov' i γ)).choose_spec.choose

theorem PreClos.reindexIso_eq (Z : PreClos X)
    (cov' : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) (i : Z.indnumb) (γ : cov'.J) :
    pullback.snd (Z.subscheme i ↘ X) (cov'.map γ) =
      (Z.reindexIso cov' i γ).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.reindexIdeal cov' i γ))) :=
  (IsClosedImmersion.Spec_iff.mp (Z.pullback_snd_isClosedImmersion cov' i γ)).choose_spec.choose_spec

noncomputable def PreClos.reindex (Z : PreClos X)
    (cov' : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) : PreClos X where
  indnumb := Z.indnumb
  subscheme := Z.subscheme
  cov := cov'
  ideal i γ := Z.reindexIdeal cov' i γ
  condiso i γ := (Z.reindexIso cov' i γ).symm
  condover i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
    show (Z.reindexIso cov' i γ).inv ≫ pullback.snd (Z.subscheme i ↘ X) (cov'.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.reindexIdeal cov' i γ)))
    rw [Z.reindexIso_eq cov' i γ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

def PreClos.reindex_rel (Z : PreClos X)
    (cov' : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) :
    relStructure (Z.reindex cov') Z where
  indnumb_equiv := Equiv.refl _
  subscheme_iso _ := Iso.refl _
  subscheme_iso_over _ := by simp [Scheme.Hom.isOver_iff]

theorem PreClos.reindex_clos_eq (Z : PreClos X)
    (cov' : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) :
    (Quotient.mk'' (Z.reindex cov') : Clos X) = Quotient.mk'' Z :=
  Quotient.sound ⟨Z.reindex_rel cov'⟩

instance PreClos.pullback_snd_isClosedImmersion' (Z : PreClos X) {W : Scheme.{u+1}}
    (h : W ⟶ X) [IsOpenImmersion h] (i : Z.indnumb) :
    IsClosedImmersion (pullback.snd (Z.subscheme i ↘ X) h) :=
  MorphismProperty.pullback_snd _ _ (Z.subscheme_isClosedImmersion i)

instance PreClos.pullback_snd_isoSpec_isClosedImmersion (Z : PreClos X) {W : Scheme.{u+1}}
    [IsAffine W] (h : W ⟶ X) [IsOpenImmersion h] (i : Z.indnumb) :
    IsClosedImmersion (pullback.snd (Z.subscheme i ↘ X) h ≫ W.isoSpec.hom) :=
  (MorphismProperty.cancel_right_of_respectsIso
    (P := @IsClosedImmersion) (pullback.snd (Z.subscheme i ↘ X) h) W.isoSpec.hom).mpr
    (Z.pullback_snd_isClosedImmersion' h i)

noncomputable def PreClos.baseIdeal (Z : PreClos X) {W : Scheme.{u+1}} [IsAffine W]
    (h : W ⟶ X) [IsOpenImmersion h] (i : Z.indnumb) :
    Ideal (Γ(W, ⊤)) :=
  (IsClosedImmersion.Spec_iff.mp
    (Z.pullback_snd_isoSpec_isClosedImmersion h i)).choose

noncomputable def PreClos.baseIso (Z : PreClos X) {W : Scheme.{u+1}} [IsAffine W]
    (h : W ⟶ X) [IsOpenImmersion h] (i : Z.indnumb) :
    pullback (Z.subscheme i ↘ X) h ≅
      Spec (CommRingCat.of (Γ(W, ⊤) ⧸ Z.baseIdeal h i)) :=
  (IsClosedImmersion.Spec_iff.mp
    (Z.pullback_snd_isoSpec_isClosedImmersion h i)).choose_spec.choose

theorem PreClos.baseIso_eq (Z : PreClos X) {W : Scheme.{u+1}} [IsAffine W]
    (h : W ⟶ X) [IsOpenImmersion h] (i : Z.indnumb) :
    pullback.snd (Z.subscheme i ↘ X) h ≫ W.isoSpec.hom =
      (Z.baseIso h i).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.baseIdeal h i))) :=
  (IsClosedImmersion.Spec_iff.mp
    (Z.pullback_snd_isoSpec_isClosedImmersion h i)).choose_spec.choose_spec

noncomputable def specQuotientPullbackIso (A B : CommRingCat.{u+1}) [Algebra A B] (I : Ideal A) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≅
      Spec (CommRingCat.of (B ⧸ Ideal.map (algebraMap A B) I)) :=
  pullbackSpecIso A (A ⧸ I) B ≪≫
    (Scheme.Spec.mapIso
      (((lemma_iso A B I).symm.toRingEquiv.toCommRingCatIso).op)).symm

lemma lemma_iso_mk (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) (b : B) :
    lemma_iso A B I (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b) =
      (1 : A ⧸ I) ⊗ₜ[A] b := by
  simp [lemma_iso, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]

@[reassoc]
lemma specQuotientPullbackIso_hom_snd (A B : CommRingCat.{u+1}) [Algebra A B] (I : Ideal A) :
    (specQuotientPullbackIso A B I).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I))) =
      pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  unfold specQuotientPullbackIso
  rw [Iso.trans_hom, Category.assoc]
  rw [show (Scheme.Spec.mapIso
      (((lemma_iso A B I).symm.toRingEquiv.toCommRingCatIso).op)).symm.hom =
      Spec.map (CommRingCat.ofHom ((lemma_iso A B I).toRingEquiv : _ →+* _)) from rfl]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact pullbackSpecIso_hom_snd A (A ⧸ I) B

lemma PreClos.pullback_snd_eq (Z : PreClos X) (γ : Z.cov.J) (i : Z.indnumb) :
    pullback.snd (Z.subscheme i ↘ X) (Z.cov.map γ) =
      (Z.condiso i γ).inv ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal i γ))) := by
  have hover := Z.condover i γ
  rw [Scheme.Hom.isOver_iff] at hover
  change (Z.condiso i γ).hom ≫ pullback.snd (Z.subscheme i ↘ X) (Z.cov.map γ) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal i γ))) at hover
  rw [← hover, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

noncomputable def PreClos.chartPasteIso (Z : PreClos X) (γ : Z.cov.J) (i : Z.indnumb)
    (B : CommRingCat.{u+1}) [Algebra (Z.cov.obj γ) B] :
    pullback (Z.subscheme i ↘ X)
      (Spec.map (CommRingCat.ofHom (algebraMap (Z.cov.obj γ) B)) ≫ Z.cov.map γ) ≅
      Spec (CommRingCat.of (B ⧸ Ideal.map (algebraMap (Z.cov.obj γ) B) (Z.ideal i γ))) :=
  (pullbackLeftPullbackSndIso (Z.subscheme i ↘ X) (Z.cov.map γ)
    (Spec.map (CommRingCat.ofHom (algebraMap (Z.cov.obj γ) B)))).symm ≪≫
  pullback.congrHom (Z.pullback_snd_eq γ i) rfl ≪≫
  asIso (pullback.map
    ((Z.condiso i γ).inv ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal i γ))))
    (Spec.map (CommRingCat.ofHom (algebraMap (Z.cov.obj γ) B)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal i γ))))
    (Spec.map (CommRingCat.ofHom (algebraMap (Z.cov.obj γ) B)))
    (Z.condiso i γ).inv (𝟙 _) (𝟙 _) (by simp) (by simp)) ≪≫
  specQuotientPullbackIso (Z.cov.obj γ) B (Z.ideal i γ)

@[reassoc]
lemma PreClos.chartPasteIso_snd (Z : PreClos X) (γ : Z.cov.J) (i : Z.indnumb)
    (B : CommRingCat.{u+1}) [Algebra (Z.cov.obj γ) B] :
    (Z.chartPasteIso γ i B).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (Z.cov.obj γ) B) (Z.ideal i γ)))) =
      pullback.snd (Z.subscheme i ↘ X)
        (Spec.map (CommRingCat.ofHom (algebraMap (Z.cov.obj γ) B)) ≫ Z.cov.map γ) := by
  unfold chartPasteIso
  simp only [Iso.trans_hom, Category.assoc, asIso_hom]
  rw [specQuotientPullbackIso_hom_snd]
  rw [pullback.lift_snd, Category.comp_id]
  rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  exact pullbackLeftPullbackSndIso_inv_snd_snd _ _ _

theorem exists_common_cover (Y D : Clos X) (hD : IsPri X D) :
    ∃ (Drep Yrep : PreClos X), Yrep.cov = Drep.cov ∧
      (Quotient.mk'' Yrep : Clos X) = Y ∧ (Quotient.mk'' Drep : Clos X) = D ∧
      IsPrePri X Drep := by
  obtain ⟨Drep, hDrep_prepri, hDrep_eq⟩ := hD
  obtain ⟨Yrep0, hYrep0_eq⟩ := Y.exists_rep
  refine ⟨Drep, Yrep0.reindex Drep.cov, rfl, ?_, hDrep_eq, hDrep_prepri⟩
  rw [Yrep0.reindex_clos_eq]
  exact hYrep0_eq

theorem exists_common_cover' (Y D : Clos X) :
    ∃ (Drep Yrep : PreClos X), Yrep.cov = Drep.cov ∧
      (Quotient.mk'' Yrep : Clos X) = Y ∧ (Quotient.mk'' Drep : Clos X) = D := by
  obtain ⟨Drep0, hDrep0_eq⟩ := D.exists_rep
  obtain ⟨Yrep0, hYrep0_eq⟩ := Y.exists_rep
  refine ⟨Drep0, Yrep0.reindex Drep0.cov, rfl, ?_, hDrep0_eq⟩
  rw [Yrep0.reindex_clos_eq]
  exact hYrep0_eq

theorem Ideal.map_eq_of_quotientIso {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (J : Ideal R) (J' : Ideal S) (φ : R ⧸ J ≃+* S ⧸ J')
    (h : ∀ r : R, Ideal.Quotient.mk J' (e r) = φ (Ideal.Quotient.mk J r)) :
    J' = Ideal.map (e : R →+* S) J := by
  apply Ideal.ext
  intro s
  rw [Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective]
  constructor
  · intro hs
    refine ⟨e.symm s, ?_, e.apply_symm_apply s⟩
    have h0 : Ideal.Quotient.mk J' (e (e.symm s)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (by rwa [e.apply_symm_apply])
    rw [h, ← map_zero φ] at h0
    exact (Ideal.Quotient.eq_zero_iff_mem).mp (φ.injective h0)
  · rintro ⟨r, hr, rfl⟩
    have h0 : Ideal.Quotient.mk J r = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hr
    have h2 := h r
    rw [h0, map_zero] at h2
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h2

theorem chartIdeal_agree_rel (Z₁ Z₂ : PreClos X) (R : relStructure Z₁ Z₂)
    {W : Scheme.{u+1}} [IsAffine W] {γ₁ : Z₁.cov.J} {γ₂ : Z₂.cov.J}
    (a : W ⟶ Spec (Z₁.cov.obj γ₁)) (b : W ⟶ Spec (Z₂.cov.obj γ₂))
    (hab : a ≫ Z₁.cov.map γ₁ = b ≫ Z₂.cov.map γ₂) (i : Z₁.indnumb) :
    Ideal.map (Spec.preimage (W.isoSpec.inv ≫ a)).hom (Z₁.ideal i γ₁) =
      Ideal.map (Spec.preimage (W.isoSpec.inv ≫ b)).hom
        (Z₂.ideal (R.indnumb_equiv i) γ₂) := by
  letI : Algebra (Z₁.cov.obj γ₁) Γ(W, ⊤) :=
    (Spec.preimage (W.isoSpec.inv ≫ a)).hom.toAlgebra
  letI : Algebra (Z₂.cov.obj γ₂) Γ(W, ⊤) :=
    (Spec.preimage (W.isoSpec.inv ≫ b)).hom.toAlgebra
  have hma : Spec.map (CommRingCat.ofHom (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤))) =
      W.isoSpec.inv ≫ a := Spec.map_preimage _
  have hmb : Spec.map (CommRingCat.ofHom (algebraMap (Z₂.cov.obj γ₂) Γ(W, ⊤))) =
      W.isoSpec.inv ≫ b := Spec.map_preimage _
  have heq : Spec.map (CommRingCat.ofHom (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤))) ≫
      Z₁.cov.map γ₁ =
      Spec.map (CommRingCat.ofHom (algebraMap (Z₂.cov.obj γ₂) Γ(W, ⊤))) ≫
        Z₂.cov.map γ₂ := by
    rw [hma, hmb, Category.assoc, Category.assoc, hab]
  have hover : (R.subscheme_iso i).hom ≫ (Z₂.subscheme (R.indnumb_equiv i) ↘ X) =
      (Z₁.subscheme i ↘ X) := by
    have h := R.subscheme_iso_over i
    rwa [Scheme.Hom.isOver_iff] at h

  set mid : pullback (Z₁.subscheme i ↘ X)
      (Spec.map (CommRingCat.ofHom (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤))) ≫
        Z₁.cov.map γ₁) ⟶
      pullback (Z₂.subscheme (R.indnumb_equiv i) ↘ X)
      (Spec.map (CommRingCat.ofHom (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤))) ≫
        Z₁.cov.map γ₁) :=
    pullback.map _ _ _ _ (R.subscheme_iso i).hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact hover.symm) (by simp) with hmid
  haveI : IsIso mid := by rw [hmid]; infer_instance
  have hmid_snd : mid ≫ pullback.snd (Z₂.subscheme (R.indnumb_equiv i) ↘ X)
      (Spec.map (CommRingCat.ofHom (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤))) ≫
        Z₁.cov.map γ₁) =
      pullback.snd (Z₁.subscheme i ↘ X)
      (Spec.map (CommRingCat.ofHom (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤))) ≫
        Z₁.cov.map γ₁) := by
    rw [hmid, pullback.lift_snd]
    exact Category.comp_id _
  have hcongr_snd : (pullback.congrHom rfl heq).hom ≫
      pullback.snd (Z₂.subscheme (R.indnumb_equiv i) ↘ X)
      (Spec.map (CommRingCat.ofHom (algebraMap (Z₂.cov.obj γ₂) Γ(W, ⊤))) ≫
        Z₂.cov.map γ₂) =
      pullback.snd (Z₂.subscheme (R.indnumb_equiv i) ↘ X)
      (Spec.map (CommRingCat.ofHom (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤))) ≫
        Z₁.cov.map γ₁) := by
    rw [pullback.congrHom_hom, pullback.lift_snd]
    exact Category.comp_id _

  set E := (Z₁.chartPasteIso γ₁ i Γ(W, ⊤)).symm ≪≫ asIso mid ≪≫
    pullback.congrHom rfl heq ≪≫
    Z₂.chartPasteIso γ₂ (R.indnumb_equiv i) Γ(W, ⊤) with hE
  have hEsq : E.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.map (algebraMap (Z₂.cov.obj γ₂) Γ(W, ⊤))
        (Z₂.ideal (R.indnumb_equiv i) γ₂)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤)) (Z₁.ideal i γ₁)))) := by
    rw [hE]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    rw [Z₂.chartPasteIso_snd γ₂ (R.indnumb_equiv i) Γ(W, ⊤), hcongr_snd, hmid_snd,
      ← Z₁.chartPasteIso_snd γ₁ i Γ(W, ⊤), ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  set φ : (Γ(W, ⊤) ⧸ Ideal.map (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤)) (Z₁.ideal i γ₁)) ≃+*
      (Γ(W, ⊤) ⧸ Ideal.map (algebraMap (Z₂.cov.obj γ₂) Γ(W, ⊤))
        (Z₂.ideal (R.indnumb_equiv i) γ₂)) :=
    CategoryTheory.Iso.commRingCatIsoToRingEquiv
      { hom := Spec.preimage E.inv
        inv := Spec.preimage E.hom
        hom_inv_id := Spec.map_injective (by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.hom_inv_id,
            Spec.map_id])
        inv_hom_id := Spec.map_injective (by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.inv_hom_id,
            Spec.map_id]) } with hφ
  have hcompat : ∀ r : Γ(W, ⊤),
      Ideal.Quotient.mk (Ideal.map (algebraMap (Z₂.cov.obj γ₂) Γ(W, ⊤))
          (Z₂.ideal (R.indnumb_equiv i) γ₂)) ((RingEquiv.refl Γ(W, ⊤)) r) =
        φ (Ideal.Quotient.mk (Ideal.map (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤))
          (Z₁.ideal i γ₁)) r) := by
    intro r
    have hring : CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (Z₁.cov.obj γ₁) Γ(W, ⊤)) (Z₁.ideal i γ₁))) ≫
        CommRingCat.ofHom (φ : _ →+* _) =
        CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.map (algebraMap (Z₂.cov.obj γ₂) Γ(W, ⊤))
            (Z₂.ideal (R.indnumb_equiv i) γ₂))) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      rw [show CommRingCat.ofHom (φ : _ →+* _) = Spec.preimage E.inv from rfl,
        Spec.map_preimage]
      rw [← hEsq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact (congrArg (fun f => (CommRingCat.Hom.hom f) r) hring).symm
  have := Ideal.map_eq_of_quotientIso (RingEquiv.refl Γ(W, ⊤)) _ _ φ hcompat
  simpa using this.symm

theorem chartIdeal_agree (Z : PreClos X) {W : Scheme.{u+1}} [IsAffine W] {γ γ' : Z.cov.J}
    (a : W ⟶ Spec (Z.cov.obj γ)) (b : W ⟶ Spec (Z.cov.obj γ'))
    (hab : a ≫ Z.cov.map γ = b ≫ Z.cov.map γ') (i : Z.indnumb) :
    Ideal.map (Spec.preimage (W.isoSpec.inv ≫ a)).hom (Z.ideal i γ) =
      Ideal.map (Spec.preimage (W.isoSpec.inv ≫ b)).hom (Z.ideal i γ') :=
  chartIdeal_agree_rel Z Z (relStructure.refl Z) a b hab i
