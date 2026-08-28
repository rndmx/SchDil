import CubeIdentity
import PreClosClosedImmersion

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

variable {X : Scheme.{u+1}}

noncomputable def PreClos.interSub (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) : Scheme :=
  pullback (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X)

noncomputable instance PreClos.interSub_over (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) : Scheme.Over (W.interSub Z e i) X :=
  ⟨pullback.fst (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≫ (W.subscheme i ↘ X)⟩

instance PreClos.interSub_isClosedImmersion (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) : IsClosedImmersion (W.interSub Z e i ↘ X) := by
  show IsClosedImmersion (pullback.fst (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≫
    (W.subscheme i ↘ X))
  haveI : IsClosedImmersion
      (pullback.fst (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X)) :=
    MorphismProperty.pullback_fst _ _ (Z.subscheme_isClosedImmersion (e i))
  haveI := W.subscheme_isClosedImmersion i
  infer_instance

instance PreClos.interSub_snd (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    IsClosedImmersion (pullback.snd (W.interSub Z e i ↘ X) (W.cov.map γ)) :=
  MorphismProperty.pullback_snd _ _ (W.interSub_isClosedImmersion Z e i)

noncomputable def PreClos.interIdeal (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) : Ideal (W.cov.obj γ) :=
  (IsClosedImmersion.Spec_iff.mp (W.interSub_snd Z e i γ)).choose

noncomputable def PreClos.interIso (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    pullback (W.interSub Z e i ↘ X) (W.cov.map γ) ≅
      Spec (CommRingCat.of (W.cov.obj γ ⧸ W.interIdeal Z e i γ)) :=
  (IsClosedImmersion.Spec_iff.mp (W.interSub_snd Z e i γ)).choose_spec.choose

theorem PreClos.interIso_eq (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    pullback.snd (W.interSub Z e i ↘ X) (W.cov.map γ) =
      (W.interIso Z e i γ).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.interIdeal Z e i γ))) :=
  (IsClosedImmersion.Spec_iff.mp (W.interSub_snd Z e i γ)).choose_spec.choose_spec

noncomputable def PreClos.inter (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb) :
    PreClos X where
  indnumb := W.indnumb
  subscheme i := W.interSub Z e i
  cov := W.cov
  ideal i γ := W.interIdeal Z e i γ
  condiso i γ := (W.interIso Z e i γ).symm
  condover i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
    show (W.interIso Z e i γ).inv ≫
      pullback.snd (W.interSub Z e i ↘ X) (W.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.interIdeal Z e i γ)))
    rw [W.interIso_eq Z e i γ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

noncomputable def relStructure.reIso {Z Z₁ : PreClos X} (R : relStructure Z Z₁)
    (i : Z.indnumb) {k : Z₁.indnumb} (h : R.indnumb_equiv i = k) :
    Z.subscheme i ≅ Z₁.subscheme k :=
  R.subscheme_iso i ≪≫ eqToIso (congrArg Z₁.subscheme h)

theorem relStructure.reIso_over {Z Z₁ : PreClos X} (R : relStructure Z Z₁)
    (i : Z.indnumb) {k : Z₁.indnumb} (h : R.indnumb_equiv i = k) :
    (R.reIso i h).hom ≫ (Z₁.subscheme k ↘ X) = (Z.subscheme i ↘ X) := by
  have hover := R.subscheme_iso_over i
  rw [Scheme.Hom.isOver_iff] at hover
  show (R.subscheme_iso i).hom ≫ eqToHom (congrArg Z₁.subscheme h) ≫
    (Z₁.subscheme k ↘ X) = _
  rw [(Z₁.index_eq_triangle _ _ h).comp_over, hover]

theorem relStructure.reIso_inv_over {Z Z₁ : PreClos X} (R : relStructure Z Z₁)
    (i : Z.indnumb) {k : Z₁.indnumb} (h : R.indnumb_equiv i = k) :
    (R.reIso i h).inv ≫ (Z.subscheme i ↘ X) = (Z₁.subscheme k ↘ X) := by
  rw [← R.reIso_over i h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

noncomputable def PreClos.interMapIso (W Z W₁ Z₁ : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (e₁ : W₁.indnumb ≃ Z₁.indnumb) (R : relStructure W W₁) (R' : relStructure Z Z₁)
    (hcomm : ∀ i, R'.indnumb_equiv (e i) = e₁ (R.indnumb_equiv i)) (i : W.indnumb) :
    pullback (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≅
      pullback (W₁.subscheme (R.indnumb_equiv i) ↘ X)
        (Z₁.subscheme (e₁ (R.indnumb_equiv i)) ↘ X) :=
  asIso (pullback.map (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X)
    (W₁.subscheme (R.indnumb_equiv i) ↘ X) (Z₁.subscheme (e₁ (R.indnumb_equiv i)) ↘ X)
    (R.subscheme_iso i).hom (R'.reIso (e i) (hcomm i)).hom (𝟙 X)
    (by rw [Category.comp_id]; exact ((R.subscheme_iso_over i).comp_over).symm)
    (by rw [Category.comp_id]; exact (R'.reIso_over (e i) (hcomm i)).symm))

theorem PreClos.interMapIso_hom_fst (W Z W₁ Z₁ : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (e₁ : W₁.indnumb ≃ Z₁.indnumb) (R : relStructure W W₁) (R' : relStructure Z Z₁)
    (hcomm : ∀ i, R'.indnumb_equiv (e i) = e₁ (R.indnumb_equiv i)) (i : W.indnumb) :
    (W.interMapIso Z W₁ Z₁ e e₁ R R' hcomm i).hom ≫
      pullback.fst (W₁.subscheme (R.indnumb_equiv i) ↘ X)
        (Z₁.subscheme (e₁ (R.indnumb_equiv i)) ↘ X) =
      pullback.fst (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≫
        (R.subscheme_iso i).hom := by
  unfold interMapIso
  rw [asIso_hom]
  exact pullback.lift_fst _ _ _

noncomputable def PreClos.interRel (W Z W₁ Z₁ : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (e₁ : W₁.indnumb ≃ Z₁.indnumb) (R : relStructure W W₁) (R' : relStructure Z Z₁)
    (hcomm : ∀ i, R'.indnumb_equiv (e i) = e₁ (R.indnumb_equiv i)) :
    relStructure (W.inter Z e) (W₁.inter Z₁ e₁) where
  indnumb_equiv := R.indnumb_equiv
  subscheme_iso i := W.interMapIso Z W₁ Z₁ e e₁ R R' hcomm i
  subscheme_iso_over i := ⟨by
    show (W.interMapIso Z W₁ Z₁ e e₁ R R' hcomm i).hom ≫
        (pullback.fst (W₁.subscheme (R.indnumb_equiv i) ↘ X)
          (Z₁.subscheme (e₁ (R.indnumb_equiv i)) ↘ X) ≫
          (W₁.subscheme (R.indnumb_equiv i) ↘ X)) =
      pullback.fst (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≫ (W.subscheme i ↘ X)
    rw [← Category.assoc, W.interMapIso_hom_fst Z W₁ Z₁ e e₁ R R' hcomm i,
      Category.assoc, (R.subscheme_iso_over i).comp_over]⟩

noncomputable def PreClosF.inter {ι : Type} (W Z : PreClosF X ι) : PreClosF X ι :=
  ⟨W.1.inter Z.1 ((Equiv.cast W.2).trans (Equiv.cast Z.2.symm)), W.2⟩

noncomputable def ClosF.inter {ι : Type} (W Z : ClosF X ι) : ClosF X ι :=
  Quotient.lift₂
    (fun W Z => (Quotient.mk'' (PreClosF.inter W Z) : ClosF X ι))
    (fun W Z W₁ Z₁ hW hZ => by
      obtain ⟨RW⟩ := hW
      obtain ⟨RZ⟩ := hZ
      refine Quotient.sound
        ⟨⟨W.1.interRel Z.1 W₁.1 Z₁.1 _ _ RW.toRel RZ.toRel ?_, ?_⟩⟩
      · intro i
        rw [RZ.rigid, RW.rigid]
        simp only [Equiv.trans_apply, Equiv.cast_apply, cast_cast]
      · intro i
        exact RW.rigid i) W Z

instance PreClos.inter_fst_isClosedImmersion (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) :
    IsClosedImmersion (pullback.fst (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X)) :=
  MorphismProperty.pullback_fst _ _ (Z.subscheme_isClosedImmersion (e i))

instance PreClos.inter_snd_isClosedImmersion (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) :
    IsClosedImmersion (pullback.snd (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X)) :=
  MorphismProperty.pullback_snd _ _ (W.subscheme_isClosedImmersion i)

theorem PreClos.inter_fst_over (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) :
    pullback.fst (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≫ (W.subscheme i ↘ X) =
      ((W.inter Z e).subscheme i ↘ X) := rfl

theorem PreClos.inter_snd_over (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) :
    pullback.snd (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≫ (Z.subscheme (e i) ↘ X) =
      ((W.inter Z e).subscheme i ↘ X) :=
  pullback.condition.symm

noncomputable def PreClos.interCommIso (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) :
    pullback (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≅
      pullback (Z.subscheme (e i) ↘ X) (W.subscheme (e.symm (e i)) ↘ X) :=
  pullbackSymmetry (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≪≫
    asIso (pullback.map (Z.subscheme (e i) ↘ X) (W.subscheme i ↘ X)
      (Z.subscheme (e i) ↘ X) (W.subscheme (e.symm (e i)) ↘ X)
      (𝟙 (Z.subscheme (e i))) (eqToHom (congrArg W.subscheme (e.symm_apply_apply i).symm))
      (𝟙 X)
      (by rw [Category.comp_id, Category.id_comp])
      (by
        rw [Category.comp_id]
        exact ((W.index_eq_triangle i (e.symm (e i))
          (e.symm_apply_apply i).symm).comp_over).symm))

theorem PreClos.interCommIso_hom_fst (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) :
    (W.interCommIso Z e i).hom ≫
      pullback.fst (Z.subscheme (e i) ↘ X) (W.subscheme (e.symm (e i)) ↘ X) =
      pullback.snd (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) := by
  unfold interCommIso
  rw [Iso.trans_hom, asIso_hom, Category.assoc, pullback.lift_fst, Category.comp_id,
    pullbackSymmetry_hom_comp_fst]

noncomputable def PreClos.interCommRel (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb) :
    relStructure (W.inter Z e) (Z.inter W e.symm) where
  indnumb_equiv := e
  subscheme_iso i := W.interCommIso Z e i
  subscheme_iso_over i := ⟨by
    show (W.interCommIso Z e i).hom ≫
        (pullback.fst (Z.subscheme (e i) ↘ X) (W.subscheme (e.symm (e i)) ↘ X) ≫
          (Z.subscheme (e i) ↘ X)) =
      pullback.fst (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≫ (W.subscheme i ↘ X)
    rw [← Category.assoc, W.interCommIso_hom_fst Z e i]
    exact pullback.condition.symm⟩

theorem ClosF.inter_comm {ι : Type} (W Z : ClosF X ι) : W.inter Z = Z.inter W := by
  induction W using Quotient.inductionOn with | h W =>
  induction Z using Quotient.inductionOn with | h Z =>
  refine Quotient.sound ⟨⟨W.1.interCommRel Z.1 _, ?_⟩⟩
  intro i
  show ((Equiv.cast W.2).trans (Equiv.cast Z.2.symm)) i = _
  simp only [Equiv.trans_apply, Equiv.cast_apply, cast_cast]

noncomputable def PreClos.interChartIso (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    pullback (pullback.snd (W.subscheme i ↘ X) (W.cov.map γ))
        (pullback.snd (Z.subscheme (e i) ↘ X) (W.cov.map γ)) ≅
      pullback ((W.inter Z e).subscheme i ↘ X) (W.cov.map γ) :=
  pullback.cube₀ (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) (W.cov.map γ) ≪≫
    pullback.squash₄ (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) (W.cov.map γ)

theorem PreClos.condiso_over (Z : PreClos X) (i : Z.indnumb) (γ : Z.cov.J) :
    (Z.condiso i γ).hom ≫ pullback.snd (Z.subscheme i ↘ X) (Z.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal i γ))) := by
  have h := Z.condover i γ
  rw [Scheme.Hom.isOver_iff] at h
  exact h

theorem PreClos.reindexIso_inv_over (Z : PreClos X)
    (cov' : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) (i : Z.indnumb) (γ : cov'.J) :
    (Z.reindexIso cov' i γ).inv ≫ pullback.snd (Z.subscheme i ↘ X) (cov'.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.reindexIdeal cov' i γ))) := by
  rw [Z.reindexIso_eq cov' i γ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

noncomputable def PreClos.interQuotIso (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.ideal i γ))))
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Z.reindexIdeal W.cov (e i) γ)))) ≅
      pullback (pullback.snd (W.subscheme i ↘ X) (W.cov.map γ))
        (pullback.snd (Z.subscheme (e i) ↘ X) (W.cov.map γ)) :=
  asIso (pullback.map
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.ideal i γ))))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.reindexIdeal W.cov (e i) γ))))
    (pullback.snd (W.subscheme i ↘ X) (W.cov.map γ))
    (pullback.snd (Z.subscheme (e i) ↘ X) (W.cov.map γ))
    (W.condiso i γ).hom (Z.reindexIso W.cov (e i) γ).inv (𝟙 (Spec (W.cov.obj γ)))
    (by rw [Category.comp_id]; exact (W.condiso_over i γ).symm)
    (by rw [Category.comp_id]; exact (Z.reindexIso_inv_over W.cov (e i) γ).symm))

theorem PreClos.interChartIso_hom_snd (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    (W.interChartIso Z e i γ).hom ≫
        pullback.snd ((W.inter Z e).subscheme i ↘ X) (W.cov.map γ) =
      pullback.fst (pullback.snd (W.subscheme i ↘ X) (W.cov.map γ))
          (pullback.snd (Z.subscheme (e i) ↘ X) (W.cov.map γ)) ≫
        pullback.snd (W.subscheme i ↘ X) (W.cov.map γ) := by
  show (W.interChartIso Z e i γ).hom ≫
      pullback.snd (pullback.fst (W.subscheme i ↘ X) (Z.subscheme (e i) ↘ X) ≫
        W.subscheme i ↘ X) (W.cov.map γ) = _
  simp [PreClos.interChartIso]

theorem lemma_iso_symm_tmul_one {A : Type*} [CommRing A] (I J : Ideal A) (r : A) :
    ((lemma_iso A (A ⧸ J) I).symm) (Ideal.Quotient.mk I r ⊗ₜ[A] (1 : A ⧸ J)) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A (A ⧸ J)) I) (Ideal.Quotient.mk J r) := by
  simp only [lemma_iso]
  erw [AlgEquiv.symm_trans_apply]
  simp only [Algebra.TensorProduct.comm_symm_tmul, AlgEquiv.symm_trans_apply]
  rw [AlgEquiv.restrictScalars_symm]
  simp only [AlgEquiv.coe_restrictScalars']
  erw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  simp only [Ideal.Quotient.mk_eq_mk]
  congr 1
  rw [Algebra.smul_def, mul_one]
  rfl

theorem quotTensorQuotEquiv_mk_tmul_one {A : Type*} [CommRing A] (I J : Ideal A) (r : A) :
    quotTensorQuotEquiv A I J (Ideal.Quotient.mk I r ⊗ₜ[A] (1 : A ⧸ J)) =
      Ideal.Quotient.mk (I ⊔ J) r := by
  simp only [quotTensorQuotEquiv, RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe]
  erw [lemma_iso_symm_tmul_one]
  rw [show (Ideal.Quotient.mk (Ideal.map (algebraMap A (A ⧸ J)) I))
        ((Ideal.Quotient.mk J) r) = DoubleQuot.quotQuotMk J I r from rfl]
  first
    | rfl
    | simp
    | simp [DoubleQuot.quotQuotMk, Ideal.quotEquivOfEq_mk]
    | (erw [Ideal.quotEquivOfEq_mk]; rfl)

set_option maxHeartbeats 1000000 in
noncomputable def PreClos.quotSupSpecIso (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    Spec (CommRingCat.of (W.cov.obj γ ⧸
        (W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ))) ≅
      Spec (CommRingCat.of (TensorProduct (W.cov.obj γ)
        (W.cov.obj γ ⧸ W.ideal i γ)
        (W.cov.obj γ ⧸ Z.reindexIdeal W.cov (e i) γ))) :=
  ⟨Spec.map (CommRingCat.ofHom
      ((quotTensorQuotEquiv (W.cov.obj γ) (W.ideal i γ)
        (Z.reindexIdeal W.cov (e i) γ)) : _ →+* _)),
   Spec.map (CommRingCat.ofHom
      ((quotTensorQuotEquiv (W.cov.obj γ) (W.ideal i γ)
        (Z.reindexIdeal W.cov (e i) γ)).symm : _ →+* _)),
   (by
     rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
     refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
     refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
     exact RingHom.ext fun x =>
       (quotTensorQuotEquiv (W.cov.obj γ) (W.ideal i γ)
         (Z.reindexIdeal W.cov (e i) γ)).apply_symm_apply x),
   (by
     rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
     refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
     refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
     exact RingHom.ext fun x =>
       (quotTensorQuotEquiv (W.cov.obj γ) (W.ideal i γ)
         (Z.reindexIdeal W.cov (e i) γ)).symm_apply_apply x)⟩

noncomputable def PreClos.interSupIso (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    Spec (CommRingCat.of (W.cov.obj γ ⧸
        (W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ))) ≅
      Spec (CommRingCat.of (W.cov.obj γ ⧸ W.interIdeal Z e i γ)) :=
  W.quotSupSpecIso Z e i γ ≪≫
    (AlgebraicGeometry.pullbackSpecIso (W.cov.obj γ) (W.cov.obj γ ⧸ W.ideal i γ)
      (W.cov.obj γ ⧸ Z.reindexIdeal W.cov (e i) γ)).symm ≪≫
    W.interQuotIso Z e i γ ≪≫ W.interChartIso Z e i γ ≪≫ W.interIso Z e i γ

set_option maxHeartbeats 1000000 in
theorem PreClos.interSupIso_hom_over (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    (W.interSupIso Z e i γ).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.interIdeal Z e i γ))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ))) := by
  have hA : (W.interChartIso Z e i γ).hom ≫ (W.interIso Z e i γ).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.interIdeal Z e i γ))) =
      pullback.fst (pullback.snd (W.subscheme i ↘ X) (W.cov.map γ))
          (pullback.snd (Z.subscheme (e i) ↘ X) (W.cov.map γ)) ≫
        pullback.snd (W.subscheme i ↘ X) (W.cov.map γ) := by
    rw [← W.interIso_eq Z e i γ]
    exact W.interChartIso_hom_snd Z e i γ
  have hB : (W.interQuotIso Z e i γ).hom ≫
      pullback.fst (pullback.snd (W.subscheme i ↘ X) (W.cov.map γ))
        (pullback.snd (Z.subscheme (e i) ↘ X) (W.cov.map γ)) =
      pullback.fst (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.ideal i γ))))
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (Z.reindexIdeal W.cov (e i) γ)))) ≫
        (W.condiso i γ).hom := by
    simp [PreClos.interQuotIso]
  have hE : CommRingCat.ofHom (Ideal.Quotient.mk (W.ideal i γ)) ≫
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          (W.cov.obj γ ⧸ W.ideal i γ) →+* TensorProduct (W.cov.obj γ)
            (W.cov.obj γ ⧸ W.ideal i γ)
            (W.cov.obj γ ⧸ Z.reindexIdeal W.cov (e i) γ)) ≫
      CommRingCat.ofHom ((quotTensorQuotEquiv (W.cov.obj γ) (W.ideal i γ)
        (Z.reindexIdeal W.cov (e i) γ)) : _ →+* _) =
      CommRingCat.ofHom (Ideal.Quotient.mk
        (W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ)) := by
    ext r
    exact quotTensorQuotEquiv_mk_tmul_one (W.ideal i γ)
      (Z.reindexIdeal W.cov (e i) γ) r
  simp only [PreClos.interSupIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, hA]
  rw [← Category.assoc ((W.interQuotIso Z e i γ).hom), hB, Category.assoc,
    W.condiso_over i γ, ← Category.assoc
      ((AlgebraicGeometry.pullbackSpecIso (W.cov.obj γ) (W.cov.obj γ ⧸ W.ideal i γ)
        (W.cov.obj γ ⧸ Z.reindexIdeal W.cov (e i) γ)).inv)]
  erw [AlgebraicGeometry.pullbackSpecIso_inv_fst]
  show Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc, hE]

set_option maxHeartbeats 1000000 in
theorem PreClos.interIdeal_eq (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    W.interIdeal Z e i γ = W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ := by
  set φ : ((W.cov.obj γ) ⧸ (W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ)) ≃+*
      ((W.cov.obj γ) ⧸ W.interIdeal Z e i γ) :=
    CategoryTheory.Iso.commRingCatIsoToRingEquiv
      { hom := Spec.preimage (W.interSupIso Z e i γ).inv
        inv := Spec.preimage (W.interSupIso Z e i γ).hom
        hom_inv_id := Spec.map_injective (by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.hom_inv_id,
            Spec.map_id])
        inv_hom_id := Spec.map_injective (by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.inv_hom_id,
            Spec.map_id]) } with hφ
  have hcompat : ∀ r : (W.cov.obj γ),
      Ideal.Quotient.mk (W.interIdeal Z e i γ)
          ((RingEquiv.refl (W.cov.obj γ)) r) =
        φ (Ideal.Quotient.mk
          (W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ) r) := by
    intro r
    have hring : CommRingCat.ofHom (Ideal.Quotient.mk
        (W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ)) ≫
        CommRingCat.ofHom (φ : _ →+* _) =
        CommRingCat.ofHom (Ideal.Quotient.mk (W.interIdeal Z e i γ)) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      rw [show CommRingCat.ofHom (φ : _ →+* _) =
          Spec.preimage (W.interSupIso Z e i γ).inv from rfl, Spec.map_preimage]
      rw [← W.interSupIso_hom_over Z e i γ, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]
    exact (congrArg (fun f => (CommRingCat.Hom.hom f) r) hring).symm
  have := Ideal.map_eq_of_quotientIso (RingEquiv.refl (W.cov.obj γ)) _ _ φ hcompat
  simpa using this
