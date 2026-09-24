import PreClosClosedImmersion
import SchemeLemma44

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

variable {X : Scheme.{u+1}}

section OfFamily

variable {ι : Type} (Y : ι → Scheme.{u+1}) [∀ i, Scheme.Over (Y i) X]
  (h : ∀ i, IsClosedImmersion (Y i ↘ X))
  (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X)

instance famPullbackSnd (i : ι) (γ : cov.J) :
    IsClosedImmersion (pullback.snd (Y i ↘ X) (cov.map γ)) :=
  MorphismProperty.pullback_snd _ _ (h i)

noncomputable def famIdeal (i : ι) (γ : cov.J) : Ideal (cov.obj γ) :=
  (IsClosedImmersion.Spec_iff.mp (famPullbackSnd Y h cov i γ)).choose

noncomputable def famIso (i : ι) (γ : cov.J) :
    pullback (Y i ↘ X) (cov.map γ) ≅
      Spec (CommRingCat.of (cov.obj γ ⧸ famIdeal Y h cov i γ)) :=
  (IsClosedImmersion.Spec_iff.mp
    (famPullbackSnd Y h cov i γ)).choose_spec.choose

theorem famIso_eq (i : ι) (γ : cov.J) :
    pullback.snd (Y i ↘ X) (cov.map γ) =
      (famIso Y h cov i γ).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (famIdeal Y h cov i γ))) :=
  (IsClosedImmersion.Spec_iff.mp (famPullbackSnd Y h cov i γ)).choose_spec.choose_spec

theorem famIdeal_unique (i : ι) (γ : cov.J) (K : Ideal (cov.obj γ))
    (e : pullback (Y i ↘ X) (cov.map γ) ≅
      Spec (CommRingCat.of (cov.obj γ ⧸ K)))
    (he : pullback.snd (Y i ↘ X) (cov.map γ) =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :
    famIdeal Y h cov i γ = K :=
  SchemeDilatation.PreMultiCenter.spec_presentation_ideal_unique _ _ _
    (famIso Y h cov i γ) e (famIso_eq Y h cov i γ) he

noncomputable def PreClos.ofFamily : PreClos X where
  indnumb := ι
  subscheme := Y
  cov := cov
  ideal := famIdeal Y h cov
  condiso i γ := (famIso Y h cov i γ).symm
  condover i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (famIso Y h cov i γ).inv ≫ pullback.snd (Y i ↘ X) (cov.map γ) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (famIdeal Y h cov i γ)))
    rw [famIso_eq Y h cov i γ, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]

@[simp] theorem PreClos.ofFamily_indnumb : (PreClos.ofFamily Y h cov).indnumb = ι := rfl

@[simp] theorem PreClos.ofFamily_subscheme :
    (PreClos.ofFamily Y h cov).subscheme = Y := rfl

end OfFamily

theorem clos_eq_iff (Z Z' : PreClos X) :
    (Quotient.mk'' Z : Clos X) = Quotient.mk'' Z' ↔ Nonempty (relStructure Z Z') :=
  Quotient.eq''

theorem PreClos.exists_presentation {ι : Type} (Y : ι → Scheme.{u+1})
    [∀ i, Scheme.Over (Y i) X] (h : ∀ i, IsClosedImmersion (Y i ↘ X))
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) :
    ∃ Z : PreClos X, ∃ e : Z.indnumb = ι, ∀ i, Z.subscheme (e ▸ i) = Y i :=
  ⟨PreClos.ofFamily Y h cov, rfl, fun _ => rfl⟩

noncomputable def Clos.ofClosedImmersions {ι : Type}
    (Y : ι → Scheme.{u+1})
    [∀ i, Scheme.Over (Y i) X] (h : ∀ i, IsClosedImmersion (Y i ↘ X))
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) :
    Clos X :=
  Quotient.mk'' (PreClos.ofFamily Y h cov)

theorem Clos.ofClosedImmersions_self (Z : PreClos X)
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) :
    Clos.ofClosedImmersions Z.subscheme
        Z.subscheme_isClosedImmersion cov =
      Quotient.mk'' Z :=
  Quotient.sound
    ⟨{ indnumb_equiv := Equiv.refl _
       subscheme_iso := fun _ => Iso.refl _
       subscheme_iso_over := fun _ => ⟨rfl⟩ }⟩
