import GlobalDilProperties

/-!
# Charts of a dilatation, and presenting closed immersions on a cover

Two pieces of infrastructure for the scheme-level Lemma 4.4 of [Ma24]:

* `dilatationCover` — the dilatation `Bl_I X` of a `PreMultiCenter` comes with a
  canonical affine cover by its own charts `Spec A_γ[M_γ]`, assembled from the glue data;
* `presentPreClos` — any closed immersion `c : V ⟶ B` together with a chosen affine
  cover of `B` determines a `PreClos B` (`PUnit`-indexed): the chart ideals are extracted
  from `IsClosedImmersion.Spec_iff` on the pullbacks, exactly as in `reindexIdeal`.

These let a second-stage multicenter live on `Bl^{νD}_Y X` with the dilatation charts as
its covering, so that the ring-level results of `MulticenterQuotient.lean` and
`MulticenterIterate.lean` apply chart-wise.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (N : PreMultiCenter X)

/-- The affine cover of a dilatation by its own charts. -/
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

/-- The chart ideal of a closed immersion on a chosen affine cover. -/
noncomputable def presentIdeal (γ : cov.J) : Ideal (cov.obj γ) :=
  (IsClosedImmersion.Spec_iff.mp (present_pullback_snd_isClosedImmersion c cov γ)).choose

/-- The chart presentation isomorphism. -/
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

/-- Any closed immersion presented as a `PreClos` on a chosen affine cover. -/
noncomputable def presentPreClos : PreClos B where
  indnumb := PUnit
  subscheme _ := V
  over _ := ⟨c⟩
  cov := cov
  ideal _ γ := presentIdeal c cov γ
  condiso _ γ := (presentIso c cov γ).symm
  condover _ γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
    show (presentIso c cov γ).inv ≫ pullback.snd c (cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (presentIdeal c cov γ)))
    rw [presentIso_eq c cov γ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[simp] theorem presentPreClos_ideal (u : PUnit) (γ : cov.J) :
    (presentPreClos c cov).ideal u γ = presentIdeal c cov γ := rfl

end Present
