import CenterCover
import PolyptychSchemeDatum
import SchemeLemma44

/-!
# The restricted datum `(D_J, X_J)|_{X_i}` as a `PreMultiCenter` on `X_i`

Dubouloz-Mayeux define the panel `(𝔻_J)_i` as the multi-centered dilatation of `X_i` along
the restricted datum

`(D_J, X_J)|_{X_i} = { (X_j ∩ X_i , (Σ_{s ∈ J≥j} D_s)|_{X_i}) }_{j ∈ J}`.

This file builds that datum.  Its covering is `centerCover`, so its charts are literally
`A_γ ⧸ M_i` and its chart ideals are literally the images of the chart ideals of `𝔻_J`;
that is what lets the ring-level theory (`quotCenter`, `quotHom`, `panelHom`,
`PolyptychRestricted`) apply chart by chart.

The chart isomorphisms `YcondIso`/`DcondIso` come from a general observation, proved here:
the chart ideal of a base-changed closed subscheme is the image of its chart ideal, as soon
as the two charts are linked by a ring map making the evident square commute
(`presentIdeal_pullback_snd_of_cone`); for `centerCover` that square is
`centerCover_map_overX`.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace SchemeDilatation
open SchemeDilatation.PreMultiCenter

section Present

variable {B V : Scheme.{u+1}} (c : V ⟶ B) [IsClosedImmersion c]
  (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) B)

set_option maxHeartbeats 1000000 in
/-- **Chart ideal of a base-changed closed subscheme**: if the chart `cov.map γ` of the new
base and the chart `Z.cov.map δ` of the old one are linked by a ring map `ρ` making the
square commute, then the chart ideal of `Z_u ×_{B_i} B` is the image along `ρ` of the chart
ideal of `Z_u`. -/
theorem presentIdeal_pullback_snd_of_cone
    {Bi : Scheme.{u+1}} (Z : PreClos Bi) (u : Z.indnumb) (fi : B ⟶ Bi)
    (γ : cov.J) (δ : Z.cov.J) (ρ : Z.cov.obj δ ⟶ cov.obj γ)
    (hcone : cov.map γ ≫ fi = Spec.map ρ ≫ Z.cov.map δ) :
    haveI : IsClosedImmersion (pullback.snd (Z.subscheme u ↘ Bi) fi) :=
      MorphismProperty.pullback_snd _ _ (Z.subscheme_isClosedImmersion u)
    presentIdeal (pullback.snd (Z.subscheme u ↘ Bi) fi) cov γ =
      Ideal.map ρ.hom (Z.ideal u δ) := by
  haveI : IsClosedImmersion (pullback.snd (Z.subscheme u ↘ Bi) fi) :=
    MorphismProperty.pullback_snd _ _ (Z.subscheme_isClosedImmersion u)
  letI : Algebra (Z.cov.obj δ) (cov.obj γ) := ρ.hom.toAlgebra
  show presentIdeal (pullback.snd (Z.subscheme u ↘ Bi) fi) cov γ =
    Ideal.map (algebraMap (Z.cov.obj δ) (cov.obj γ)) (Z.ideal u δ)
  have hcone' : cov.map γ ≫ fi =
      Spec.map (CommRingCat.ofHom (algebraMap (Z.cov.obj δ) (cov.obj γ))) ≫ Z.cov.map δ :=
    hcone
  refine spec_presentation_ideal_unique
    (pullback.snd (pullback.snd (Z.subscheme u ↘ Bi) fi) (cov.map γ)) _ _
    (presentIso (pullback.snd (Z.subscheme u ↘ Bi) fi) cov γ)
    (pullbackLeftPullbackSndIso (Z.subscheme u ↘ Bi) fi (cov.map γ) ≪≫
      pullback.congrHom rfl hcone' ≪≫ Z.chartPasteIso δ u (cov.obj γ))
    (presentIso_eq (pullback.snd (Z.subscheme u ↘ Bi) fi) cov γ) ?_
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    Z.chartPasteIso_snd δ u (cov.obj γ),
    pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]

/-- The chart presentation isomorphism, transported along a computation of the chart
ideal. -/
def presentIsoOfEq (γ : cov.J) {I : Ideal (cov.obj γ)}
    (h : presentIdeal c cov γ = I) :
    Spec (CommRingCat.of (cov.obj γ ⧸ I)) ≅ pullback c (cov.map γ) :=
  eqToIso (congrArg (fun K => Spec (CommRingCat.of (cov.obj γ ⧸ K))) h.symm) ≪≫
    (presentIso c cov γ).symm

theorem presentIsoOfEq_over (γ : cov.J) {I : Ideal (cov.obj γ)}
    (h : presentIdeal c cov γ = I) :
    (presentIsoOfEq c cov γ h).hom ≫ pullback.snd c (cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  subst h
  show (eqToIso (congrArg (fun K => Spec (CommRingCat.of (cov.obj γ ⧸ K))) rfl) ≪≫
    (presentIso c cov γ).symm).hom ≫ _ = _
  rw [Iso.trans_hom, Iso.symm_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp,
    presentIso_eq c cov γ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Present

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb]

section RestrictedDatum

variable (J : Finset M.indnumb) (i : M.indnumb)

instance restYsub_isClosedImmersion (j : (M.defSpace J).indnumb) :
    IsClosedImmersion (pullback.snd ((M.defSpace J).Ysub j ↘ X) (M.Ysub i ↘ X)) :=
  MorphismProperty.pullback_snd _ _
    ((M.defSpace J).Yrep.subscheme_isClosedImmersion j)

instance restDsub_isClosedImmersion (j : (M.defSpace J).indnumb) :
    IsClosedImmersion (pullback.snd ((M.defSpace J).Dsub j ↘ X) (M.Ysub i ↘ X)) :=
  MorphismProperty.pullback_snd _ _
    ((M.defSpace J).Drep.subscheme_isClosedImmersion j)

/-- On the chart `A_γ ⧸ M_i` of `X_i`, the center `X_j ∩ X_i` is cut out by the image of
the ideal of `X_j`. -/
theorem centerCover_presentIdeal_Y (j : (M.defSpace J).indnumb) (γ : M.cov.J) :
    presentIdeal (pullback.snd ((M.defSpace J).Ysub j ↘ X) (M.Ysub i ↘ X))
        (M.centerCover i) γ =
      Ideal.map (Ideal.Quotient.mk (M.Yideal i γ))
        ((M.defSpace J).Yideal j γ) :=
  presentIdeal_pullback_snd_of_cone (M.centerCover i) (M.defSpace J).Yrep j
    (M.Ysub i ↘ X) γ γ (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i γ)))
    (M.centerCover_map_overX i γ)

/-- On the chart `A_γ ⧸ M_i` of `X_i`, the divisor `(Σ_{s ∈ J≥j} D_s)|_{X_i}` is cut out by
the image of the ideal of `Σ_{s ∈ J≥j} D_s`. -/
theorem centerCover_presentIdeal_D (j : (M.defSpace J).indnumb) (γ : M.cov.J) :
    presentIdeal (pullback.snd ((M.defSpace J).Dsub j ↘ X) (M.Ysub i ↘ X))
        (M.centerCover i) γ =
      Ideal.map (Ideal.Quotient.mk (M.Yideal i γ))
        ((M.defSpace J).Dideal j γ) :=
  presentIdeal_pullback_snd_of_cone (M.centerCover i) (M.defSpace J).Drep j
    (M.Ysub i ↘ X) γ γ (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i γ)))
    (M.centerCover_map_overX i γ)

/-- **The restricted datum `(D_J, X_J)|_{X_i}`**, as a multicenter on the center `X_i`:
centers `X_j ∩ X_i`, divisors `(Σ_{s ∈ J≥j} D_s)|_{X_i}`, on the covering `centerCover`
whose charts are `A_γ ⧸ M_i`. -/
def restCenterScheme : PreMultiCenter (M.Ysub i) where
  indnumb := (M.defSpace J).indnumb
  cov := M.centerCover i
  Ysub j := pullback ((M.defSpace J).Ysub j ↘ X) (M.Ysub i ↘ X)
  Dsub j := pullback ((M.defSpace J).Dsub j ↘ X) (M.Ysub i ↘ X)
  Yover j := ⟨pullback.snd _ _⟩
  Dover j := ⟨pullback.snd _ _⟩
  Yideal j γ := Ideal.map (Ideal.Quotient.mk (M.Yideal i γ))
    ((M.defSpace J).Yideal j γ)
  Dideal j γ := Ideal.map (Ideal.Quotient.mk (M.Yideal i γ))
    ((M.defSpace J).Dideal j γ)
  YcondIso j γ := presentIsoOfEq
    (pullback.snd ((M.defSpace J).Ysub j ↘ X) (M.Ysub i ↘ X)) (M.centerCover i) γ
    (M.centerCover_presentIdeal_Y J i j γ)
  YcondOver j γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
    exact presentIsoOfEq_over
      (pullback.snd ((M.defSpace J).Ysub j ↘ X) (M.Ysub i ↘ X)) (M.centerCover i) γ
      (M.centerCover_presentIdeal_Y J i j γ)
  DcondIso j γ := presentIsoOfEq
    (pullback.snd ((M.defSpace J).Dsub j ↘ X) (M.Ysub i ↘ X)) (M.centerCover i) γ
    (M.centerCover_presentIdeal_D J i j γ)
  DcondOver j γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
    exact presentIsoOfEq_over
      (pullback.snd ((M.defSpace J).Dsub j ↘ X) (M.Ysub i ↘ X)) (M.centerCover i) γ
      (M.centerCover_presentIdeal_D J i j γ)
  Dprin j γ := by
    apply Submodule.IsPrincipal.map_ringHom
    exact (M.defSpace J).Dprin j γ

@[simp] theorem restCenterScheme_indnumb :
    (M.restCenterScheme J i).indnumb = (M.defSpace J).indnumb := rfl

@[simp] theorem restCenterScheme_cov :
    (M.restCenterScheme J i).cov = M.centerCover i := rfl

@[simp] theorem restCenterScheme_Yideal (j : (M.defSpace J).indnumb) (γ : M.cov.J) :
    (M.restCenterScheme J i).Yideal j γ =
      Ideal.map (Ideal.Quotient.mk (M.Yideal i γ))
        (M.Yideal j.1 γ) := rfl

@[simp] theorem restCenterScheme_Dideal (j : (M.defSpace J).indnumb) (γ : M.cov.J) :
    (M.restCenterScheme J i).Dideal j γ =
      Ideal.map (Ideal.Quotient.mk (M.Yideal i γ))
        (∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γ) := rfl

/-- **The panel `(𝔻_J)_i`**, constructed the way the paper defines it: the multi-centered
dilatation of `X_i` along the restricted datum `(D_J, X_J)|_{X_i}`. -/
def restPanel : Scheme.{u+1} := (M.restCenterScheme J i).dilatation

/-- The panel is a scheme over `X_i`. -/
instance : Scheme.Over (M.restPanel J i) (M.Ysub i) :=
  ⟨(M.restCenterScheme J i).structureMap⟩

end RestrictedDatum

end PreMultiCenter

end SchemeDilatation
