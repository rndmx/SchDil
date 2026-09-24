import RestrictedPanelPullback

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

def specRingEquivIso {A B : CommRingCat.{u+1}} (e : A ≃+* B) : Spec B ≅ Spec A where
  hom := Spec.map (CommRingCat.ofHom (e : A →+* B))
  inv := Spec.map (CommRingCat.ofHom (e.symm : B →+* A))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((e : A →+* B).comp (e.symm : B →+* A)) = RingHom.id B from
        RingHom.ext fun x => e.apply_symm_apply x]
    show Spec.map (𝟙 _) = 𝟙 _
    rw [Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A from
        RingHom.ext fun x => e.symm_apply_apply x]
    show Spec.map (𝟙 _) = 𝟙 _
    rw [Spec.map_id]

@[simp] theorem specRingEquivIso_hom {A B : CommRingCat.{u+1}} (e : A ≃+* B) :
    (specRingEquivIso e).hom = Spec.map (CommRingCat.ofHom (e : A →+* B)) := rfl

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb] (J : Finset M.indnumb) (i : M.indnumb) (γ : M.cov.J)

section ClosedImmersion

theorem panelHomScheme_isClosedImmersion :
    IsClosedImmersion (M.panelHomScheme J i) := by
  rw [IsLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    ((M.defSpace J).dilatationCover.cover)]
  intro δ
  show IsClosedImmersion (pullback.snd (M.panelHomScheme J i)
    ((M.defSpace J).dilatationCover.map δ))
  haveI : IsClosedImmersion (M.restRhoSch J i δ ) := by
    rw [restRhoSch]
    exact IsClosedImmersion.spec_of_surjective _ (M.restChartRho_surjective J i δ )
  rw [show pullback.snd (M.panelHomScheme J i) ((M.defSpace J).dilatationCover.map δ) =
      inv (M.restChartToPullback J i δ ) ≫ M.restRhoSch J i δ  from by
    rw [← show M.restChartToPullback J i δ  ≫
        pullback.snd (M.panelHomScheme J i) ((M.defSpace J).chartTo δ) =
        M.restRhoSch J i δ  from pullback.lift_snd _ _ _,
      IsIso.inv_hom_id_assoc]
    rfl]
  infer_instance

def restChartQuotEquiv :
    (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ) ⧸
        M.panelChartIdeal J i γ) ≃+*
      Multicenter.Dilatation ((M.restCenterScheme J i).localMulticenter γ) :=
  (Ideal.quotEquivOfEq (M.ker_restChartRho J i γ ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (M.restChartRho_surjective J i γ ))

theorem restChartQuotEquiv_mk
    (x : Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) :
    M.restChartQuotEquiv J i γ  (Ideal.Quotient.mk _ x) =
      M.restChartRho J i γ  x := by
  rfl

def restChartGenIso :
    (M.restCenterScheme J i).chart γ ≅
      Spec (CommRingCat.of (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ) ⧸
        M.panelChartIdeal J i γ)) :=
  specRingEquivIso (M.restChartQuotEquiv J i γ )

theorem restChartGenIso_mk :
    (M.restChartGenIso J i γ ).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.panelChartIdeal J i γ))) =
      M.restRhoSch J i γ  := by
  rw [restChartGenIso, specRingEquivIso_hom, ← Spec.map_comp, restRhoSch]
  congr 1

theorem presentIdeal_panelHomScheme :
    haveI := M.panelHomScheme_isClosedImmersion J i 
    presentIdeal (M.panelHomScheme J i)
        ((M.defSpace J).dilatationCover) γ =
      M.panelChartIdeal J i γ := by
  haveI := M.panelHomScheme_isClosedImmersion J i 
  refine spec_presentation_ideal_unique
    (pullback.snd (M.panelHomScheme J i) ((M.defSpace J).dilatationCover.map γ)) _ _
    (presentIso (M.panelHomScheme J i) ((M.defSpace J).dilatationCover) γ)
    ((asIso (M.restChartToPullback J i γ )).symm ≪≫ M.restChartGenIso J i γ )
    (presentIso_eq (M.panelHomScheme J i) ((M.defSpace J).dilatationCover) γ) ?_
  rw [Iso.trans_hom, Category.assoc, M.restChartGenIso_mk J i γ , Iso.symm_hom,
    asIso_inv]
  symm
  rw [IsIso.inv_comp_eq]
  show M.restRhoSch J i γ  =
    M.restChartToPullback J i γ  ≫
      pullback.snd (M.panelHomScheme J i) ((M.defSpace J).chartTo γ)
  rw [restChartToPullback, pullback.lift_snd]

end ClosedImmersion

end PreMultiCenter

end SchemeDilatation
