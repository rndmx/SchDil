import RestrictedPanelPullback
import PolyptychPaperForm

/-!
# The constructed panel **is** the panel of `PolyptychStage`

`panelHomScheme : (𝔻_J)_i ⟶ 𝔻_J` is a closed immersion whose chart ideal is the panel ideal
`ker(F_J(i)^*)`.  Under dilatation-regularity that is exactly the chart ideal of the
second-stage center of `panelStage`, so the two closed subschemes of `𝔻_J` coincide:

`restPanelIso : 𝔻((D_J, X_J)|_{X_i} / X_i) ≅ (𝔻𝔻_J)`'s `i`-th center.

Everything except the last step is unconditional given `CartierDatum`; `DilRegular` enters
only where the two ideals are compared, because `panelStage`'s centers are given by
`panelSubIdeal` and the constructed panel's by `ker(F_J(i)^*)`, and these agree exactly by
the kernel formula.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

/-- `Spec` of a ring isomorphism. -/
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

variable (hC : M.CartierDatum)

include hC in
/-- **The comparison morphism is a closed immersion**: on each chart of `𝔻_J` it is `Spec`
of the surjection `F_J(i)^*`. -/
theorem panelHomScheme_isClosedImmersion :
    IsClosedImmersion (M.panelHomScheme J i) := by
  rw [IsLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    ((M.defSpace J).dilatationCover.cover)]
  intro δ
  show IsClosedImmersion (pullback.snd (M.panelHomScheme J i)
    ((M.defSpace J).dilatationCover.map δ))
  haveI : IsClosedImmersion (M.restRhoSch J i δ hC) := by
    rw [restRhoSch]
    exact IsClosedImmersion.spec_of_surjective _ (M.restChartRho_surjective J i δ hC)
  rw [show pullback.snd (M.panelHomScheme J i) ((M.defSpace J).dilatationCover.map δ) =
      inv (M.restChartToPullback J i δ hC) ≫ M.restRhoSch J i δ hC from by
    rw [← show M.restChartToPullback J i δ hC ≫
        pullback.snd (M.panelHomScheme J i) ((M.defSpace J).chartTo δ) =
        M.restRhoSch J i δ hC from pullback.lift_snd _ _ _,
      IsIso.inv_hom_id_assoc]
    rfl]
  infer_instance

/-- The chart ring of the panel is the quotient of the chart ring of `𝔻_J` by the panel
ideal. -/
def restChartQuotEquiv :
    (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ) ⧸
        M.panelChartIdeal hC J i γ) ≃+*
      Multicenter.Dilatation ((M.restCenterScheme J i).localMulticenter γ) :=
  (Ideal.quotEquivOfEq (M.ker_restChartRho J i γ hC).symm).trans
    (RingHom.quotientKerEquivOfSurjective (M.restChartRho_surjective J i γ hC))

theorem restChartQuotEquiv_mk
    (x : Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) :
    M.restChartQuotEquiv J i γ hC (Ideal.Quotient.mk _ x) =
      M.restChartRho J i γ hC x := by
  rfl

/-- `Spec` form: the chart of the panel is `Spec` of that quotient. -/
def restChartGenIso :
    (M.restCenterScheme J i).chart γ ≅
      Spec (CommRingCat.of (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ) ⧸
        M.panelChartIdeal hC J i γ)) :=
  specRingEquivIso (M.restChartQuotEquiv J i γ hC)

theorem restChartGenIso_mk :
    (M.restChartGenIso J i γ hC).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.panelChartIdeal hC J i γ))) =
      M.restRhoSch J i γ hC := by
  rw [restChartGenIso, specRingEquivIso_hom, ← Spec.map_comp, restRhoSch]
  congr 1

/-- **The chart ideal of the constructed panel is the panel ideal `ker(F_J(i)^*)`.** -/
theorem presentIdeal_panelHomScheme :
    haveI := M.panelHomScheme_isClosedImmersion J i hC
    presentIdeal (M.panelHomScheme J i) ((M.defSpace J).dilatationCover) γ =
      M.panelChartIdeal hC J i γ := by
  haveI := M.panelHomScheme_isClosedImmersion J i hC
  refine spec_presentation_ideal_unique
    (pullback.snd (M.panelHomScheme J i) ((M.defSpace J).dilatationCover.map γ)) _ _
    (presentIso (M.panelHomScheme J i) ((M.defSpace J).dilatationCover) γ)
    ((asIso (M.restChartToPullback J i γ hC)).symm ≪≫ M.restChartGenIso J i γ hC)
    (presentIso_eq (M.panelHomScheme J i) ((M.defSpace J).dilatationCover) γ) ?_
  rw [Iso.trans_hom, Category.assoc, M.restChartGenIso_mk J i γ hC, Iso.symm_hom,
    asIso_inv]
  symm
  rw [IsIso.inv_comp_eq]
  show M.restRhoSch J i γ hC =
    M.restChartToPullback J i γ hC ≫
      pullback.snd (M.panelHomScheme J i) ((M.defSpace J).chartTo γ)
  rw [restChartToPullback, pullback.lift_snd]

end ClosedImmersion

section PanelIdentification

variable (hC : M.CartierDatum) (hb : M.CarsOnCenterAll) (hM : M.MonoDatum)

/-- The `i`-th center of `𝔻𝔻_J`, packaged as a one-index closed-subscheme datum on the
charts of `𝔻_J`. -/
def panelPreClos (i' : (M.panelStage J hC hb hM).indnumb) :
    PreClos ((M.defSpace J).dilatation) where
  indnumb := PUnit
  subscheme _ := (M.panelStage J hC hb hM).Ysub i'
  over _ := (M.panelStage J hC hb hM).Yover i'
  cov := (M.defSpace J).dilatationCover
  ideal _ γ := (M.panelStage J hC hb hM).Yideal i' γ
  condiso _ γ := (M.panelStage J hC hb hM).YcondIso i' γ
  condover _ γ := (M.panelStage J hC hb hM).YcondOver i' γ

/-- The comparison `relStructure` between the constructed panel and the `i`-th center of
`𝔻𝔻_J`, both read as closed subschemes of `𝔻_J` on its own charts. -/
def restPanelRel (i' : (M.panelStage J hC hb hM).indnumb) (hreg : M.DilRegular J) :
    haveI := M.panelHomScheme_isClosedImmersion J i'.1 hC
    _root_.relStructure
      (presentPreClos (M.panelHomScheme J i'.1) ((M.defSpace J).dilatationCover))
      (M.panelPreClos J hC hb hM i') :=
  haveI := M.panelHomScheme_isClosedImmersion J i'.1 hC
  PreClos.relStructure_of_ideal_eq
    (presentPreClos (M.panelHomScheme J i'.1) ((M.defSpace J).dilatationCover))
    (M.panelPreClos J hC hb hM i') (Equiv.refl PUnit)
    (fun u γ => by
      have h1 := (M.presentIdeal_panelHomScheme J i'.1 γ hC).trans
        (M.panelStage_Yideal_eq J hC hb hM hreg i' γ).symm
      show presentIdeal (M.panelHomScheme J i'.1) ((M.defSpace J).dilatationCover) γ =
        (M.panelPreClos J hC hb hM i').reindexIdeal
          (M.panelPreClos J hC hb hM i').cov u γ
      rw [PreClos.reindexIdeal_self]
      exact h1)

/-- **The constructed panel is the panel of `PolyptychStage`.**  This is the scheme-level
form of the paper's definition `(𝔻_J)_i = 𝔻((D_J, X_J)|_{X_i} / X_i)`: the second-stage
center of `𝔻𝔻_J` at `i` really is the multi-centered dilatation of `X_i` along the
restricted datum. -/
def restPanelIso (i' : (M.panelStage J hC hb hM).indnumb) (hreg : M.DilRegular J) :
    M.restPanel J i'.1 ≅ (M.panelStage J hC hb hM).Ysub i' :=
  haveI := M.panelHomScheme_isClosedImmersion J i'.1 hC
  (M.restPanelRel J hC hb hM i' hreg).subscheme_iso PUnit.unit

/-- The identification is an identification of closed subschemes **of `𝔻_J`**: it carries the
canonical morphism `(𝔻_J)_i ⟶ 𝔻_J` to the inclusion of the panel. -/
theorem restPanelIso_over (i' : (M.panelStage J hC hb hM).indnumb)
    (hreg : M.DilRegular J) :
    (M.restPanelIso J hC hb hM i' hreg).hom ≫
        ((M.panelStage J hC hb hM).Ysub i' ↘ (M.defSpace J).dilatation) =
      M.panelHomScheme J i'.1 := by
  haveI := M.panelHomScheme_isClosedImmersion J i'.1 hC
  have h := (M.restPanelRel J hC hb hM i' hreg).subscheme_iso_over PUnit.unit
  rw [Scheme.Hom.isOver_iff] at h
  exact h

/-- **The panels of `𝔻𝔻_J` are the dilatations of the restricted data.**  Combined with
`panelizationIso` (Theorem 3.7) this says that `𝔻_I` is obtained from `𝔻_J` by dilating
the panels `(𝔻_J)_i = 𝔻((D_J, X_J)|_{X_i} / X_i)`, `i ∉ J`, exactly as the paper states
it. -/
theorem panelStage_Ysub_eq_restPanel (i' : (M.panelStage J hC hb hM).indnumb)
    (hreg : M.DilRegular J) :
    Nonempty (M.restPanel J i'.1 ≅ (M.panelStage J hC hb hM).Ysub i') :=
  ⟨M.restPanelIso J hC hb hM i' hreg⟩

end PanelIdentification

end PreMultiCenter

end SchemeDilatation
