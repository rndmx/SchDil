import IteratedSchemeMultiCore

/-!
# The second-stage center is the strict transform: the multi-index `(P!)`

`IteratedSchemeMultiCore.lean` builds the second-stage multicenter `iterCenter` on
`Bl^{Dθ}_Y X` by *chart ideals*: at index `i` the center is `Ideal.map (projRho i θ γ)`
of the mono-centered exceptional colon ideal.  This file proves that this chart-ideal
description agrees with the geometric one used in [Ma24, §4] — the honest fiber product

  `Zᵢ := Yᵢ ×_{Bl^{θᵢDᵢ}_{Yᵢ}X} Bl^{Dθ}_Y X`

(`strictTransform`), whose second projection into `Bl^{Dθ}_Y X` is a closed immersion by
base change.  The main result is

  `presentIdeal_strictTransform :
     presentIdeal (strictTransformTo) (dilatationCover) γ
       = Ideal.map (projRho i θ γ) (monoExceptIdeal)`

and hence `iterCenter_Yideal_eq_presentIdeal`.

The proof avoids the tensor-product computation `Spec(R/I) ×_{Spec R} Spec S ≅ Spec(S/IS)`
entirely.  Instead the ideal equality is obtained from two opposite inclusions, each read
off a morphism of affine schemes over the base:

* `ideal_le_of_quot_hom_over` — a morphism `Spec (R ⧸ I) ⟶ Spec (R ⧸ J)` over `Spec R`
  forces `J ≤ I`;
* `ideal_map_le_of_quot_hom_over` — its relative version over a ring map `ρ`.

For the first inclusion, `pullback.lift` assembles a map into
`Zᵢ ×_{Bl^{Dθ}} chart_γ` out of the mono-centered chart data of Lemma 4.4
(`mono_chart_leg`, itself `cone_eq` composed with `chartOfY_exceptIso_mk`) together with
the generic quotient-extension map `quotMapHom`.  For the second, the two legs of
`Zᵢ ×_{Bl^{Dθ}} chart_γ` lift into `Yᵢ ×_{Bᵢ} chart_γ(Bᵢ)`, which the mono-centered
comparison `liftToPullback` identifies with `Spec` of the exceptional quotient.

So no pullback pasting isomorphisms, no `pullbackSpecIso`, and no manufactured `Algebra`
instance are needed.
-/

suppress_compilation
universe u
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

/-- A morphism `Spec (R ⧸ I) ⟶ Spec (R ⧸ J)` over `Spec R` forces `J ≤ I`. -/
theorem ideal_le_of_quot_hom_over {R : CommRingCat.{u+1}} (I J : Ideal R)
    (h : Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec (CommRingCat.of (R ⧸ J)))
    (hover : h ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : J ≤ I := by
  have hring : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ Spec.preimage h =
      CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact hover
  intro x hx
  have happ := congrArg (fun f => (CommRingCat.Hom.hom f) x) hring
  simp only [CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at happ
  rw [show (Ideal.Quotient.mk J) x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    map_zero] at happ
  exact Ideal.Quotient.eq_zero_iff_mem.mp happ.symm

/-- A morphism `Spec (S ⧸ J) ⟶ Spec (R ⧸ E)` lying over `Spec ρ` forces
`Ideal.map ρ E ≤ J`. -/
theorem ideal_map_le_of_quot_hom_over {R S : CommRingCat.{u+1}} (ρ : R ⟶ S)
    (E : Ideal R) (J : Ideal S)
    (d : Spec (CommRingCat.of (S ⧸ J)) ⟶ Spec (CommRingCat.of (R ⧸ E)))
    (hover : d ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk E)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Spec.map ρ) :
    Ideal.map ρ.hom E ≤ J := by
  have hring : CommRingCat.ofHom (Ideal.Quotient.mk E) ≫ Spec.preimage d =
      ρ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_comp]
    exact hover
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  have happ := congrArg (fun f => (CommRingCat.Hom.hom f) x) hring
  simp only [CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at happ
  rw [show (Ideal.Quotient.mk E) x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    map_zero] at happ
  exact Ideal.Quotient.eq_zero_iff_mem.mp happ.symm

/-- The map on quotients induced by extending an ideal along a ring map. -/
def quotMapHom {R S : CommRingCat.{u+1}} (ρ : R ⟶ S) (E : Ideal R) :
    CommRingCat.of (R ⧸ E) ⟶ CommRingCat.of (S ⧸ Ideal.map ρ.hom E) :=
  CommRingCat.ofHom (Ideal.Quotient.lift E
    ((Ideal.Quotient.mk (Ideal.map ρ.hom E)).comp ρ.hom)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)))

theorem quotMapHom_comp {R S : CommRingCat.{u+1}} (ρ : R ⟶ S) (E : Ideal R) :
    CommRingCat.ofHom (Ideal.Quotient.mk E) ≫ quotMapHom ρ E =
      ρ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.map ρ.hom E)) := by
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    quotMapHom]
  exact Ideal.Quotient.lift_mk _ _ _

theorem quotMapHom_spec {R S : CommRingCat.{u+1}} (ρ : R ⟶ S) (E : Ideal R) :
    Spec.map (quotMapHom ρ E) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk E)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.map ρ.hom E))) ≫
        Spec.map ρ := by
  rw [← Spec.map_comp, ← Spec.map_comp, quotMapHom_comp]

namespace SchemeDilatation

namespace PreMultiCenter

section MonoLeg

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]
  (ν : M.indnumb → ℕ) (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot) (γ : M.cov.J)

/-- The chart of the center, presented through the exceptional quotient, lands in the
dilatation chart. -/
theorem mono_chart_leg :
    (M.chartOfY_exceptIso ν hSt γ).inv ≫ M.chartOfY_to γ ≫ M.Ylift ν hb =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (((M.multiple ν).localMulticenter γ).exceptIdeal))) ≫
        (M.multiple ν).chartTo γ := by
  rw [M.cone_eq ν hb hSt γ, ← M.chartOfY_exceptIso_mk ν hSt γ]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]

/-- The mono comparison `Λ` is compatible with the projection to the chart. -/
theorem liftToPullback_snd :
    M.liftToPullback ν hb hSt γ ≫
        pullback.snd (M.Ylift ν hb) ((M.multiple ν).chartTo γ) =
      M.chartOfY_kappa ν hSt γ :=
  pullback.lift_snd _ _ _

end MonoLeg


section StrictTransform

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (θ : M.indnumb → ℕ)
  (i : M.indnumb) (hb : M.CarsOnYAll) (hSt : M.ElemNzdOnQuotAll) (γ : M.cov.J)

instance monoYlift_isClosedImmersion :
    IsClosedImmersion ((M.restrict (fun _ : PUnit => i)).Ylift
      (fun _ : PUnit => θ i) (hb i)) :=
  (M.restrict (fun _ : PUnit => i)).Ylift_isClosedImmersion _ (hb i)

/-- **The strict transform of `Yᵢ`** on `Bl^{Dθ}_Y X`, as the honest fiber product
`Yᵢ ×_{Bl^{θᵢDᵢ}_{Yᵢ}X} Bl^{Dθ}_Y X` of [Ma24, §4]. -/
def strictTransform : Scheme.{u+1} :=
  pullback ((M.restrict (fun _ : PUnit => i)).Ylift (fun _ : PUnit => θ i) (hb i))
    (M.projAt i θ)

/-- Its closed immersion into `Bl^{Dθ}_Y X`. -/
def strictTransformTo :
    M.strictTransform θ i hb ⟶ (M.multiple θ).dilatation :=
  pullback.snd ((M.restrict (fun _ : PUnit => i)).Ylift (fun _ : PUnit => θ i) (hb i))
    (M.projAt i θ)

instance strictTransformTo_isClosedImmersion :
    IsClosedImmersion (M.strictTransformTo θ i hb) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- Its projection to `Yᵢ`. -/
def strictTransformToY :
    M.strictTransform θ i hb ⟶ M.Ysub i :=
  pullback.fst ((M.restrict (fun _ : PUnit => i)).Ylift (fun _ : PUnit => θ i) (hb i))
    (M.projAt i θ)

/-- The mono-centered chart ring at index `i`. -/
abbrev monoChartRing : CommRingCat.{u+1} :=
  CommRingCat.of (Multicenter.Dilatation
    (((M.restrict (fun _ : PUnit => i)).multiple
      (fun _ : PUnit => θ i)).localMulticenter γ))

/-- The mono-centered exceptional colon ideal at index `i`. -/
abbrev monoExceptIdeal : Ideal (M.monoChartRing θ i γ) :=
  (((M.restrict (fun _ : PUnit => i)).multiple
    (fun _ : PUnit => θ i)).localMulticenter γ).exceptIdeal

/-- The chart comparison as a morphism of `CommRingCat`. -/
abbrev projChartRho :
    M.monoChartRing θ i γ ⟶ (M.multiple θ).dilatationCover.obj γ :=
  CommRingCat.ofHom (M.projRho i θ γ).toRingHom

theorem projRhoSch_eq_projChartRho :
    M.projRhoSch i θ γ = Spec.map (M.projChartRho θ i γ) := rfl

include hSt in
/-- **The multi-index chart identification `(P!)`**: on the dilatation charts of
`Bl^{Dθ}_Y X`, the chart ideal of the strict transform
`Yᵢ ×_{Bl^{θᵢDᵢ}_{Yᵢ}X} Bl^{Dθ}_Y X` is exactly the extension along `projRho` of the
mono-centered exceptional colon ideal — that is, exactly `iterCenter.Yideal i`. -/
theorem presentIdeal_strictTransform :
    presentIdeal (M.strictTransformTo θ i hb) ((M.multiple θ).dilatationCover) γ =
      Ideal.map (M.projChartRho θ i γ).hom (M.monoExceptIdeal θ i γ) := by
  have hpc := M.proj_chart_cone i θ γ
  have hpres := presentIso_eq (M.strictTransformTo θ i hb)
    ((M.multiple θ).dilatationCover) γ
  have hmid := (M.restrict (fun _ : PUnit => i)).mono_chart_leg
    (fun _ : PUnit => θ i) (hb i) (hSt i) γ
  refine le_antisymm ?_ ?_
  · -- `J ≤ map ρ E`, from the comparison built out of the mono chart data
    have hagree : (Spec.map (quotMapHom (M.projChartRho θ i γ)
            (M.monoExceptIdeal θ i γ)) ≫
          ((M.restrict (fun _ : PUnit => i)).chartOfY_exceptIso
            (fun _ : PUnit => θ i) (hSt i) γ).inv ≫
          (M.restrict (fun _ : PUnit => i)).chartOfY_to γ) ≫
          (M.restrict (fun _ : PUnit => i)).Ylift (fun _ : PUnit => θ i) (hb i) =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (Ideal.map (M.projChartRho θ i γ).hom (M.monoExceptIdeal θ i γ)))) ≫
          (M.multiple θ).chartTo γ) ≫ M.projAt i θ := by
      simp only [Category.assoc]
      rw [hmid, hpc, M.projRhoSch_eq_projChartRho θ i γ, ← Category.assoc,
        ← Category.assoc, quotMapHom_spec]
      rfl
    have hwsnd : pullback.lift _ _ hagree ≫ M.strictTransformTo θ i hb =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.map (M.projChartRho θ i γ).hom (M.monoExceptIdeal θ i γ)))) ≫
          (M.multiple θ).dilatationCover.map γ :=
      pullback.lift_snd _ _ hagree
    refine ideal_le_of_quot_hom_over _ _
      (pullback.lift _ _ hwsnd ≫
        (presentIso (M.strictTransformTo θ i hb)
          ((M.multiple θ).dilatationCover) γ).hom) ?_
    rw [Category.assoc, ← hpres]
    exact pullback.lift_snd _ _ hwsnd
  · -- `map ρ E ≤ J`, from the leg of the strict-transform chart down to `Yᵢ`
    have hinvsnd : (presentIso (M.strictTransformTo θ i hb)
          ((M.multiple θ).dilatationCover) γ).inv ≫
        pullback.snd (M.strictTransformTo θ i hb)
          ((M.multiple θ).dilatationCover.map γ) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (presentIdeal (M.strictTransformTo θ i hb)
            ((M.multiple θ).dilatationCover) γ))) := by
      rw [hpres, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have houter : pullback.fst (M.strictTransformTo θ i hb)
          ((M.multiple θ).dilatationCover.map γ) ≫ M.strictTransformTo θ i hb =
        pullback.snd (M.strictTransformTo θ i hb)
          ((M.multiple θ).dilatationCover.map γ) ≫
          (M.multiple θ).dilatationCover.map γ := pullback.condition
    have hinner : M.strictTransformToY θ i hb ≫
        (M.restrict (fun _ : PUnit => i)).Ylift (fun _ : PUnit => θ i) (hb i) =
        M.strictTransformTo θ i hb ≫ M.projAt i θ := pullback.condition
    have hagree2 : ((presentIso (M.strictTransformTo θ i hb)
            ((M.multiple θ).dilatationCover) γ).inv ≫
          pullback.fst (M.strictTransformTo θ i hb)
            ((M.multiple θ).dilatationCover.map γ) ≫
          M.strictTransformToY θ i hb) ≫
          (M.restrict (fun _ : PUnit => i)).Ylift (fun _ : PUnit => θ i) (hb i) =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (presentIdeal (M.strictTransformTo θ i hb)
              ((M.multiple θ).dilatationCover) γ))) ≫
          M.projRhoSch i θ γ) ≫
          (((M.restrict (fun _ : PUnit => i)).multiple
            (fun _ : PUnit => θ i)).chartTo γ) := by
      simp only [Category.assoc]
      rw [hinner, reassoc_of% houter,
        show ((M.multiple θ).dilatationCover.map γ ≫ M.projAt i θ) =
          M.projRhoSch i θ γ ≫ (((M.restrict (fun _ : PUnit => i)).multiple
            (fun _ : PUnit => θ i)).chartTo γ) from hpc,
        ← Category.assoc, hinvsnd]
    have hcsnd : pullback.lift _ _ hagree2 ≫
        pullback.snd ((M.restrict (fun _ : PUnit => i)).Ylift
          (fun _ : PUnit => θ i) (hb i))
          (((M.restrict (fun _ : PUnit => i)).multiple
            (fun _ : PUnit => θ i)).chartTo γ) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (presentIdeal (M.strictTransformTo θ i hb)
            ((M.multiple θ).dilatationCover) γ))) ≫ M.projRhoSch i θ γ :=
      pullback.lift_snd _ _ hagree2
    have hdover : (pullback.lift _ _ hagree2 ≫
          inv ((M.restrict (fun _ : PUnit => i)).liftToPullback
            (fun _ : PUnit => θ i) (hb i) (hSt i) γ) ≫
          ((M.restrict (fun _ : PUnit => i)).chartOfY_exceptIso
            (fun _ : PUnit => θ i) (hSt i) γ).hom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (M.monoExceptIdeal θ i γ))) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (presentIdeal (M.strictTransformTo θ i hb)
            ((M.multiple θ).dilatationCover) γ))) ≫
          Spec.map (M.projChartRho θ i γ) := by
      simp only [Category.assoc]
      rw [(M.restrict (fun _ : PUnit => i)).chartOfY_exceptIso_mk
          (fun _ : PUnit => θ i) (hSt i) γ,
        ← (M.restrict (fun _ : PUnit => i)).liftToPullback_snd
          (fun _ : PUnit => θ i) (hb i) (hSt i) γ,
        IsIso.inv_hom_id_assoc, hcsnd, M.projRhoSch_eq_projChartRho θ i γ]
    exact ideal_map_le_of_quot_hom_over (M.projChartRho θ i γ)
      (M.monoExceptIdeal θ i γ) _ _ hdover

include hSt in
/-- **The second-stage center of [Ma24, Prop. 4.6] IS the strict transform.** Its chart
ideal, used to build `iterCenter`, is the chart ideal of the honest fiber product
`Yᵢ ×_{Bl^{θᵢDᵢ}_{Yᵢ}X} Bl^{Dθ}_Y X`. -/
theorem iterCenter_Yideal_eq_presentIdeal (n : M.indnumb → ℕ) :
    (M.iterCenter θ n hb hSt).Yideal i γ =
      presentIdeal (M.strictTransformTo θ i hb)
        ((M.multiple θ).dilatationCover) γ :=
  (M.presentIdeal_strictTransform θ i hb hSt γ).symm

end StrictTransform

end PreMultiCenter

end SchemeDilatation
