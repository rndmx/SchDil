import MulticenterQuotient
import MulticenterExceptional
import DilatationCover
import IteratedMultiple
import DilatationChart
import MulticenterMonopoly
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Iterated dilatations of schemes: [Ma24, Lemma 4.4]

Let `M` be a mono-centered `PreMultiCenter` on `X` (center `Y`, divisor `D`), and
`ν n : M.indnumb → ℕ`.  Write `B := Bl^{νD}_Y X` for the dilatation of the `ν`-th
multiple.  Under the two chart-level standing hypotheses of [Ma24, §4] —

* `CarsOnY` : `D` restricts to a Cartier divisor on `Y` (chart form on the canonical
  covering of `Y ×_X U_γ`);
* `ElemNzdOnQuot` : on each chart, the distinguished element of `D` is a
  non-zero-divisor in the coordinate ring `A_γ/M_γ` of the center —

this file constructs, in order:

1. `Ylift` — the unique lift `ℓ : Y ⟶ B` of `Y ⟶ X` (universal property; the
   containment condition is free since the center dies in its own quotient, by
   `Ysub_pull_mor_ring_Yideal_eq_bot` through the bridge `spec_map_pull_mor_ring`);
2. `Ylift_isClosedImmersion` — **[Ma24, Prop. 4.3]**: `ℓ` is a closed immersion
   (`ℓ ≫ θ` is one and `θ` is separated, being affine);
3. `secondStage` — the second-stage multicenter on `B`: center `ℓ` presented on the
   dilatation charts (`presentPreClos`-style), divisor the `n`-th multiple of the total
   transform `θ*D` (a `ChartDatum` gluing);
4. `presentIdeal_eq_exceptIdeal` — **the chart identification**: the presented ideal of
   `ℓ` on the chart `A_γ[G_ν]` is the exceptional colon ideal
   `(M_γ·A_γ[G_ν] : g_ν)` of `MulticenterExceptional.lean`.  Proved by uniqueness of
   `Spec`-quotient presentations (`spec_presentation_ideal_unique`), comparing
   `presentIso` with the isomorphism `Y ×_B chart_γ ≅ Spec (A_γ/M_γ)` built from the
   cone equality `cone_eq` (itself an instance of the universal property applied to the
   chart piece of the center, using `exceptQuotEquiv`);
5. `chartRho` / `chart_cone` — the canonical ring map `A_γ[G_ν] → A_γ[G_{ν+n}]` and the
   fact that the canonical morphism `Bl^{(ν+n)D} ⟶ Bl^{νD}` restricts to it on charts;
6. `secondStage_pullSubset` / `secondStage_isCars` — the forward conditions: the
   exceptional ideal maps into the `n`-th power of the total transform
   (`chartRho_exceptIdeal_le`, a colon-cancellation against the non-zero-divisor
   `α^{ν}`), chart-wise through the flat piece factorization
   `secondStage_piece_factor`;
7. `backward_pullSubset` / `backward_isCars` — the backward conditions: in the
   second-stage chart `(A_γ[G_ν])[H_γ]` a section `m` of the center factors as
   `z·g_ν` with `z` in the exceptional ideal, which factors through `α^n` by the
   second stage's own condition (`secondChart_M_le`), through the two-stage flat
   factorization `backward_piece_factor`;
8. `iterateSchemeIso` — **[Ma24, Lemma 4.4]**:

   `Bl^{(ν+n)D}_Y X ≅ Bl^{n·θ*D}_{ℓ(Y)} (Bl^{νD}_Y X)`

   over `Bl^{νD}_Y X` (hence over `X`), unique as such (`iterateSchemeIso_unique`).
-/

suppress_compilation
universe u
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

section Bridge
variable {X : Scheme.{u+1}} (Z : PreClos X) {X' : Scheme.{u+1}} (f : X' ⟶ X)

/-- `pull_mor_ring` is the ring-side of the chart-to-base morphism. -/
lemma spec_map_pull_mor_ring (γβ : (pull_cov X Z X' f).J) :
    Spec.map (pull_mor_ring X Z X' f γβ) =
      (pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫ pullback.snd f (Z.cov.map γβ.1) := by
  simp only [pull_mor_ring, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc]
  rw [show Scheme.Γ.map (Opposite.op ((pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫
      pullback.snd f (Z.cov.map γβ.1))) =
      ((pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫
        pullback.snd f (Z.cov.map γβ.1)).appTop from rfl]
  rw [← Scheme.toSpecΓ_naturality_assoc]
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

end Bridge

namespace PreMultiCenter

section Ylift

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]
  (ν n : M.indnumb → ℕ)

local notation "i₀" => (default : M.indnumb)

/-- On the canonical covering of `Y ×_X U_γ`, the ring map from the chart kills the
center ideal: the pullback of `Y` to itself is everything. -/
theorem Ysub_pull_mor_ring_Yideal_eq_bot
    (γβ : (pull_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X)).J) :
    Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
      (M.Yideal i₀ γβ.1) = ⊥ := by
  -- the chart-to-base morphism factors through `Spec (A_γ ⧸ Yideal)`
  have hover := M.YcondOver i₀ γβ.1
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  have hsnd : pullback.snd (M.Ysub i₀ ↘ X) (M.Drep.cov.map γβ.1) =
      (M.YcondIso i₀ γβ.1).inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))) := by
    show pullback.snd (M.Ysub i₀ ↘ X) (M.cov.map γβ.1) = _
    rw [← hover, Iso.inv_hom_id_assoc]
  set ψ := Spec.preimage
    ((pull_loc_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ.1).map γβ.2 ≫
      (M.YcondIso i₀ γβ.1).inv) with hψ
  have hfact : pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ =
      CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1)) ≫ ψ := by
    apply Spec.map_injective
    rw [spec_map_pull_mor_ring, Spec.map_comp, hψ, Spec.map_preimage, hsnd,
      Category.assoc]
  rw [hfact, CommRingCat.hom_comp, ← Ideal.map_map,
    show (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))).hom =
      Ideal.Quotient.mk (M.Yideal i₀ γβ.1) from rfl,
    Ideal.map_quotient_self, Ideal.map_bot]

/-- Chart form of the containment condition for lifting `Y ⟶ X` to `Bl^{νD}` — free,
since the center dies in its own quotient. -/
theorem Ylift_pullSubset_chart (i : M.indnumb)
    (γβ : (pull_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X)).J) :
    Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
        (M.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
        ((M.Dideal i γβ.1) ^ (ν i)) := by
  rw [Unique.eq_default i, M.Ysub_pull_mor_ring_Yideal_eq_bot γβ]
  exact bot_le

/-- The containment condition for lifting `Y ⟶ X` to `Bl^{νD}`. -/
theorem Ylift_pullSubset : (M.multiple ν).pullSubset (M.Ysub i₀ ↘ X) :=
  fun i γβ => M.Ylift_pullSubset_chart ν i γβ

/-- The §4 standing hypothesis, chart form: the restriction of `D` to `Y` is a Cartier
divisor on `Y` — the divisor ideal pulls back to a principal ideal with non-zero-divisor
generator on the canonical charts of `Y ×_X U_γ`. -/
def CarsOnY : Prop :=
  ∀ (i : M.indnumb) (γβ : (pull_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X)).J),
    ∃ g : (pull_loc_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ.1).obj γβ.2,
      Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
        (M.Dideal i γβ.1) = Ideal.span {g} ∧
      g ∈ nonZeroDivisors
        ((pull_loc_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ.1).obj γβ.2)

/-- Under the standing hypothesis, the multiple `νD` also restricts to a Cartier
divisor on `Y`. -/
theorem Ylift_isCars (hb : M.CarsOnY) :
    IsCars (M.Ysub i₀) (Clos.pullback (M.Ysub i₀ ↘ X) (M.multiple ν).D) := by
  refine ⟨pullback_PreClos X (M.Ysub i₀) (M.Ysub i₀ ↘ X) (M.multiple ν).Drep,
    pullback_IsPreCars_of_charts _ _ _ (fun i γβ => ?_), rfl⟩
  obtain ⟨g, hg, hgnzd⟩ := hb i γβ
  refine ⟨g ^ ν i, ?_, pow_mem hgnzd _⟩
  show Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
      ((M.Dideal i γβ.1) ^ (ν i)) = _
  rw [Ideal.map_pow, hg, Ideal.span_singleton_pow]

/-- **The lift of the center**: under the standing hypothesis, `Y ⟶ X` lifts uniquely
to `ℓ : Y ⟶ Bl^{νD}_Y X`. -/
theorem existsUnique_Ylift (hb : M.CarsOnY) :
    ∃! ℓ : M.Ysub i₀ ⟶ (M.multiple ν).dilatation,
      ℓ ≫ (M.multiple ν).structureMap = M.Ysub i₀ ↘ X :=
  (M.multiple ν).universal_property (M.Ysub i₀) (M.Ysub i₀ ↘ X)
    (M.Ylift_isCars ν hb) (M.Ylift_pullSubset ν)

/-- The canonical lift `ℓ : Y ⟶ Bl^{νD}_Y X` of [Ma24, §4]. -/
noncomputable def Ylift (hb : M.CarsOnY) : M.Ysub i₀ ⟶ (M.multiple ν).dilatation :=
  (M.existsUnique_Ylift ν hb).choose

@[simp] theorem Ylift_over (hb : M.CarsOnY) :
    M.Ylift ν hb ≫ (M.multiple ν).structureMap = M.Ysub i₀ ↘ X :=
  (M.existsUnique_Ylift ν hb).choose_spec.1

theorem Ylift_unique (hb : M.CarsOnY) (g : M.Ysub i₀ ⟶ (M.multiple ν).dilatation)
    (hg : g ≫ (M.multiple ν).structureMap = M.Ysub i₀ ↘ X) : g = M.Ylift ν hb :=
  (M.existsUnique_Ylift ν hb).choose_spec.2 g hg

/-- **[Ma24, Prop. 4.3]**: the lift `ℓ : Y ⟶ Bl^{νD}_Y X` is a closed immersion —
`ℓ ≫ θ` is the closed immersion `Y ↪ X` and `θ` is separated (being affine). -/
theorem Ylift_isClosedImmersion (hb : M.CarsOnY) :
    IsClosedImmersion (M.Ylift ν hb) := by
  haveI h1 : IsClosedImmersion (M.Ylift ν hb ≫ (M.multiple ν).structureMap) := by
    rw [M.Ylift_over ν hb]
    exact M.Yrep.subscheme_isClosedImmersion i₀
  haveI ha : IsAffineHom (M.multiple ν).structureMap :=
    (M.multiple ν).structureMap_isAffineHom
  haveI h2 : IsSeparated (M.multiple ν).structureMap :=
    IsSeparated.of_isAffineHom _
  exact IsClosedImmersion.of_comp (M.Ylift ν hb) (M.multiple ν).structureMap

end Ylift

section SecondStage

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]
  (ν n : M.indnumb → ℕ)

local notation "i₀" => (default : M.indnumb)

/-- The chart datum, on the charts of `Bl^{νD}`, of the `n`-th multiple of the total
transform of `D`. -/
noncomputable def transformDChartDatum (i : M.indnumb) :
    ChartDatum (M.multiple ν).dilatation where
  cov := (M.multiple ν).dilatationCover
  idl γ := (Ideal.map (algebraMap ((M.multiple ν).cov.obj γ)
    (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
      (M.Dideal i γ)) ^ (n i)
  compat {W} _ {γ γ'} a b hab := by
    rw [Ideal.map_pow, Ideal.map_pow]
    congr 1
    have hab' : (a ≫ (M.multiple ν).chartHom γ) ≫ M.cov.map γ =
        (b ≫ (M.multiple ν).chartHom γ') ≫ M.cov.map γ' := by
      simp only [Category.assoc]
      show a ≫ (M.multiple ν).chartToX γ = b ≫ (M.multiple ν).chartToX γ'
      rw [← (M.multiple ν).structureMap_chart γ,
        ← (M.multiple ν).structureMap_chart γ', ← Category.assoc,
        ← Category.assoc]
      exact congrArg (· ≫ (M.multiple ν).structureMap) hab
    have h := chartIdeal_agree M.Drep (a ≫ (M.multiple ν).chartHom γ)
      (b ≫ (M.multiple ν).chartHom γ') hab' i
    have hpa : Spec.preimage (W.isoSpec.inv ≫ a ≫ (M.multiple ν).chartHom γ) =
        CommRingCat.ofHom (algebraMap ((M.multiple ν).cov.obj γ)
          (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))) ≫
          Spec.preimage (W.isoSpec.inv ≫ a) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ a ≫ (M.multiple ν).chartHom γ =
        (W.isoSpec.inv ≫ a) ≫ (M.multiple ν).chartHom γ
      rw [Category.assoc]
    have hpb : Spec.preimage (W.isoSpec.inv ≫ b ≫ (M.multiple ν).chartHom γ') =
        CommRingCat.ofHom (algebraMap ((M.multiple ν).cov.obj γ')
          (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ'))) ≫
          Spec.preimage (W.isoSpec.inv ≫ b) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ b ≫ (M.multiple ν).chartHom γ' =
        (W.isoSpec.inv ≫ b) ≫ (M.multiple ν).chartHom γ'
      rw [Category.assoc]
    rw [hpa, hpb, CommRingCat.hom_comp, CommRingCat.hom_comp] at h
    rw [← Ideal.map_map, ← Ideal.map_map] at h
    exact h

/-- **The second-stage multicenter of [Ma24, Lemma 4.4]** on `B = Bl^{νD}_Y X`: the
center is the lift `ℓ : Y ↪ B` presented on the dilatation charts, the divisor is the
`n`-th multiple of the total transform of `D`. -/
noncomputable def secondStage (hb : M.CarsOnY) :
    PreMultiCenter (M.multiple ν).dilatation :=
  haveI : IsClosedImmersion (M.Ylift ν hb) := M.Ylift_isClosedImmersion ν hb
  { indnumb := M.indnumb
    cov := (M.multiple ν).dilatationCover
    Ysub _ := M.Ysub i₀
    Dsub i := (M.transformDChartDatum ν n i).glued
    Yover _ := ⟨M.Ylift ν hb⟩
    Dover i := ⟨(M.transformDChartDatum ν n i).structureMap⟩
    Yideal _ γ := presentIdeal (M.Ylift ν hb) (M.multiple ν).dilatationCover γ
    Dideal i γ := (Ideal.map (algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
        (M.Dideal i γ)) ^ (n i)
    YcondIso _ γ :=
      (presentIso (M.Ylift ν hb) (M.multiple ν).dilatationCover γ).symm
    YcondOver _ γ := by
      rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
      show (presentIso (M.Ylift ν hb) (M.multiple ν).dilatationCover γ).inv ≫
          pullback.snd (M.Ylift ν hb) ((M.multiple ν).dilatationCover.map γ) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (presentIdeal (M.Ylift ν hb) (M.multiple ν).dilatationCover γ)))
      rw [presentIso_eq (M.Ylift ν hb) (M.multiple ν).dilatationCover γ,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    DcondIso i γ := asIso ((M.transformDChartDatum ν n i).chartCompare γ)
    DcondOver i γ := by
      rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
      show (M.transformDChartDatum ν n i).chartCompare γ ≫
          pullback.snd ((M.transformDChartDatum ν n i).structureMap)
            ((M.multiple ν).dilatationCover.map γ) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          ((Ideal.map (algebraMap ((M.multiple ν).cov.obj γ)
            (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
              (M.Dideal i γ)) ^ (n i))))
      exact (M.transformDChartDatum ν n i).chartCompare_snd γ
    Dprin i γ := by
      letI : Submodule.IsPrincipal (M.Dideal i γ) := M.Dprin i γ
      refine ⟨⟨(algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
          ((M.localMulticenter γ).elem i) ^ (n i), ?_⟩⟩
      rw [Ideal.submodule_span_eq, ← Ideal.span_singleton_pow]
      congr 1
      conv_lhs => rw [show M.Dideal i γ =
        Ideal.span {(M.localMulticenter γ).elem i} from
          (Ideal.span_singleton_generator (M.Dideal i γ)).symm]
      rw [Ideal.map_span, Set.image_singleton]
      rfl }

@[simp] theorem secondStage_Yideal (hb : M.CarsOnY) (i : M.indnumb)
    (γ : M.cov.J) :
    (M.secondStage ν n hb).Yideal i γ =
      haveI : IsClosedImmersion (M.Ylift ν hb) := M.Ylift_isClosedImmersion ν hb
      presentIdeal (M.Ylift ν hb) (M.multiple ν).dilatationCover γ := rfl

@[simp] theorem secondStage_Dideal (hb : M.CarsOnY) (i : M.indnumb)
    (γ : M.cov.J) :
    (M.secondStage ν n hb).Dideal i γ =
      (Ideal.map (algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
          (M.Dideal i γ)) ^ (n i) := rfl

end SecondStage

section PresentationUnique

/-- **Uniqueness of quotient presentations**: two presentations of the same morphism to
`Spec R` as `Spec` of a quotient have equal ideals. -/
theorem spec_presentation_ideal_unique {R : CommRingCat.{u+1}} {V : Scheme.{u+1}}
    (c : V ⟶ Spec R) (I J : Ideal R)
    (eI : V ≅ Spec (CommRingCat.of (R ⧸ I)))
    (eJ : V ≅ Spec (CommRingCat.of (R ⧸ J)))
    (hI : c = eI.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (hJ : c = eJ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :
    I = J := by
  set E : Spec (CommRingCat.of (R ⧸ I)) ≅ Spec (CommRingCat.of (R ⧸ J)) :=
    eI.symm ≪≫ eJ with hE
  have hEsq : E.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [hE]
    show eI.inv ≫ eJ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = _
    rw [← hJ, hI, Iso.inv_hom_id_assoc]
  set φ : (R ⧸ I) ≃+* (R ⧸ J) :=
    CategoryTheory.Iso.commRingCatIsoToRingEquiv
      { hom := Spec.preimage E.inv
        inv := Spec.preimage E.hom
        hom_inv_id := Spec.map_injective (by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.hom_inv_id,
            Spec.map_id])
        inv_hom_id := Spec.map_injective (by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.inv_hom_id,
            Spec.map_id]) } with hφ
  have hcompat : ∀ r : R, Ideal.Quotient.mk J ((RingEquiv.refl R) r) =
      φ (Ideal.Quotient.mk I r) := by
    intro r
    have hring : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        CommRingCat.ofHom (φ : _ →+* _) =
        CommRingCat.ofHom (Ideal.Quotient.mk J) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      rw [show CommRingCat.ofHom (φ : _ →+* _) = Spec.preimage E.inv from rfl,
        Spec.map_preimage]
      rw [← hEsq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact (congrArg (fun f => (CommRingCat.Hom.hom f) r) hring).symm
  have h := Ideal.map_eq_of_quotientIso (RingEquiv.refl R) I J φ hcompat
  simpa using h.symm

end PresentationUnique

section FactorThroughY

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]
  (ν : M.indnumb → ℕ)

local notation "i₀" => (default : M.indnumb)

/-- Anything factoring through the center kills its ideal: generalization of
`Ysub_pull_mor_ring_Yideal_eq_bot` to an arbitrary scheme over `Y`. -/
theorem pull_mor_ring_Yideal_eq_bot_of_factor {T : Scheme.{u+1}}
    (u : T ⟶ M.Ysub i₀)
    (γβ : (pull_cov X M.Drep T (u ≫ (M.Ysub i₀ ↘ X))).J) :
    Ideal.map (pull_mor_ring X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ).hom
      (M.Yideal i₀ γβ.1) = ⊥ := by
  have hover := M.YcondOver i₀ γβ.1
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  set pmap : pullback (u ≫ (M.Ysub i₀ ↘ X)) (M.Drep.cov.map γβ.1) ⟶
      pullback (M.Ysub i₀ ↘ X) (M.Drep.cov.map γβ.1) :=
    pullback.map _ _ _ _ u (𝟙 _) (𝟙 _) (by rw [Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp]) with hpmap
  have hsnd : pullback.snd (u ≫ (M.Ysub i₀ ↘ X)) (M.Drep.cov.map γβ.1) =
      pmap ≫ (M.YcondIso i₀ γβ.1).inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))) := by
    have h1 : pmap ≫ pullback.snd (M.Ysub i₀ ↘ X) (M.Drep.cov.map γβ.1) =
        pullback.snd (u ≫ (M.Ysub i₀ ↘ X)) (M.Drep.cov.map γβ.1) := by
      rw [hpmap, pullback.lift_snd, Category.comp_id]
    have h2 : pullback.snd (M.Ysub i₀ ↘ X) (M.Drep.cov.map γβ.1) =
        (M.YcondIso i₀ γβ.1).inv ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))) := by
      show pullback.snd (M.Ysub i₀ ↘ X) (M.cov.map γβ.1) = _
      rw [← hover, Iso.inv_hom_id_assoc]
    rw [← h1, h2]
  set ψ := Spec.preimage
    ((pull_loc_cov X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ.1).map γβ.2 ≫ pmap ≫
      (M.YcondIso i₀ γβ.1).inv) with hψ
  have hfact : pull_mor_ring X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ =
      CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1)) ≫ ψ := by
    apply Spec.map_injective
    rw [spec_map_pull_mor_ring, Spec.map_comp, hψ, Spec.map_preimage, hsnd]
    simp only [Category.assoc]
  rw [hfact, CommRingCat.hom_comp, ← Ideal.map_map,
    show (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))).hom =
      Ideal.Quotient.mk (M.Yideal i₀ γβ.1) from rfl,
    Ideal.map_quotient_self, Ideal.map_bot]

/-- Chart form of the containment condition for anything factoring through the
center. -/
theorem pullSubset_of_factor_chart {T : Scheme.{u+1}} (u : T ⟶ M.Ysub i₀)
    (i : M.indnumb)
    (γβ : (pull_cov X M.Drep T (u ≫ (M.Ysub i₀ ↘ X))).J) :
    Ideal.map (pull_mor_ring X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ).hom
        (M.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ).hom
        ((M.Dideal i γβ.1) ^ (ν i)) := by
  rw [Unique.eq_default i, M.pull_mor_ring_Yideal_eq_bot_of_factor u γβ]
  exact bot_le

/-- The containment condition holds for anything factoring through the center. -/
theorem pullSubset_of_factor {T : Scheme.{u+1}} (u : T ⟶ M.Ysub i₀) :
    (M.multiple ν).pullSubset (u ≫ (M.Ysub i₀ ↘ X)) :=
  fun i γβ => M.pullSubset_of_factor_chart ν u i γβ

/-- The Cartier condition holds for anything flat over the center. -/
theorem isCars_of_factor {T : Scheme.{u+1}} (u : T ⟶ M.Ysub i₀)
    [AlgebraicGeometry.Flat u] (hb : M.CarsOnY) :
    IsCars T (Clos.pullback (u ≫ (M.Ysub i₀ ↘ X)) (M.multiple ν).D) := by
  have hstep : Clos.pullback (u ≫ (M.Ysub i₀ ↘ X)) (M.multiple ν).D =
      pullback_Clos u (Clos.pullback (M.Ysub i₀ ↘ X) (M.multiple ν).D) := by
    show pullback_Clos (u ≫ (M.Ysub i₀ ↘ X))
      (Quotient.mk'' (M.multiple ν).Drep) = _
    rw [pullback_assoc]
    rfl
  rw [hstep]
  exact pullback_IsCars T u _ (M.Ylift_isCars ν hb)

/-- The universal lift for anything flat over the center. -/
theorem existsUnique_lift_of_factor {T : Scheme.{u+1}} (u : T ⟶ M.Ysub i₀)
    [AlgebraicGeometry.Flat u] (hb : M.CarsOnY) :
    ∃! g : T ⟶ (M.multiple ν).dilatation,
      g ≫ (M.multiple ν).structureMap = u ≫ (M.Ysub i₀ ↘ X) :=
  (M.multiple ν).universal_property T (u ≫ (M.Ysub i₀ ↘ X))
    (M.isCars_of_factor ν u hb) (M.pullSubset_of_factor ν u)

end FactorThroughY

section ChartNzd

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]
  (ν : M.indnumb → ℕ)

local notation "i₀" => (default : M.indnumb)

/-- The §4 standing hypothesis, ring form on the charts of `X`: the distinguished
element of the divisor is a non-zero-divisor in the coordinate ring of the center. -/
def ElemNzdOnQuot : Prop :=
  ∀ γ : M.cov.J,
    Ideal.Quotient.mk (M.Yideal i₀ γ) ((M.localMulticenter γ).elem i₀) ∈
      nonZeroDivisors ((M.cov.obj γ) ⧸ M.Yideal i₀ γ)

instance multiple_localMulticenter_index_unique (γ : M.cov.J) :
    Unique ((M.multiple ν).localMulticenter γ).index :=
  inferInstanceAs (Unique M.indnumb)

/-- The chosen generator of the multiplied divisor ideal spans it. -/
theorem multiple_localGen_span (γ : M.cov.J) :
    Ideal.span {((M.multiple ν).localMulticenter γ).elem i₀} =
      (M.Dideal i₀ γ) ^ (ν i₀) := by
  letI : Submodule.IsPrincipal ((M.Dideal i₀ γ) ^ (ν i₀)) :=
    (M.multiple ν).Dprin i₀ γ
  show Ideal.span {Submodule.IsPrincipal.generator ((M.Dideal i₀ γ) ^ (ν i₀))} = _
  exact Ideal.span_singleton_generator _

/-- Under the standing hypothesis, the class of the chosen generator of the multiplied
divisor ideal is a non-zero-divisor in the coordinate ring of the center. -/
theorem multiple_localGen_nzd (hSt : M.ElemNzdOnQuot) (γ : M.cov.J) :
    Ideal.Quotient.mk (((M.multiple ν).localMulticenter γ).ideal i₀)
        (((M.multiple ν).localMulticenter γ).elem i₀) ∈
      nonZeroDivisors (((M.multiple ν).cov.obj γ) ⧸
        ((M.multiple ν).localMulticenter γ).ideal i₀) := by
  show Ideal.Quotient.mk (M.Yideal i₀ γ)
      (((M.multiple ν).localMulticenter γ).elem i₀) ∈
    nonZeroDivisors ((M.cov.obj γ) ⧸ M.Yideal i₀ γ)
  have hbD : (M.localMulticenter γ).elem i₀ ∈ M.Dideal i₀ γ := by
    letI : Submodule.IsPrincipal (M.Dideal i₀ γ) := M.Dprin i₀ γ
    rw [← Ideal.span_singleton_generator (M.Dideal i₀ γ)]
    exact Ideal.mem_span_singleton_self _
  have hmem : (M.localMulticenter γ).elem i₀ ^ (ν i₀) ∈
      Ideal.span {((M.multiple ν).localMulticenter γ).elem i₀} := by
    rw [M.multiple_localGen_span ν γ]
    exact Ideal.pow_mem_pow hbD (ν i₀)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have h1 : Ideal.Quotient.mk (M.Yideal i₀ γ)
      ((M.localMulticenter γ).elem i₀ ^ (ν i₀)) ∈
      nonZeroDivisors ((M.cov.obj γ) ⧸ M.Yideal i₀ γ) := by
    rw [map_pow]
    exact pow_mem (hSt γ) (ν i₀)
  rw [← hc, map_mul] at h1
  exact (mul_mem_nonZeroDivisors.mp h1).2

end ChartNzd

section ConeEq

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]
  (ν : M.indnumb → ℕ)

local notation "i₀" => (default : M.indnumb)

/-- The chart piece of the center: `Spec (A_γ ⧸ M_γ) = Y ×_X U_γ`, as a scheme over
`Y`. -/
noncomputable def chartOfY (γ : M.cov.J) : Scheme.{u+1} :=
  Spec (CommRingCat.of ((M.cov.obj γ) ⧸ M.Yideal i₀ γ))

/-- Its open immersion into the center. -/
noncomputable def chartOfY_to (γ : M.cov.J) : M.chartOfY γ ⟶ M.Ysub i₀ :=
  (M.YcondIso i₀ γ).hom ≫ pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ)

instance chartOfY_to_flat (γ : M.cov.J) :
    AlgebraicGeometry.Flat (M.chartOfY_to γ) := by
  haveI h1 : IsOpenImmersion (pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ)) := by
    haveI := M.cov.map_prop γ
    infer_instance
  haveI : AlgebraicGeometry.Flat (pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ)) :=
    inferInstance
  haveI : AlgebraicGeometry.Flat (M.YcondIso i₀ γ).hom := inferInstance
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

/-- The map from the chart piece of the center into the chart of the dilatation, via
the exceptional quotient. -/
noncomputable def chartOfY_kappa (hSt : M.ElemNzdOnQuot) (γ : M.cov.J) :
    M.chartOfY γ ⟶ (M.multiple ν).chart γ :=
  Spec.map (CommRingCat.ofHom
    ((((M.multiple ν).localMulticenter γ).descQuotE
      (M.multiple_localGen_nzd ν hSt γ)).toRingHom))

/-- `κ` composed with the chart-to-base morphism is the quotient over `U_γ`. -/
theorem chartOfY_kappa_chartHom (hSt : M.ElemNzdOnQuot) (γ : M.cov.J) :
    M.chartOfY_kappa ν hSt γ ≫ (M.multiple ν).chartHom γ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γ))) := by
  rw [chartOfY_kappa]
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact ((((M.multiple ν).localMulticenter γ).descQuotE
    (M.multiple_localGen_nzd ν hSt γ)).commutes a)

/-- The chart piece of the center, mapped to `X` through the covering. -/
theorem chartOfY_to_overX (γ : M.cov.J) :
    M.chartOfY_to γ ≫ (M.Ysub i₀ ↘ X) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γ))) ≫
        M.cov.map γ := by
  have hover := M.YcondOver i₀ γ
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  rw [chartOfY_to, Category.assoc, pullback.condition, ← Category.assoc, hover]

/-- **The cone equality**: the two natural maps from the chart piece of the center to
the dilatation agree — through the lift `ℓ`, and through the exceptional quotient of
the chart. -/
theorem cone_eq (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot) (γ : M.cov.J) :
    M.chartOfY_to γ ≫ M.Ylift ν hb =
      M.chartOfY_kappa ν hSt γ ≫ (M.multiple ν).chartTo γ := by
  refine ((M.existsUnique_lift_of_factor ν (M.chartOfY_to γ) hb).unique ?_ ?_)
  · rw [Category.assoc, M.Ylift_over ν hb]
  · rw [Category.assoc, (M.multiple ν).structureMap_chart γ]
    show M.chartOfY_kappa ν hSt γ ≫ (M.multiple ν).chartHom γ ≫ M.cov.map γ = _
    rw [← Category.assoc, M.chartOfY_kappa_chartHom ν hSt γ,
      ← M.chartOfY_to_overX γ]

/-- The comparison map `Spec (A_γ/M_γ) ⟶ Y ×_B chart_γ`. -/
noncomputable def liftToPullback (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot)
    (γ : M.cov.J) :
    M.chartOfY γ ⟶ pullback (M.Ylift ν hb) ((M.multiple ν).chartTo γ) :=
  pullback.lift (M.chartOfY_to γ) (M.chartOfY_kappa ν hSt γ) (M.cone_eq ν hb hSt γ)

/-- The inverse comparison `Y ×_B chart_γ ⟶ Spec (A_γ/M_γ)`, through
`Y ×_X U_γ`. -/
noncomputable def pullbackToChartOfY (hb : M.CarsOnY) (γ : M.cov.J) :
    pullback (M.Ylift ν hb) ((M.multiple ν).chartTo γ) ⟶ M.chartOfY γ :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (M.multiple ν).chartHom γ)
    (by
      rw [← M.Ylift_over ν hb, ← Category.assoc, pullback.condition,
        Category.assoc, (M.multiple ν).structureMap_chart γ,
        show (M.multiple ν).chartToX γ =
          (M.multiple ν).chartHom γ ≫ M.cov.map γ from rfl, ← Category.assoc]) ≫
    (M.YcondIso i₀ γ).inv

theorem pullbackToChartOfY_comp_liftToPullback (hb : M.CarsOnY)
    (hSt : M.ElemNzdOnQuot) (γ : M.cov.J) :
    M.pullbackToChartOfY ν hb γ ≫ M.liftToPullback ν hb hSt γ = 𝟙 _ := by
  haveI : Mono ((M.multiple ν).chartTo γ) := by
    haveI := (M.multiple ν).chartTo_isOpenImmersion γ
    infer_instance
  have hfst : M.pullbackToChartOfY ν hb γ ≫ M.chartOfY_to γ =
      pullback.fst (M.Ylift ν hb) ((M.multiple ν).chartTo γ) := by
    rw [pullbackToChartOfY, chartOfY_to, Category.assoc, Iso.inv_hom_id_assoc,
      pullback.lift_fst]
  apply pullback.hom_ext
  · rw [Category.assoc, liftToPullback, pullback.lift_fst, Category.id_comp]
    exact hfst
  · rw [Category.assoc, liftToPullback, pullback.lift_snd, Category.id_comp]
    apply Mono.right_cancellation
      (f := (M.multiple ν).chartTo γ)
    rw [Category.assoc, ← M.cone_eq ν hb hSt γ, ← Category.assoc, hfst]
    exact pullback.condition

theorem liftToPullback_comp_pullbackToChartOfY (hb : M.CarsOnY)
    (hSt : M.ElemNzdOnQuot) (γ : M.cov.J) :
    M.liftToPullback ν hb hSt γ ≫ M.pullbackToChartOfY ν hb γ = 𝟙 _ := by
  have hover := M.YcondOver i₀ γ
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  rw [pullbackToChartOfY, ← Category.assoc, Iso.comp_inv_eq, Category.id_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, liftToPullback, pullback.lift_fst]
    rfl
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, liftToPullback,
      pullback.lift_snd, M.chartOfY_kappa_chartHom ν hSt γ, hover]

instance liftToPullback_isIso (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot)
    (γ : M.cov.J) : IsIso (M.liftToPullback ν hb hSt γ) :=
  ⟨M.pullbackToChartOfY ν hb γ,
    M.liftToPullback_comp_pullbackToChartOfY ν hb hSt γ,
    M.pullbackToChartOfY_comp_liftToPullback ν hb hSt γ⟩

/-- The Spec-level isomorphism of the exceptional quotient
`Spec (A_γ/M_γ) ≅ Spec (A_γ[G_γ] ⧸ exceptIdeal)`. -/
noncomputable def chartOfY_exceptIso (hSt : M.ElemNzdOnQuot) (γ : M.cov.J) :
    M.chartOfY γ ≅
      Spec (CommRingCat.of
        ((Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) ⧸
          ((M.multiple ν).localMulticenter γ).exceptIdeal)) where
  hom := Spec.map (CommRingCat.ofHom
    ((((M.multiple ν).localMulticenter γ).exceptQuotEquiv
      (M.multiple_localGen_nzd ν hSt γ)).toRingEquiv.toRingHom))
  inv := Spec.map (CommRingCat.ofHom
    ((((M.multiple ν).localMulticenter γ).exceptQuotEquiv
      (M.multiple_localGen_nzd ν hSt γ)).toRingEquiv.symm.toRingHom))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((((M.multiple ν).localMulticenter γ).exceptQuotEquiv
          (M.multiple_localGen_nzd ν hSt γ)).toRingEquiv.toRingHom).comp
        ((((M.multiple ν).localMulticenter γ).exceptQuotEquiv
          (M.multiple_localGen_nzd ν hSt γ)).toRingEquiv.symm.toRingHom) =
        RingHom.id _ from RingHom.ext fun x =>
          (((M.multiple ν).localMulticenter γ).exceptQuotEquiv
            (M.multiple_localGen_nzd ν hSt γ)).toRingEquiv.apply_symm_apply x]
    show Spec.map (𝟙 _) = 𝟙 _
    rw [Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((((M.multiple ν).localMulticenter γ).exceptQuotEquiv
          (M.multiple_localGen_nzd ν hSt γ)).toRingEquiv.symm.toRingHom).comp
        ((((M.multiple ν).localMulticenter γ).exceptQuotEquiv
          (M.multiple_localGen_nzd ν hSt γ)).toRingEquiv.toRingHom) =
        RingHom.id _ from RingHom.ext fun x =>
          (((M.multiple ν).localMulticenter γ).exceptQuotEquiv
            (M.multiple_localGen_nzd ν hSt γ)).toRingEquiv.symm_apply_apply x]
    show Spec.map (𝟙 _) = 𝟙 _
    rw [Spec.map_id]

@[simp] theorem chartOfY_exceptIso_hom (hSt : M.ElemNzdOnQuot) (γ : M.cov.J) :
    (M.chartOfY_exceptIso ν hSt γ).hom = Spec.map (CommRingCat.ofHom
      ((((M.multiple ν).localMulticenter γ).exceptQuotEquiv
        (M.multiple_localGen_nzd ν hSt γ)).toRingEquiv.toRingHom)) := rfl

/-- The exceptional quotient followed by the quotient projection is `κ`. -/
theorem chartOfY_exceptIso_mk (hSt : M.ElemNzdOnQuot) (γ : M.cov.J) :
    (M.chartOfY_exceptIso ν hSt γ).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (((M.multiple ν).localMulticenter γ).exceptIdeal))) =
      M.chartOfY_kappa ν hSt γ := by
  rw [chartOfY_exceptIso_hom, chartOfY_kappa, ← Spec.map_comp]
  congr 1

/-- **The presented ideal of the lifted center is the exceptional colon ideal** — the
chart identification `(P!)` at the heart of [Ma24, Lemma 4.4]. -/
theorem presentIdeal_eq_exceptIdeal (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot)
    (γ : M.cov.J) :
    haveI : IsClosedImmersion (M.Ylift ν hb) := M.Ylift_isClosedImmersion ν hb
    presentIdeal (M.Ylift ν hb) (M.multiple ν).dilatationCover γ =
      ((M.multiple ν).localMulticenter γ).exceptIdeal := by
  haveI : IsClosedImmersion (M.Ylift ν hb) := M.Ylift_isClosedImmersion ν hb
  refine spec_presentation_ideal_unique
    (pullback.snd (M.Ylift ν hb) ((M.multiple ν).dilatationCover.map γ))
    _ _
    (presentIso (M.Ylift ν hb) (M.multiple ν).dilatationCover γ)
    ((asIso (M.liftToPullback ν hb hSt γ)).symm ≪≫ M.chartOfY_exceptIso ν hSt γ)
    (presentIso_eq (M.Ylift ν hb) (M.multiple ν).dilatationCover γ)
    ?_
  rw [Iso.trans_hom, Category.assoc, M.chartOfY_exceptIso_mk ν hSt γ,
    Iso.symm_hom, asIso_inv]
  symm
  rw [IsIso.inv_comp_eq]
  show M.chartOfY_kappa ν hSt γ = M.liftToPullback ν hb hSt γ ≫
    pullback.snd (M.Ylift ν hb) ((M.multiple ν).chartTo γ)
  rw [liftToPullback, pullback.lift_snd]

end ConeEq

section OverDilatation

variable {X : Scheme.{u+1}} (M : PreMultiCenter X)

/-- Enhanced chart factorization: the factoring map exists at the scheme level, over
both the dilatation and the base chart. -/
theorem exists_chart_factorisation' (γ : M.cov.J) {C : CommRingCat.{u+1}}
    (c : Spec C ⟶ M.dilatation) (w : M.cov.obj γ ⟶ C)
    (hcw : c ≫ M.structureMap = Spec.map w ≫ M.cov.map γ) :
    ∃ s : Spec C ⟶ M.chart γ,
      s ≫ M.chartTo γ = c ∧ s ≫ M.chartHom γ = Spec.map w := by
  set s : Spec C ⟶ M.chart γ :=
    pullback.lift c (Spec.map w) hcw ≫ inv (M.chartCompare γ) with hs
  refine ⟨s, ?_, ?_⟩
  · rw [hs, Category.assoc, show inv (M.chartCompare γ) ≫ M.chartTo γ =
        pullback.fst M.structureMap (M.cov.map γ) from by
      rw [← M.chartCompare_fst γ, IsIso.inv_hom_id_assoc], pullback.lift_fst]
  · rw [hs, Category.assoc, show inv (M.chartCompare γ) ≫ M.chartHom γ =
        pullback.snd M.structureMap (M.cov.map γ) from by
      rw [← M.chartCompare_snd γ, IsIso.inv_hom_id_assoc], pullback.lift_snd]

variable [Unique M.indnumb] (ν : M.indnumb → ℕ)

local notation "i₀" => (default : M.indnumb)

omit [Unique M.indnumb] in
/-- **Cover-free `pullSubset` for schemes over the dilatation**: anything mapping to
`Bl^{νD}` compatibly over `X` satisfies the containment condition of `Bl^{νD}`. -/
theorem pullSubset_of_over_dilatation {T' : Scheme.{u+1}}
    (u : T' ⟶ (M.multiple ν).dilatation) :
    (M.multiple ν).pullSubset (u ≫ (M.multiple ν).structureMap) := by
  have hchart : ∀ (i : M.indnumb)
      (γβ : (pull_cov X M.Drep T' (u ≫ (M.multiple ν).structureMap)).J),
      Ideal.map (pull_mor_ring X M.Drep T'
          (u ≫ (M.multiple ν).structureMap) γβ).hom (M.Yideal i γβ.1) ≤
        Ideal.map (pull_mor_ring X M.Drep T'
          (u ≫ (M.multiple ν).structureMap) γβ).hom
          ((M.Dideal i γβ.1) ^ (ν i)) := by
    intro i γβ
    have hcw : ((pull_loc_cov X M.Drep T' (u ≫ (M.multiple ν).structureMap)
          γβ.1).map γβ.2 ≫
          pullback.fst (u ≫ (M.multiple ν).structureMap) (M.Drep.cov.map γβ.1) ≫ u) ≫
        (M.multiple ν).structureMap =
        Spec.map (pull_mor_ring X M.Drep T'
          (u ≫ (M.multiple ν).structureMap) γβ) ≫ M.cov.map γβ.1 := by
      rw [spec_map_pull_mor_ring]
      simp only [Category.assoc]
      rw [pullback.condition]
      rfl
    exact (M.multiple ν).Yideal_le_Dideal_of_over_dilatation γβ.1 _ _ hcw i
  exact fun i γβ => hchart i γβ

end OverDilatation

section RingChart

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]
  (γ : M.cov.J)

local notation "i₀" => (default : M.indnumb)

/-- The divisor ideal on a chart is spanned by the distinguished element. -/
theorem local_Dideal_span :
    M.Dideal i₀ γ = Ideal.span {(M.localMulticenter γ).elem i₀} := by
  letI : Submodule.IsPrincipal (M.Dideal i₀ γ) := M.Dprin i₀ γ
  exact (Ideal.span_singleton_generator (M.Dideal i₀ γ)).symm

section RingHomTarget

variable {B : Type (u+1)} [CommRing B]

/-- Under any ring map, the image of the chosen generator of `D^w` spans the same ideal
as the `w`-th power of the image of the distinguished element of `D`. -/
theorem hom_multipleGen_span (w : M.indnumb → ℕ) (f : (M.cov.obj γ) →+* B) :
    Ideal.span {f (((M.multiple w).localMulticenter γ).elem i₀)} =
      Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ (w i₀)} := by
  have h1 : Ideal.span {f (((M.multiple w).localMulticenter γ).elem i₀)} =
      Ideal.map f ((M.Dideal i₀ γ) ^ (w i₀)) := by
    rw [← M.multiple_localGen_span w γ, Ideal.map_span, Set.image_singleton]
  rw [h1, Ideal.map_pow, M.local_Dideal_span γ, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow]

/-- The generator image as a multiple of the power of the distinguished element. -/
theorem hom_multipleGen_mem (w : M.indnumb → ℕ) (f : (M.cov.obj γ) →+* B) :
    ∃ u : B, u * f ((M.localMulticenter γ).elem i₀) ^ (w i₀) =
      f (((M.multiple w).localMulticenter γ).elem i₀) :=
  Ideal.mem_span_singleton'.mp (by
    rw [← M.hom_multipleGen_span γ w f]
    exact Ideal.mem_span_singleton_self _)

/-- The power of the distinguished element as a multiple of the generator image. -/
theorem hom_multipleGen_mem' (w : M.indnumb → ℕ) (f : (M.cov.obj γ) →+* B) :
    ∃ v : B, v * f (((M.multiple w).localMulticenter γ).elem i₀) =
      f ((M.localMulticenter γ).elem i₀) ^ (w i₀) :=
  Ideal.mem_span_singleton'.mp (by
    rw [M.hom_multipleGen_span γ w f]
    exact Ideal.mem_span_singleton_self _)

end RingHomTarget

/-- In the dilatation `A_γ[G_w]`, every power `α^k` with `k ≤ w` of the image of the
distinguished element is a non-zero-divisor. -/
theorem chart_alpha_pow_nzd (w k : M.indnumb → ℕ) (hkw : k i₀ ≤ w i₀) :
    (algebraMap ((M.multiple w).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ))
        ((M.localMulticenter γ).elem i₀)) ^ (k i₀) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) := by
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :=
    (algebraMap ((M.multiple w).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :
        _ →+* _) with hf
  show f ((M.localMulticenter γ).elem i₀) ^ (k i₀) ∈ nonZeroDivisors _
  have hgen : f (((M.multiple w).localMulticenter γ).elem i₀) ∈
      nonZeroDivisors _ :=
    nonzerodiv_image_single ((M.multiple w).localMulticenter γ) i₀
  obtain ⟨u, hu⟩ := M.hom_multipleGen_mem γ w f
  have h2 : u * f ((M.localMulticenter γ).elem i₀) ^ (w i₀) ∈
      nonZeroDivisors _ := by
    rw [hu]; exact hgen
  have hpow := (mul_mem_nonZeroDivisors.mp h2).2
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hkw
  rw [hm, pow_add] at hpow
  exact (mul_mem_nonZeroDivisors.mp hpow).1

/-- In `A_γ[G_w]`, the image of the chosen generator of `D^k` is a non-zero-divisor
for `k ≤ w`. -/
theorem chart_gen_nzd (w k : M.indnumb → ℕ) (hkw : k i₀ ≤ w i₀) :
    algebraMap ((M.multiple w).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ))
        (((M.multiple k).localMulticenter γ).elem i₀) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) := by
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :=
    (algebraMap ((M.multiple w).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :
        _ →+* _) with hf
  show f (((M.multiple k).localMulticenter γ).elem i₀) ∈ nonZeroDivisors _
  obtain ⟨v, hv⟩ := M.hom_multipleGen_mem' γ k f
  have h : v * f (((M.multiple k).localMulticenter γ).elem i₀) ∈
      nonZeroDivisors _ := by
    rw [hv]
    exact M.chart_alpha_pow_nzd γ w k hkw
  exact (mul_mem_nonZeroDivisors.mp h).2

section RhoMap

variable (ν n : M.indnumb → ℕ)

/-- Bridge instance: the target dilatation is an algebra over the chart ring in the
`ν`-spelling (definitionally the `ν+n`-spelling). -/
noncomputable instance chartAlgebraBridge :
    Algebra ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) :=
  inferInstanceAs (Algebra ((M.multiple (ν + n)).cov.obj γ)
    (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)))

/-- The center ideal maps into the span of `α^{ν+n}` in `A_γ[G_{ν+n}]`. -/
theorem chart_M_le_alpha_pow :
    Ideal.map (algebraMap ((M.multiple (ν + n)).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)))
        (M.Yideal i₀ γ) ≤
      Ideal.span {algebraMap ((M.multiple (ν + n)).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ))
        ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀)} := by
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) :=
    (algebraMap ((M.multiple (ν + n)).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) :
        _ →+* _) with hf
  show Ideal.map f (M.Yideal i₀ γ) ≤
    Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀)}
  have h1 : Ideal.map f (((M.multiple (ν + n)).localMulticenter γ).ideal i₀) ≤
      Ideal.span {f (((M.multiple (ν + n)).localMulticenter γ).elem i₀)} :=
    Multicenter.self_le ((M.multiple (ν + n)).localMulticenter γ) i₀
  rw [M.hom_multipleGen_span γ (ν + n) f] at h1
  exact h1

/-- The universal-property conditions for the canonical chart map
`A_γ[G_ν] → A_γ[G_{ν+n}]`: non-zero-divisor condition. -/
theorem chartRho_nzd :
    ∀ i, algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ))
        (((M.multiple ν).localMulticenter γ).elem i) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) := by
  intro i
  rw [Unique.eq_default i]
  exact M.chart_gen_nzd γ (ν + n) ν (by
    show ν i₀ ≤ ν i₀ + n i₀
    exact Nat.le_add_right _ _)

/-- Span condition. -/
theorem chartRho_gen :
    ∀ i, Ideal.span {algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ))
        (((M.multiple ν).localMulticenter γ).elem i)} =
      Ideal.map (algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)))
        (((M.multiple ν).localMulticenter γ).LargeIdeal i) := by
  intro i
  rw [Unique.eq_default i]
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) :=
    (algebraMap ((M.multiple (ν + n)).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) :
        _ →+* _) with hf
  have hle : Ideal.map f (((M.multiple ν).localMulticenter γ).ideal i₀) ≤
      Ideal.span {f (((M.multiple ν).localMulticenter γ).elem i₀)} := by
    have h1 : Ideal.map f (M.Yideal i₀ γ) ≤
        Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀)} :=
      M.chart_M_le_alpha_pow γ ν n
    have h2 : Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀)} ≤
        Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ (ν i₀)} :=
      Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow _ (by
          show ν i₀ ≤ ν i₀ + n i₀
          exact Nat.le_add_right _ _))
    have h3 := le_trans h1 h2
    rw [← M.hom_multipleGen_span γ ν f] at h3
    exact h3
  show Ideal.span {f (((M.multiple ν).localMulticenter γ).elem i₀)} =
    Ideal.map f (((M.multiple ν).localMulticenter γ).ideal i₀ +
      Ideal.span {((M.multiple ν).localMulticenter γ).elem i₀})
  rw [Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact (sup_eq_right.mpr hle).symm

/-- **The canonical chart comparison map** `A_γ[G_ν] →ₐ A_γ[G_{ν+n}]` of the
dilatation charts, from the ring-level universal property. -/
noncomputable def chartRho :
    Multicenter.Dilatation ((M.multiple ν).localMulticenter γ) →ₐ[(M.multiple ν).cov.obj γ]
      Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ) :=
  desc ((M.multiple ν).localMulticenter γ) (M.chartRho_nzd γ ν n) (M.chartRho_gen γ ν n)

/-- `chartRho` restricts to the identity on the base ring. -/
theorem chartRho_algebraMap (x : (M.cov.obj γ)) :
    M.chartRho γ ν n (algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) x) =
    algebraMap ((M.multiple (ν + n)).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) x :=
  (M.chartRho γ ν n).commutes x

/-- **The forward containment** of [Ma24, Lemma 4.4]: the exceptional colon ideal of
`A_γ[G_ν]` maps into the `n`-th power of the total-transform ideal in
`A_γ[G_{ν+n}]`. -/
theorem chartRho_exceptIdeal_le :
    Ideal.map (M.chartRho γ ν n).toRingHom
        (((M.multiple ν).localMulticenter γ).exceptIdeal) ≤
      (Ideal.map (algebraMap ((M.multiple (ν + n)).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)))
        (M.Dideal i₀ γ)) ^ (n i₀) := by
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) :=
    (algebraMap ((M.multiple (ν + n)).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) :
        _ →+* _) with hf
  show Ideal.map (M.chartRho γ ν n).toRingHom
      (((M.multiple ν).localMulticenter γ).exceptIdeal) ≤
    (Ideal.map f (M.Dideal i₀ γ)) ^ (n i₀)
  have htarget : (Ideal.map f (M.Dideal i₀ γ)) ^ (n i₀) =
      Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ (n i₀)} := by
    rw [M.local_Dideal_span γ, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow]
  rw [htarget, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  show M.chartRho γ ν n x ∈
    Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ (n i₀)}
  have hx' := (((M.multiple ν).localMulticenter γ).mem_exceptIdeal).mp hx
  have h1 : (M.chartRho γ ν n)
      (algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))
        (((M.multiple ν).localMulticenter γ).elem i₀) * x) ∈
      Ideal.map (M.chartRho γ ν n).toRingHom
        (Ideal.map (algebraMap ((M.multiple ν).cov.obj γ)
          (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
          (((M.multiple ν).localMulticenter γ).ideal i₀)) :=
    Ideal.mem_map_of_mem _ hx'
  rw [Ideal.map_map,
    show (M.chartRho γ ν n).toRingHom.comp
        (algebraMap ((M.multiple ν).cov.obj γ)
          (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))) = f from
      RingHom.ext fun a => (M.chartRho γ ν n).commutes a,
    map_mul,
    show (M.chartRho γ ν n)
        (algebraMap ((M.multiple ν).cov.obj γ)
          (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))
          (((M.multiple ν).localMulticenter γ).elem i₀)) =
      f (((M.multiple ν).localMulticenter γ).elem i₀) from
      (M.chartRho γ ν n).commutes _] at h1
  have h2 : f (((M.multiple ν).localMulticenter γ).elem i₀) *
      (M.chartRho γ ν n) x ∈
      Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀)} := by
    have hb : Ideal.map f (((M.multiple ν).localMulticenter γ).ideal i₀) ≤
        Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀)} :=
      M.chart_M_le_alpha_pow γ ν n
    exact hb h1
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h2
  obtain ⟨v, hv⟩ := M.hom_multipleGen_mem' γ ν f
  have hcalc : f (((M.multiple ν).localMulticenter γ).elem i₀) *
      ((M.chartRho γ ν n) x -
        z * v * f ((M.localMulticenter γ).elem i₀) ^ (n i₀)) = 0 := by
    have hgoal : f (((M.multiple ν).localMulticenter γ).elem i₀) *
        (M.chartRho γ ν n) x =
        z * v * f (((M.multiple ν).localMulticenter γ).elem i₀) *
          f ((M.localMulticenter γ).elem i₀) ^ (n i₀) := by
      rw [← hz,
        show ((ν + n) i₀ : ℕ) = ν i₀ + n i₀ from rfl, pow_add, ← hv]
      ring
    rw [mul_sub, hgoal]
    ring
  have hnzd' : f (((M.multiple ν).localMulticenter γ).elem i₀) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γ)) :=
    M.chartRho_nzd γ ν n i₀
  have hxeq : (M.chartRho γ ν n) x =
      z * v * f ((M.localMulticenter γ).elem i₀) ^ (n i₀) :=
    sub_eq_zero.mp ((mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd').mp hcalc)
  rw [hxeq]
  exact Ideal.mem_span_singleton'.mpr ⟨z * v, rfl⟩

end RhoMap

end RingChart

section ChartCone

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]
  (ν n : M.indnumb → ℕ) (γ : M.cov.J)

local notation "i₀" => (default : M.indnumb)

/-- Pointwise inequality `ν ≤ ν + n`. -/
theorem nu_le_add : ∀ i : M.indnumb, ν i ≤ (ν + n) i := fun i => Nat.le_add_right _ _

/-- The chart comparison morphism `chart^{ν+n}_γ ⟶ chart^ν_γ` of the dilatations. -/
noncomputable def chartRhoSch :
    (M.multiple (ν + n)).chart γ ⟶ (M.multiple ν).chart γ :=
  Spec.map (CommRingCat.ofHom (M.chartRho γ ν n).toRingHom)

/-- `chartRhoSch` lies over the chart-to-base morphisms. -/
theorem chartRhoSch_chartHom :
    M.chartRhoSch ν n γ ≫ (M.multiple ν).chartHom γ =
      (M.multiple (ν + n)).chartHom γ := by
  rw [chartRhoSch]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact M.chartRho_algebraMap γ ν n a

/-- The chart of `Bl^{(ν+n)D}` maps to `X` through the covering. -/
theorem chartT_overX :
    ((M.multiple (ν + n)).chartTo γ ≫ M.multipleHom (ν + n) ν (M.nu_le_add ν n)) ≫
      (M.multiple ν).structureMap = (M.multiple (ν + n)).chartToX γ := by
  rw [Category.assoc, M.multipleHom_over (ν + n) ν (M.nu_le_add ν n),
    (M.multiple (ν + n)).structureMap_chart γ]

/-- The Cartier condition for the chart of `Bl^{(ν+n)D}` over `X` with respect to
`Bl^{νD}`. -/
theorem chartT_isCars :
    IsCars ((M.multiple (ν + n)).chart γ)
      (Clos.pullback ((M.multiple (ν + n)).chartToX γ) (M.multiple ν).D) := by
  have heq : (M.multiple (ν + n)).chartToX γ =
      (M.multiple (ν + n)).chartTo γ ≫ (M.multiple (ν + n)).structureMap :=
    ((M.multiple (ν + n)).structureMap_chart γ).symm
  rw [heq]
  have hstep : Clos.pullback
      ((M.multiple (ν + n)).chartTo γ ≫ (M.multiple (ν + n)).structureMap)
      (M.multiple ν).D =
      pullback_Clos ((M.multiple (ν + n)).chartTo γ)
        (Clos.pullback (M.multiple (ν + n)).structureMap (M.multiple ν).D) := by
    show pullback_Clos _ (Quotient.mk'' (M.multiple ν).Drep) = _
    rw [pullback_assoc]
    rfl
  rw [hstep]
  haveI : IsOpenImmersion ((M.multiple (ν + n)).chartTo γ) :=
    (M.multiple (ν + n)).chartTo_isOpenImmersion γ
  haveI : AlgebraicGeometry.Flat ((M.multiple (ν + n)).chartTo γ) := inferInstance
  exact pullback_IsCars _ _ _ (M.multiple_isCars (ν + n) ν (M.nu_le_add ν n))

/-- The containment condition for the chart of `Bl^{(ν+n)D}` over `X`. -/
theorem chartT_pullSubset :
    (M.multiple ν).pullSubset ((M.multiple (ν + n)).chartToX γ) := by
  have h := M.pullSubset_of_over_dilatation ν
    ((M.multiple (ν + n)).chartTo γ ≫ M.multipleHom (ν + n) ν (M.nu_le_add ν n))
  rw [Category.assoc, M.multipleHom_over (ν + n) ν (M.nu_le_add ν n),
    (M.multiple (ν + n)).structureMap_chart γ] at h
  exact h

/-- **The chart cone**: the canonical morphism `Bl^{(ν+n)D} ⟶ Bl^{νD}` restricted to a
chart is the `Spec` of the ring-level comparison map. -/
theorem chart_cone :
    (M.multiple (ν + n)).chartTo γ ≫ M.multipleHom (ν + n) ν (M.nu_le_add ν n) =
      M.chartRhoSch ν n γ ≫ (M.multiple ν).chartTo γ := by
  refine ((M.multiple ν).universal_property ((M.multiple (ν + n)).chart γ)
    ((M.multiple (ν + n)).chartToX γ) (M.chartT_isCars ν n γ)
    (M.chartT_pullSubset ν n γ)).unique ?_ ?_
  · exact M.chartT_overX ν n γ
  · rw [Category.assoc, (M.multiple ν).structureMap_chart γ,
      show (M.multiple ν).chartToX γ =
        (M.multiple ν).chartHom γ ≫ M.cov.map γ from rfl,
      ← Category.assoc, M.chartRhoSch_chartHom ν n γ]
    show (M.multiple (ν + n)).chartHom γ ≫ M.cov.map γ = _
    rfl

/-- The factorization of a pull-covering piece of `Bl^{(ν+n)D} ×_B chart^ν_γ` through
the chart of `Bl^{(ν+n)D}`, compatibly with the ring comparison map. -/
theorem secondStage_piece_factor (hb : M.CarsOnY)
    (γβ : (pull_cov (M.multiple ν).dilatation (M.secondStage ν n hb).Drep
      (M.multiple (ν + n)).dilatation
      (M.multipleHom (ν + n) ν (M.nu_le_add ν n))).J) :
    ∃ ψ : CommRingCat.of
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γβ.1)) ⟶
        (pull_loc_cov (M.multiple ν).dilatation (M.secondStage ν n hb).Drep
          (M.multiple (ν + n)).dilatation
          (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ.1).obj γβ.2,
      pull_mor_ring (M.multiple ν).dilatation (M.secondStage ν n hb).Drep
          (M.multiple (ν + n)).dilatation
          (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ =
        CommRingCat.ofHom (M.chartRho γβ.1 ν n).toRingHom ≫ ψ ∧
      RingHom.Flat ψ.hom := by
  have hsnd : (pull_loc_cov (M.multiple ν).dilatation
      (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
      (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ.1).map γβ.2 ≫
      pullback.snd (M.multipleHom (ν + n) ν (M.nu_le_add ν n))
        ((M.secondStage ν n hb).Drep.cov.map γβ.1) =
      Spec.map (pull_mor_ring (M.multiple ν).dilatation
        (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
        (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ) :=
    (spec_map_pull_mor_ring _ _ γβ).symm
  have hcφ : ((pull_loc_cov (M.multiple ν).dilatation
      (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
      (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ.1).map γβ.2 ≫
      pullback.fst (M.multipleHom (ν + n) ν (M.nu_le_add ν n))
        ((M.secondStage ν n hb).Drep.cov.map γβ.1)) ≫
      M.multipleHom (ν + n) ν (M.nu_le_add ν n) =
      Spec.map (pull_mor_ring (M.multiple ν).dilatation
        (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
        (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ) ≫
      (M.multiple ν).chartTo γβ.1 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd]
    rfl
  have hcw : ((pull_loc_cov (M.multiple ν).dilatation
      (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
      (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ.1).map γβ.2 ≫
      pullback.fst (M.multipleHom (ν + n) ν (M.nu_le_add ν n))
        ((M.secondStage ν n hb).Drep.cov.map γβ.1)) ≫
      (M.multiple (ν + n)).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ((M.multiple ν).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1))) ≫
        pull_mor_ring (M.multiple ν).dilatation (M.secondStage ν n hb).Drep
          (M.multiple (ν + n)).dilatation
          (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ) ≫ M.cov.map γβ.1 := by
    rw [← M.multipleHom_over (ν + n) ν (M.nu_le_add ν n), ← Category.assoc,
      hcφ, Spec.map_comp]
    rw [Category.assoc, Category.assoc, (M.multiple ν).structureMap_chart γβ.1]
    rfl
  obtain ⟨s, hs1, hs2⟩ := (M.multiple (ν + n)).exists_chart_factorisation' γβ.1
    _ _ hcw
  haveI : IsOpenImmersion ((M.multiple ν).chartTo γβ.1) :=
    (M.multiple ν).chartTo_isOpenImmersion γβ.1
  haveI : Mono ((M.multiple ν).chartTo γβ.1) := inferInstance
  have hkey : Spec.map (pull_mor_ring (M.multiple ν).dilatation
      (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
      (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ) =
      s ≫ M.chartRhoSch ν n γβ.1 := by
    apply Mono.right_cancellation (f := (M.multiple ν).chartTo γβ.1)
    rw [← hcφ]
    simp only [Category.assoc]
    rw [← M.chart_cone ν n γβ.1, reassoc_of% hs1]
  refine ⟨Spec.preimage s, ?_, ?_⟩
  · apply Spec.map_injective
    rw [hkey, Spec.map_comp, Spec.map_preimage]
    rfl
  · -- `s` is an open immersion, hence flat
    haveI hc : IsOpenImmersion ((pull_loc_cov (M.multiple ν).dilatation
        (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
        (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ.1).map γβ.2 ≫
        pullback.fst (M.multipleHom (ν + n) ν (M.nu_le_add ν n))
          ((M.secondStage ν n hb).Drep.cov.map γβ.1)) :=
      (pull_cov (M.multiple ν).dilatation (M.secondStage ν n hb).Drep
        (M.multiple (ν + n)).dilatation
        (M.multipleHom (ν + n) ν (M.nu_le_add ν n))).map_prop γβ
    haveI hsc : IsOpenImmersion (s ≫ (M.multiple (ν + n)).chartTo γβ.1) := by
      rw [hs1]
      exact hc
    haveI hs : IsOpenImmersion s :=
      IsOpenImmersion.of_comp s ((M.multiple (ν + n)).chartTo γβ.1)
    haveI hflat : AlgebraicGeometry.Flat s := inferInstance
    haveI hflat2 : AlgebraicGeometry.Flat (Spec.map (Spec.preimage s)) := by
      rw [Spec.map_preimage]
      exact hflat
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Flat)).mp hflat2

/-- Chart form of the containment condition of the second stage along the canonical
morphism. -/
theorem secondStage_pullSubset_chart (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot)
    (i : M.indnumb)
    (γβ : (pull_cov (M.multiple ν).dilatation (M.secondStage ν n hb).Drep
      (M.multiple (ν + n)).dilatation
      (M.multipleHom (ν + n) ν (M.nu_le_add ν n))).J) :
    Ideal.map (pull_mor_ring (M.multiple ν).dilatation
        (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
        (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ).hom
        ((M.secondStage ν n hb).Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring (M.multiple ν).dilatation
        (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
        (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ).hom
        ((M.secondStage ν n hb).Dideal i γβ.1) := by
  obtain ⟨ψ, hψ, -⟩ := M.secondStage_piece_factor ν n hb γβ
  rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hY : (M.secondStage ν n hb).Yideal i γβ.1 =
      ((M.multiple ν).localMulticenter γβ.1).exceptIdeal := by
    rw [M.secondStage_Yideal ν n hb i γβ.1]
    exact M.presentIdeal_eq_exceptIdeal ν hb hSt γβ.1
  rw [hY]
  rw [show (M.secondStage ν n hb).Dideal i γβ.1 =
    (Ideal.map (algebraMap ((M.multiple ν).cov.obj γβ.1)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1)))
      (M.Dideal i γβ.1)) ^ (n i) from rfl]
  rw [← Ideal.map_map, ← Ideal.map_map]
  refine Ideal.map_mono ?_
  rw [Unique.eq_default i]
  refine le_trans (M.chartRho_exceptIdeal_le γβ.1 ν n) ?_
  rw [Ideal.map_pow]
  refine Ideal.pow_right_mono ?_ _
  rw [Ideal.map_map]
  rw [show ((M.chartRho γβ.1 ν n).toRingHom).comp
      (algebraMap ((M.multiple ν).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1))) =
      (algebraMap ((M.multiple (ν + n)).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γβ.1))) from
    RingHom.ext fun a => M.chartRho_algebraMap γβ.1 ν n a]

/-- **The containment condition of the second stage holds along the canonical
morphism** `Bl^{(ν+n)D} ⟶ Bl^{νD}`. -/
theorem secondStage_pullSubset (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot) :
    (M.secondStage ν n hb).pullSubset
      (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) :=
  fun i γβ => M.secondStage_pullSubset_chart ν n hb hSt i γβ

/-- Chart form of the Cartier condition of the second stage along the canonical
morphism. -/
theorem secondStage_isCars_chart (hb : M.CarsOnY) (i : M.indnumb)
    (γβ : (pull_cov (M.multiple ν).dilatation (M.secondStage ν n hb).Drep
      (M.multiple (ν + n)).dilatation
      (M.multipleHom (ν + n) ν (M.nu_le_add ν n))).J) :
    ∃ g : (pull_loc_cov (M.multiple ν).dilatation (M.secondStage ν n hb).Drep
        (M.multiple (ν + n)).dilatation
        (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ.1).obj γβ.2,
      (pullback_PreClos (M.multiple ν).dilatation
          (M.multiple (ν + n)).dilatation
          (M.multipleHom (ν + n) ν (M.nu_le_add ν n))
          (M.secondStage ν n hb).Drep).ideal i γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov (M.multiple ν).dilatation
        (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
        (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ.1).obj γβ.2) := by
  rw [Unique.eq_default i]
  obtain ⟨ψ, hψ, hflat⟩ := M.secondStage_piece_factor ν n hb γβ
  refine ⟨ψ.hom ((algebraMap ((M.multiple (ν + n)).cov.obj γβ.1)
    (Multicenter.Dilatation ((M.multiple (ν + n)).localMulticenter γβ.1)))
      ((M.localMulticenter γβ.1).elem i₀)) ^ (n i₀), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring (M.multiple ν).dilatation
        (M.secondStage ν n hb).Drep (M.multiple (ν + n)).dilatation
        (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) γβ).hom
        ((M.secondStage ν n hb).Dideal i₀ γβ.1) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [show (M.secondStage ν n hb).Dideal i₀ γβ.1 =
      (Ideal.map (algebraMap ((M.multiple ν).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1)))
        (M.Dideal i₀ γβ.1)) ^ (n i₀) from rfl]
    rw [Ideal.map_pow, Ideal.map_map, RingHom.comp_assoc,
      show ((M.chartRho γβ.1 ν n).toRingHom).comp
        (algebraMap ((M.multiple ν).cov.obj γβ.1)
          (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1))) =
        (algebraMap ((M.multiple (ν + n)).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((M.multiple (ν + n)).localMulticenter γβ.1))) from
      RingHom.ext fun a => M.chartRho_algebraMap γβ.1 ν n a,
      ← Ideal.map_map]
    rw [M.local_Dideal_span γβ.1, Ideal.map_span, Set.image_singleton,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    rfl
  · rw [← map_pow]
    exact hflat.preserves_nonzeroDivisors
      (M.chart_alpha_pow_nzd γβ.1 (ν + n) n (Nat.le_add_left _ _))

/-- **The Cartier condition of the second stage holds along the canonical
morphism.** -/
theorem secondStage_isCars (hb : M.CarsOnY) :
    IsCars (M.multiple (ν + n)).dilatation
      (Clos.pullback (M.multipleHom (ν + n) ν (M.nu_le_add ν n))
        (M.secondStage ν n hb).D) :=
  ⟨pullback_PreClos (M.multiple ν).dilatation (M.multiple (ν + n)).dilatation
      (M.multipleHom (ν + n) ν (M.nu_le_add ν n)) (M.secondStage ν n hb).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun i γβ => M.secondStage_isCars_chart ν n hb i γβ), rfl⟩

/-- **The forward morphism of [Ma24, Lemma 4.4]**: `Bl^{(ν+n)D}_Y X` maps to the
second-stage dilatation over `Bl^{νD}_Y X`, uniquely. -/
theorem existsUnique_iterFwd (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot) :
    ∃! g : (M.multiple (ν + n)).dilatation ⟶
        (M.secondStage ν n hb).dilatation,
      g ≫ (M.secondStage ν n hb).structureMap =
        M.multipleHom (ν + n) ν (M.nu_le_add ν n) :=
  (M.secondStage ν n hb).universal_property _
    (M.multipleHom (ν + n) ν (M.nu_le_add ν n))
    (M.secondStage_isCars ν n hb) (M.secondStage_pullSubset ν n hb hSt)

end ChartCone

section BackwardRing

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]
  (ν n : M.indnumb → ℕ) (γ : M.cov.J)

local notation "i₀" => (default : M.indnumb)

instance secondStage_localMulticenter_index_unique (hb : M.CarsOnY) :
    Unique ((M.secondStage ν n hb).localMulticenter γ).index :=
  inferInstanceAs (Unique M.indnumb)

/-- The chosen generator of the second-stage divisor spans the `n`-th power of the
total-transform ideal. -/
theorem secondStage_localGen_span (hb : M.CarsOnY) :
    Ideal.span {((M.secondStage ν n hb).localMulticenter γ).elem i₀} =
      (Ideal.map (algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
        (M.Dideal i₀ γ)) ^ (n i₀) := by
  letI : Submodule.IsPrincipal ((Ideal.map (algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
      (M.Dideal i₀ γ)) ^ (n i₀)) :=
    (M.secondStage ν n hb).Dprin i₀ γ
  show Ideal.span {Submodule.IsPrincipal.generator
    ((Ideal.map (algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
      (M.Dideal i₀ γ)) ^ (n i₀))} = _
  exact Ideal.span_singleton_generator _

/-- In the second-stage dilatation, the image of `α^{ν+n}` is a non-zero-divisor. -/
theorem secondChart_alpha_nzd (hb : M.CarsOnY) :
    ((algebraMap ((M.secondStage ν n hb).cov.obj γ)
        (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ))).comp
      (algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))))
      ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γ)) := by
  set g2 : (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) →+*
      (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ)) :=
    (algebraMap ((M.secondStage ν n hb).cov.obj γ)
      (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ)) :
        _ →+* _) with hg2
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :=
    (algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :
        _ →+* _) with hf
  show (g2.comp f) ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀) ∈ _
  simp only [RingHom.comp_apply]
  have hgen1 : f (((M.multiple ν).localMulticenter γ).elem i₀) ∈
      nonZeroDivisors (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :=
    nonzerodiv_image_single ((M.multiple ν).localMulticenter γ) i₀
  have hgen1' : g2 (f (((M.multiple ν).localMulticenter γ).elem i₀)) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γ)) :=
    Multicenter.Dilatation.nonzerodiv_of_nonzerodiv
      (F := (M.secondStage ν n hb).localMulticenter γ) hgen1
  obtain ⟨u, hu⟩ := M.hom_multipleGen_mem γ ν f
  have h1 : g2 u * (g2 (f ((M.localMulticenter γ).elem i₀))) ^ (ν i₀) =
      g2 (f (((M.multiple ν).localMulticenter γ).elem i₀)) := by
    rw [← map_pow, ← map_mul, hu]
  have h2 : g2 u * (g2 (f ((M.localMulticenter γ).elem i₀))) ^ (ν i₀) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γ)) := by
    rw [h1]; exact hgen1'
  have hν := (mul_mem_nonZeroDivisors.mp h2).2
  have hgenH : g2 (((M.secondStage ν n hb).localMulticenter γ).elem i₀) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γ)) :=
    nonzerodiv_image_single ((M.secondStage ν n hb).localMulticenter γ) i₀
  have hspan2 : Ideal.span
      {((M.secondStage ν n hb).localMulticenter γ).elem i₀} =
      Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ (n i₀)} := by
    rw [M.secondStage_localGen_span ν n γ hb]
    show (Ideal.map f (M.Dideal i₀ γ)) ^ (n i₀) = _
    rw [M.local_Dideal_span γ, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow]
  have hmemH : ((M.secondStage ν n hb).localMulticenter γ).elem i₀ ∈
      Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ (n i₀)} := by
    rw [← hspan2]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmemH
  have h3 : g2 c * (g2 (f ((M.localMulticenter γ).elem i₀))) ^ (n i₀) =
      g2 (((M.secondStage ν n hb).localMulticenter γ).elem i₀) := by
    rw [← map_pow, ← map_mul, hc]
  have h4 : g2 c * (g2 (f ((M.localMulticenter γ).elem i₀))) ^ (n i₀) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γ)) := by
    rw [h3]; exact hgenH
  have hn := (mul_mem_nonZeroDivisors.mp h4).2
  rw [show ((ν + n) i₀ : ℕ) = ν i₀ + n i₀ from rfl, pow_add]
  exact mul_mem hν hn

/-- **The backward containment of [Ma24, Lemma 4.4]**: in the second-stage dilatation,
the center ideal is contained in the span of `α^{ν+n}`.  A section `m` of the center
factors as `z · g_ν` with `z` in the exceptional ideal, and the exceptional ideal
factors through `α^n` by the second stage's own condition. -/
theorem secondChart_M_le (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot) :
    Ideal.map ((algebraMap ((M.secondStage ν n hb).cov.obj γ)
        (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ))).comp
      (algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))))
        (M.Yideal i₀ γ) ≤
      Ideal.span {((algebraMap ((M.secondStage ν n hb).cov.obj γ)
        (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ))).comp
      (algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))))
        ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀)} := by
  set g2 : (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) →+*
      (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ)) :=
    (algebraMap ((M.secondStage ν n hb).cov.obj γ)
      (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ)) :
        _ →+* _) with hg2
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :=
    (algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :
        _ →+* _) with hf
  rw [Ideal.map_le_iff_le_comap]
  intro m hm
  rw [Ideal.mem_comap]
  show (g2.comp f) m ∈ Ideal.span
    {(g2.comp f) ((M.localMulticenter γ).elem i₀) ^ ((ν + n) i₀)}
  simp only [RingHom.comp_apply]
  have hself : Ideal.map f (((M.multiple ν).localMulticenter γ).ideal i₀) ≤
      Ideal.span {f (((M.multiple ν).localMulticenter γ).elem i₀)} :=
    Multicenter.self_le ((M.multiple ν).localMulticenter γ) i₀
  have hm2 : f m ∈
      Ideal.span {f (((M.multiple ν).localMulticenter γ).elem i₀)} :=
    hself (Ideal.mem_map_of_mem _ hm)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hm2
  have hzE : z ∈ ((M.multiple ν).localMulticenter γ).exceptIdeal := by
    rw [Multicenter.mem_exceptIdeal]
    show f (((M.multiple ν).localMulticenter γ).elem i₀) * z ∈
      Ideal.map f (((M.multiple ν).localMulticenter γ).ideal i₀)
    rw [mul_comm, hz]
    exact Ideal.mem_map_of_mem _ hm
  have hHi : ((M.secondStage ν n hb).localMulticenter γ).ideal i₀ =
      ((M.multiple ν).localMulticenter γ).exceptIdeal := by
    show (M.secondStage ν n hb).Yideal i₀ γ = _
    rw [M.secondStage_Yideal ν n hb i₀ γ]
    exact M.presentIdeal_eq_exceptIdeal ν hb hSt γ
  have hselfH : Ideal.map g2
      (((M.secondStage ν n hb).localMulticenter γ).ideal i₀) ≤
      Ideal.span {g2 (((M.secondStage ν n hb).localMulticenter γ).elem i₀)} :=
    Multicenter.self_le ((M.secondStage ν n hb).localMulticenter γ) i₀
  have hz2 : g2 z ∈
      Ideal.span {g2 (((M.secondStage ν n hb).localMulticenter γ).elem i₀)} := by
    refine hselfH ?_
    rw [hHi]
    exact Ideal.mem_map_of_mem _ hzE
  have hspan2 : Ideal.span
      {((M.secondStage ν n hb).localMulticenter γ).elem i₀} =
      Ideal.span {f ((M.localMulticenter γ).elem i₀) ^ (n i₀)} := by
    rw [M.secondStage_localGen_span ν n γ hb]
    show (Ideal.map f (M.Dideal i₀ γ)) ^ (n i₀) = _
    rw [M.local_Dideal_span γ, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow]
  have hg2span : Ideal.span
      {g2 (((M.secondStage ν n hb).localMulticenter γ).elem i₀)} =
      Ideal.span {g2 (f ((M.localMulticenter γ).elem i₀)) ^ (n i₀)} := by
    calc Ideal.span {g2 (((M.secondStage ν n hb).localMulticenter γ).elem i₀)}
        = Ideal.map g2 (Ideal.span
            {((M.secondStage ν n hb).localMulticenter γ).elem i₀}) := by
          rw [Ideal.map_span, Set.image_singleton]
          rfl
      _ = Ideal.map g2 (Ideal.span
            {f ((M.localMulticenter γ).elem i₀) ^ (n i₀)}) := by rw [hspan2]
      _ = Ideal.span {g2 (f ((M.localMulticenter γ).elem i₀) ^ (n i₀))} := by
          rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.span {g2 (f ((M.localMulticenter γ).elem i₀)) ^ (n i₀)} := by
          rw [map_pow]
  rw [hg2span] at hz2
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hz2
  obtain ⟨u, hu⟩ := M.hom_multipleGen_mem γ ν f
  refine Ideal.mem_span_singleton'.mpr ⟨t * g2 u, ?_⟩
  rw [show ((ν + n) i₀ : ℕ) = ν i₀ + n i₀ from rfl, pow_add]
  rw [← hz, map_mul, ← ht, ← hu, map_mul, map_pow]
  ring

/-- **Two-stage factorization**: a pull-covering piece of the second-stage dilatation
over a chart of `X` factors through the second-stage chart `(A_γ[G_ν])[H_γ]`,
flatly. -/
theorem backward_piece_factor (hb : M.CarsOnY)
    (γβ : (pull_cov X M.Drep (M.secondStage ν n hb).dilatation
      ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)).J) :
    ∃ ψ : CommRingCat.of (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γβ.1)) ⟶
        (pull_loc_cov X M.Drep (M.secondStage ν n hb).dilatation
          ((M.secondStage ν n hb).structureMap ≫
            (M.multiple ν).structureMap) γβ.1).obj γβ.2,
      pull_mor_ring X M.Drep (M.secondStage ν n hb).dilatation
          ((M.secondStage ν n hb).structureMap ≫
            (M.multiple ν).structureMap) γβ =
        CommRingCat.ofHom ((algebraMap ((M.secondStage ν n hb).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((M.secondStage ν n hb).localMulticenter γβ.1))).comp
          (algebraMap ((M.multiple ν).cov.obj γβ.1)
            (Multicenter.Dilatation
              ((M.multiple ν).localMulticenter γβ.1)))) ≫ ψ ∧
      RingHom.Flat ψ.hom := by
  have hsnd : (pull_loc_cov X M.Drep (M.secondStage ν n hb).dilatation
      ((M.secondStage ν n hb).structureMap ≫
        (M.multiple ν).structureMap) γβ.1).map γβ.2 ≫
      pullback.snd ((M.secondStage ν n hb).structureMap ≫
        (M.multiple ν).structureMap) (M.Drep.cov.map γβ.1) =
      Spec.map (pull_mor_ring X M.Drep (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ) :=
    (spec_map_pull_mor_ring _ _ γβ).symm
  have hcwB : (((pull_loc_cov X M.Drep (M.secondStage ν n hb).dilatation
      ((M.secondStage ν n hb).structureMap ≫
        (M.multiple ν).structureMap) γβ.1).map γβ.2 ≫
      pullback.fst ((M.secondStage ν n hb).structureMap ≫
        (M.multiple ν).structureMap) (M.Drep.cov.map γβ.1)) ≫
      (M.secondStage ν n hb).structureMap) ≫ (M.multiple ν).structureMap =
      Spec.map (pull_mor_ring X M.Drep (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ) ≫ M.cov.map γβ.1 := by
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc, hsnd]
    rfl
  obtain ⟨sB, hsB1, hsB2⟩ := (M.multiple ν).exists_chart_factorisation' γβ.1
    _ _ hcwB
  have hcwN : ((pull_loc_cov X M.Drep (M.secondStage ν n hb).dilatation
      ((M.secondStage ν n hb).structureMap ≫
        (M.multiple ν).structureMap) γβ.1).map γβ.2 ≫
      pullback.fst ((M.secondStage ν n hb).structureMap ≫
        (M.multiple ν).structureMap) (M.Drep.cov.map γβ.1)) ≫
      (M.secondStage ν n hb).structureMap =
      Spec.map (Spec.preimage sB) ≫ (M.secondStage ν n hb).cov.map γβ.1 := by
    rw [Spec.map_preimage]
    exact hsB1.symm
  obtain ⟨sN, hsN1, hsN2⟩ := (M.secondStage ν n hb).exists_chart_factorisation'
    γβ.1 _ _ hcwN
  refine ⟨Spec.preimage sN, ?_, ?_⟩
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_comp, Spec.map_comp]
    have hsN2' : sN ≫ (M.secondStage ν n hb).chartHom γβ.1 = sB := by
      rw [hsN2, Spec.map_preimage]
    rw [← hsB2, ← hsN2']
    simp only [Category.assoc]
    rfl
  · haveI hc : IsOpenImmersion ((pull_loc_cov X M.Drep
        (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ.1).map γβ.2 ≫
        pullback.fst ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) (M.Drep.cov.map γβ.1)) :=
      (pull_cov X M.Drep (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap)).map_prop γβ
    haveI hsc : IsOpenImmersion (sN ≫ (M.secondStage ν n hb).chartTo γβ.1) := by
      rw [hsN1]
      exact hc
    haveI hsn : IsOpenImmersion sN :=
      IsOpenImmersion.of_comp sN ((M.secondStage ν n hb).chartTo γβ.1)
    haveI hflat : AlgebraicGeometry.Flat sN := inferInstance
    haveI hflat2 : AlgebraicGeometry.Flat (Spec.map (Spec.preimage sN)) := by
      rw [Spec.map_preimage]
      exact hflat
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Flat)).mp hflat2

set_option maxHeartbeats 4000000 in
/-- Chart form of the backward containment condition. -/
theorem backward_pullSubset_chart (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot)
    (i : M.indnumb)
    (γβ : (pull_cov X M.Drep (M.secondStage ν n hb).dilatation
      ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)).J) :
    Ideal.map (pull_mor_ring X M.Drep (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ).hom (M.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ).hom
        ((M.Dideal i γβ.1) ^ ((ν + n) i)) := by
  rw [Unique.eq_default i]
  obtain ⟨ψ, hψ, -⟩ := M.backward_piece_factor ν n hb γβ
  rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hstep : ∀ (I : Ideal (M.cov.obj γβ.1)),
      Ideal.map ((CommRingCat.Hom.hom ψ).comp
        ((algebraMap ((M.secondStage ν n hb).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((M.secondStage ν n hb).localMulticenter γβ.1))).comp
          (algebraMap ((M.multiple ν).cov.obj γβ.1)
            (Multicenter.Dilatation
              ((M.multiple ν).localMulticenter γβ.1))))) I =
      Ideal.map (CommRingCat.Hom.hom ψ)
        (Ideal.map ((algebraMap ((M.secondStage ν n hb).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((M.secondStage ν n hb).localMulticenter γβ.1))).comp
          (algebraMap ((M.multiple ν).cov.obj γβ.1)
            (Multicenter.Dilatation
              ((M.multiple ν).localMulticenter γβ.1)))) I) :=
    fun I => (Ideal.map_map _ _).symm
  rw [hstep, hstep]
  refine Ideal.map_mono ?_
  refine le_trans (M.secondChart_M_le ν n γβ.1 hb hSt) ?_
  rw [Ideal.map_pow, M.local_Dideal_span γβ.1, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow]
  exact le_rfl

/-- Chart form of the backward Cartier condition. -/
theorem backward_isCars_chart (hb : M.CarsOnY) (i : M.indnumb)
    (γβ : (pull_cov X M.Drep (M.secondStage ν n hb).dilatation
      ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)).J) :
    ∃ g : (pull_loc_cov X M.Drep (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ.1).obj γβ.2,
      (pullback_PreClos X (M.secondStage ν n hb).dilatation
          ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)
          (M.multiple (ν + n)).Drep).ideal i γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov X M.Drep
        (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ.1).obj γβ.2) := by
  rw [Unique.eq_default i]
  obtain ⟨ψ, hψ, hflat⟩ := M.backward_piece_factor ν n hb γβ
  refine ⟨ψ.hom (((algebraMap ((M.secondStage ν n hb).cov.obj γβ.1)
      (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γβ.1))).comp
      (algebraMap ((M.multiple ν).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1))))
      ((M.localMulticenter γβ.1).elem i₀) ^ ((ν + n) i₀)), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ).hom
        ((M.Dideal i₀ γβ.1) ^ ((ν + n) i₀)) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [M.local_Dideal_span γβ.1, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, RingHom.comp_apply, map_pow]
    rfl
  · exact hflat.preserves_nonzeroDivisors (M.secondChart_alpha_nzd ν n γβ.1 hb)

/-- **The backward containment condition** of [Ma24, Lemma 4.4]. -/
theorem backward_pullSubset (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot) :
    (M.multiple (ν + n)).pullSubset
      ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap) :=
  fun i γβ => M.backward_pullSubset_chart ν n hb hSt i γβ

/-- **The backward Cartier condition** of [Ma24, Lemma 4.4]. -/
theorem backward_isCars (hb : M.CarsOnY) :
    IsCars (M.secondStage ν n hb).dilatation
      (Clos.pullback ((M.secondStage ν n hb).structureMap ≫
        (M.multiple ν).structureMap) (M.multiple (ν + n)).D) :=
  ⟨pullback_PreClos X (M.secondStage ν n hb).dilatation
      ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)
      (M.multiple (ν + n)).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun i γβ => M.backward_isCars_chart ν n hb i γβ), rfl⟩

/-- **The backward morphism of [Ma24, Lemma 4.4]**: the second-stage dilatation maps
to `Bl^{(ν+n)D}_Y X` over `X`, uniquely. -/
theorem existsUnique_iterBwd (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot) :
    ∃! g : (M.secondStage ν n hb).dilatation ⟶
        (M.multiple (ν + n)).dilatation,
      g ≫ (M.multiple (ν + n)).structureMap =
        (M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap :=
  (M.multiple (ν + n)).universal_property _
    ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)
    (M.backward_isCars ν n hb) (M.backward_pullSubset ν n hb hSt)

/-- The `ν`-part of `secondChart_alpha_nzd`, standalone. -/
theorem secondChart_alpha_nzd_nu (hb : M.CarsOnY) :
    ((algebraMap ((M.secondStage ν n hb).cov.obj γ)
        (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ))).comp
      (algebraMap ((M.multiple ν).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))))
      ((M.localMulticenter γ).elem i₀) ^ (ν i₀) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γ)) := by
  set g2 : (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) →+*
      (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ)) :=
    (algebraMap ((M.secondStage ν n hb).cov.obj γ)
      (Multicenter.Dilatation ((M.secondStage ν n hb).localMulticenter γ)) :
        _ →+* _) with hg2
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :=
    (algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :
        _ →+* _) with hf
  show (g2.comp f) ((M.localMulticenter γ).elem i₀) ^ (ν i₀) ∈ _
  simp only [RingHom.comp_apply]
  have hgen1 : f (((M.multiple ν).localMulticenter γ).elem i₀) ∈
      nonZeroDivisors (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :=
    nonzerodiv_image_single ((M.multiple ν).localMulticenter γ) i₀
  have hgen1' : g2 (f (((M.multiple ν).localMulticenter γ).elem i₀)) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γ)) :=
    Multicenter.Dilatation.nonzerodiv_of_nonzerodiv
      (F := (M.secondStage ν n hb).localMulticenter γ) hgen1
  obtain ⟨u, hu⟩ := M.hom_multipleGen_mem γ ν f
  have h1 : g2 u * (g2 (f ((M.localMulticenter γ).elem i₀))) ^ (ν i₀) =
      g2 (f (((M.multiple ν).localMulticenter γ).elem i₀)) := by
    rw [← map_pow, ← map_mul, hu]
  have h2 : g2 u * (g2 (f ((M.localMulticenter γ).elem i₀))) ^ (ν i₀) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γ)) := by
    rw [h1]; exact hgen1'
  exact (mul_mem_nonZeroDivisors.mp h2).2

/-- Chart form of the `ν`-level Cartier condition on the second-stage dilatation. -/
theorem backward_isCars_nu_chart (hb : M.CarsOnY) (i : M.indnumb)
    (γβ : (pull_cov X M.Drep (M.secondStage ν n hb).dilatation
      ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)).J) :
    ∃ g : (pull_loc_cov X M.Drep (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ.1).obj γβ.2,
      (pullback_PreClos X (M.secondStage ν n hb).dilatation
          ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)
          (M.multiple ν).Drep).ideal i γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov X M.Drep
        (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ.1).obj γβ.2) := by
  rw [Unique.eq_default i]
  obtain ⟨ψ, hψ, hflat⟩ := M.backward_piece_factor ν n hb γβ
  refine ⟨ψ.hom (((algebraMap ((M.secondStage ν n hb).cov.obj γβ.1)
      (Multicenter.Dilatation
        ((M.secondStage ν n hb).localMulticenter γβ.1))).comp
      (algebraMap ((M.multiple ν).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1))))
      ((M.localMulticenter γβ.1).elem i₀) ^ (ν i₀)), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep (M.secondStage ν n hb).dilatation
        ((M.secondStage ν n hb).structureMap ≫
          (M.multiple ν).structureMap) γβ).hom
        ((M.Dideal i₀ γβ.1) ^ (ν i₀)) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [M.local_Dideal_span γβ.1, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, RingHom.comp_apply, map_pow]
    rfl
  · exact hflat.preserves_nonzeroDivisors (M.secondChart_alpha_nzd_nu ν n γβ.1 hb)

/-- The `ν`-level Cartier condition on the second-stage dilatation. -/
theorem backward_isCars_nu (hb : M.CarsOnY) :
    IsCars (M.secondStage ν n hb).dilatation
      (Clos.pullback ((M.secondStage ν n hb).structureMap ≫
        (M.multiple ν).structureMap) (M.multiple ν).D) :=
  ⟨pullback_PreClos X (M.secondStage ν n hb).dilatation
      ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)
      (M.multiple ν).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun i γβ => M.backward_isCars_nu_chart ν n hb i γβ), rfl⟩

section MainIso

variable (hb : M.CarsOnY) (hSt : M.ElemNzdOnQuot)

/-- The forward morphism. -/
noncomputable def iterFwd :
    (M.multiple (ν + n)).dilatation ⟶ (M.secondStage ν n hb).dilatation :=
  (M.existsUnique_iterFwd ν n hb hSt).choose

@[simp] theorem iterFwd_over :
    M.iterFwd ν n hb hSt ≫ (M.secondStage ν n hb).structureMap =
      M.multipleHom (ν + n) ν (M.nu_le_add ν n) :=
  (M.existsUnique_iterFwd ν n hb hSt).choose_spec.1

/-- The backward morphism. -/
noncomputable def iterBwd :
    (M.secondStage ν n hb).dilatation ⟶ (M.multiple (ν + n)).dilatation :=
  (M.existsUnique_iterBwd ν n hb hSt).choose

@[simp] theorem iterBwd_over :
    M.iterBwd ν n hb hSt ≫ (M.multiple (ν + n)).structureMap =
      (M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap :=
  (M.existsUnique_iterBwd ν n hb hSt).choose_spec.1

theorem iterFwd_comp_iterBwd :
    M.iterFwd ν n hb hSt ≫ M.iterBwd ν n hb hSt = 𝟙 _ := by
  have e₁ : (M.iterFwd ν n hb hSt ≫ M.iterBwd ν n hb hSt) ≫
      (M.multiple (ν + n)).structureMap =
      (M.multiple (ν + n)).structureMap := by
    rw [Category.assoc, M.iterBwd_over ν n hb hSt, ← Category.assoc,
      M.iterFwd_over ν n hb hSt, M.multipleHom_over (ν + n) ν (M.nu_le_add ν n)]
  exact ((M.multiple (ν + n)).universal_property
    (M.multiple (ν + n)).dilatation (M.multiple (ν + n)).structureMap
    (M.multiple (ν + n)).structureMap_isCars
    (M.multiple (ν + n)).structureMap_pullSubset).unique e₁ (Category.id_comp _)

/-- The backward morphism lies over `Bl^{νD}`. -/
theorem iterBwd_over_base :
    M.iterBwd ν n hb hSt ≫ M.multipleHom (ν + n) ν (M.nu_le_add ν n) =
      (M.secondStage ν n hb).structureMap := by
  have e₁ : (M.iterBwd ν n hb hSt ≫
      M.multipleHom (ν + n) ν (M.nu_le_add ν n)) ≫
      (M.multiple ν).structureMap =
      (M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap := by
    rw [Category.assoc, M.multipleHom_over (ν + n) ν (M.nu_le_add ν n),
      M.iterBwd_over ν n hb hSt]
  exact ((M.multiple ν).universal_property (M.secondStage ν n hb).dilatation
    ((M.secondStage ν n hb).structureMap ≫ (M.multiple ν).structureMap)
    (M.backward_isCars_nu ν n hb)
    (M.pullSubset_of_over_dilatation ν
      ((M.secondStage ν n hb).structureMap))).unique e₁ rfl

theorem iterBwd_comp_iterFwd :
    M.iterBwd ν n hb hSt ≫ M.iterFwd ν n hb hSt = 𝟙 _ := by
  have e₁ : (M.iterBwd ν n hb hSt ≫ M.iterFwd ν n hb hSt) ≫
      (M.secondStage ν n hb).structureMap =
      (M.secondStage ν n hb).structureMap := by
    rw [Category.assoc, M.iterFwd_over ν n hb hSt, M.iterBwd_over_base ν n hb hSt]
  exact ((M.secondStage ν n hb).universal_property
    (M.secondStage ν n hb).dilatation (M.secondStage ν n hb).structureMap
    (M.secondStage ν n hb).structureMap_isCars
    (M.secondStage ν n hb).structureMap_pullSubset).unique e₁
    (Category.id_comp _)

/-- **[Ma24, Lemma 4.4], scheme level**: the canonical isomorphism
`Bl^{(ν+n)D}_Y X ≅ Bl^{n·θ*D}_{ℓ(Y)} (Bl^{νD}_Y X)` — dilating along the `(ν+n)`-th
multiple is dilating the `ν`-th dilatation along the lifted center and the `n`-th
multiple of the total transform. -/
noncomputable def iterateSchemeIso :
    (M.multiple (ν + n)).dilatation ≅ (M.secondStage ν n hb).dilatation where
  hom := M.iterFwd ν n hb hSt
  inv := M.iterBwd ν n hb hSt
  hom_inv_id := M.iterFwd_comp_iterBwd ν n hb hSt
  inv_hom_id := M.iterBwd_comp_iterFwd ν n hb hSt

@[simp] theorem iterateSchemeIso_hom_over :
    (M.iterateSchemeIso ν n hb hSt).hom ≫
      (M.secondStage ν n hb).structureMap =
      M.multipleHom (ν + n) ν (M.nu_le_add ν n) :=
  M.iterFwd_over ν n hb hSt

/-- The isomorphism of Lemma 4.4 is the unique morphism over `Bl^{νD}`. -/
theorem iterateSchemeIso_unique
    (g : (M.multiple (ν + n)).dilatation ⟶ (M.secondStage ν n hb).dilatation)
    (hg : g ≫ (M.secondStage ν n hb).structureMap =
      M.multipleHom (ν + n) ν (M.nu_le_add ν n)) :
    g = (M.iterateSchemeIso ν n hb hSt).hom :=
  ((M.existsUnique_iterFwd ν n hb hSt).unique hg
    (M.iterFwd_over ν n hb hSt)).trans rfl

end MainIso

end BackwardRing

end PreMultiCenter

end SchemeDilatation
