import UniversalProperty
import GlobalDilProperties
import Project.Blowups.UniqueBlowup
import Project.Blowups.BlowupExists
import PreClosReindex

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SchemeDilatation

variable {X : Scheme.{u+1}}

instance preDilatationOver (M : PreMultiCenter X) : (M.dilatation).Over X :=
  ⟨M.structureMap⟩

@[simp] theorem preDilatationOver_hom (M : PreMultiCenter X) :
    (M.dilatation ↘ X) = M.structureMap := rfl

theorem dilatation_mem_cars (M : PreMultiCenter X) :
    pullback_Clos (M.dilatation ↘ X) M.D ∈ CarsAsSubsetOfClos M.dilatation := by
  simpa using M.structureMap_isCars

instance blowupOver {Z : Clos X} (B : conceptual_blowup (X := X) Z) :
    B.scheme.Over X := B.over

def toBlowup (M : PreMultiCenter X)
    (B : conceptual_blowup (X := X) M.D) :
    M.dilatation ⟶ B.scheme :=
  B.φ M.dilatation (dilatation_mem_cars M)

theorem toBlowup_over (M : PreMultiCenter X) (B : conceptual_blowup (X := X) M.D) :
    Scheme.Hom.IsOver (toBlowup M B) X :=
  B.φ_over M.dilatation (dilatation_mem_cars M)

theorem toBlowup_unique (M : PreMultiCenter X) (B : conceptual_blowup (X := X) M.D)
    (g : M.dilatation ⟶ B.scheme) (hg : Scheme.Hom.IsOver g X) :
    g = toBlowup M B :=
  B.φ_uniq M.dilatation (dilatation_mem_cars M) g hg

theorem toBlowup_subsingleton (M : PreMultiCenter X)
    (B : conceptual_blowup (X := X) M.D)
    (g g' : M.dilatation ⟶ B.scheme)
    (hg : Scheme.Hom.IsOver g X) (hg' : Scheme.Hom.IsOver g' X) : g = g' := by
  rw [toBlowup_unique M B g hg, toBlowup_unique M B g' hg']

namespace Mono

def toBlowup (M : PreMultiCenter X) [Unique M.indnumb]
    (B : conceptual_blowup (X := X) M.D) : M.dilatation ⟶ B.scheme :=
  SchemeDilatation.toBlowup M B

theorem toBlowup_over (M : PreMultiCenter X) [Unique M.indnumb]
    (B : conceptual_blowup (X := X) M.D) :
    Scheme.Hom.IsOver (toBlowup M B) X :=
  SchemeDilatation.toBlowup_over M B

theorem toBlowup_unique (M : PreMultiCenter X) [Unique M.indnumb]
    (B : conceptual_blowup (X := X) M.D)
    (g : M.dilatation ⟶ B.scheme) (hg : Scheme.Hom.IsOver g X) :
    g = toBlowup M B :=
  SchemeDilatation.toBlowup_unique M B g hg

end Mono

section ProjBlowup

variable (M : PreMultiCenter X) [Fintype M.indnumb]

noncomputable def projConceptualBlowup : conceptual_blowup (X := X) M.D := by
  letI : DecidableEq M.Drep.indnumb := Classical.decEq _
  letI : Fintype M.Drep.indnumb := inferInstanceAs (Fintype M.indnumb)
  letI : (i : M.Drep.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt M.Drep.indnumb)) :=
    fun _ => Classical.dec _
  exact
  { scheme := BlGlob M.Drep
    over := inferInstance
    in_cars := BlGlob_IsCars M.Drep
    φ := fun T _ cond => (PreProjBlowup_UnivProp_existence_Cars M.Drep cond).choose
    φ_over := fun T _ cond => (PreProjBlowup_UnivProp_existence_Cars M.Drep cond).choose_spec
    φ_uniq := fun T _ cond φ' hφ' =>
      PreProjBlowup_UnivProp_unicity_Cars M.Drep cond φ'
        (PreProjBlowup_UnivProp_existence_Cars M.Drep cond).choose hφ'
        (PreProjBlowup_UnivProp_existence_Cars M.Drep cond).choose_spec }

noncomputable def toProjBlowup : M.dilatation ⟶ (projConceptualBlowup M).scheme :=
  toBlowup M (projConceptualBlowup M)

theorem toProjBlowup_over : Scheme.Hom.IsOver (toProjBlowup M) X :=
  toBlowup_over M (projConceptualBlowup M)

theorem toProjBlowup_unique (g : M.dilatation ⟶ (projConceptualBlowup M).scheme)
    (hg : Scheme.Hom.IsOver g X) : g = toProjBlowup M :=
  toBlowup_unique M (projConceptualBlowup M) g hg

noncomputable def Mono.toProjBlowup [Unique M.indnumb] :
    M.dilatation ⟶ (projConceptualBlowup M).scheme :=
  SchemeDilatation.toProjBlowup M

theorem Mono.toProjBlowup_over [Unique M.indnumb] :
    Scheme.Hom.IsOver (Mono.toProjBlowup M) X :=
  SchemeDilatation.toProjBlowup_over M

end ProjBlowup

section CenterBlowup

variable (M : PreMultiCenter X)

noncomputable abbrev interRep : PreClos X :=
  M.Yrep.inter M.Drep (Equiv.refl M.indnumb)

instance interRep_fintype [Fintype M.indnumb] : Fintype (interRep M).indnumb :=
  inferInstanceAs (Fintype M.indnumb)

noncomputable instance interRep_decEq : DecidableEq (interRep M).indnumb :=
  Classical.decEq _

noncomputable instance interRep_decRange :
    (i : (interRep M).indnumb →₀ ℤ) →
      Decidable (i ∈ Set.range (ρNatToInt (interRep M).indnumb)) :=
  fun _ => Classical.dec _

noncomputable instance interRepChartAlgebra {M : PreMultiCenter X} {γ : M.cov.J} :
    Algebra ((interRep M).cov.obj γ)
      (Multicenter.Dilatation (M.localMulticenter γ)) :=
  inferInstanceAs (Algebra (M.cov.obj γ) _)

noncomputable instance blMuChartOver {M : PreMultiCenter X} [Fintype M.indnumb]
    {γ : M.cov.J} :
    Scheme.Over (BlMu (ideal_loc X (interRep M) γ)) (Spec (M.cov.obj γ)) :=
  BlMuOverSpec (ideal_loc X (interRep M) γ)

theorem dilatation_inter_isCars_chart (i : M.indnumb)
    (γβ : (pull_cov X (interRep M) M.dilatation M.structureMap).J) :
    ∃ g : (pull_loc_cov X (interRep M) M.dilatation M.structureMap γβ.1).obj γβ.2,
      (pullback_PreClos X M.dilatation M.structureMap (interRep M)).ideal i γβ =
        Ideal.span {g} ∧
      g ∈ nonZeroDivisors
        ((pull_loc_cov X (interRep M) M.dilatation M.structureMap γβ.1).obj γβ.2) := by
  obtain ⟨g, hg, hnzd⟩ := M.structureMap_isCars_chart i γβ
  refine ⟨g, ?_, hnzd⟩
  show Ideal.map (pull_mor_ring X (interRep M) M.dilatation M.structureMap γβ).hom
      ((interRep M).ideal i γβ.1) = Ideal.span {g}
  have h := M.structureMap_pull_inter_ideal_eq_D i γβ
  rw [show ((interRep M).ideal i γβ.1) =
      (M.Yrep.interIdeal M.Drep (Equiv.refl M.indnumb) i γβ.1) from rfl]
  rw [show (pull_mor_ring X (interRep M) M.dilatation M.structureMap γβ) =
      (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ) from rfl]
  rw [h]
  exact hg

theorem dilatation_inter_isPreCars :
    IsPreCars _ (pullback_PreClos X M.dilatation M.structureMap (interRep M)) :=
  pullback_IsPreCars_of_charts M.dilatation M.structureMap (interRep M)
    (dilatation_inter_isCars_chart M)

theorem dilatation_inter_isCars :
    IsCars M.dilatation
      (pullback_Clos (M.dilatation ↘ X) (Quotient.mk'' (interRep M))) :=
  ⟨_, dilatation_inter_isPreCars M, rfl⟩

theorem exceptional_inter_ideal_eq (i : M.indnumb)
    (γβ : (pullback_PreClos X M.dilatation M.structureMap (interRep M)).cov.J) :
    (pullback_PreClos X M.dilatation M.structureMap (interRep M)).ideal i γβ =
      (pullback_PreClos X M.dilatation M.structureMap M.Drep).reindexIdeal
        (pullback_PreClos X M.dilatation M.structureMap (interRep M)).cov i γβ :=
  (M.structureMap_pull_inter_ideal_eq_D i γβ).trans
    (PreClos.reindexIdeal_self
      (pullback_PreClos X M.dilatation M.structureMap M.Drep) i γβ).symm

theorem exceptional_inter_pullback_eq :
    Clos.pullback M.structureMap (Quotient.mk'' (interRep M)) =
      Clos.pullback M.structureMap M.D := by
  rw [← M.Drep_eq, Clos.pullback_mk, Clos.pullback_mk]
  exact PreClos.clos_eq_of_ideal_eq _ _ (Equiv.refl _)
    (exceptional_inter_ideal_eq M)

theorem exceptional_inter_ideal_prod_eq (S : Finset M.indnumb) (ν : M.indnumb → ℕ)
    (γβ : (pull_cov X M.Drep M.dilatation M.structureMap).J) :
    Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
        (∏ i ∈ S, M.Yrep.interIdeal M.Drep (Equiv.refl M.indnumb) i γβ.1 ^ ν i) =
      Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
        (∏ i ∈ S, M.Drep.ideal i γβ.1 ^ ν i) := by
  change Ideal.mapHom _ _ = Ideal.mapHom _ _
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, map_pow]
  exact congrArg (· ^ ν i) (M.structureMap_pull_inter_ideal_eq_D i γβ)

noncomputable def exceptionalInterRel :
    relStructure (pullback_PreClos X M.dilatation M.structureMap (interRep M))
      (pullback_PreClos X M.dilatation M.structureMap M.Drep) :=
  PreClos.relStructure_of_ideal_eq _ _ (Equiv.refl _)
    (exceptional_inter_ideal_eq M)

noncomputable def exceptionalInterIso (i : M.indnumb) :
    pullback (M.Yrep.interSub M.Drep (Equiv.refl M.indnumb) i ↘ X)
        M.structureMap ≅
      pullback (M.Dsub i ↘ X) M.structureMap :=
  (exceptionalInterRel M).subscheme_iso i

theorem exceptionalInterIso_over (i : M.indnumb) :
    Scheme.Hom.IsOver (exceptionalInterIso M i).hom M.dilatation :=
  (exceptionalInterRel M).subscheme_iso_over i

def centerSubDivisor : Prop :=
  PreClos.subset M.Yrep M.Drep (Equiv.refl M.indnumb) M.cov rfl rfl

theorem exceptional_ideal_eq (hZD : centerSubDivisor M) (i : M.indnumb)
    (γβ : (pullback_PreClos X M.dilatation M.structureMap M.Yrep).cov.J) :
    (pullback_PreClos X M.dilatation M.structureMap M.Yrep).ideal i γβ =
      (pullback_PreClos X M.dilatation M.structureMap M.Drep).reindexIdeal
        (pullback_PreClos X M.dilatation M.structureMap M.Yrep).cov i γβ := by
  refine Eq.trans (le_antisymm (M.structureMap_pullSubset i γβ) ?_)
    (PreClos.reindexIdeal_self
      (pullback_PreClos X M.dilatation M.structureMap M.Drep) i γβ).symm
  exact Ideal.map_mono (hZD i γβ.1)

theorem exceptional_pullback_eq (hZD : centerSubDivisor M) :
    Clos.pullback M.structureMap M.Y = Clos.pullback M.structureMap M.D := by
  rw [← M.Yrep_eq, ← M.Drep_eq, Clos.pullback_mk, Clos.pullback_mk]
  exact PreClos.clos_eq_of_ideal_eq _ _ (Equiv.refl _) (exceptional_ideal_eq M hZD)

noncomputable def exceptionalRel (hZD : centerSubDivisor M) :
    relStructure (pullback_PreClos X M.dilatation M.structureMap M.Yrep)
      (pullback_PreClos X M.dilatation M.structureMap M.Drep) :=
  PreClos.relStructure_of_ideal_eq _ _ (Equiv.refl _) (exceptional_ideal_eq M hZD)

noncomputable def exceptionalIso (hZD : centerSubDivisor M)
    (i : M.indnumb) :
    pullback (M.Ysub i ↘ X) M.structureMap ≅
      pullback (M.Dsub i ↘ X) M.structureMap :=
  (exceptionalRel M hZD).subscheme_iso i

theorem exceptionalIso_over (hZD : centerSubDivisor M) (i : M.indnumb) :
    Scheme.Hom.IsOver (exceptionalIso M hZD i).hom M.dilatation :=
  (exceptionalRel M hZD).subscheme_iso_over i

variable [Fintype M.indnumb]

noncomputable def centerBlowup :
    conceptual_blowup (X := X) (Quotient.mk'' (interRep M)) :=
  { scheme := BlGlob (interRep M)
    over := inferInstance
    in_cars := BlGlob_IsCars (interRep M)
    φ := fun T _ cond => (PreProjBlowup_UnivProp_existence_Cars (interRep M) cond).choose
    φ_over := fun T _ cond =>
      (PreProjBlowup_UnivProp_existence_Cars (interRep M) cond).choose_spec
    φ_uniq := fun T _ cond φ' hφ' =>
      PreProjBlowup_UnivProp_unicity_Cars (interRep M) cond φ'
        (PreProjBlowup_UnivProp_existence_Cars (interRep M) cond).choose hφ'
        (PreProjBlowup_UnivProp_existence_Cars (interRep M) cond).choose_spec }

noncomputable def toCenterBlowup : M.dilatation ⟶ (centerBlowup M).scheme :=
  (centerBlowup M).φ M.dilatation (dilatation_inter_isCars M)

theorem toCenterBlowup_over : Scheme.Hom.IsOver (toCenterBlowup M) X :=
  (centerBlowup M).φ_over M.dilatation (dilatation_inter_isCars M)

theorem toCenterBlowup_unique (g : M.dilatation ⟶ (centerBlowup M).scheme)
    (hg : Scheme.Hom.IsOver g X) : g = toCenterBlowup M :=
  (centerBlowup M).φ_uniq M.dilatation (dilatation_inter_isCars M) g hg

end CenterBlowup

section AffineStep

variable (M : PreMultiCenter X) [Fintype M.indnumb] (γ : M.cov.J)

theorem localMulticenter_largeIdeal_eq (i : M.indnumb) :
    (M.localMulticenter γ).LargeIdeal i = (interRep M).ideal i γ := by
  show M.Yideal i γ + Ideal.span {(M.Dprin i γ).generator} = _
  letI : (M.Dideal i γ).IsPrincipal := M.Dprin i γ
  rw [Ideal.span_singleton_generator]
  rw [show (interRep M).ideal i γ =
      M.Yrep.interIdeal M.Drep (Equiv.refl M.indnumb) i γ from rfl]
  rw [M.Yrep.interIdeal_eq M.Drep (Equiv.refl M.indnumb) i γ]
  show M.Yideal i γ + M.Dideal i γ =
    M.Yideal i γ ⊔ M.Drep.reindexIdeal M.Drep.cov i γ
  rw [PreClos.reindexIdeal_self M.Drep i γ, Submodule.add_eq_sup]
  rfl

noncomputable def chartMu : Mu (ideal_loc X (interRep M) γ) where
  multicenter := M.localMulticenter γ
  fin := inferInstanceAs (Fintype M.indnumb)
  Ψ := id
  sec := id
  surj _ := rfl
  cond i := localMulticenter_largeIdeal_eq M γ i

noncomputable abbrev chartPotionEquiv :=
  (Mu_mor_iso (ideal_loc X (interRep M) γ) (chartMu M γ)).toRingEquiv

noncomputable def chartPotionIso :
    M.chart γ ≅
      Spec (CommRingCat.of
        ((map_index (ideal_loc X (interRep M) γ) (chartMu M γ)).Potion)) where
  hom := Spec.map (CommRingCat.ofHom (chartPotionEquiv M γ).symm.toRingHom)
  inv := Spec.map (CommRingCat.ofHom (chartPotionEquiv M γ).toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (chartPotionEquiv M γ).symm.toRingHom.comp
          (chartPotionEquiv M γ).toRingHom = RingHom.id _ from
        RingHom.ext fun a => (chartPotionEquiv M γ).symm_apply_apply a]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (chartPotionEquiv M γ).toRingHom.comp
          (chartPotionEquiv M γ).symm.toRingHom = RingHom.id _ from
        RingHom.ext fun a => (chartPotionEquiv M γ).apply_symm_apply a]
    exact Spec.map_id _

noncomputable def chartToProjLoc : M.chart γ ⟶ Proj_loc X (interRep M) γ :=
  (chartPotionIso M γ).hom ≫
    (GoodPotionIngredient.glueData
      (map_index (ideal_loc X (interRep M) γ))).ι (chartMu M γ)

instance chartToProjLoc_isOpenImmersion : IsOpenImmersion (chartToProjLoc M γ) := by
  unfold chartToProjLoc
  infer_instance

theorem chartToProjLoc_over :
    chartToProjLoc M γ ≫
        ((Proj_loc X (interRep M) γ) ↘ Spec ((interRep M).cov.obj γ)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (M.cov.obj γ)
          (Multicenter.Dilatation (M.localMulticenter γ)))) := by
  show (chartPotionIso M γ).hom ≫
      (GoodPotionIngredient.glueData
        (map_index (ideal_loc X (interRep M) γ))).ι (chartMu M γ) ≫
      ((BlMu (ideal_loc X (interRep M) γ)) ↘ Spec ((interRep M).cov.obj γ)) = _
  rw [BlMu_ι_over]
  show Spec.map (CommRingCat.ofHom (chartPotionEquiv M γ).symm.toRingHom) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  exact AlgEquiv.commutes
    ((Mu_mor_iso (ideal_loc X (interRep M) γ) (chartMu M γ)).symm) a

end AffineStep

section GlobalStep

variable (M : PreMultiCenter X) [Fintype M.indnumb] (γ : M.cov.J)

theorem chart_isCars :
    IsCars (Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ))))
      (pullback_Clos
        (Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ))) ↘
          Spec ((interRep M).cov.obj γ))
        (loc_to_Clos ((interRep M).cov.obj γ) (ideal_loc X (interRep M) γ))) := by
  refine loc_isCars_of_principal ((interRep M).cov.obj γ)
    (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ)))
    (ideal_loc X (interRep M) γ)
    (g := fun i : (interRep M).indnumb =>
      algebraMap _ (Multicenter.Dilatation (M.localMulticenter γ))
        ((M.localMulticenter γ).elem i)) (fun i => ?_) (fun i => ?_)
  · rw [show ideal_loc X (interRep M) γ i = (interRep M).ideal i γ from rfl,
      ← localMulticenter_largeIdeal_eq M γ i]
    have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal
      (F := M.localMulticenter γ) (Finsupp.single i 1)
    rw [familyPow_single, familyPow_single] at h
    exact h.symm
  · have h := Multicenter.Dilatation.nonzerodiv_image
      (F := M.localMulticenter γ) (Finsupp.single i 1)
    rwa [familyPow_single] at h

theorem eq_chartToProjLoc
    (ψ : Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ))) ⟶
      Proj_loc X (interRep M) γ)
    (hψ : ψ ≫ ((Proj_loc X (interRep M) γ) ↘ Spec ((interRep M).cov.obj γ)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (M.cov.obj γ)
          (Multicenter.Dilatation (M.localMulticenter γ))))) :
    ψ = chartToProjLoc M γ :=
  @ProjBlowup_UnivProp_unicity_affine ((interRep M).indnumb)
    (interRep_decEq M) (interRep_decRange M) ((interRep M).cov.obj γ)
    (ideal_loc X (interRep M) γ) (interRep_fintype M) _ _
    (chart_isCars M γ) ψ (chartToProjLoc M γ)
    ⟨hψ⟩ ⟨chartToProjLoc_over M γ⟩

theorem toCenterBlowup_comp_over :
    toCenterBlowup M ≫ ((centerBlowup M).scheme ↘ X) = M.structureMap :=
  (toCenterBlowup_over M).comp_over

noncomputable def chartRestrictIso :
    pullback (toCenterBlowup M)
        (pullback.fst ((centerBlowup M).scheme ↘ X) ((interRep M).cov.map γ)) ≅
      M.chart γ :=
  pullbackRightPullbackFstIso ((centerBlowup M).scheme ↘ X)
      ((interRep M).cov.map γ) (toCenterBlowup M) ≪≫
    pullback.congrHom (toCenterBlowup_comp_over M) rfl ≪≫
    (asIso (M.chartCompare γ)).symm

theorem chartRestrict_eq :
    pullback.snd (toCenterBlowup M)
        (pullback.fst ((centerBlowup M).scheme ↘ X) ((interRep M).cov.map γ)) =
      (chartRestrictIso M γ).hom ≫ chartToProjLoc M γ ≫
        (Proj_loc_pullback_over (interRep M) γ).hom := by
  set e₂ := Proj_loc_pullback_over (interRep M) γ with he₂
  set ψ := (chartRestrictIso M γ).inv ≫
    pullback.snd (toCenterBlowup M) (pullback.fst ((centerBlowup M).scheme ↘ X) ((interRep M).cov.map γ)) ≫
      e₂.inv with hψ
  have hover : ψ ≫ ((Proj_loc X (interRep M) γ) ↘ Spec ((interRep M).cov.obj γ)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (M.cov.obj γ)
          (Multicenter.Dilatation (M.localMulticenter γ)))) := by
    have h1 : e₂.inv ≫ ((Proj_loc X (interRep M) γ) ↘ Spec ((interRep M).cov.obj γ)) =
        pullback.snd ((centerBlowup M).scheme ↘ X) ((interRep M).cov.map γ) := by
      rw [he₂, ← Proj_loc_pullback_over_hom_snd (interRep M) γ, Iso.inv_hom_id_assoc]
      rfl
    rw [hψ, Category.assoc, Category.assoc, h1, chartRestrictIso]
    simp only [Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc]
    rw [← pullbackRightPullbackFstIso_hom_snd, Iso.inv_hom_id_assoc]
    simp only [pullback.congrHom_inv, pullback.lift_snd, Category.comp_id]
    exact M.chartCompare_snd γ
  have heq := eq_chartToProjLoc M γ ψ hover
  rw [hψ] at heq
  calc pullback.snd (toCenterBlowup M) (pullback.fst ((centerBlowup M).scheme ↘ X) ((interRep M).cov.map γ))
      = (chartRestrictIso M γ).hom ≫ ((chartRestrictIso M γ).inv ≫
          pullback.snd (toCenterBlowup M)
            (pullback.fst ((centerBlowup M).scheme ↘ X) ((interRep M).cov.map γ)) ≫ e₂.inv) ≫ e₂.hom := by
        simp
    _ = (chartRestrictIso M γ).hom ≫ chartToProjLoc M γ ≫ e₂.hom := by
        rw [heq]

instance toCenterBlowup_isOpenImmersion : IsOpenImmersion (toCenterBlowup M) := by
  rw [IsLocalAtTarget.iff_of_openCover (P := @IsOpenImmersion)
    ((interRep M).cov.cover.pullbackCover ((centerBlowup M).scheme ↘ X))]
  intro γ
  show IsOpenImmersion (pullback.snd (toCenterBlowup M)
    (pullback.fst ((centerBlowup M).scheme ↘ X) ((interRep M).cov.map γ)))
  rw [chartRestrict_eq M γ]
  infer_instance

namespace Mono

variable [Unique M.indnumb]

noncomputable def toCenterBlowup :
    M.dilatation ⟶ (centerBlowup M).scheme :=
  SchemeDilatation.toCenterBlowup M

theorem toCenterBlowup_over : Scheme.Hom.IsOver (toCenterBlowup M) X :=
  SchemeDilatation.toCenterBlowup_over M

instance toCenterBlowup_isOpenImmersion :
    IsOpenImmersion (toCenterBlowup M) :=
  SchemeDilatation.toCenterBlowup_isOpenImmersion M

end Mono

end GlobalStep

end SchemeDilatation
