import UniversalProperty
import ClosInterSch

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

variable {X : Scheme.{u+1}}

namespace SchemeDilatation

namespace PreMultiCenter

variable (M : PreMultiCenter X)

theorem chart_pull_mor_ring (γβ : (pull_cov X M.Drep M.dilatation M.structureMap).J) :
    pull_mor_ring X M.Drep M.dilatation M.structureMap γβ =
      CommRingCat.ofHom (algebraMap (M.cov.obj γβ.1)
        (Multicenter.Dilatation (M.localMulticenter γβ.1))) ≫
      Spec.preimage
        ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).map γβ.2 ≫
          inv (M.chartCompare γβ.1)) := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage, Spec_pull_mor_ring, Category.assoc]
  show _ = (pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).map γβ.2 ≫
    inv (M.chartCompare γβ.1) ≫ M.chartHom γβ.1
  rw [← M.chartCompare_snd γβ.1, IsIso.inv_hom_id_assoc]
  rfl

instance chart_open_immersion (γβ : (pull_cov X M.Drep M.dilatation M.structureMap).J) :
    IsOpenImmersion
      ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).map γβ.2 ≫
        inv (M.chartCompare γβ.1)) :=
  inferInstance

theorem structureMap_pullSubset : M.pullSubset M.structureMap := by
  intro i γβ
  letI := M.Dprin i γβ.1
  letI : Submodule.IsPrincipal (M.Drep.ideal i γβ.1) := M.Dprin i γβ.1
  have hinner : Ideal.map (algebraMap (M.cov.obj γβ.1)
      (Multicenter.Dilatation (M.localMulticenter γβ.1))) (M.Yideal i γβ.1) ≤
      Ideal.map (algebraMap (M.cov.obj γβ.1)
        (Multicenter.Dilatation (M.localMulticenter γβ.1))) (M.Drep.ideal i γβ.1) := by
    have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal
      (F := M.localMulticenter γβ.1) (Finsupp.single i 1)
    rw [familyPow_single, familyPow_single] at h
    have hle : M.Yideal i γβ.1 ≤ (M.localMulticenter γβ.1).LargeIdeal i := by
      show (M.localMulticenter γβ.1).ideal i ≤ _
      unfold Multicenter.LargeIdeal
      rw [Submodule.add_eq_sup]
      exact le_sup_left
    refine le_trans (Ideal.map_mono hle) ?_
    rw [← h, ← Ideal.span_singleton_generator (M.Drep.ideal i γβ.1), Ideal.map_span,
      Set.image_singleton]
    exact le_rfl
  show Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
      (M.Yideal i γβ.1) ≤
    Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
      (M.Drep.ideal i γβ.1)
  rw [M.chart_pull_mor_ring γβ, CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.map_map]
  exact Ideal.map_mono hinner

theorem structureMap_isCars_chart (i : M.indnumb)
    (γβ : (pull_cov X M.Drep M.dilatation M.structureMap).J) :
    ∃ g : (pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2,
      (pullback_PreClos X M.dilatation M.structureMap M.Drep).ideal i γβ =
        Ideal.span {g} ∧
      g ∈ nonZeroDivisors
        ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) := by
  classical
  letI := M.Dprin i γβ.1
  letI : Submodule.IsPrincipal (M.Drep.ideal i γβ.1) := M.Dprin i γβ.1
  set mr := Spec.preimage
    ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).map γβ.2 ≫
      inv (M.chartCompare γβ.1)) with hmr
  have hmr_eq : Spec.map mr =
      (pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).map γβ.2 ≫
        inv (M.chartCompare γβ.1) := Spec.map_preimage _
  letI : Algebra (Multicenter.Dilatation (M.localMulticenter γβ.1))
      ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) :=
    mr.hom.toAlgebra
  haveI : IsOpenImmersion
      (Spec ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) ↘
        Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γβ.1)))) := by
    show IsOpenImmersion (Spec.map (CommRingCat.ofHom mr.hom))
    rw [CommRingCat.ofHom_hom, hmr_eq]
    infer_instance
  have hflat : RingHom.Flat (algebraMap (Multicenter.Dilatation (M.localMulticenter γβ.1))
      ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2)) :=
    open_flat_ring _ _
  refine ⟨(pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
    ((M.localMulticenter γβ.1).elem i), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
      (M.Drep.ideal i γβ.1) = _
    rw [← Ideal.span_singleton_generator (M.Drep.ideal i γβ.1), Ideal.map_span,
      Set.image_singleton]
    rfl
  · rw [chart_pull_mor_ring]
    show mr.hom ((algebraMap (M.cov.obj γβ.1)
      (Multicenter.Dilatation (M.localMulticenter γβ.1)))
      ((M.localMulticenter γβ.1).elem i)) ∈ _
    refine hflat.preserves_nonzeroDivisors ?_
    have h := Multicenter.Dilatation.nonzerodiv_image
      (F := M.localMulticenter γβ.1) (Finsupp.single i 1)
    rwa [familyPow_single] at h

theorem structureMap_isCars :
    IsCars M.dilatation (Clos.pullback M.structureMap M.D) :=
  ⟨pullback_PreClos X M.dilatation M.structureMap M.Drep,
    pullback_IsPreCars_of_charts M.dilatation M.structureMap M.Drep
      M.structureMap_isCars_chart, rfl⟩

set_option maxHeartbeats 1000000 in
theorem structureMap_pull_inter_ideal_eq_D (i : M.indnumb)
    (γβ : (pull_cov X M.Drep M.dilatation M.structureMap).J) :
    Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
        (M.Yrep.interIdeal M.Drep (Equiv.refl M.indnumb) i γβ.1) =
      Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
        (M.Drep.ideal i γβ.1) := by
  have hself : ∀ (Z : PreClos X) (j : Z.indnumb) (γ : Z.cov.J),
      Z.reindexIdeal Z.cov j γ = Z.ideal j γ := by
    intro Z j γ
    set φ : ((Z.cov.obj γ) ⧸ Z.ideal j γ) ≃+*
        ((Z.cov.obj γ) ⧸ Z.reindexIdeal Z.cov j γ) :=
      CategoryTheory.Iso.commRingCatIsoToRingEquiv
        { hom := Spec.preimage (Z.condiso j γ ≪≫ Z.reindexIso Z.cov j γ).inv
          inv := Spec.preimage (Z.condiso j γ ≪≫ Z.reindexIso Z.cov j γ).hom
          hom_inv_id := Spec.map_injective (by
            rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.hom_inv_id,
              Spec.map_id])
          inv_hom_id := Spec.map_injective (by
            rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.inv_hom_id,
              Spec.map_id]) } with hφ
    have hEsq : (Z.condiso j γ ≪≫ Z.reindexIso Z.cov j γ).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.reindexIdeal Z.cov j γ))) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal j γ))) := by
      rw [Iso.trans_hom, Category.assoc, ← Z.reindexIso_eq Z.cov j γ]
      exact Z.condiso_over j γ
    have hcompat : ∀ r : (Z.cov.obj γ),
        Ideal.Quotient.mk (Z.reindexIdeal Z.cov j γ)
            ((RingEquiv.refl (Z.cov.obj γ)) r) =
          φ (Ideal.Quotient.mk (Z.ideal j γ) r) := by
      intro r
      have hring : CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal j γ)) ≫
          CommRingCat.ofHom (φ : _ →+* _) =
          CommRingCat.ofHom (Ideal.Quotient.mk (Z.reindexIdeal Z.cov j γ)) := by
        apply Spec.map_injective
        rw [Spec.map_comp]
        rw [show CommRingCat.ofHom (φ : _ →+* _) =
            Spec.preimage (Z.condiso j γ ≪≫ Z.reindexIso Z.cov j γ).inv from rfl,
          Spec.map_preimage]
        rw [← hEsq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      exact (congrArg (fun f => (CommRingCat.Hom.hom f) r) hring).symm
    have := Ideal.map_eq_of_quotientIso (RingEquiv.refl (Z.cov.obj γ)) _ _ φ hcompat
    simpa using this
  have hD : M.Drep.reindexIdeal M.Yrep.cov i γβ.1 = M.Drep.ideal i γβ.1 :=
    hself M.Drep i γβ.1
  rw [M.Yrep.interIdeal_eq M.Drep (Equiv.refl M.indnumb) i γβ.1]
  show Ideal.map _ (M.Yideal i γβ.1 ⊔ M.Drep.reindexIdeal M.Yrep.cov i γβ.1) = _
  rw [hD, Ideal.map_sup, sup_eq_right]
  exact M.structureMap_pullSubset i γβ

def restrict {J : Type} (ι : J → M.indnumb) : PreMultiCenter X where
  indnumb := J
  cov := M.cov
  Ysub k := M.Ysub (ι k)
  Dsub k := M.Dsub (ι k)
  Yover k := M.Yover (ι k)
  Dover k := M.Dover (ι k)
  Yideal k := M.Yideal (ι k)
  Dideal k := M.Dideal (ι k)
  YcondIso k := M.YcondIso (ι k)
  YcondOver k := M.YcondOver (ι k)
  DcondIso k := M.DcondIso (ι k)
  DcondOver k := M.DcondOver (ι k)
  Dprin k := M.Dprin (ι k)

theorem restrict_pullSubset {J : Type} (ι : J → M.indnumb) :
    (M.restrict ι).pullSubset M.structureMap :=
  fun k γβ => M.structureMap_pullSubset (ι k) γβ

theorem restrict_isCars {J : Type} (ι : J → M.indnumb) :
    IsCars M.dilatation (Clos.pullback M.structureMap (M.restrict ι).D) :=
  ⟨pullback_PreClos X M.dilatation M.structureMap (M.restrict ι).Drep,
    pullback_IsPreCars_of_charts M.dilatation M.structureMap (M.restrict ι).Drep
      (fun k γβ => M.structureMap_isCars_chart (ι k) γβ), rfl⟩

theorem exists_unique_hom_restrict {J : Type} (ι : J → M.indnumb) :
    ∃! g : M.dilatation ⟶ (M.restrict ι).dilatation,
      g ≫ (M.restrict ι).structureMap = M.structureMap :=
  (M.restrict ι).universal_property M.dilatation M.structureMap
    (M.restrict_isCars ι) (M.restrict_pullSubset ι)

end PreMultiCenter

namespace MultiCenter

variable (M : MultiCenter X)

theorem structureMap_isAffineHom : IsAffineHom M.structureMap :=
  M.rep.structureMap_isAffineHom

theorem structureMap_isCars :
    IsCars M.dilatation (Clos.pullback M.structureMap M.D) := by
  have h := M.rep.structureMap_isCars
  rwa [M.rep_D] at h



end MultiCenter

end SchemeDilatation
