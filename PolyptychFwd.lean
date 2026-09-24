import PolyptychUpsChart

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter Family
open Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb]

section Bridge

variable (J : Finset M.indnumb) (γ : M.cov.J)

theorem restCenter_elem_nzd_univ
    (j : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) :
    algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ))
        ((Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ)) := by
  classical
  show algebraMap (M.cov.obj γ) _
      (∏ s ∈ J.filter (fun s => j.1 ≤ s), (M.localMulticenter γ).elem s) ∈ _
  rw [map_prod]
  exact prod_mem fun s _ =>
    M.defSpace_chart_gen_nzd Finset.univ γ s (Finset.mem_univ s)

theorem restCenter_gen_univ
    (j : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) :
    Ideal.span {algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ))
        ((Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j)} =
      Ideal.map (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ)))
        ((Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).LargeIdeal j) := by
  classical
  refine (gen_iff_le (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J) j).mpr ?_
  show Ideal.map _ (M.Yideal j.1 γ) ≤
    Ideal.span {algebraMap (M.cov.obj γ) _
      (∏ s ∈ J.filter (fun s => j.1 ≤ s), (M.localMulticenter γ).elem s)}
  have hspan : Ideal.span {algebraMap (M.cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ))
      (∏ s ∈ J.filter (fun s => j.1 ≤ s), (M.localMulticenter γ).elem s)} =
      Ideal.map (algebraMap ((M.defSpace Finset.univ).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ)))
        (∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γ) := by
    rw [Ideal.span_singleton_map, Ideal.span_singleton_finset_prod]
    exact congrArg _ (Finset.prod_congr rfl fun s _ => (M.local_Dideal_span' γ s).symm)
  rw [hspan]
  refine le_trans (M.defSpace_chart_self_le Finset.univ γ j.1 (Finset.mem_univ _))
    (Ideal.map_mono ?_)
  rw [Finset.prod_filter_split (Finset.subset_univ J) (fun s => j.1 ≤ s)
    (fun s => M.Dideal s γ)]
  exact Ideal.mul_le_right

theorem upsRho_comp_chartEquiv :
    (M.upsRho (Finset.subset_univ J) γ).toRingHom.comp
        (M.chartEquiv J γ).toRingHom =
      (M.chartEquiv Finset.univ γ).toRingHom.comp
        (Polyptych.upsilonFull (M.chartM γ) (M.chartd γ) J).toRingHom := by
  classical
  let L : Polyptych.Ring (M.chartM γ) (M.chartd γ) J →ₐ[M.cov.obj γ]
      Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ) :=
    AlgHom.mk ((M.upsRho (Finset.subset_univ J) γ).toRingHom.comp
      (M.chartEquiv J γ).toRingHom) (fun a => by
        show M.upsRho (Finset.subset_univ J) γ (M.chartEquiv J γ
          (algebraMap (M.cov.obj γ)
            (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) a)) = _
        rw [M.chartEquiv_algebraMap J γ a]
        exact M.upsRho_algebraMap (Finset.subset_univ J) γ a)
  let R : Polyptych.Ring (M.chartM γ) (M.chartd γ) J →ₐ[M.cov.obj γ]
      Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ) :=
    AlgHom.mk ((M.chartEquiv Finset.univ γ).toRingHom.comp
      (Polyptych.upsilonFull (M.chartM γ) (M.chartd γ) J).toRingHom) (fun a => by
        show M.chartEquiv Finset.univ γ
          (Polyptych.upsilonFull (M.chartM γ) (M.chartd γ) J
            (algebraMap (M.cov.obj γ)
              (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) a)) = _
        rw [Polyptych.upsilonFull_algebraMap]
        exact M.chartEquiv_algebraMap Finset.univ γ a)
  have h : L = R :=
    lemma_exists_unique_morphism' (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J)
      (M.restCenter_elem_nzd_univ J γ) (M.restCenter_gen_univ J γ) L R
  exact congrArg AlgHom.toRingHom h

end Bridge

section PieceFactor

variable (J : Finset M.indnumb)

theorem panel_piece_factor
    (γβ : (pull_cov ((M.defSpace J).dilatation) ((M.panelStage J).Drep)
      ((M.defSpace Finset.univ).dilatation)
      (M.upsilonScheme (Finset.subset_univ J))).J) :
    ∃ ψ : CommRingCat.of (Multicenter.Dilatation
        ((M.defSpace Finset.univ).localMulticenter γβ.1)) ⟶
        (pull_loc_cov ((M.defSpace J).dilatation) ((M.panelStage J).Drep)
          ((M.defSpace Finset.univ).dilatation)
          (M.upsilonScheme (Finset.subset_univ J)) γβ.1).obj γβ.2,
      pull_mor_ring ((M.defSpace J).dilatation) ((M.panelStage J).Drep)
          ((M.defSpace Finset.univ).dilatation)
          (M.upsilonScheme (Finset.subset_univ J)) γβ =
        CommRingCat.ofHom (M.upsRho (Finset.subset_univ J) γβ.1).toRingHom ≫ ψ ∧
      RingHom.Flat ψ.hom := by
  have hsnd : (pull_loc_cov ((M.defSpace J).dilatation)
      ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
      (M.upsilonScheme (Finset.subset_univ J)) γβ.1).map γβ.2 ≫
      pullback.snd (M.upsilonScheme (Finset.subset_univ J))
        ((M.panelStage J).Drep.cov.map γβ.1) =
      Spec.map (pull_mor_ring ((M.defSpace J).dilatation)
        ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
        (M.upsilonScheme (Finset.subset_univ J)) γβ) :=
    (spec_map_pull_mor_ring _ _ γβ).symm
  have hcφ : ((pull_loc_cov ((M.defSpace J).dilatation)
      ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
      (M.upsilonScheme (Finset.subset_univ J)) γβ.1).map γβ.2 ≫
      pullback.fst (M.upsilonScheme (Finset.subset_univ J))
        ((M.panelStage J).Drep.cov.map γβ.1)) ≫
      M.upsilonScheme (Finset.subset_univ J) =
      Spec.map (pull_mor_ring ((M.defSpace J).dilatation)
        ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
        (M.upsilonScheme (Finset.subset_univ J)) γβ) ≫
      (M.defSpace J).chartTo γβ.1 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd]
    rfl
  have hcw : ((pull_loc_cov ((M.defSpace J).dilatation)
      ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
      (M.upsilonScheme (Finset.subset_univ J)) γβ.1).map γβ.2 ≫
      pullback.fst (M.upsilonScheme (Finset.subset_univ J))
        ((M.panelStage J).Drep.cov.map γβ.1)) ≫
      (M.defSpace Finset.univ).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ((M.defSpace J).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γβ.1))) ≫
        pull_mor_ring ((M.defSpace J).dilatation)
          ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
          (M.upsilonScheme (Finset.subset_univ J)) γβ) ≫
      M.cov.map γβ.1 := by
    rw [← M.upsilonScheme_over (Finset.subset_univ J), ← Category.assoc,
      hcφ, Spec.map_comp]
    rw [Category.assoc, Category.assoc, (M.defSpace J).structureMap_chart γβ.1]
    rfl
  obtain ⟨sT, hsT1, hsT2⟩ :=
    (M.defSpace Finset.univ).exists_chart_factorisation' γβ.1 _ _ hcw
  haveI : IsOpenImmersion ((M.defSpace J).chartTo γβ.1) :=
    (M.defSpace J).chartTo_isOpenImmersion γβ.1
  haveI : Mono ((M.defSpace J).chartTo γβ.1) := inferInstance
  have hkey : Spec.map (pull_mor_ring ((M.defSpace J).dilatation)
      ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
      (M.upsilonScheme (Finset.subset_univ J)) γβ) =
      sT ≫ M.upsRhoSch (Finset.subset_univ J) γβ.1 := by
    apply Mono.right_cancellation (f := (M.defSpace J).chartTo γβ.1)
    rw [← hcφ]
    simp only [Category.assoc]
    rw [← M.ups_chart_cone (Finset.subset_univ J) γβ.1, reassoc_of% hsT1]
  refine ⟨Spec.preimage sT, ?_, ?_⟩
  · apply Spec.map_injective
    rw [hkey, Spec.map_comp, Spec.map_preimage]
    rfl
  · haveI hc : IsOpenImmersion ((pull_loc_cov ((M.defSpace J).dilatation)
        ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
        (M.upsilonScheme (Finset.subset_univ J)) γβ.1).map γβ.2 ≫
        pullback.fst (M.upsilonScheme (Finset.subset_univ J))
          ((M.panelStage J).Drep.cov.map γβ.1)) :=
      (pull_cov ((M.defSpace J).dilatation) ((M.panelStage J).Drep)
        ((M.defSpace Finset.univ).dilatation)
        (M.upsilonScheme (Finset.subset_univ J))).map_prop γβ
    haveI hsc : IsOpenImmersion (sT ≫ (M.defSpace Finset.univ).chartTo γβ.1) := by
      rw [hsT1]
      exact hc
    haveI hs : IsOpenImmersion sT :=
      IsOpenImmersion.of_comp sT ((M.defSpace Finset.univ).chartTo γβ.1)
    haveI hflat : AlgebraicGeometry.Flat sT := inferInstance
    haveI hflat2 : AlgebraicGeometry.Flat (Spec.map (Spec.preimage sT)) := by
      rw [Spec.map_preimage]
      exact hflat
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Flat)).mp hflat2

end PieceFactor

section UpsilonPanel

theorem elemOf_comp_nzd_univ (J : Finset M.indnumb) (i : M.indnumb) (γ : M.cov.J) :
    algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ))
        (Polyptych.elemOf (M.chartd γ) (Polyptych.Comp J) i) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ)) := by
  classical
  show algebraMap (M.cov.obj γ) _
      (∏ s ∈ (Polyptych.Comp J).filter (fun s => i ≤ s),
        (M.localMulticenter γ).elem s) ∈ _
  rw [map_prod]
  exact prod_mem fun s _ =>
    M.defSpace_chart_gen_nzd Finset.univ γ s (Finset.mem_univ s)

theorem panelStage_Dideal_upsRho (J : Finset M.indnumb)
    (i : (M.panelStage J).indnumb) (γ : M.cov.J) :
    Ideal.map (M.upsRho (Finset.subset_univ J) γ).toRingHom
        ((M.panelStage J).Dideal i γ) =
      Ideal.span {algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γ))
        (Polyptych.elemOf (M.chartd γ) (Polyptych.Comp J) i.1)} := by
  classical
  show Ideal.map _ (Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
    (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
    (∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s), M.Dideal s γ)) = _
  rw [Ideal.map_map,
    show (M.upsRho (Finset.subset_univ J) γ).toRingHom.comp
      (algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))) =
      (algebraMap (M.cov.obj γ) (Multicenter.Dilatation
        ((M.defSpace Finset.univ).localMulticenter γ)) : _ →+* _) from
      RingHom.ext fun a => M.upsRho_algebraMap (Finset.subset_univ J) γ a,
    show (∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s), M.Dideal s γ) =
      Ideal.span {∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s),
        (M.localMulticenter γ).elem s} from by
      rw [Ideal.span_singleton_finset_prod]
      exact Finset.prod_congr rfl fun s _ => M.local_Dideal_span' γ s,
    Ideal.map_span, Set.image_singleton]
  rfl

theorem upsilon_ker_le' (J : Finset M.indnumb) (hC : M.CartierDatum) (hM : M.MonoDatum)
    (hreg : M.DilRegular J) (i : M.indnumb) (hiC : i ∈ Polyptych.Comp J)
    (γ : M.cov.J) :
    Ideal.map (Polyptych.upsilonFull (M.chartM γ) (M.chartd γ) J).toRingHom
        (RingHom.ker (Polyptych.panelHom (M.chartM γ) (M.chartd γ) J i)) ≤
      Ideal.span {algebraMap (M.cov.obj γ)
        (Polyptych.Full (M.chartM γ) (M.chartd γ))
        (Polyptych.elemOf (M.chartd γ) (Polyptych.Comp J) i)} :=
  Polyptych.upsilon_ker_le (hC γ) (hM γ) J i hiC
    (hreg γ i (Finset.mem_sdiff.mp hiC).2).1
    (hreg γ i (Finset.mem_sdiff.mp hiC).2).2

theorem panelStage_pullSubset_chart (J : Finset M.indnumb) (hC : M.CartierDatum)
    (hM : M.MonoDatum) (hreg : M.DilRegular J)
    (i : (M.panelStage J).indnumb)
    (γβ : (pull_cov ((M.defSpace J).dilatation) ((M.panelStage J).Drep)
      ((M.defSpace Finset.univ).dilatation)
      (M.upsilonScheme (Finset.subset_univ J))).J) :
    Ideal.map (pull_mor_ring ((M.defSpace J).dilatation)
        ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
        (M.upsilonScheme (Finset.subset_univ J)) γβ).hom
        ((M.panelStage J).Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring ((M.defSpace J).dilatation)
        ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
        (M.upsilonScheme (Finset.subset_univ J)) γβ).hom
        ((M.panelStage J).Dideal i γβ.1) := by
  obtain ⟨ψ, hψ, -⟩ := M.panel_piece_factor J γβ
  rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hstep : ∀ (I : Ideal (Multicenter.Dilatation
      ((M.defSpace J).localMulticenter γβ.1))),
      Ideal.map ((CommRingCat.Hom.hom ψ).comp
        (M.upsRho (Finset.subset_univ J) γβ.1).toRingHom) I =
      Ideal.map (CommRingCat.Hom.hom ψ)
        (Ideal.map (M.upsRho (Finset.subset_univ J) γβ.1).toRingHom I) :=
    fun I => (Ideal.map_map _ _).symm
  rw [hstep, hstep]
  refine Ideal.map_mono ?_
  rw [M.panelStage_Yideal_eq J i γβ.1, Ideal.map_map,
    M.upsRho_comp_chartEquiv J γβ.1, ← Ideal.map_map,
    M.panelStage_Dideal_upsRho J i γβ.1]
  refine le_trans (Ideal.map_mono
    (M.upsilon_ker_le' J hC hM hreg i.1 i.2 γβ.1)) ?_
  rw [Ideal.map_span, Set.image_singleton,
    show (M.chartEquiv Finset.univ γβ.1).toRingHom (algebraMap (M.cov.obj γβ.1)
        (Polyptych.Full (M.chartM γβ.1) (M.chartd γβ.1))
        (Polyptych.elemOf (M.chartd γβ.1) (Polyptych.Comp J) i.1)) =
        algebraMap (M.cov.obj γβ.1)
          (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γβ.1))
          (Polyptych.elemOf (M.chartd γβ.1) (Polyptych.Comp J) i.1) from
      M.chartEquiv_algebraMap Finset.univ γβ.1 _]

theorem panelStage_pullSubset (J : Finset M.indnumb) (hC : M.CartierDatum)
    (hM : M.MonoDatum) (hreg : M.DilRegular J) :
    (M.panelStage J).pullSubset
      (M.upsilonScheme (Finset.subset_univ J)) :=
  ((M.panelStage J).pullSubset_iff _).mpr
    (fun i γβ => M.panelStage_pullSubset_chart J hC hM hreg i γβ)

theorem panelStage_isCars_chart (J : Finset M.indnumb)
    (i : (M.panelStage J).indnumb)
    (γβ : (pull_cov ((M.defSpace J).dilatation) ((M.panelStage J).Drep)
      ((M.defSpace Finset.univ).dilatation)
      (M.upsilonScheme (Finset.subset_univ J))).J) :
    ∃ g : (pull_loc_cov ((M.defSpace J).dilatation)
        ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
        (M.upsilonScheme (Finset.subset_univ J)) γβ.1).obj γβ.2,
      (pullback_PreClos ((M.defSpace J).dilatation)
          ((M.defSpace Finset.univ).dilatation)
          (M.upsilonScheme (Finset.subset_univ J))
          (M.panelStage J).Drep).ideal i γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov ((M.defSpace J).dilatation)
        ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
        (M.upsilonScheme (Finset.subset_univ J)) γβ.1).obj γβ.2) := by
  obtain ⟨ψ, hψ, hflat⟩ := M.panel_piece_factor J γβ
  refine ⟨ψ.hom (algebraMap (M.cov.obj γβ.1)
    (Multicenter.Dilatation ((M.defSpace Finset.univ).localMulticenter γβ.1))
    (Polyptych.elemOf (M.chartd γβ.1) (Polyptych.Comp J) i.1)), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring ((M.defSpace J).dilatation)
        ((M.panelStage J).Drep) ((M.defSpace Finset.univ).dilatation)
        (M.upsilonScheme (Finset.subset_univ J)) γβ).hom
        ((M.panelStage J).Dideal i γβ.1) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom, ← Ideal.map_map,
      M.panelStage_Dideal_upsRho J i γβ.1, Ideal.map_span,
      Set.image_singleton]
  · exact hflat.preserves_nonzeroDivisors (M.elemOf_comp_nzd_univ J i.1 γβ.1)

theorem panelStage_isCars (J : Finset M.indnumb) :
    IsCars ((M.defSpace Finset.univ).dilatation)
      (Clos.pullback (M.upsilonScheme (Finset.subset_univ J))
        (M.panelStage J).D) :=
  ⟨pullback_PreClos ((M.defSpace J).dilatation)
      ((M.defSpace Finset.univ).dilatation)
      (M.upsilonScheme (Finset.subset_univ J)) (M.panelStage J).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun i γβ => M.panelStage_isCars_chart J i γβ), rfl⟩

theorem existsUnique_upsilonPanel (J : Finset M.indnumb) (hC : M.CartierDatum)
    (hM : M.MonoDatum) (hreg : M.DilRegular J) :
    ∃! g : (M.defSpace Finset.univ).dilatation ⟶ M.panelSpace J,
      g ≫ M.tauJ J = M.upsilonScheme (Finset.subset_univ J) :=
  (M.panelStage J).universal_property _
    (M.upsilonScheme (Finset.subset_univ J))
    (M.panelStage_isCars J) (M.panelStage_pullSubset J hC hM hreg)

def upsilonPanelSch (J : Finset M.indnumb) (hC : M.CartierDatum)
    (hM : M.MonoDatum) (hreg : M.DilRegular J) :
    (M.defSpace Finset.univ).dilatation ⟶ M.panelSpace J :=
  (M.existsUnique_upsilonPanel J hC hM hreg).choose

@[simp] theorem upsilonPanelSch_over (J : Finset M.indnumb) (hC : M.CartierDatum)
    (hM : M.MonoDatum) (hreg : M.DilRegular J) :
    M.upsilonPanelSch J hC hM hreg ≫ M.tauJ J =
      M.upsilonScheme (Finset.subset_univ J) :=
  (M.existsUnique_upsilonPanel J hC hM hreg).choose_spec.1

theorem upsilonPanelSch_unique (J : Finset M.indnumb) (hC : M.CartierDatum)
    (hM : M.MonoDatum) (hreg : M.DilRegular J)
    (g : (M.defSpace Finset.univ).dilatation ⟶ M.panelSpace J)
    (hg : g ≫ M.tauJ J = M.upsilonScheme (Finset.subset_univ J)) :
    g = M.upsilonPanelSch J hC hM hreg :=
  (M.existsUnique_upsilonPanel J hC hM hreg).choose_spec.2 g hg

end UpsilonPanel

end PreMultiCenter
end SchemeDilatation
