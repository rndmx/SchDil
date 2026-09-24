import GlobalDilProperties
import ClosSumSche
import MulticenterMonopoly

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

theorem Ideal.map_finset_prod {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    Ideal.map f (∏ j ∈ s, I j) = ∏ j ∈ s, Ideal.map f (I j) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [Ideal.one_eq_top, Ideal.map_top]
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, Ideal.map_mul, ih]

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X)
variable [Fintype M.indnumb] [DecidableEq M.indnumb]

instance localMulticenter_index_fintype (γ : M.cov.J) :
    Fintype (M.localMulticenter γ).index := inferInstanceAs (Fintype M.indnumb)

instance localMulticenter_index_decEq (γ : M.cov.J) :
    DecidableEq (M.localMulticenter γ).index := inferInstanceAs (DecidableEq M.indnumb)

section Dictionary

theorem localMonopoly_ideal_eq (γ : M.cov.J) :
    (M.localMulticenter γ).monopoly.ideal PUnit.unit =
      ⨆ i, M.Yideal i γ * ∏ j ∈ Finset.univ.erase i, M.Dideal j γ := by
  rw [Multicenter.monopoly_ideal]
  refine iSup_congr fun i => ?_
  show M.Yideal i γ * Ideal.span {(M.localMulticenter γ).coElem i} = _
  congr 1
  rw [Multicenter.coElem, ← Ideal.prod_span_singleton]
  refine Finset.prod_congr rfl fun j _ => ?_
  letI : Submodule.IsPrincipal (M.Dideal j γ) := M.Dprin j γ
  show Ideal.span {Submodule.IsPrincipal.generator (M.Dideal j γ)} = M.Dideal j γ
  exact Ideal.span_singleton_generator _

theorem localMonopoly_elem_span (γ : M.cov.J) :
    Ideal.span {(M.localMulticenter γ).monopoly.elem PUnit.unit} =
      ∏ j, M.Dideal j γ := by
  rw [Multicenter.monopoly_elem, Multicenter.prodElem, ← Ideal.prod_span_singleton]
  refine Finset.prod_congr rfl fun j _ => ?_
  letI : Submodule.IsPrincipal (M.Dideal j γ) := M.Dprin j γ
  show Ideal.span {Submodule.IsPrincipal.generator (M.Dideal j γ)} = M.Dideal j γ
  exact Ideal.span_singleton_generator _

end Dictionary

section Construction

noncomputable def monopolyDChartDatum : ChartDatum X where
  cov := M.cov
  idl γ := ∏ j, M.Dideal j γ
  compat a b hab := by
    rw [Ideal.map_finset_prod, Ideal.map_finset_prod]
    exact Finset.prod_congr rfl fun j _ => chartIdeal_agree M.Drep a b hab j

noncomputable def monopolyYChartDatum : ChartDatum X where
  cov := M.cov
  idl γ := ⨆ i, M.Yideal i γ * ∏ j ∈ Finset.univ.erase i, M.Dideal j γ
  compat a b hab := by
    rw [(Ideal.gc_map_comap _).l_iSup, (Ideal.gc_map_comap _).l_iSup]
    refine iSup_congr fun i => ?_
    rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_finset_prod, Ideal.map_finset_prod]
    congr 1
    · exact chartIdeal_agree M.Yrep a b hab i
    · exact Finset.prod_congr rfl fun j _ => chartIdeal_agree M.Drep a b hab j

noncomputable def monopolyCenter : PreMultiCenter X where
  indnumb := PUnit
  cov := M.cov
  Ysub _ := (M.monopolyYChartDatum).glued
  Dsub _ := (M.monopolyDChartDatum).glued
  Yover _ := ⟨(M.monopolyYChartDatum).structureMap⟩
  Dover _ := ⟨(M.monopolyDChartDatum).structureMap⟩
  Yideal _ γ :=
    ⨆ i, M.Yideal i γ * ∏ j ∈ Finset.univ.erase i, M.Dideal j γ
  Dideal _ γ := ∏ j, M.Dideal j γ
  YcondIso _ γ := asIso ((M.monopolyYChartDatum).chartCompare γ)
  YcondOver _ γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (M.monopolyYChartDatum).chartCompare γ ≫
        pullback.snd ((M.monopolyYChartDatum).structureMap) (M.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (⨆ i, M.Yideal i γ * ∏ j ∈ Finset.univ.erase i, M.Dideal j γ)))
    exact (M.monopolyYChartDatum).chartCompare_snd γ
  DcondIso _ γ := asIso ((M.monopolyDChartDatum).chartCompare γ)
  DcondOver _ γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (M.monopolyDChartDatum).chartCompare γ ≫
        pullback.snd ((M.monopolyDChartDatum).structureMap) (M.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (∏ j, M.Dideal j γ)))
    exact (M.monopolyDChartDatum).chartCompare_snd γ
  Dprin _ γ := ⟨⟨(M.localMulticenter γ).prodElem, by
    rw [Ideal.submodule_span_eq]
    exact (M.localMonopoly_elem_span γ).symm⟩⟩

@[simp] theorem monopolyCenter_Yideal (u : PUnit) (γ : M.cov.J) :
    M.monopolyCenter.Yideal u γ =
      ⨆ i, M.Yideal i γ * ∏ j ∈ Finset.univ.erase i, M.Dideal j γ := rfl

@[simp] theorem monopolyCenter_Dideal (u : PUnit) (γ : M.cov.J) :
    M.monopolyCenter.Dideal u γ = ∏ j, M.Dideal j γ := rfl

end Construction

section Conditions

omit [Fintype M.indnumb] [DecidableEq M.indnumb] in
theorem elem_nzd_on_dilatation_chart (i : M.indnumb)
    (γβ : (pull_cov X M.Drep M.dilatation M.structureMap).J) :
    (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
        ((M.localMulticenter γβ.1).elem i) ∈
      nonZeroDivisors
        ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) := by
  obtain ⟨g, hg, hgnzd⟩ := M.structureMap_isCars_chart i γβ
  refine nonZeroDivisors_of_span_singleton_eq ?_ hgnzd
  rw [← hg]
  letI : Submodule.IsPrincipal (M.Drep.ideal i γβ.1) := M.Dprin i γβ.1
  show _ = Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
    (M.Drep.ideal i γβ.1)
  conv_rhs => rw [← Ideal.span_singleton_generator (M.Drep.ideal i γβ.1)]
  rw [Ideal.map_span, Set.image_singleton]
  rfl

theorem monopoly_isCars_on_dilatation :
    IsCars M.dilatation (Clos.pullback M.structureMap M.monopolyCenter.D) := by
  refine ⟨pullback_PreClos X M.dilatation M.structureMap M.monopolyCenter.Drep,
    pullback_IsPreCars_of_charts _ _ _ (fun u γβ => ?_), rfl⟩
  refine ⟨(pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
    ((M.localMulticenter γβ.1).prodElem), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
      (∏ j, M.Dideal j γβ.1) = _
    rw [← M.localMonopoly_elem_span γβ.1, Ideal.map_span, Set.image_singleton]
    rfl
  · letI : Algebra (M.cov.obj γβ.1)
        ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) :=
      (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom.toAlgebra
    exact (M.localMulticenter γβ.1).prodElem_nzd_iff.mpr
      (fun i => M.elem_nzd_on_dilatation_chart i γβ)

theorem monopoly_pullSubset_chart
    (γβ : (pull_cov X M.Drep M.dilatation M.structureMap).J) :
    Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
        (⨆ i, M.Yideal i γβ.1 * ∏ j ∈ Finset.univ.erase i, M.Dideal j γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
        (∏ j, M.Dideal j γβ.1) := by
  letI : Algebra (M.cov.obj γβ.1)
      ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) :=
    (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom.toAlgebra
  have hnzd : ∀ i, algebraMap (M.cov.obj γβ.1) _ ((M.localMulticenter γβ.1).elem i) ∈
      nonZeroDivisors
        ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) :=
    fun i => M.elem_nzd_on_dilatation_chart i γβ
  have hall : ∀ i, Ideal.map (algebraMap (M.cov.obj γβ.1) _)
      ((M.localMulticenter γβ.1).ideal i) ≤
      Ideal.span {algebraMap (M.cov.obj γβ.1)
        ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2)
        ((M.localMulticenter γβ.1).elem i)} := by
    intro i
    have h : Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
        (M.Yideal i γβ.1) ≤
        Ideal.map (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom
          (M.Drep.ideal i γβ.1) := M.structureMap_pullSubset i γβ
    refine le_trans h (le_of_eq ?_)
    letI : Submodule.IsPrincipal (M.Drep.ideal i γβ.1) := M.Dprin i γβ.1
    conv_lhs => rw [← Ideal.span_singleton_generator (M.Drep.ideal i γβ.1)]
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have key := ((M.localMulticenter γβ.1).monopoly_map_le_iff hnzd).mpr hall
  rw [← M.localMonopoly_ideal_eq γβ.1, ← M.localMonopoly_elem_span γβ.1,
    Ideal.map_span, Set.image_singleton]
  exact key

theorem monopoly_pullSubset_on_dilatation :
    M.monopolyCenter.pullSubset M.structureMap :=
  fun _ γβ => M.monopoly_pullSubset_chart γβ

theorem prodElem_nzd_on_monopoly_chart
    (γβ : (pull_cov X M.Drep M.monopolyCenter.dilatation
      M.monopolyCenter.structureMap).J) :
    (pull_mor_ring X M.Drep M.monopolyCenter.dilatation
        M.monopolyCenter.structureMap γβ).hom ((M.localMulticenter γβ.1).prodElem) ∈
      nonZeroDivisors ((pull_loc_cov X M.Drep M.monopolyCenter.dilatation
        M.monopolyCenter.structureMap γβ.1).obj γβ.2) := by
  obtain ⟨g, hg, hgnzd⟩ := M.monopolyCenter.structureMap_isCars_chart PUnit.unit γβ
  refine nonZeroDivisors_of_span_singleton_eq ?_ hgnzd
  rw [← hg]
  show Ideal.span {(pull_mor_ring X M.Drep M.monopolyCenter.dilatation
      M.monopolyCenter.structureMap γβ).hom ((M.localMulticenter γβ.1).prodElem)} =
    Ideal.map (pull_mor_ring X M.Drep M.monopolyCenter.dilatation
      M.monopolyCenter.structureMap γβ).hom (∏ j, M.Dideal j γβ.1)
  rw [← M.localMonopoly_elem_span γβ.1, Ideal.map_span, Set.image_singleton]
  rfl

theorem isCars_on_monopolyDil :
    IsCars M.monopolyCenter.dilatation
      (Clos.pullback M.monopolyCenter.structureMap M.D) := by
  refine ⟨pullback_PreClos X M.monopolyCenter.dilatation
      M.monopolyCenter.structureMap M.Drep,
    pullback_IsPreCars_of_charts _ _ _ (fun i γβ => ?_), rfl⟩
  refine ⟨(pull_mor_ring X M.Drep M.monopolyCenter.dilatation
      M.monopolyCenter.structureMap γβ).hom ((M.localMulticenter γβ.1).elem i), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep M.monopolyCenter.dilatation
        M.monopolyCenter.structureMap γβ).hom (M.Drep.ideal i γβ.1) = _
    letI : Submodule.IsPrincipal (M.Drep.ideal i γβ.1) := M.Dprin i γβ.1
    conv_lhs => rw [← Ideal.span_singleton_generator (M.Drep.ideal i γβ.1)]
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  · letI : Algebra (M.cov.obj γβ.1)
        ((pull_loc_cov X M.Drep M.monopolyCenter.dilatation
          M.monopolyCenter.structureMap γβ.1).obj γβ.2) :=
      (pull_mor_ring X M.Drep M.monopolyCenter.dilatation
        M.monopolyCenter.structureMap γβ).hom.toAlgebra
    exact (M.localMulticenter γβ.1).prodElem_nzd_iff.mp
      (M.prodElem_nzd_on_monopoly_chart γβ) i

theorem pullSubset_on_monopolyDil_chart (i : M.indnumb)
    (γβ : (pull_cov X M.Drep M.monopolyCenter.dilatation
      M.monopolyCenter.structureMap).J) :
    Ideal.map (pull_mor_ring X M.Drep M.monopolyCenter.dilatation
        M.monopolyCenter.structureMap γβ).hom (M.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep M.monopolyCenter.dilatation
        M.monopolyCenter.structureMap γβ).hom (M.Drep.ideal i γβ.1) := by
  letI : Algebra (M.cov.obj γβ.1)
      ((pull_loc_cov X M.Drep M.monopolyCenter.dilatation
        M.monopolyCenter.structureMap γβ.1).obj γβ.2) :=
    (pull_mor_ring X M.Drep M.monopolyCenter.dilatation
      M.monopolyCenter.structureMap γβ).hom.toAlgebra
  have hnzd : ∀ j, algebraMap (M.cov.obj γβ.1) _ ((M.localMulticenter γβ.1).elem j) ∈
      nonZeroDivisors ((pull_loc_cov X M.Drep M.monopolyCenter.dilatation
        M.monopolyCenter.structureMap γβ.1).obj γβ.2) :=
    (M.localMulticenter γβ.1).prodElem_nzd_iff.mp (M.prodElem_nzd_on_monopoly_chart γβ)
  have hsub : Ideal.map (pull_mor_ring X M.Drep M.monopolyCenter.dilatation
      M.monopolyCenter.structureMap γβ).hom
        (⨆ i', M.Yideal i' γβ.1 * ∏ j ∈ Finset.univ.erase i', M.Dideal j γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep M.monopolyCenter.dilatation
        M.monopolyCenter.structureMap γβ).hom (∏ j, M.Dideal j γβ.1) :=
    M.monopolyCenter.structureMap_pullSubset PUnit.unit γβ
  have hmono : Ideal.map (algebraMap (M.cov.obj γβ.1) _)
      ((M.localMulticenter γβ.1).monopoly.ideal PUnit.unit) ≤
      Ideal.span {algebraMap (M.cov.obj γβ.1)
        ((pull_loc_cov X M.Drep M.monopolyCenter.dilatation
          M.monopolyCenter.structureMap γβ.1).obj γβ.2)
        ((M.localMulticenter γβ.1).prodElem)} := by
    rw [M.localMonopoly_ideal_eq γβ.1]
    refine le_trans hsub (le_of_eq ?_)
    rw [← M.localMonopoly_elem_span γβ.1, Ideal.map_span, Set.image_singleton]
    rfl
  have key := ((M.localMulticenter γβ.1).monopoly_map_le_iff hnzd).mp hmono i
  refine le_trans key (le_of_eq ?_)
  letI : Submodule.IsPrincipal (M.Drep.ideal i γβ.1) := M.Dprin i γβ.1
  conv_rhs => rw [← Ideal.span_singleton_generator (M.Drep.ideal i γβ.1)]
  rw [Ideal.map_span, Set.image_singleton]
  rfl

theorem pullSubset_on_monopolyDil : M.pullSubset M.monopolyCenter.structureMap :=
  fun i γβ => M.pullSubset_on_monopolyDil_chart i γβ

end Conditions

section Assembly

theorem existsUnique_monopolyHom :
    ∃! g : M.dilatation ⟶ M.monopolyCenter.dilatation,
      g ≫ M.monopolyCenter.structureMap = M.structureMap :=
  M.monopolyCenter.universal_property M.dilatation M.structureMap
    M.monopoly_isCars_on_dilatation M.monopoly_pullSubset_on_dilatation

theorem existsUnique_monopolyInv :
    ∃! g : M.monopolyCenter.dilatation ⟶ M.dilatation,
      g ≫ M.structureMap = M.monopolyCenter.structureMap :=
  M.universal_property M.monopolyCenter.dilatation M.monopolyCenter.structureMap
    M.isCars_on_monopolyDil M.pullSubset_on_monopolyDil

noncomputable def monopolyHom : M.dilatation ⟶ M.monopolyCenter.dilatation :=
  (M.existsUnique_monopolyHom).choose

theorem monopolyHom_over :
    M.monopolyHom ≫ M.monopolyCenter.structureMap = M.structureMap :=
  (M.existsUnique_monopolyHom).choose_spec.1

noncomputable def monopolyInv : M.monopolyCenter.dilatation ⟶ M.dilatation :=
  (M.existsUnique_monopolyInv).choose

theorem monopolyInv_over :
    M.monopolyInv ≫ M.structureMap = M.monopolyCenter.structureMap :=
  (M.existsUnique_monopolyInv).choose_spec.1

theorem monopolyHom_comp_monopolyInv : M.monopolyHom ≫ M.monopolyInv = 𝟙 _ :=
  (M.universal_property M.dilatation M.structureMap
    M.structureMap_isCars M.structureMap_pullSubset).unique
    (by rw [Category.assoc, M.monopolyInv_over, M.monopolyHom_over])
    (Category.id_comp _)

theorem monopolyInv_comp_monopolyHom : M.monopolyInv ≫ M.monopolyHom = 𝟙 _ :=
  (M.monopolyCenter.universal_property M.monopolyCenter.dilatation
    M.monopolyCenter.structureMap M.monopolyCenter.structureMap_isCars
    M.monopolyCenter.structureMap_pullSubset).unique
    (by rw [Category.assoc, M.monopolyHom_over, M.monopolyInv_over])
    (Category.id_comp _)

noncomputable def monopolyIso : M.dilatation ≅ M.monopolyCenter.dilatation where
  hom := M.monopolyHom
  inv := M.monopolyInv
  hom_inv_id := M.monopolyHom_comp_monopolyInv
  inv_hom_id := M.monopolyInv_comp_monopolyHom

@[simp] theorem monopolyIso_hom_over :
    (M.monopolyIso).hom ≫ M.monopolyCenter.structureMap = M.structureMap :=
  M.monopolyHom_over

theorem monopolyIso_unique (g : M.dilatation ⟶ M.monopolyCenter.dilatation)
    (hg : g ≫ M.monopolyCenter.structureMap = M.structureMap) :
    g = (M.monopolyIso).hom :=
  (M.existsUnique_monopolyHom).choose_spec.2 g hg

end Assembly

end PreMultiCenter

end SchemeDilatation
