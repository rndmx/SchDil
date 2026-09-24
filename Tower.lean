import MultiCenterBaseChange
import DilatationNonZeroDivisor
import DilatationChart
import ClosInterPullback

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

variable {X : Scheme.{u+1}}

namespace SchemeDilatation

namespace PreMultiCenter

variable (M : PreMultiCenter X) {Jt Kt : Type} (ι : Jt → M.indnumb) (κ : Kt → M.indnumb)

section Restrict

theorem restrict_pullSubset_of {T : Scheme.{u+1}} (f : T ⟶ X) (h : M.pullSubset f) :
    (M.restrict ι).pullSubset f := fun k γβ => h (ι k) γβ

theorem restrict_id : M.restrict (id : M.indnumb → M.indnumb) = M := rfl

end Restrict

section Tower

abbrev towerCenter : PreMultiCenter (M.restrict ι).dilatation :=
  (M.restrict κ).baseChange (M.restrict ι).structureMap

abbrev tower : Scheme.{u+1} := (M.towerCenter ι κ).dilatation

abbrev towerToBase : M.tower ι κ ⟶ (M.restrict ι).dilatation :=
  (M.towerCenter ι κ).structureMap

abbrev towerToX : M.tower ι κ ⟶ X :=
  M.towerToBase ι κ ≫ (M.restrict ι).structureMap

end Tower

section InParticular

theorem existsUnique_homToBase :
    ∃! g : M.dilatation ⟶ (M.restrict ι).dilatation,
      g ≫ (M.restrict ι).structureMap = M.structureMap :=
  M.exists_unique_hom_restrict ι

def homToBase : M.dilatation ⟶ (M.restrict ι).dilatation :=
  (M.existsUnique_homToBase ι).choose

@[simp] theorem homToBase_comp :
    M.homToBase ι ≫ (M.restrict ι).structureMap = M.structureMap :=
  (M.existsUnique_homToBase ι).choose_spec.1

theorem homToBase_unique (g : M.dilatation ⟶ (M.restrict ι).dilatation)
    (hg : g ≫ (M.restrict ι).structureMap = M.structureMap) : g = M.homToBase ι :=
  (M.existsUnique_homToBase ι).choose_spec.2 g hg

end InParticular

section Cartier

theorem towerCenter_isCars :
    IsCars M.dilatation (Clos.pullback (M.homToBase ι) (M.towerCenter ι κ).D) := by
  rw [baseChange_D]
  show IsCars M.dilatation
    (pullback_Clos (M.homToBase ι)
      (pullback_Clos (M.restrict ι).structureMap (M.restrict κ).D))
  rw [pullback_Clos_comp, homToBase_comp]
  exact M.restrict_isCars κ

theorem tower_isCars_chart (i : M.indnumb) (hi : (∃ j, ι j = i) ∨ ∃ k, κ k = i)
    (γβδ : (pull_cov (M.restrict ι).dilatation
      (pullback_PreClos X (M.restrict ι).dilatation (M.restrict ι).structureMap M.Drep)
      (M.tower ι κ) (M.towerToBase ι κ)).J) :
    ∃ g : (pull_loc_cov (M.restrict ι).dilatation
        (pullback_PreClos X (M.restrict ι).dilatation (M.restrict ι).structureMap M.Drep)
        (M.tower ι κ) (M.towerToBase ι κ) γβδ.1).obj γβδ.2,
      (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
          (pullback_PreClos X (M.restrict ι).dilatation
            (M.restrict ι).structureMap M.Drep)).ideal i γβδ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors _ := by
  rcases hi with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨g, hg, hgnzd⟩ := (M.restrict ι).structureMap_isCars_chart j γβδ.1
    refine ⟨(pull_mor_ring (M.restrict ι).dilatation
      (pullback_PreClos X (M.restrict ι).dilatation (M.restrict ι).structureMap M.Drep)
      (M.tower ι κ) (M.towerToBase ι κ) γβδ).hom g, ?_, ?_⟩
    · show Ideal.map _ (Ideal.map (pull_mor_ring X M.Drep _ _ γβδ.1).hom
        (M.Drep.ideal (ι j) γβδ.1.1)) = _
      rw [show Ideal.map (pull_mor_ring X M.Drep _ (M.restrict ι).structureMap γβδ.1).hom
            (M.Drep.ideal (ι j) γβδ.1.1) = Ideal.span {g} from hg,
        Ideal.map_span, Set.image_singleton]
      rfl
    · exact (M.towerCenter ι κ).structureMap_preserves_nonzerodiv γβδ hgnzd
  · exact (M.towerCenter ι κ).structureMap_isCars_chart k γβδ

theorem tower_isCars_restrict {Lt : Type} (lam : Lt → M.indnumb)
    (hL : ∀ l, (∃ j, ι j = lam l) ∨ ∃ k, κ k = lam l) :
    IsCars (M.tower ι κ) (Clos.pullback (M.towerToX ι κ) (M.restrict lam).D) := by
  refine ⟨pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
      (pullback_PreClos X (M.restrict ι).dilatation (M.restrict ι).structureMap
        (M.restrict lam).Drep), ?_, ?_⟩
  · exact pullback_IsPreCars_of_charts _ _ _
      (fun l γβδ => M.tower_isCars_chart ι κ (lam l) (hL l) γβδ)
  · exact pullback_Clos_comp (M.restrict lam).D (M.restrict ι).structureMap
      (M.towerToBase ι κ)

theorem tower_isCars (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    IsCars (M.tower ι κ) (Clos.pullback (M.towerToX ι κ) M.D) :=
  M.tower_isCars_restrict ι κ id hIK

theorem tower_isCars_base :
    IsCars (M.tower ι κ) (Clos.pullback (M.towerToX ι κ) (M.restrict ι).D) :=
  M.tower_isCars_restrict ι κ ι (fun j => Or.inl ⟨j, rfl⟩)

end Cartier

section PullSubset

theorem towerCenter_pullSubset : (M.towerCenter ι κ).pullSubset (M.homToBase ι) := by
  intro k γβδ
  have h1 : (pull_cov (M.restrict ι).dilatation (M.towerCenter ι κ).Drep M.dilatation
        (M.homToBase ι)).map γβδ ≫ M.homToBase ι =
      Spec.map (pull_mor_ring (M.restrict ι).dilatation (M.towerCenter ι κ).Drep
          M.dilatation (M.homToBase ι) γβδ) ≫
        (pull_cov X M.Drep (M.restrict ι).dilatation
          (M.restrict ι).structureMap).map γβδ.1 :=
    pull_cov_map_comp (M.towerCenter ι κ).Drep (M.homToBase ι) γβδ
  have h2 : (pull_cov X M.Drep (M.restrict ι).dilatation
        (M.restrict ι).structureMap).map γβδ.1 ≫ (M.restrict ι).structureMap =
      Spec.map (pull_mor_ring X M.Drep (M.restrict ι).dilatation
        (M.restrict ι).structureMap γβδ.1) ≫ M.cov.map γβδ.1.1 :=
    pull_cov_map_comp M.Drep (M.restrict ι).structureMap γβδ.1
  have hcomm :
      (pull_cov (M.restrict ι).dilatation (M.towerCenter ι κ).Drep M.dilatation
        (M.homToBase ι)).map γβδ ≫ M.structureMap =
      Spec.map (pull_mor_ring X M.Drep (M.restrict ι).dilatation
          (M.restrict ι).structureMap γβδ.1 ≫
        pull_mor_ring (M.restrict ι).dilatation (M.towerCenter ι κ).Drep M.dilatation
          (M.homToBase ι) γβδ) ≫ M.cov.map γβδ.1.1 := by
    rw [Spec.map_comp, Category.assoc, ← h2, ← Category.assoc, ← h1, Category.assoc,
      M.homToBase_comp ι]
  have key := M.Yideal_le_Dideal_of_over_dilatation γβδ.1.1
    ((pull_cov (M.restrict ι).dilatation (M.towerCenter ι κ).Drep M.dilatation
      (M.homToBase ι)).map γβδ) _ hcomm (κ k)
  rw [CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.map_map] at key
  exact key

theorem pullSubset_of_split {T : Scheme.{u+1}} (f : T ⟶ X)
    (hJ : (M.restrict ι).pullSubset f) (hK : (M.restrict κ).pullSubset f)
    (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) : M.pullSubset f := by
  intro i γβ
  rcases hIK i with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · exact hJ j γβ
  · exact hK k γβ

theorem restrict_pullSubset_of_over {T : Scheme.{u+1}} (f : T ⟶ X)
    (g : T ⟶ (M.restrict ι).dilatation) (hg : g ≫ (M.restrict ι).structureMap = f) :
    (M.restrict ι).pullSubset f := by
  intro j γε
  have hcw : ((pull_cov X (M.restrict ι).Drep T f).map γε ≫ g) ≫
      (M.restrict ι).structureMap =
      Spec.map (pull_mor_ring X (M.restrict ι).Drep T f γε) ≫ M.cov.map γε.1 := by
    rw [Category.assoc, hg]
    exact pull_cov_map_comp (M.restrict ι).Drep f γε
  exact (M.restrict ι).Yideal_le_Dideal_of_over_dilatation γε.1
    ((pull_cov X (M.restrict ι).Drep T f).map γε ≫ g) _ hcw j

theorem tower_pullSubset_base : (M.restrict ι).pullSubset (M.towerToX ι κ) :=
  M.restrict_pullSubset_of_over ι (M.towerToX ι κ) (M.towerToBase ι κ) rfl

noncomputable def towerKRel :
    _root_.relStructure
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ)
        ((M.restrict κ).Yrep.inter (M.restrict κ).Drep (Equiv.refl _)))
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ) (M.restrict κ).Drep) :=
  (pullback_Pre_assoc' (M.tower ι κ) (M.restrict ι).dilatation
      (M.towerToBase ι κ) (M.restrict ι).structureMap
      ((M.restrict κ).Yrep.inter (M.restrict κ).Drep (Equiv.refl _))).trans
  ((pullback_lem (M.restrict ι).dilatation _ _ (M.tower ι κ) (M.towerToBase ι κ)
      (inter_pullback_rel (M.restrict κ).Yrep (M.restrict κ).Drep (Equiv.refl _)
        (M.restrict ι).dilatation (M.restrict ι).structureMap)).trans
  ((PreClos.relStructure_of_ideal_eq
      (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
        ((M.towerCenter ι κ).Yrep.inter (M.towerCenter ι κ).Drep (Equiv.refl _)))
      (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
        (M.towerCenter ι κ).Drep)
      (Equiv.refl _)
      (by
        intro k γβ
        have hmain := (M.towerCenter ι κ).structureMap_pull_inter_ideal_eq_D k γβ
        have h2 : (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ)
              (M.towerToBase ι κ) (M.towerCenter ι κ).Drep).reindexIdeal
              (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
                ((M.towerCenter ι κ).Yrep.inter (M.towerCenter ι κ).Drep (Equiv.refl _))).cov
              k γβ =
            (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ)
              (M.towerToBase ι κ) (M.towerCenter ι κ).Drep).ideal k γβ :=
          PreClos.reindexIdeal_self
            (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ)
              (M.towerToBase ι κ) (M.towerCenter ι κ).Drep) k γβ
        exact hmain.trans h2.symm)).trans
  (pullback_Pre_assoc' (M.tower ι κ) (M.restrict ι).dilatation
      (M.towerToBase ι κ) (M.restrict ι).structureMap (M.restrict κ).Drep).symm))

theorem tower_pullSubset_K : (M.restrict κ).pullSubset (M.towerToX ι κ) := by
  intro k γε
  have key := PreClos.ideal_eq_reindexIdeal _ _ (M.towerKRel ι κ) γε k
  have hself : (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ)
        (M.restrict κ).Drep).reindexIdeal
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ)
        ((M.restrict κ).Yrep.inter (M.restrict κ).Drep (Equiv.refl _))).cov
      ((M.towerKRel ι κ).indnumb_equiv k) γε =
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ) (M.restrict κ).Drep).ideal
        ((M.towerKRel ι κ).indnumb_equiv k) γε :=
    PreClos.reindexIdeal_self
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ) (M.restrict κ).Drep) _ γε
  rw [hself] at key
  have hek : (M.towerKRel ι κ).indnumb_equiv k = k := rfl
  rw [hek] at key
  have hexp : (M.restrict κ).Yrep.interIdeal (M.restrict κ).Drep (Equiv.refl _) k γε.1 =
      (M.restrict κ).Yrep.ideal k γε.1 ⊔ (M.restrict κ).Drep.ideal k γε.1 := by
    rw [(M.restrict κ).Yrep.interIdeal_eq (M.restrict κ).Drep (Equiv.refl _) k γε.1]
    congr 1
    exact PreClos.reindexIdeal_self (M.restrict κ).Drep k γε.1
  have key2 : Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
        (M.towerToX ι κ) γε).hom
        ((M.restrict κ).Yrep.ideal k γε.1 ⊔ (M.restrict κ).Drep.ideal k γε.1) =
      Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
        (M.towerToX ι κ) γε).hom ((M.restrict κ).Drep.ideal k γε.1) := by
    have : (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ)
        ((M.restrict κ).Yrep.inter (M.restrict κ).Drep (Equiv.refl _))).ideal k γε =
        Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
          (M.towerToX ι κ) γε).hom
          ((M.restrict κ).Yrep.interIdeal (M.restrict κ).Drep (Equiv.refl _) k γε.1) := rfl
    rw [← hexp]
    exact this.symm.trans key
  rw [Ideal.map_sup] at key2
  show Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
        (M.towerToX ι κ) γε).hom ((M.restrict κ).Yrep.ideal k γε.1) ≤
      Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
        (M.towerToX ι κ) γε).hom ((M.restrict κ).Drep.ideal k γε.1)
  exact le_trans le_sup_left key2.le

end PullSubset

section Comparison

theorem existsUnique_towerHom :
    ∃! a : M.dilatation ⟶ M.tower ι κ, a ≫ M.towerToBase ι κ = M.homToBase ι :=
  (M.towerCenter ι κ).universal_property M.dilatation (M.homToBase ι)
    (M.towerCenter_isCars ι κ) (M.towerCenter_pullSubset ι κ)

theorem existsUnique_towerInv (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    ∃! b : M.tower ι κ ⟶ M.dilatation, b ≫ M.structureMap = M.towerToX ι κ :=
  M.universal_property (M.tower ι κ) (M.towerToX ι κ) (M.tower_isCars ι κ hIK)
    (M.pullSubset_of_split ι κ (M.towerToX ι κ) (M.tower_pullSubset_base ι κ)
      (M.tower_pullSubset_K ι κ) hIK)

def towerHom : M.dilatation ⟶ M.tower ι κ :=
  (M.existsUnique_towerHom ι κ).choose

theorem towerHom_comp :
    M.towerHom ι κ ≫ M.towerToBase ι κ = M.homToBase ι :=
  (M.existsUnique_towerHom ι κ).choose_spec.1

theorem towerHom_over :
    M.towerHom ι κ ≫ M.towerToX ι κ = M.structureMap := by
  show M.towerHom ι κ ≫ M.towerToBase ι κ ≫ (M.restrict ι).structureMap = _
  rw [← Category.assoc, M.towerHom_comp ι κ, M.homToBase_comp ι]

def towerInv (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) : M.tower ι κ ⟶ M.dilatation :=
  (M.existsUnique_towerInv ι κ hIK).choose

theorem towerInv_over (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.towerInv ι κ hIK ≫ M.structureMap = M.towerToX ι κ :=
  (M.existsUnique_towerInv ι κ hIK).choose_spec.1

theorem towerInv_comp_homToBase (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.towerInv ι κ hIK ≫ M.homToBase ι = M.towerToBase ι κ := by
  have e₁ : (M.towerInv ι κ hIK ≫ M.homToBase ι) ≫ (M.restrict ι).structureMap =
      M.towerToX ι κ := by
    rw [Category.assoc, M.homToBase_comp ι, M.towerInv_over ι κ hIK]
  have e₂ : M.towerToBase ι κ ≫ (M.restrict ι).structureMap = M.towerToX ι κ := rfl
  exact ((M.restrict ι).universal_property (M.tower ι κ) (M.towerToX ι κ)
    (M.tower_isCars_base ι κ)
    (M.tower_pullSubset_base ι κ)).unique e₁ e₂

theorem towerHom_comp_towerInv
    (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.towerHom ι κ ≫ M.towerInv ι κ hIK = 𝟙 _ := by
  have e₁ : (M.towerHom ι κ ≫ M.towerInv ι κ hIK) ≫ M.structureMap =
      M.structureMap := by
    rw [Category.assoc, M.towerInv_over ι κ hIK, M.towerHom_over ι κ]
  have e₂ : 𝟙 M.dilatation ≫ M.structureMap = M.structureMap := Category.id_comp _
  exact (M.universal_property M.dilatation M.structureMap
    M.structureMap_isCars M.structureMap_pullSubset).unique e₁ e₂

theorem towerInv_comp_towerHom
    (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.towerInv ι κ hIK ≫ M.towerHom ι κ = 𝟙 _ := by
  have e₁ : (M.towerInv ι κ hIK ≫ M.towerHom ι κ) ≫ M.towerToBase ι κ =
      M.towerToBase ι κ := by
    rw [Category.assoc, M.towerHom_comp ι κ,
      M.towerInv_comp_homToBase ι κ hIK]
  have e₂ : 𝟙 (M.tower ι κ) ≫ M.towerToBase ι κ = M.towerToBase ι κ := Category.id_comp _
  exact ((M.towerCenter ι κ).universal_property (M.tower ι κ) (M.towerToBase ι κ)
    (M.towerCenter ι κ).structureMap_isCars
    (M.towerCenter ι κ).structureMap_pullSubset).unique e₁ e₂

def towerIso (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.dilatation ≅ M.tower ι κ where
  hom := M.towerHom ι κ
  inv := M.towerInv ι κ hIK
  hom_inv_id := M.towerHom_comp_towerInv ι κ hIK
  inv_hom_id := M.towerInv_comp_towerHom ι κ hIK

@[simp] theorem towerIso_hom_over
    (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    (M.towerIso ι κ hIK).hom ≫ M.towerToX ι κ = M.structureMap :=
  M.towerHom_over ι κ

theorem towerIso_unique (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i)
    (e : M.dilatation ⟶ M.tower ι κ) (he : e ≫ M.towerToX ι κ = M.structureMap) :
    e = (M.towerIso ι κ hIK).hom :=
  (M.existsUnique_towerHom ι κ).unique
    (M.homToBase_unique ι (e ≫ M.towerToBase ι κ) (by rw [Category.assoc]; exact he))
    (M.towerHom_comp ι κ)

end Comparison

end PreMultiCenter

end SchemeDilatation
