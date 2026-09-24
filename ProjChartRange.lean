import ChartCover
import ChartEq
import Project.Proj.Construction

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

universe u

open HomogeneousSubmonoid AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open GoodPotionIngredient

namespace ProjChartRange

variable {ι : Type} {τ R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]
variable (ℱ : τ → GoodPotionIngredient 𝒜)

theorem ι_mem_range_of_overlap (i j : τ)
    (q : Spec (CommRingCat.of ((ℱ i * ℱ j).Potion))) :
    (((glueData ℱ).f i j ≫ (glueData ℱ).ι i)).base q ∈
      Set.range ((glueData ℱ).ι j).base := by
  rw [← (glueData ℱ).glue_condition i j]
  exact ⟨_, rfl⟩

theorem ι_mem_range_of_potionToMul (i j : τ)
    (x : Spec (CommRingCat.of ((ℱ i).Potion)))
    (q : Spec (CommRingCat.of ((ℱ i * ℱ j).Potion)))
    (hq : (Spec.map (CommRingCat.ofHom
      ((ℱ i).toHomogeneousSubmonoid.potionToMul (ℱ j).toHomogeneousSubmonoid))).base q = x) :
    ((glueData ℱ).ι i).base x ∈ Set.range ((glueData ℱ).ι j).base := by
  subst hq
  have h1 := ι_mem_range_of_overlap ℱ i j q
  have h2 : ((glueData ℱ).f i j ≫ (glueData ℱ).ι i).base q =
      ((glueData ℱ).ι i).base ((Spec.map (CommRingCat.ofHom
        ((ℱ i).toHomogeneousSubmonoid.potionToMul (ℱ j).toHomogeneousSubmonoid))).base q) := by
    rfl
  rwa [h2] at h1

theorem range_subset_of_bar_eq (i j : τ)
    (h : (ℱ i).toHomogeneousSubmonoid.bar =
      ((ℱ i).toHomogeneousSubmonoid * (ℱ j).toHomogeneousSubmonoid).bar) :
    Set.range ((glueData ℱ).ι i).base ⊆ Set.range ((glueData ℱ).ι j).base := by
  rintro _ ⟨x, rfl⟩
  set e := ChartEq.potionMulEquiv (ℱ i).toHomogeneousSubmonoid
    (ℱ j).toHomogeneousSubmonoid h with he
  have hid : e.symm.toRingHom.comp ((ℱ i).toHomogeneousSubmonoid.potionToMul
      (ℱ j).toHomogeneousSubmonoid) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    exact e.symm_apply_apply z
  have hstep : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ (glueData ℱ).f i j = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((ℱ i).toHomogeneousSubmonoid.potionToMul
        (ℱ j).toHomogeneousSubmonoid)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id]
  have hcomp : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      ((glueData ℱ).f i j ≫ (glueData ℱ).ι i) = (glueData ℱ).ι i := by
    rw [← Category.assoc, hstep, Category.id_comp]
  have h1 := ι_mem_range_of_overlap ℱ i j
    ((Spec.map (CommRingCat.ofHom e.symm.toRingHom)).base x)
  have h2 : ((glueData ℱ).f i j ≫ (glueData ℱ).ι i).base
      ((Spec.map (CommRingCat.ofHom e.symm.toRingHom)).base x) =
      ((glueData ℱ).ι i).base x := by
    have h3 := congrArg (fun m : Spec (CommRingCat.of ((ℱ i).Potion)) ⟶ (glueData ℱ).glued =>
      m.base x) hcomp
    simpa using h3
  rwa [h2] at h1

theorem exists_chart_of_sum {κ : Type*} (S : GoodPotionIngredient 𝒜) {d : ι} {f : A}
    (hf : f ∈ 𝒜 d) (hfS : f ∈ S.toHomogeneousSubmonoid)
    (J : Finset κ) (G : κ → A) (hG : ∀ j : κ, G j ∈ 𝒜 d)
    (hsum : ∑ j ∈ J, G j = f)
    (hrel : ∀ j : κ, (ChartBar.gen (G j) ⟨d, hG j⟩).IsRelevant)
    (hfg : ∀ j : κ, (ChartBar.gen (G j) ⟨d, hG j⟩).toSubmonoid.FG)
    (x : Spec (CommRingCat.of (S.Potion))) :
    ∃ j ∈ J, ((glueData (id : GoodPotionIngredient 𝒜 → GoodPotionIngredient 𝒜)).ι S).base x ∈
      Set.range ((glueData (id : GoodPotionIngredient 𝒜 → GoodPotionIngredient 𝒜)).ι
        ⟨ChartBar.gen (G j) ⟨d, hG j⟩, hrel j, hfg j⟩).base := by
  classical
  obtain ⟨j, hjJ, q, hq, hqx⟩ :=
    ChartCover.exists_summand_comap_eq S.toHomogeneousSubmonoid hf hfS J G hG hsum
      x.asIdeal (hp := x.isPrime)
  refine ⟨j, hjJ, ?_⟩
  refine ι_mem_range_of_potionToMul (id : GoodPotionIngredient 𝒜 → GoodPotionIngredient 𝒜)
    S ⟨ChartBar.gen (G j) ⟨d, hG j⟩, hrel j, hfg j⟩ x ⟨q, hq⟩ ?_
  apply PrimeSpectrum.ext
  exact hqx

end ProjChartRange
