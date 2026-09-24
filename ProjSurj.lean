import ProjChartRange
import Project.Proj.OfLE

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

open HomogeneousSubmonoid AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open GoodPotionIngredient

namespace ProjSurj

variable {ι : Type} {R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

def leOfSet (𝒢 : Set (GoodPotionIngredient 𝒜)) :
    LE_ (Subtype.val : 𝒢 → GoodPotionIngredient 𝒜)
      (id : GoodPotionIngredient 𝒜 → GoodPotionIngredient 𝒜) where
  t := ⟨Subtype.val, Subtype.val_injective⟩
  comp := rfl

@[simp] theorem leOfSet_potionEquivMap (𝒢 : Set (GoodPotionIngredient 𝒜)) (i : 𝒢) :
    (leOfSet 𝒢).potionEquivMap i = RingEquiv.refl _ := by
  ext z
  induction z using Quotient.inductionOn' with | h z => rfl

theorem range_ι_subset (𝒢 : Set (GoodPotionIngredient 𝒜)) (T : GoodPotionIngredient 𝒜)
    (hT : T ∈ 𝒢) :
    Set.range ((glueData (id : GoodPotionIngredient 𝒜 → _)).ι T).base ⊆
      Set.range (projHomOfLE (leOfSet 𝒢)).base := by
  rintro _ ⟨y, rfl⟩
  refine ⟨((glueData (Subtype.val : 𝒢 → _)).ι ⟨T, hT⟩).base y, ?_⟩
  rw [projHomOfLE_comp_ι_base_apply, leOfSet_potionEquivMap]
  simp only [RingEquiv.toRingHom_refl, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem surjective_of_covering (𝒢 : Set (GoodPotionIngredient 𝒜))
    (hcov : ∀ (S : GoodPotionIngredient 𝒜) (x : Spec (CommRingCat.of (S.Potion))),
      ∃ T ∈ 𝒢, ((glueData (id : GoodPotionIngredient 𝒜 → _)).ι S).base x ∈
        Set.range ((glueData (id : GoodPotionIngredient 𝒜 → _)).ι T).base) :
    Function.Surjective (projHomOfLE (leOfSet 𝒢)).base := by
  intro p
  obtain ⟨S, x, rfl⟩ := (glueData (id : GoodPotionIngredient 𝒜 → _)).ι_jointly_surjective p
  obtain ⟨T, hT, hmem⟩ := hcov S x
  exact range_ι_subset 𝒢 T hT hmem

end ProjSurj
