import ProjReindex
import Project.Blowups.Bl

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open GoodPotionIngredient HomogeneousSubmonoid

namespace BlMuOpen

variable {A : Type (u+1)} [CommRing A]
variable {ι : Type} [Fintype ι] (L : ι → Ideal A) [DecidableEq ι]
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

abbrev muSet : Set (GoodPotionIngredient (ReesAlgebra.intGrading L)) :=
  rangeSet (map_index L)

def leOfSet (S : Set (GoodPotionIngredient (ReesAlgebra.intGrading L))) :
    LE_ (𝒜 := ReesAlgebra.intGrading L) (Subtype.val : S → _) id where
  t := ⟨Subtype.val, Subtype.val_injective⟩
  comp := rfl

def blMuToBl : BlMu L ⟶ Bl L :=
  (projToRange (map_index L)) ≫ projHomOfLE (leOfSet L (muSet L))

instance : IsOpenImmersion (blMuToBl L) := by
  unfold blMuToBl
  haveI : IsIso (projToRange (map_index L)) := isIso_projToRange _
  infer_instance

@[simp] lemma leOfSet_potionEquivMap
    (S : Set (GoodPotionIngredient (ReesAlgebra.intGrading L))) (i : S) :
    (leOfSet L S).potionEquivMap i = RingEquiv.refl _ := by
  ext z
  induction z using Quotient.inductionOn' with | h z =>
  rfl

theorem blMuToBl_eq : blMuToBl L = BlMuToBl L := by
  apply Multicoequalizer.hom_ext
  intro P
  rw [blMuToBl, ← Category.assoc]
  erw [ι_comp_projToRange, projHomOfLE_comp_ι, leOfSet_potionEquivMap,
    Multicoequalizer.π_desc]
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _ = _
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rfl

instance : IsOpenImmersion (BlMuToBl L) := by
  rw [← blMuToBl_eq]
  infer_instance

theorem isIso_of_surjective (h : Function.Surjective (BlMuToBl L).base) :
    IsIso (BlMuToBl L) := by
  rw [AlgebraicGeometry.isIso_iff_isOpenImmersion]
  exact ⟨inferInstance, (TopCat.epi_iff_surjective _).2 h⟩

end BlMuOpen
