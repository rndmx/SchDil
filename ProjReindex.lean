import Project.Proj.OfLE

suppress_compilation

set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace Topology
open HomogeneousSubmonoid

universe u

namespace GoodPotionIngredient

variable {ι : Type} {τ R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ℱ : τ → GoodPotionIngredient 𝒜)

abbrev rangeSet : Set (GoodPotionIngredient 𝒜) := Set.range ℱ

def rangeIdx (i : τ) : rangeSet ℱ := ⟨ℱ i, ⟨i, rfl⟩⟩

def projToRange : Proj ℱ ⟶ Proj (τ := rangeSet ℱ) Subtype.val :=
  Multicoequalizer.desc _ _
    (fun i ↦ (glueData (τ := rangeSet ℱ) Subtype.val).ι (rangeIdx ℱ i)) <| by
    rintro ⟨i, j⟩
    show (glueData ℱ).f i j ≫ _ = ((glueData ℱ).t i j ≫ (glueData ℱ).f j i) ≫ _
    rw [Category.assoc]
    exact ((glueData (τ := rangeSet ℱ) Subtype.val).glue_condition
      (rangeIdx ℱ i) (rangeIdx ℱ j)).symm

noncomputable def rangeSection (s : rangeSet ℱ) : τ := s.2.choose

@[simp]
lemma rangeSection_spec (s : rangeSet ℱ) : ℱ (rangeSection ℱ s) = (s : GoodPotionIngredient 𝒜) :=
  s.2.choose_spec

lemma rangeSection_injective : Function.Injective (rangeSection ℱ) := by
  intro a b h
  apply Subtype.ext
  rw [← rangeSection_spec ℱ a, ← rangeSection_spec ℱ b, h]

def leOfRange : LE_ (𝒜 := 𝒜) (τ := rangeSet ℱ) (τ' := τ) Subtype.val ℱ where
  t := ⟨rangeSection ℱ, rangeSection_injective ℱ⟩
  comp := funext fun s ↦ rangeSection_spec ℱ s

@[simp]
lemma leOfRange_apply (s : rangeSet ℱ) : leOfRange ℱ s = rangeSection ℱ s := rfl

def projFromRange : Proj (τ := rangeSet ℱ) Subtype.val ⟶ Proj ℱ :=
  projHomOfLE (leOfRange ℱ)

instance : IsOpenImmersion (projFromRange ℱ) := projHomOfLE_isOpenImmersion _

@[reassoc (attr := simp)]
lemma ι_comp_projToRange (i : τ) :
    (glueData ℱ).ι i ≫ projToRange ℱ =
    (glueData (τ := rangeSet ℱ) Subtype.val).ι (rangeIdx ℱ i) := by
  erw [Multicoequalizer.π_desc]

lemma rangeSection_rangeIdx (i : τ) : ℱ (rangeSection ℱ (rangeIdx ℱ i)) = ℱ i :=
  rangeSection_spec ℱ (rangeIdx ℱ i)

lemma rangeSection_rangeIdx_le (i : τ) :
    (ℱ (rangeSection ℱ (rangeIdx ℱ i))).toHomogeneousSubmonoid ≤
      (ℱ i).toHomogeneousSubmonoid := by
  rw [rangeSection_rangeIdx ℱ i]

lemma projToRange_comp_projFromRange : projToRange ℱ ≫ projFromRange ℱ = 𝟙 _ := by
  refine Multicoequalizer.hom_ext _ _ _ fun i ↦ ?_
  show ((glueData ℱ).ι i ≫ projToRange ℱ) ≫ projFromRange ℱ = (glueData ℱ).ι i ≫ 𝟙 _
  rw [ι_comp_projToRange, projFromRange, projHomOfLE_comp_ι, Category.comp_id]
  rw [proj_glue_condition ℱ _ i (rangeSection_rangeIdx_le ℱ i)]
  congr 2

lemma projFromRange_comp_projToRange : projFromRange ℱ ≫ projToRange ℱ = 𝟙 _ := by
  have h : (projFromRange ℱ ≫ projToRange ℱ) ≫ projFromRange ℱ = 𝟙 _ ≫ projFromRange ℱ := by
    rw [Category.assoc, projToRange_comp_projFromRange, Category.comp_id, Category.id_comp]
  exact (cancel_mono (projFromRange ℱ)).1 h

instance isIso_projToRange : IsIso (projToRange ℱ) :=
  ⟨projFromRange ℱ, projToRange_comp_projFromRange ℱ, projFromRange_comp_projToRange ℱ⟩

instance isIso_projFromRange : IsIso (projFromRange ℱ) :=
  ⟨projToRange ℱ, projFromRange_comp_projToRange ℱ, projToRange_comp_projFromRange ℱ⟩

def projRangeIso : Proj ℱ ≅ Proj (τ := rangeSet ℱ) Subtype.val :=
  asIso (projToRange ℱ)

@[simp] lemma projRangeIso_hom : (projRangeIso ℱ).hom = projToRange ℱ := rfl

@[simp] lemma projRangeIso_inv : (projRangeIso ℱ).inv = projFromRange ℱ := by
  rw [← cancel_epi (projRangeIso ℱ).hom, Iso.hom_inv_id]
  exact (projToRange_comp_projFromRange ℱ).symm

end GoodPotionIngredient
