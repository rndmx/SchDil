import ProjAwayIngredient
import ProjOverlap
import ProjGlueCompat
import Project.Proj.OfLE

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousLocalization HomogeneousSubmonoid
open ProjComparison ProjGlueCompat ProjOverlap
open GoodPotionIngredient

namespace ProjIsoC

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem toRingHom_awayMulEquivPotionMul {f g : A} {m n : ℕ} (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 n)
    (S T : HomogeneousSubmonoid (intGrading 𝒜))
    (hS : S.toSubmonoid = Submonoid.powers f)
    (hT : T.toSubmonoid = Submonoid.powers g)
    (hle : Submonoid.powers (f * g) ≤ (S * T).toSubmonoid) :
    (awayMulEquivPotionMul 𝒜 hf hg S T hS hT).toRingHom =
      awayToPotion 𝒜 (f * g) (S * T) hle := by
  refine ringHom_ext_val fun z => ?_
  obtain ⟨y, rfl⟩ := mk_surjective z
  rfl

theorem potionEquiv_comp_awayToPotion (f : A) (U U' : HomogeneousSubmonoid (intGrading 𝒜))
    (eq : U = U') (h : Submonoid.powers f ≤ U.toSubmonoid)
    (h' : Submonoid.powers f ≤ U'.toSubmonoid) :
    (potionEquiv eq).toRingHom.comp (awayToPotion 𝒜 f U h) = awayToPotion 𝒜 f U' h' := by
  subst eq
  refine ringHom_ext_val fun z => ?_
  obtain ⟨y, rfl⟩ := mk_surjective z
  rfl

abbrev Idx : Type u := Σ i : ℕ+, 𝒜 (i : ℕ)

def elt (j : Idx 𝒜) : A := (j.2 : A)

theorem elt_mem (j : Idx 𝒜) : elt 𝒜 j ∈ 𝒜 (j.1 : ℕ) := j.2.2
theorem elt_pos (j : Idx 𝒜) : 0 < (j.1 : ℕ) := j.1.2

theorem eltMul_mem (i j : Idx 𝒜) :
    elt 𝒜 i * elt 𝒜 j ∈ 𝒜 ((i.1 : ℕ) + (j.1 : ℕ)) :=
  SetLike.mul_mem_graded (elt_mem 𝒜 i) (elt_mem 𝒜 j)

theorem eltMul_pos (i j : Idx 𝒜) : 0 < (i.1 : ℕ) + (j.1 : ℕ) :=
  Nat.lt_of_lt_of_le (elt_pos 𝒜 i) (Nat.le_add_right _ _)

def fam (j : Idx 𝒜) : GoodPotionIngredient (intGrading 𝒜) :=
  awayIngredient 𝒜 (elt_mem 𝒜 j) (elt_pos 𝒜 j)

theorem fam_toSubmonoid (j : Idx 𝒜) :
    (fam 𝒜 j).toSubmonoid = Submonoid.powers (elt 𝒜 j) :=
  awayIngredient_toSubmonoid 𝒜 (elt_mem 𝒜 j) (elt_pos 𝒜 j)

theorem famMul_toSubmonoid (i j : Idx 𝒜) :
    (fam 𝒜 i * fam 𝒜 j).toSubmonoid =
      Submonoid.powers (elt 𝒜 i) * Submonoid.powers (elt 𝒜 j) := by
  rw [GoodPotionIngredient.mul_toHomogeneousSubmonoid,
    HomogeneousSubmonoid.mul_toSubmonoid, fam_toSubmonoid, fam_toSubmonoid]

theorem powers_le_left (i j : Idx 𝒜) :
    Submonoid.powers (elt 𝒜 i) ≤ (fam 𝒜 i * fam 𝒜 j).toSubmonoid := by
  rw [famMul_toSubmonoid]
  intro x hx
  exact Submonoid.mem_mul_iff.mpr ⟨x, hx, 1, one_mem _, mul_one x⟩

theorem powers_le_right (i j : Idx 𝒜) :
    Submonoid.powers (elt 𝒜 j) ≤ (fam 𝒜 i * fam 𝒜 j).toSubmonoid := by
  rw [famMul_toSubmonoid]
  intro x hx
  exact Submonoid.mem_mul_iff.mpr ⟨1, one_mem _, x, hx, one_mul x⟩

theorem powers_mul_le (i j : Idx 𝒜) :
    Submonoid.powers (elt 𝒜 i * elt 𝒜 j) ≤ (fam 𝒜 i * fam 𝒜 j).toSubmonoid := by
  rw [famMul_toSubmonoid]
  exact powers_mul_le_mul

def chartEquiv (j : Idx 𝒜) : Away 𝒜 (elt 𝒜 j) ≃+* (fam 𝒜 j).Potion :=
  awayEquivPotion 𝒜 (elt 𝒜 j) (fam 𝒜 j).toHomogeneousSubmonoid (fam_toSubmonoid 𝒜 j)

def mulEquiv (i j : Idx 𝒜) :
    Away 𝒜 (elt 𝒜 i * elt 𝒜 j) ≃+* (fam 𝒜 i * fam 𝒜 j).Potion :=
  awayMulEquivPotionMul 𝒜 (elt_mem 𝒜 i) (elt_mem 𝒜 j)
    (fam 𝒜 i).toHomogeneousSubmonoid (fam 𝒜 j).toHomogeneousSubmonoid
    (fam_toSubmonoid 𝒜 i) (fam_toSubmonoid 𝒜 j)

theorem toRingHom_mulEquiv (i j : Idx 𝒜) :
    (mulEquiv 𝒜 i j).toRingHom =
      awayToPotion 𝒜 (elt 𝒜 i * elt 𝒜 j) (fam 𝒜 i * fam 𝒜 j).toHomogeneousSubmonoid
        (powers_mul_le 𝒜 i j) :=
  toRingHom_awayMulEquivPotionMul 𝒜 _ _ _ _ _ _ (powers_mul_le 𝒜 i j)

theorem toRingHom_chartEquiv (j : Idx 𝒜) :
    (chartEquiv 𝒜 j).toRingHom =
      awayToPotion 𝒜 (elt 𝒜 j) (fam 𝒜 j).toHomogeneousSubmonoid
        (le_of_eq (fam_toSubmonoid 𝒜 j).symm) :=
  awayEquivPotion_eq_awayToPotion 𝒜 _ _ _

theorem key1 (i j : Idx 𝒜) :
    (mulEquiv 𝒜 i j).toRingHom.comp
        (awayMap 𝒜 (elt_mem 𝒜 j) (rfl : elt 𝒜 i * elt 𝒜 j = elt 𝒜 i * elt 𝒜 j)) =
      ((fam 𝒜 i).potionToMul (fam 𝒜 j).toHomogeneousSubmonoid).comp
        (chartEquiv 𝒜 i).toRingHom := by
  rw [toRingHom_mulEquiv, toRingHom_chartEquiv,
    awayToPotion_comp_awayMap 𝒜 (elt_mem 𝒜 j) rfl _ (powers_le_left 𝒜 i j),
    potionToMul_comp_awayToPotion]
  rfl

theorem key2 (i j : Idx 𝒜) :
    (mulEquiv 𝒜 i j).toRingHom.comp
        (awayMap 𝒜 (elt_mem 𝒜 i) (mul_comm (elt 𝒜 i) (elt 𝒜 j))) =
      (potionEquiv (mul_comm (fam 𝒜 j).toHomogeneousSubmonoid
          (fam 𝒜 i).toHomogeneousSubmonoid)).toRingHom.comp
        (((fam 𝒜 j).potionToMul (fam 𝒜 i).toHomogeneousSubmonoid).comp
          (chartEquiv 𝒜 j).toRingHom) := by
  rw [toRingHom_mulEquiv, toRingHom_chartEquiv,
    awayToPotion_comp_awayMap 𝒜 (elt_mem 𝒜 i) (mul_comm (elt 𝒜 i) (elt 𝒜 j)) _
      (powers_le_right 𝒜 i j),
    potionToMul_comp_awayToPotion,
    potionEquiv_comp_awayToPotion 𝒜 (elt 𝒜 j) _ _ _ _ (powers_le_right 𝒜 i j)]

def specIso {B C : Type u} [CommRing B] [CommRing C] (e : B ≃+* C) :
    Spec (CommRingCat.of C) ≅ Spec (CommRingCat.of B) where
  hom := Spec.map (CommRingCat.ofHom e.toRingHom)
  inv := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from
        RingHom.ext fun a => e.apply_symm_apply a]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show e.symm.toRingHom.comp e.toRingHom = RingHom.id _ from
        RingHom.ext fun a => e.symm_apply_apply a]
    exact Spec.map_id _

@[simp] theorem specIso_hom {B C : Type u} [CommRing B] [CommRing C] (e : B ≃+* C) :
    (specIso e).hom = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

def chartIso (j : Idx 𝒜) :
    Spec (CommRingCat.of ((fam 𝒜 j).Potion)) ≅
      Spec (CommRingCat.of (Away 𝒜 (elt 𝒜 j))) :=
  specIso (chartEquiv 𝒜 j)

def mulIso (i j : Idx 𝒜) :
    Spec (CommRingCat.of ((fam 𝒜 i * fam 𝒜 j).Potion)) ≅
      Spec (CommRingCat.of (Away 𝒜 (elt 𝒜 i * elt 𝒜 j))) :=
  specIso (mulEquiv 𝒜 i j)

theorem specSquare_left (i j : Idx 𝒜) :
    (glueData (fam 𝒜)).f i j ≫ (chartIso 𝒜 i).hom =
      (mulIso 𝒜 i j).hom ≫
        Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 j)
          (rfl : elt 𝒜 i * elt 𝒜 j = elt 𝒜 i * elt 𝒜 j))) := by
  simp only [glueData_f, chartIso, mulIso, specIso_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [key1]

theorem specSquare_right (i j : Idx 𝒜) :
    ((glueData (fam 𝒜)).t i j ≫ (glueData (fam 𝒜)).f j i) ≫ (chartIso 𝒜 j).hom =
      (mulIso 𝒜 i j).hom ≫
        Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 i)
          (mul_comm (elt 𝒜 i) (elt 𝒜 j)))) := by
  simp only [glueData_f, glueData_t, chartIso, mulIso, specIso_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [key2, RingHom.comp_assoc]

def chart (j : Idx 𝒜) :
    Spec (CommRingCat.of ((fam 𝒜 j).Potion)) ⟶ AlgebraicGeometry.Proj 𝒜 :=
  (chartIso 𝒜 j).hom ≫ Proj.awayι 𝒜 (elt 𝒜 j) (elt_mem 𝒜 j) (elt_pos 𝒜 j)

theorem chart_left (i j : Idx 𝒜) :
    (glueData (fam 𝒜)).f i j ≫ chart 𝒜 i =
      (mulIso 𝒜 i j).hom ≫
        Proj.awayι 𝒜 (elt 𝒜 i * elt 𝒜 j) (eltMul_mem 𝒜 i j) (eltMul_pos 𝒜 i j) := by
  rw [chart, ← Category.assoc, specSquare_left, Category.assoc,
    Proj.SpecMap_awayMap_awayι]

theorem chart_right (i j : Idx 𝒜) :
    ((glueData (fam 𝒜)).t i j ≫ (glueData (fam 𝒜)).f j i) ≫ chart 𝒜 j =
      (mulIso 𝒜 i j).hom ≫
        Proj.awayι 𝒜 (elt 𝒜 i * elt 𝒜 j) (eltMul_mem 𝒜 i j) (eltMul_pos 𝒜 i j) := by
  rw [chart, ← Category.assoc, specSquare_right, Category.assoc,
    Proj.SpecMap_awayMap_awayι]
  rfl

def toProj : GoodPotionIngredient.Proj (fam 𝒜) ⟶ AlgebraicGeometry.Proj 𝒜 :=
  Multicoequalizer.desc _ _ (chart 𝒜) <| by
    rintro ⟨i, j⟩
    show (glueData (fam 𝒜)).f i j ≫ chart 𝒜 i =
      ((glueData (fam 𝒜)).t i j ≫ (glueData (fam 𝒜)).f j i) ≫ chart 𝒜 j
    rw [chart_left, chart_right]

@[reassoc]
theorem ι_toProj (j : Idx 𝒜) :
    (glueData (fam 𝒜)).ι j ≫ toProj 𝒜 = chart 𝒜 j := by
  erw [Multicoequalizer.π_desc]

def cover : (AlgebraicGeometry.Proj 𝒜).OpenCover := (Proj.affineOpenCover 𝒜).openCover

theorem cover_map (j : Idx 𝒜) :
    (cover 𝒜).map j = Proj.awayι 𝒜 (elt 𝒜 j) (elt_mem 𝒜 j) (elt_pos 𝒜 j) := rfl

theorem cover_obj (j : Idx 𝒜) :
    (cover 𝒜).obj j = Spec (CommRingCat.of (Away 𝒜 (elt 𝒜 j))) := rfl

@[reassoc]
theorem awayMapLeft_chartIso_inv (i j : Idx 𝒜) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 j)
        (rfl : elt 𝒜 i * elt 𝒜 j = elt 𝒜 i * elt 𝒜 j))) ≫ (chartIso 𝒜 i).inv =
      (mulIso 𝒜 i j).inv ≫ (glueData (fam 𝒜)).f i j := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← specSquare_left, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

@[reassoc]
theorem awayMapRight_chartIso_inv (i j : Idx 𝒜) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 i)
        (mul_comm (elt 𝒜 i) (elt 𝒜 j)))) ≫ (chartIso 𝒜 j).inv =
      (mulIso 𝒜 i j).inv ≫ ((glueData (fam 𝒜)).t i j ≫ (glueData (fam 𝒜)).f j i) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← specSquare_right, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

def descFrom : (cover 𝒜).gluedCover.glued ⟶ GoodPotionIngredient.Proj (fam 𝒜) :=
  Multicoequalizer.desc _ _
    (fun j => (chartIso 𝒜 j).inv ≫ (glueData (fam 𝒜)).ι j) <| by
    rintro ⟨i, j⟩
    show pullback.fst (Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (elt_pos 𝒜 i))
          (Proj.awayι 𝒜 (elt 𝒜 j) (elt_mem 𝒜 j) (elt_pos 𝒜 j)) ≫
        ((chartIso 𝒜 i).inv ≫ (glueData (fam 𝒜)).ι i) =
      ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫
        ((chartIso 𝒜 j).inv ≫ (glueData (fam 𝒜)).ι j)
    rw [pullbackSymmetry_hom_comp_fst,
      ← cancel_epi (Proj.pullbackAwayιIso 𝒜 (elt_mem 𝒜 i) (elt_pos 𝒜 i)
        (elt_mem 𝒜 j) (elt_pos 𝒜 j) (rfl : elt 𝒜 i * elt 𝒜 j = elt 𝒜 i * elt 𝒜 j)).inv,
      Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc,
      awayMapLeft_chartIso_inv_assoc, awayMapRight_chartIso_inv_assoc,
      (glueData (fam 𝒜)).glue_condition i j]

@[reassoc]
theorem ι_descFrom (j : Idx 𝒜) :
    (cover 𝒜).gluedCover.ι j ≫ descFrom 𝒜 =
      (chartIso 𝒜 j).inv ≫ (glueData (fam 𝒜)).ι j := by
  erw [Multicoequalizer.π_desc]

@[reassoc]
theorem awayι_inv_fromGlued (j : Idx 𝒜) :
    Proj.awayι 𝒜 (elt 𝒜 j) (elt_mem 𝒜 j) (elt_pos 𝒜 j) ≫ inv (cover 𝒜).fromGlued =
      (cover 𝒜).gluedCover.ι j := by
  rw [← cover_map, ← Scheme.Cover.ι_fromGlued, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

def fromProj : AlgebraicGeometry.Proj 𝒜 ⟶ GoodPotionIngredient.Proj (fam 𝒜) :=
  inv (cover 𝒜).fromGlued ≫ descFrom 𝒜

theorem toProj_fromProj : toProj 𝒜 ≫ fromProj 𝒜 = 𝟙 _ := by
  refine Multicoequalizer.hom_ext _ _ _ fun j => ?_
  show ((glueData (fam 𝒜)).ι j ≫ toProj 𝒜) ≫ fromProj 𝒜 = (glueData (fam 𝒜)).ι j ≫ 𝟙 _
  rw [ι_toProj, Category.comp_id, chart, fromProj, Category.assoc,
    awayι_inv_fromGlued_assoc, ι_descFrom, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]

theorem fromProj_toProj : fromProj 𝒜 ≫ toProj 𝒜 = 𝟙 _ := by
  rw [← cancel_epi (cover 𝒜).fromGlued, fromProj, Category.assoc, IsIso.hom_inv_id_assoc,
    Category.comp_id]
  refine Multicoequalizer.hom_ext _ _ _ fun j => ?_
  show ((cover 𝒜).gluedCover.ι j ≫ descFrom 𝒜) ≫ toProj 𝒜 =
    (cover 𝒜).gluedCover.ι j ≫ (cover 𝒜).fromGlued
  rw [ι_descFrom, Category.assoc, ι_toProj, chart, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, Scheme.Cover.ι_fromGlued, cover_map]

instance isIso_toProj : IsIso (toProj 𝒜) :=
  ⟨fromProj 𝒜, toProj_fromProj 𝒜, fromProj_toProj 𝒜⟩

def projIso : AlgebraicGeometry.Proj 𝒜 ≅ GoodPotionIngredient.Proj (fam 𝒜) :=
  (asIso (toProj 𝒜)).symm

@[simp] theorem projIso_inv : (projIso 𝒜).inv = toProj 𝒜 := rfl

@[simp] theorem projIso_hom : (projIso 𝒜).hom = fromProj 𝒜 := by
  rw [← cancel_mono (projIso 𝒜).inv, Iso.hom_inv_id]
  exact (fromProj_toProj 𝒜).symm

end ProjIsoC
