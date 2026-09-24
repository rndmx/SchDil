import ProjAwayIngredient
import ProjOverlap
import ProjGlueCompat
import Mathlib.AlgebraicGeometry.Gluing

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousLocalization HomogeneousSubmonoid
open ProjComparison ProjOverlap ProjGlueCompat

namespace ProjIsoB

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

abbrev Idx := Σ i : ℕ+, 𝒜 (i : ℕ)

def elt (i : Idx 𝒜) : A := i.2.1

theorem elt_mem (i : Idx 𝒜) : elt 𝒜 i ∈ 𝒜 (i.1 : ℕ) := i.2.2

theorem deg_pos (i : Idx 𝒜) : 0 < (i.1 : ℕ) := i.1.2

noncomputable def fam (i : Idx 𝒜) : GoodPotionIngredient (intGrading 𝒜) :=
  awayIngredient 𝒜 (elt_mem 𝒜 i) (deg_pos 𝒜 i)

@[simp] theorem fam_toSubmonoid (i : Idx 𝒜) :
    (fam 𝒜 i).toSubmonoid = Submonoid.powers (elt 𝒜 i) :=
  awayIngredient_toSubmonoid 𝒜 _ _

theorem mul_fam_toSubmonoid (i j : Idx 𝒜) :
    (fam 𝒜 i * fam 𝒜 j).toSubmonoid =
      Submonoid.powers (elt 𝒜 i) * Submonoid.powers (elt 𝒜 j) := by
  show ((fam 𝒜 i).toHomogeneousSubmonoid * (fam 𝒜 j).toHomogeneousSubmonoid).toSubmonoid = _
  rw [HomogeneousSubmonoid.mul_toSubmonoid, fam_toSubmonoid, fam_toSubmonoid]

theorem awayι_congr {f : A} {m m' : ℕ} (h : f ∈ 𝒜 m) (hm : 0 < m)
    (h' : f ∈ 𝒜 m') (hm' : 0 < m') :
    Proj.awayι 𝒜 f h hm = Proj.awayι 𝒜 f h' hm' := rfl

theorem affineOpenCover_obj (i : Idx 𝒜) :
    (Proj.affineOpenCover 𝒜).openCover.obj i =
      Spec (CommRingCat.of (Away 𝒜 (elt 𝒜 i))) := rfl

theorem affineOpenCover_map (i : Idx 𝒜) :
    (Proj.affineOpenCover 𝒜).openCover.map i =
      Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (deg_pos 𝒜 i) := rfl

theorem powers_le_mulFam (i j : Idx 𝒜) :
    Submonoid.powers (elt 𝒜 i * elt 𝒜 j) ≤ (fam 𝒜 i * fam 𝒜 j).toSubmonoid := by
  rw [mul_fam_toSubmonoid]
  exact powers_mul_le_mul

theorem powers_le_mulFam' (i j : Idx 𝒜) :
    Submonoid.powers (elt 𝒜 i * elt 𝒜 j) ≤ (fam 𝒜 j * fam 𝒜 i).toSubmonoid := by
  rw [mul_fam_toSubmonoid, mul_comm (elt 𝒜 i)]
  exact powers_mul_le_mul

theorem mulFam_comm (i j : Idx 𝒜) :
    (fam 𝒜 j * fam 𝒜 i).toHomogeneousSubmonoid =
      (fam 𝒜 i * fam 𝒜 j).toHomogeneousSubmonoid :=
  mul_comm _ _

noncomputable def chartHom (i : Idx 𝒜) : Away 𝒜 (elt 𝒜 i) →+* (fam 𝒜 i).Potion :=
  awayToPotion 𝒜 (elt 𝒜 i) (fam 𝒜 i).toHomogeneousSubmonoid
    (le_of_eq (fam_toSubmonoid 𝒜 i).symm)

theorem chartHom_bijective (i : Idx 𝒜) : Function.Bijective (chartHom 𝒜 i) := by
  have h : (awayEquivPotion 𝒜 (elt 𝒜 i) (fam 𝒜 i).toHomogeneousSubmonoid
      (fam_toSubmonoid 𝒜 i)).toRingHom = chartHom 𝒜 i :=
    awayEquivPotion_eq_awayToPotion 𝒜 _ _ _
  rw [← h]
  exact (awayEquivPotion 𝒜 (elt 𝒜 i) (fam 𝒜 i).toHomogeneousSubmonoid
    (fam_toSubmonoid 𝒜 i)).bijective

noncomputable def ovHom (i j : Idx 𝒜) :
    Away 𝒜 (elt 𝒜 i * elt 𝒜 j) →+* (fam 𝒜 i * fam 𝒜 j).Potion :=
  awayToPotion 𝒜 (elt 𝒜 i * elt 𝒜 j) (fam 𝒜 i * fam 𝒜 j).toHomogeneousSubmonoid
    (powers_le_mulFam 𝒜 i j)

noncomputable def ovHomSwap (i j : Idx 𝒜) :
    Away 𝒜 (elt 𝒜 i * elt 𝒜 j) →+* (fam 𝒜 j * fam 𝒜 i).Potion :=
  awayToPotion 𝒜 (elt 𝒜 i * elt 𝒜 j) (fam 𝒜 j * fam 𝒜 i).toHomogeneousSubmonoid
    (powers_le_mulFam' 𝒜 i j)

theorem ovHom_eq (i j : Idx 𝒜) :
    (awayMulEquivPotionMul 𝒜 (elt_mem 𝒜 i) (elt_mem 𝒜 j)
      (fam 𝒜 i).toHomogeneousSubmonoid (fam 𝒜 j).toHomogeneousSubmonoid
      (fam_toSubmonoid 𝒜 i) (fam_toSubmonoid 𝒜 j)).toRingHom = ovHom 𝒜 i j := by
  refine ringHom_ext_val fun z => ?_
  obtain ⟨y, rfl⟩ := mk_surjective z
  rfl

theorem ovHom_bijective (i j : Idx 𝒜) : Function.Bijective (ovHom 𝒜 i j) := by
  rw [← ovHom_eq]
  exact (awayMulEquivPotionMul 𝒜 (elt_mem 𝒜 i) (elt_mem 𝒜 j)
      (fam 𝒜 i).toHomogeneousSubmonoid (fam 𝒜 j).toHomogeneousSubmonoid
      (fam_toSubmonoid 𝒜 i) (fam_toSubmonoid 𝒜 j)).bijective

theorem awayToPotion_congr {x : A} {S T : HomogeneousSubmonoid (intGrading 𝒜)}
    (e : S = T) (h : Submonoid.powers x ≤ S.toSubmonoid)
    (h' : Submonoid.powers x ≤ T.toSubmonoid) :
    (potionEquiv e).toRingHom.comp (awayToPotion 𝒜 x S h) = awayToPotion 𝒜 x T h' := by
  subst e
  simp

theorem potionEquiv_ovHomSwap (i j : Idx 𝒜) :
    (potionEquiv (mulFam_comm 𝒜 i j)).toRingHom.comp (ovHomSwap 𝒜 i j) = ovHom 𝒜 i j :=
  awayToPotion_congr 𝒜 _ _ _

theorem ovHomSwap_eq (i j : Idx 𝒜) :
    ovHomSwap 𝒜 i j =
      ((potionEquiv (mulFam_comm 𝒜 i j)).symm.toRingHom).comp (ovHom 𝒜 i j) := by
  refine RingHom.ext fun z => ?_
  have h := congrArg (fun F => F z) (potionEquiv_ovHomSwap 𝒜 i j)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe] at h ⊢
  rw [← h, RingEquiv.symm_apply_apply]

theorem ovHomSwap_bijective (i j : Idx 𝒜) : Function.Bijective (ovHomSwap 𝒜 i j) := by
  simp only [ovHomSwap_eq, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact Function.Bijective.comp (potionEquiv (mulFam_comm 𝒜 i j)).symm.bijective
    (ovHom_bijective 𝒜 i j)

noncomputable def specIsoOfBijective {B C : Type u} [CommRing B] [CommRing C]
    (φ : B →+* C) (hφ : Function.Bijective φ) :
    Spec (CommRingCat.of C) ≅ Spec (CommRingCat.of B) where
  hom := Spec.map (CommRingCat.ofHom φ)
  inv := Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective φ hφ).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show φ.comp (RingEquiv.ofBijective φ hφ).symm.toRingHom = RingHom.id _ from
        RingHom.ext fun a => (RingEquiv.ofBijective φ hφ).apply_symm_apply a]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (RingEquiv.ofBijective φ hφ).symm.toRingHom.comp φ = RingHom.id _ from
        RingHom.ext fun a => (RingEquiv.ofBijective φ hφ).symm_apply_apply a]
    exact Spec.map_id _

noncomputable def chartIso (i : Idx 𝒜) :
    Spec (CommRingCat.of ((fam 𝒜 i).Potion)) ≅
      Spec (CommRingCat.of (Away 𝒜 (elt 𝒜 i))) :=
  specIsoOfBijective (chartHom 𝒜 i) (chartHom_bijective 𝒜 i)

noncomputable def ovIso (i j : Idx 𝒜) :
    Spec (CommRingCat.of ((fam 𝒜 i * fam 𝒜 j).Potion)) ≅
      Spec (CommRingCat.of (Away 𝒜 (elt 𝒜 i * elt 𝒜 j))) :=
  specIsoOfBijective (ovHom 𝒜 i j) (ovHom_bijective 𝒜 i j)

noncomputable def ovIsoSwap (i j : Idx 𝒜) :
    Spec (CommRingCat.of ((fam 𝒜 j * fam 𝒜 i).Potion)) ≅
      Spec (CommRingCat.of (Away 𝒜 (elt 𝒜 i * elt 𝒜 j))) :=
  specIsoOfBijective (ovHomSwap 𝒜 i j) (ovHomSwap_bijective 𝒜 i j)

@[simp] theorem chartIso_hom (i : Idx 𝒜) :
    (chartIso 𝒜 i).hom = Spec.map (CommRingCat.ofHom (chartHom 𝒜 i)) := rfl

@[simp] theorem ovIso_hom (i j : Idx 𝒜) :
    (ovIso 𝒜 i j).hom = Spec.map (CommRingCat.ofHom (ovHom 𝒜 i j)) := rfl

@[simp] theorem ovIsoSwap_hom (i j : Idx 𝒜) :
    (ovIsoSwap 𝒜 i j).hom = Spec.map (CommRingCat.ofHom (ovHomSwap 𝒜 i j)) := rfl

theorem mulElt_mem (i j : Idx 𝒜) :
    elt 𝒜 i * elt 𝒜 j ∈ 𝒜 ((i.1 : ℕ) + (j.1 : ℕ)) :=
  SetLike.mul_mem_graded (elt_mem 𝒜 i) (elt_mem 𝒜 j)

theorem mulDeg_pos (i j : Idx 𝒜) : 0 < (i.1 : ℕ) + (j.1 : ℕ) :=
  Nat.add_pos_left (deg_pos 𝒜 i) _

theorem ovHom_awayMap (i j : Idx 𝒜) :
    (ovHom 𝒜 i j).comp (awayMap 𝒜 (elt_mem 𝒜 j)
        (show elt 𝒜 i * elt 𝒜 j = elt 𝒜 i * elt 𝒜 j from rfl)) =
      ((fam 𝒜 i).toHomogeneousSubmonoid.potionToMul
        (fam 𝒜 j).toHomogeneousSubmonoid).comp (chartHom 𝒜 i) :=
  awayMap_potionToMul_square 𝒜 (elt_mem 𝒜 j) rfl _ _ _ _

theorem ovHomSwap_awayMap (i j : Idx 𝒜) :
    (ovHomSwap 𝒜 i j).comp (awayMap 𝒜 (elt_mem 𝒜 i)
        (show elt 𝒜 i * elt 𝒜 j = elt 𝒜 j * elt 𝒜 i from mul_comm _ _)) =
      ((fam 𝒜 j).toHomogeneousSubmonoid.potionToMul
        (fam 𝒜 i).toHomogeneousSubmonoid).comp (chartHom 𝒜 j) :=
  awayMap_potionToMul_square 𝒜 (elt_mem 𝒜 i) (mul_comm _ _) _ _ _ _

@[reassoc] theorem specSquare (i j : Idx 𝒜) :
    (GoodPotionIngredient.glueData (fam 𝒜)).f i j ≫ (chartIso 𝒜 i).hom =
      (ovIso 𝒜 i j).hom ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 j)
        (show elt 𝒜 i * elt 𝒜 j = elt 𝒜 i * elt 𝒜 j from rfl))) := by
  simp only [GoodPotionIngredient.glueData_f, chartIso_hom, ovIso_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ovHom_awayMap]

@[reassoc] theorem specSquareSwap (i j : Idx 𝒜) :
    (GoodPotionIngredient.glueData (fam 𝒜)).f j i ≫ (chartIso 𝒜 j).hom =
      (ovIsoSwap 𝒜 i j).hom ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 i)
        (show elt 𝒜 i * elt 𝒜 j = elt 𝒜 j * elt 𝒜 i from mul_comm _ _))) := by
  simp only [GoodPotionIngredient.glueData_f, chartIso_hom, ovIsoSwap_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ovHomSwap_awayMap]

@[reassoc] theorem t_ovIsoSwap (i j : Idx 𝒜) :
    (GoodPotionIngredient.glueData (fam 𝒜)).t i j ≫ (ovIsoSwap 𝒜 i j).hom =
      (ovIso 𝒜 i j).hom := by
  simp only [GoodPotionIngredient.glueData_t, ovIsoSwap_hom, ovIso_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, potionEquiv_ovHomSwap]

theorem specMap_awayMap_awayι_left (i j : Idx 𝒜) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 j)
        (show elt 𝒜 i * elt 𝒜 j = elt 𝒜 i * elt 𝒜 j from rfl))) ≫
      Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (deg_pos 𝒜 i) =
      Proj.awayι 𝒜 (elt 𝒜 i * elt 𝒜 j) (mulElt_mem 𝒜 i j) (mulDeg_pos 𝒜 i j) := by
  rw [Proj.SpecMap_awayMap_awayι]

theorem specMap_awayMap_awayι_right (i j : Idx 𝒜) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 i)
        (show elt 𝒜 i * elt 𝒜 j = elt 𝒜 j * elt 𝒜 i from mul_comm _ _))) ≫
      Proj.awayι 𝒜 (elt 𝒜 j) (elt_mem 𝒜 j) (deg_pos 𝒜 j) =
      Proj.awayι 𝒜 (elt 𝒜 i * elt 𝒜 j) (mulElt_mem 𝒜 i j) (mulDeg_pos 𝒜 i j) := by
  rw [Proj.SpecMap_awayMap_awayι]
  exact awayι_congr 𝒜 _ _ _ _

noncomputable def chartMap (i : Idx 𝒜) :
    Spec (CommRingCat.of ((fam 𝒜 i).Potion)) ⟶ Proj 𝒜 :=
  (chartIso 𝒜 i).hom ≫ Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (deg_pos 𝒜 i)

theorem chartMap_def (i : Idx 𝒜) :
    chartMap 𝒜 i = (chartIso 𝒜 i).hom ≫
      Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (deg_pos 𝒜 i) := rfl

noncomputable def chartMapInv (i : Idx 𝒜) :
    Spec (CommRingCat.of (Away 𝒜 (elt 𝒜 i))) ⟶ GoodPotionIngredient.Proj (fam 𝒜) :=
  (chartIso 𝒜 i).inv ≫ (GoodPotionIngredient.glueData (fam 𝒜)).ι i

theorem chartMapInv_def (i : Idx 𝒜) :
    chartMapInv 𝒜 i =
      (chartIso 𝒜 i).inv ≫ (GoodPotionIngredient.glueData (fam 𝒜)).ι i := rfl

theorem chartMap_cond (i j : Idx 𝒜) :
    (GoodPotionIngredient.glueData (fam 𝒜)).f i j ≫ chartMap 𝒜 i =
      ((GoodPotionIngredient.glueData (fam 𝒜)).t i j ≫
        (GoodPotionIngredient.glueData (fam 𝒜)).f j i) ≫ chartMap 𝒜 j := by
  have hL : (GoodPotionIngredient.glueData (fam 𝒜)).f i j ≫ chartMap 𝒜 i =
      (ovIso 𝒜 i j).hom ≫
        Proj.awayι 𝒜 (elt 𝒜 i * elt 𝒜 j) (mulElt_mem 𝒜 i j) (mulDeg_pos 𝒜 i j) := by
    rw [chartMap_def, ← Category.assoc, specSquare, Category.assoc,
      specMap_awayMap_awayι_left]
  have hR : ((GoodPotionIngredient.glueData (fam 𝒜)).t i j ≫
        (GoodPotionIngredient.glueData (fam 𝒜)).f j i) ≫ chartMap 𝒜 j =
      (ovIso 𝒜 i j).hom ≫
        Proj.awayι 𝒜 (elt 𝒜 i * elt 𝒜 j) (mulElt_mem 𝒜 i j) (mulDeg_pos 𝒜 i j) := by
    rw [chartMap_def, Category.assoc, specSquareSwap_assoc, specMap_awayMap_awayι_right,
      ← Category.assoc, t_ovIsoSwap]
  rw [hL, hR]

noncomputable def phi : GoodPotionIngredient.Proj (fam 𝒜) ⟶ Proj 𝒜 :=
  Multicoequalizer.desc _ _ (fun i => chartMap 𝒜 i) (by
    rintro ⟨i, j⟩
    exact chartMap_cond 𝒜 i j)

@[reassoc]
theorem ι_phi (i : Idx 𝒜) :
    (GoodPotionIngredient.glueData (fam 𝒜)).ι i ≫ phi 𝒜 = chartMap 𝒜 i := by
  erw [Multicoequalizer.π_desc]

theorem specSquare' (i j : Idx 𝒜) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 j)
        (show elt 𝒜 i * elt 𝒜 j = elt 𝒜 i * elt 𝒜 j from rfl))) ≫ (chartIso 𝒜 i).inv =
      (ovIso 𝒜 i j).inv ≫ (GoodPotionIngredient.glueData (fam 𝒜)).f i j := by
  rw [← cancel_epi (ovIso 𝒜 i j).hom, Iso.hom_inv_id_assoc, ← specSquare_assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem specSquareSwap' (i j : Idx 𝒜) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 (elt_mem 𝒜 i)
        (show elt 𝒜 i * elt 𝒜 j = elt 𝒜 j * elt 𝒜 i from mul_comm _ _))) ≫
        (chartIso 𝒜 j).inv =
      (ovIsoSwap 𝒜 i j).inv ≫ (GoodPotionIngredient.glueData (fam 𝒜)).f j i := by
  rw [← cancel_epi (ovIsoSwap 𝒜 i j).hom, Iso.hom_inv_id_assoc, ← specSquareSwap_assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem ovIso_inv_t (i j : Idx 𝒜) :
    (ovIso 𝒜 i j).inv ≫ (GoodPotionIngredient.glueData (fam 𝒜)).t i j =
      (ovIsoSwap 𝒜 i j).inv := by
  rw [← cancel_mono (ovIsoSwap 𝒜 i j).hom, Category.assoc, t_ovIsoSwap,
    Iso.inv_hom_id, Iso.inv_hom_id]

theorem chartMapInv_cond (i j : Idx 𝒜) :
    pullback.fst (Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (deg_pos 𝒜 i))
        (Proj.awayι 𝒜 (elt 𝒜 j) (elt_mem 𝒜 j) (deg_pos 𝒜 j)) ≫ chartMapInv 𝒜 i =
      pullback.snd (Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (deg_pos 𝒜 i))
        (Proj.awayι 𝒜 (elt 𝒜 j) (elt_mem 𝒜 j) (deg_pos 𝒜 j)) ≫ chartMapInv 𝒜 j := by
  rw [← cancel_epi (Proj.pullbackAwayιIso 𝒜 (elt_mem 𝒜 i) (deg_pos 𝒜 i) (elt_mem 𝒜 j)
      (deg_pos 𝒜 j) (show elt 𝒜 i * elt 𝒜 j = elt 𝒜 i * elt 𝒜 j from rfl)).inv,
    Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc,
    chartMapInv_def, chartMapInv_def, ← Category.assoc, ← Category.assoc,
    specSquare', specSquareSwap', Category.assoc, Category.assoc, ← ovIso_inv_t,
    Category.assoc, (GoodPotionIngredient.glueData (fam 𝒜)).glue_condition]

noncomputable def psi : Proj 𝒜 ⟶ GoodPotionIngredient.Proj (fam 𝒜) :=
  (Proj.affineOpenCover 𝒜).openCover.glueMorphisms (fun i => chartMapInv 𝒜 i)
    (fun i j => chartMapInv_cond 𝒜 i j)

@[reassoc]
theorem awayι_psi (i : Idx 𝒜) :
    Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (deg_pos 𝒜 i) ≫ psi 𝒜 = chartMapInv 𝒜 i :=
  (Proj.affineOpenCover 𝒜).openCover.ι_glueMorphisms _ _ i

theorem phi_psi : phi 𝒜 ≫ psi 𝒜 = 𝟙 _ := by
  refine Multicoequalizer.hom_ext _ _ _ fun i => ?_
  show (GoodPotionIngredient.glueData (fam 𝒜)).ι i ≫ phi 𝒜 ≫ psi 𝒜 =
    (GoodPotionIngredient.glueData (fam 𝒜)).ι i ≫ 𝟙 _
  rw [← Category.assoc, ι_phi, chartMap_def, Category.assoc, awayι_psi, chartMapInv_def,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]

theorem psi_phi : psi 𝒜 ≫ phi 𝒜 = 𝟙 _ := by
  refine (Proj.affineOpenCover 𝒜).openCover.hom_ext _ _ fun i => ?_
  show Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (deg_pos 𝒜 i) ≫ psi 𝒜 ≫ phi 𝒜 =
    Proj.awayι 𝒜 (elt 𝒜 i) (elt_mem 𝒜 i) (deg_pos 𝒜 i) ≫ 𝟙 _
  rw [← Category.assoc, awayι_psi, chartMapInv_def, Category.assoc, ι_phi, chartMap_def,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

noncomputable def projIso : GoodPotionIngredient.Proj (fam 𝒜) ≅ Proj 𝒜 where
  hom := phi 𝒜
  inv := psi 𝒜
  hom_inv_id := phi_psi 𝒜
  inv_hom_id := psi_phi 𝒜

noncomputable def projIso' : Proj 𝒜 ≅ GoodPotionIngredient.Proj (fam 𝒜) :=
  (projIso 𝒜).symm

end ProjIsoB
