import ProjIsoB

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousLocalization HomogeneousSubmonoid
open ProjComparison ProjOverlap ProjGlueCompat ProjIsoB

namespace ProjMathlibIso

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

abbrev famH (i : Idx 𝒜) : HomogeneousSubmonoid (intGrading 𝒜) :=
  (fam 𝒜 i).toHomogeneousSubmonoid

@[simp] theorem famH_toSubmonoid (i : Idx 𝒜) :
    (famH 𝒜 i).toSubmonoid = Submonoid.powers (elt 𝒜 i) :=
  fam_toSubmonoid 𝒜 i

theorem powers_mul_le_fam_mul (i j : Idx 𝒜) :
    Submonoid.powers (elt 𝒜 i * elt 𝒜 j) ≤ (famH 𝒜 i * famH 𝒜 j).toSubmonoid := by
  rw [show (famH 𝒜 i * famH 𝒜 j).toSubmonoid = _ from mul_fam_toSubmonoid 𝒜 i j]
  exact powers_mul_le_mul

noncomputable def chartInv (i : Idx 𝒜) : (fam 𝒜 i).Potion →+* Away 𝒜 (elt 𝒜 i) :=
  (awayEquivPotion 𝒜 (elt 𝒜 i) (famH 𝒜 i) (famH_toSubmonoid 𝒜 i)).symm.toRingHom

theorem chartInv_awayToPotion (i : Idx 𝒜) (z : Away 𝒜 (elt 𝒜 i)) :
    chartInv 𝒜 i (awayToPotion 𝒜 (elt 𝒜 i) (famH 𝒜 i)
      (le_of_eq (famH_toSubmonoid 𝒜 i).symm) z) = z := by
  rw [chartInv, ← awayEquivPotion_eq_awayToPotion 𝒜 (elt 𝒜 i) (famH 𝒜 i) (famH_toSubmonoid 𝒜 i)]
  exact (awayEquivPotion 𝒜 (elt 𝒜 i) (famH 𝒜 i) (famH_toSubmonoid 𝒜 i)).symm_apply_apply z

theorem awayToPotion_chartInv (i : Idx 𝒜) (w : (fam 𝒜 i).Potion) :
    awayToPotion 𝒜 (elt 𝒜 i) (famH 𝒜 i)
      (le_of_eq (famH_toSubmonoid 𝒜 i).symm) (chartInv 𝒜 i w) = w := by
  rw [chartInv, ← awayEquivPotion_eq_awayToPotion 𝒜 (elt 𝒜 i) (famH 𝒜 i) (famH_toSubmonoid 𝒜 i)]
  exact (awayEquivPotion 𝒜 (elt 𝒜 i) (famH 𝒜 i) (famH_toSubmonoid 𝒜 i)).apply_symm_apply w

theorem square (i j : Idx 𝒜) (z : Away 𝒜 (elt 𝒜 i)) :
    awayToPotion 𝒜 (elt 𝒜 i * elt 𝒜 j) (famH 𝒜 i * famH 𝒜 j) (powers_mul_le_fam_mul 𝒜 i j)
        (awayMap 𝒜 (elt_mem 𝒜 j) rfl z) =
      (famH 𝒜 i).potionToMul (famH 𝒜 j)
        (awayToPotion 𝒜 (elt 𝒜 i) (famH 𝒜 i) (le_of_eq (famH_toSubmonoid 𝒜 i).symm) z) :=
  congrArg (fun F => F z)
    (awayMap_potionToMul_square 𝒜 (elt_mem 𝒜 j) rfl (famH 𝒜 i) (famH 𝒜 j) (le_of_eq (famH_toSubmonoid 𝒜 i).symm)
      (powers_mul_le_fam_mul 𝒜 i j))

noncomputable def ovEquiv (i j : Idx 𝒜) :
    Away 𝒜 (elt 𝒜 i * elt 𝒜 j) ≃+* (famH 𝒜 i * famH 𝒜 j).Potion :=
  awayMulEquivPotionMul 𝒜 (elt_mem 𝒜 i) (elt_mem 𝒜 j) (famH 𝒜 i) (famH 𝒜 j)
    (famH_toSubmonoid 𝒜 i) (famH_toSubmonoid 𝒜 j)

theorem ovEquiv_eq (i j : Idx 𝒜) :
    (ovEquiv 𝒜 i j).toRingHom =
      awayToPotion 𝒜 (elt 𝒜 i * elt 𝒜 j) (famH 𝒜 i * famH 𝒜 j)
        (powers_mul_le_fam_mul 𝒜 i j) :=
  ringHom_ext_val fun z => by
    obtain ⟨y, rfl⟩ := mk_surjective z
    rfl

theorem chart_square (i j : Idx 𝒜) (w : (fam 𝒜 i).Potion) :
    awayMap 𝒜 (elt_mem 𝒜 j) rfl (chartInv 𝒜 i w) =
      (ovEquiv 𝒜 i j).symm ((famH 𝒜 i).potionToMul (famH 𝒜 j) w) := by
  have h := square 𝒜 i j (chartInv 𝒜 i w)
  rw [awayToPotion_chartInv] at h
  have h2 : (ovEquiv 𝒜 i j) (awayMap 𝒜 (elt_mem 𝒜 j) rfl (chartInv 𝒜 i w)) =
      (famH 𝒜 i).potionToMul (famH 𝒜 j) w := by
    rw [show (ovEquiv 𝒜 i j) (awayMap 𝒜 (elt_mem 𝒜 j) rfl (chartInv 𝒜 i w)) =
        (ovEquiv 𝒜 i j).toRingHom (awayMap 𝒜 (elt_mem 𝒜 j) rfl (chartInv 𝒜 i w)) from rfl,
      ovEquiv_eq]
    exact h
  rw [← h2, RingEquiv.symm_apply_apply]

theorem powers_mul_le_fam_mul_swap (i j : Idx 𝒜) :
    Submonoid.powers (elt 𝒜 i * elt 𝒜 j) ≤ (famH 𝒜 j * famH 𝒜 i).toSubmonoid := by
  rw [show (famH 𝒜 j * famH 𝒜 i).toSubmonoid = _ from mul_fam_toSubmonoid 𝒜 j i]
  rw [mul_comm (elt 𝒜 i)]
  exact powers_mul_le_mul

noncomputable def ovEquivSwap (i j : Idx 𝒜) :
    Away 𝒜 (elt 𝒜 i * elt 𝒜 j) ≃+* (famH 𝒜 j * famH 𝒜 i).Potion :=
  (congrSubmonoid 𝒜 (by rw [mul_comm] :
      Submonoid.powers (elt 𝒜 i * elt 𝒜 j) = Submonoid.powers (elt 𝒜 j * elt 𝒜 i))).trans
    (awayMulEquivPotionMul 𝒜 (elt_mem 𝒜 j) (elt_mem 𝒜 i) (famH 𝒜 j) (famH 𝒜 i)
      (famH_toSubmonoid 𝒜 j) (famH_toSubmonoid 𝒜 i))

theorem ovEquivSwap_eq (i j : Idx 𝒜) :
    (ovEquivSwap 𝒜 i j).toRingHom =
      awayToPotion 𝒜 (elt 𝒜 i * elt 𝒜 j) (famH 𝒜 j * famH 𝒜 i)
        (powers_mul_le_fam_mul_swap 𝒜 i j) :=
  ringHom_ext_val fun z => by
    obtain ⟨y, rfl⟩ := mk_surjective z
    rfl

theorem chart_square_swap (i j : Idx 𝒜) (w : (fam 𝒜 j).Potion) :
    awayMap 𝒜 (elt_mem 𝒜 i) (mul_comm (elt 𝒜 i) (elt 𝒜 j)) (chartInv 𝒜 j w) =
      (ovEquivSwap 𝒜 i j).symm ((famH 𝒜 j).potionToMul (famH 𝒜 i) w) := by
  have h := congrArg (fun F => F (chartInv 𝒜 j w))
    (awayMap_potionToMul_square 𝒜 (elt_mem 𝒜 i) (mul_comm (elt 𝒜 i) (elt 𝒜 j))
      (famH 𝒜 j) (famH 𝒜 i) (le_of_eq (famH_toSubmonoid 𝒜 j).symm)
      (powers_mul_le_fam_mul_swap 𝒜 i j))
  simp only [RingHom.comp_apply] at h
  rw [awayToPotion_chartInv] at h
  have h2 : (ovEquivSwap 𝒜 i j)
      (awayMap 𝒜 (elt_mem 𝒜 i) (mul_comm (elt 𝒜 i) (elt 𝒜 j)) (chartInv 𝒜 j w)) =
      (famH 𝒜 j).potionToMul (famH 𝒜 i) w := by
    rw [show (ovEquivSwap 𝒜 i j) (awayMap 𝒜 (elt_mem 𝒜 i)
          (mul_comm (elt 𝒜 i) (elt 𝒜 j)) (chartInv 𝒜 j w)) =
        (ovEquivSwap 𝒜 i j).toRingHom (awayMap 𝒜 (elt_mem 𝒜 i)
          (mul_comm (elt 𝒜 i) (elt 𝒜 j)) (chartInv 𝒜 j w)) from rfl,
      ovEquivSwap_eq]
    exact h
  rw [← h2, RingEquiv.symm_apply_apply]

theorem square_swap (i j : Idx 𝒜) (z : Away 𝒜 (elt 𝒜 j)) :
    awayToPotion 𝒜 (elt 𝒜 i * elt 𝒜 j) (famH 𝒜 j * famH 𝒜 i)
        (powers_mul_le_fam_mul_swap 𝒜 i j)
        (awayMap 𝒜 (elt_mem 𝒜 i) (mul_comm (elt 𝒜 i) (elt 𝒜 j)) z) =
      (famH 𝒜 j).potionToMul (famH 𝒜 i)
        (awayToPotion 𝒜 (elt 𝒜 j) (famH 𝒜 j) (le_of_eq (famH_toSubmonoid 𝒜 j).symm) z) :=
  congrArg (fun F => F z)
    (awayMap_potionToMul_square 𝒜 (elt_mem 𝒜 i) (mul_comm (elt 𝒜 i) (elt 𝒜 j))
      (famH 𝒜 j) (famH 𝒜 i) (le_of_eq (famH_toSubmonoid 𝒜 j).symm)
      (powers_mul_le_fam_mul_swap 𝒜 i j))

theorem potionEquiv_awayToPotion (i j : Idx 𝒜) (z : Away 𝒜 (elt 𝒜 i * elt 𝒜 j)) :
    potionEquiv (mul_comm (famH 𝒜 j) (famH 𝒜 i))
        (awayToPotion 𝒜 (elt 𝒜 i * elt 𝒜 j) (famH 𝒜 j * famH 𝒜 i)
          (powers_mul_le_fam_mul_swap 𝒜 i j) z) =
      awayToPotion 𝒜 (elt 𝒜 i * elt 𝒜 j) (famH 𝒜 i * famH 𝒜 j)
        (powers_mul_le_fam_mul 𝒜 i j) z := by
  obtain ⟨y, rfl⟩ := mk_surjective z
  rfl

theorem ovEquiv_symm_potionEquiv (i j : Idx 𝒜) :
    (ovEquiv 𝒜 i j).symm.toRingHom.comp
        (potionEquiv (mul_comm (famH 𝒜 j) (famH 𝒜 i))).toRingHom =
      (ovEquivSwap 𝒜 i j).symm.toRingHom := by
  apply RingHom.ext
  intro w
  apply (ovEquivSwap 𝒜 i j).injective
  show (ovEquivSwap 𝒜 i j) ((ovEquiv 𝒜 i j).symm
    ((potionEquiv (mul_comm (famH 𝒜 j) (famH 𝒜 i))) w)) =
    (ovEquivSwap 𝒜 i j) ((ovEquivSwap 𝒜 i j).symm w)
  rw [RingEquiv.apply_symm_apply]
  apply (potionEquiv (mul_comm (famH 𝒜 j) (famH 𝒜 i))).injective
  show (potionEquiv _) ((ovEquivSwap 𝒜 i j).toRingHom _) = _
  rw [ovEquivSwap_eq, potionEquiv_awayToPotion]
  rw [← ovEquiv_eq]
  exact (ovEquiv 𝒜 i j).apply_symm_apply _

noncomputable def chartToProj (i : Idx 𝒜) :
    Spec (CommRingCat.of (Away 𝒜 (elt 𝒜 i))) ⟶ GoodPotionIngredient.Proj (fam 𝒜) :=
  Spec.map (CommRingCat.ofHom (chartInv 𝒜 i)) ≫
    (GoodPotionIngredient.glueData (fam 𝒜)).ι i

noncomputable def psi :
    AlgebraicGeometry.Proj 𝒜 ⟶ GoodPotionIngredient.Proj (fam 𝒜) :=
  (Proj.affineOpenCover 𝒜).openCover.glueMorphisms (fun i => chartToProj 𝒜 i) <| by
    intro i j
    rw [← cancel_epi (Proj.pullbackAwayιIso 𝒜 (elt_mem 𝒜 i) (deg_pos 𝒜 i)
      (elt_mem 𝒜 j) (deg_pos 𝒜 j) (rfl : elt 𝒜 i * elt 𝒜 j = _)).inv]
    rw [← Category.assoc, ← Category.assoc]
    erw [Proj.pullbackAwayιIso_inv_fst, Proj.pullbackAwayιIso_inv_snd]
    simp only [chartToProj]
    rw [← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rw [show (awayMap 𝒜 (elt_mem 𝒜 j) rfl).comp (chartInv 𝒜 i) =
          (ovEquiv 𝒜 i j).symm.toRingHom.comp ((famH 𝒜 i).potionToMul (famH 𝒜 j)) from
        RingHom.ext fun w => chart_square 𝒜 i j w,
      show (awayMap 𝒜 (elt_mem 𝒜 i) (mul_comm (elt 𝒜 i) (elt 𝒜 j))).comp (chartInv 𝒜 j) =
          (ovEquivSwap 𝒜 i j).symm.toRingHom.comp ((famH 𝒜 j).potionToMul (famH 𝒜 i)) from
        RingHom.ext fun w => chart_square_swap 𝒜 i j w,
      ← ovEquiv_symm_potionEquiv]
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
      Spec.map_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Category.assoc]
    exact congrArg (fun t => Spec.map (CommRingCat.ofHom
      (ovEquiv 𝒜 i j).symm.toRingHom) ≫ t)
      ((GoodPotionIngredient.glueData (fam 𝒜)).glue_condition i j).symm

end ProjMathlibIso
