import ProjAwayIngredient
import ProjOverlap
import ProjGlueCompat
import Mathlib.AlgebraicGeometry.Gluing

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousLocalization HomogeneousSubmonoid
open ProjComparison ProjOverlap ProjGlueCompat

namespace ProjIsoA

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

def ringSpecIso {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Spec (CommRingCat.of T) ≅ Spec (CommRingCat.of S) where
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

theorem ringSpecIso_hom {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T) :
    (ringSpecIso e).hom = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

theorem ringSpecIso_inv {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T) :
    (ringSpecIso e).inv = Spec.map (CommRingCat.ofHom e.symm.toRingHom) := rfl

theorem awayIngredientSpecIso_eq {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    awayIngredientSpecIso 𝒜 hf hm = ringSpecIso (awayIngredientEquiv 𝒜 hf hm) := rfl

abbrev Index : Type u := Σ n : ℕ+, (𝒜 (n : ℕ))

def ing (i : Index 𝒜) : GoodPotionIngredient (intGrading 𝒜) :=
  awayIngredient 𝒜 i.2.2 i.1.2

theorem ing_toSubmonoid (i : Index 𝒜) :
    (ing 𝒜 i).toSubmonoid = Submonoid.powers (i.2 : A) :=
  awayIngredient_toSubmonoid 𝒜 i.2.2 i.1.2

theorem powers_le (i : Index 𝒜) :
    Submonoid.powers (i.2 : A) ≤ (ing 𝒜 i).toSubmonoid :=
  le_of_eq (ing_toSubmonoid 𝒜 i).symm

theorem mul_toSubmonoid_eq (i j : Index 𝒜) :
    (ing 𝒜 i * ing 𝒜 j).toSubmonoid
      = Submonoid.powers (i.2 : A) * Submonoid.powers (j.2 : A) := by
  show (ing 𝒜 i).toSubmonoid * (ing 𝒜 j).toSubmonoid = _
  rw [ing_toSubmonoid, ing_toSubmonoid]

theorem powers_mul_le (i j : Index 𝒜) :
    Submonoid.powers ((i.2 : A) * (j.2 : A)) ≤ (ing 𝒜 i * ing 𝒜 j).toSubmonoid := by
  rw [mul_toSubmonoid_eq]
  exact ProjOverlap.powers_mul_le_mul

theorem powers_left_le (i j : Index 𝒜) :
    Submonoid.powers (i.2 : A) ≤ (ing 𝒜 i * ing 𝒜 j).toSubmonoid :=
  (powers_le 𝒜 i).trans (toSubmonoid_le_mul _ _)

theorem powers_right_le (i j : Index 𝒜) :
    Submonoid.powers (j.2 : A) ≤ (ing 𝒜 i * ing 𝒜 j).toSubmonoid := by
  rw [mul_toSubmonoid_eq]
  exact fun x hx => Submonoid.mem_mul_iff.mpr ⟨1, one_mem _, x, hx, (one_mul x)⟩

def E (i : Index 𝒜) : Away 𝒜 (i.2 : A) ≃+* (ing 𝒜 i).Potion :=
  awayIngredientEquiv 𝒜 i.2.2 i.1.2

def Efg (i j : Index 𝒜) :
    Away 𝒜 ((i.2 : A) * (j.2 : A)) ≃+* (ing 𝒜 i * ing 𝒜 j).Potion :=
  awayMulEquivPotionMul 𝒜 i.2.2 j.2.2 (ing 𝒜 i).toHomogeneousSubmonoid
    (ing 𝒜 j).toHomogeneousSubmonoid (ing_toSubmonoid 𝒜 i) (ing_toSubmonoid 𝒜 j)

theorem val_E (i : Index 𝒜) (z : Away 𝒜 (i.2 : A)) :
    (E 𝒜 i z).val = locMap (powers_le 𝒜 i) z.val := by
  obtain ⟨y, rfl⟩ := mk_surjective z
  rw [val_mk, locMap_mk]
  rfl

theorem val_Efg (i j : Index 𝒜) (z : Away 𝒜 ((i.2 : A) * (j.2 : A))) :
    (Efg 𝒜 i j z).val = locMap (powers_mul_le 𝒜 i j) z.val := by
  obtain ⟨y, rfl⟩ := mk_surjective z
  rw [val_mk, locMap_mk]
  rfl

theorem val_potionEquiv {S T : HomogeneousSubmonoid (intGrading 𝒜)} (eq : S = T)
    (h : S.toSubmonoid ≤ T.toSubmonoid) (z : S.Potion) :
    (potionEquiv eq z).val = locMap h z.val := by
  obtain ⟨y, rfl⟩ := mk_surjective z
  rw [potionEquiv_mk, val_mk, val_mk, locMap_mk]

theorem key_left (i j : Index 𝒜) :
    ((ing 𝒜 i).potionToMul (ing 𝒜 j).toHomogeneousSubmonoid).comp (E 𝒜 i).toRingHom
      = (Efg 𝒜 i j).toRingHom.comp
          (awayMap 𝒜 j.2.2 (rfl : ((i.2 : A) * (j.2 : A)) = (i.2 : A) * (j.2 : A))) := by
  refine ProjGlueCompat.ringHom_ext_val fun z => ?_
  show (((ing 𝒜 i).potionToMul (ing 𝒜 j).toHomogeneousSubmonoid) (E 𝒜 i z)).val
      = (Efg 𝒜 i j (awayMap 𝒜 j.2.2 rfl z)).val
  rw [val_potionToMul, val_E, locMap_locMap, val_Efg,
    locMap_val_awayMap 𝒜 j.2.2 rfl (powers_left_le 𝒜 i j) (powers_mul_le 𝒜 i j)]
  rfl

theorem peq (i j : Index 𝒜) :
    (ing 𝒜 j).toHomogeneousSubmonoid * (ing 𝒜 i).toHomogeneousSubmonoid
      = (ing 𝒜 i).toHomogeneousSubmonoid * (ing 𝒜 j).toHomogeneousSubmonoid :=
  mul_comm _ _

theorem key_right (i j : Index 𝒜) :
    (potionEquiv (peq 𝒜 i j)).toRingHom.comp
        (((ing 𝒜 j).potionToMul (ing 𝒜 i).toHomogeneousSubmonoid).comp (E 𝒜 j).toRingHom)
      = (Efg 𝒜 i j).toRingHom.comp
          (awayMap 𝒜 i.2.2 (mul_comm (i.2 : A) (j.2 : A))) := by
  refine ProjGlueCompat.ringHom_ext_val fun z => ?_
  show (potionEquiv (peq 𝒜 i j)
        (((ing 𝒜 j).potionToMul (ing 𝒜 i).toHomogeneousSubmonoid) (E 𝒜 j z))).val
      = (Efg 𝒜 i j (awayMap 𝒜 i.2.2 (mul_comm (i.2 : A) (j.2 : A)) z)).val
  rw [val_potionEquiv 𝒜 (peq 𝒜 i j)
      (le_of_eq (congrArg HomogeneousSubmonoid.toSubmonoid (peq 𝒜 i j))),
    val_potionToMul, val_E, locMap_locMap, locMap_locMap, val_Efg,
    locMap_val_awayMap 𝒜 i.2.2 (mul_comm (i.2 : A) (j.2 : A))
      (powers_right_le 𝒜 i j) (powers_mul_le 𝒜 i j)]
  rfl

theorem sqLeft (i j : Index 𝒜) :
    (GoodPotionIngredient.glueData (ing 𝒜)).f i j ≫ (ringSpecIso (E 𝒜 i)).hom
      = (ringSpecIso (Efg 𝒜 i j)).hom ≫
          Spec.map (CommRingCat.ofHom (awayMap 𝒜 j.2.2
            (rfl : ((i.2 : A) * (j.2 : A)) = (i.2 : A) * (j.2 : A)))) := by
  have hf : (GoodPotionIngredient.glueData (ing 𝒜)).f i j
      = Spec.map (CommRingCat.ofHom
          ((ing 𝒜 i).potionToMul (ing 𝒜 j).toHomogeneousSubmonoid)) := rfl
  rw [hf, ringSpecIso_hom, ringSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, key_left]

theorem sqRight (i j : Index 𝒜) :
    ((GoodPotionIngredient.glueData (ing 𝒜)).t i j ≫
        (GoodPotionIngredient.glueData (ing 𝒜)).f j i) ≫ (ringSpecIso (E 𝒜 j)).hom
      = (ringSpecIso (Efg 𝒜 i j)).hom ≫
          Spec.map (CommRingCat.ofHom (awayMap 𝒜 i.2.2 (mul_comm (i.2 : A) (j.2 : A)))) := by
  have ht : (GoodPotionIngredient.glueData (ing 𝒜)).t i j
      = Spec.map (CommRingCat.ofHom (potionEquiv (peq 𝒜 i j)).toRingHom) := rfl
  have hf : (GoodPotionIngredient.glueData (ing 𝒜)).f j i
      = Spec.map (CommRingCat.ofHom
          ((ing 𝒜 j).potionToMul (ing 𝒜 i).toHomogeneousSubmonoid)) := rfl
  rw [ht, hf, ringSpecIso_hom, ringSpecIso_hom, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, key_right]

theorem sqLeftInv (i j : Index 𝒜) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 j.2.2
        (rfl : ((i.2 : A) * (j.2 : A)) = (i.2 : A) * (j.2 : A)))) ≫ (ringSpecIso (E 𝒜 i)).inv
      = (ringSpecIso (Efg 𝒜 i j)).inv ≫ (GoodPotionIngredient.glueData (ing 𝒜)).f i j := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (sqLeft 𝒜 i j).symm

theorem sqRightInv (i j : Index 𝒜) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 i.2.2 (mul_comm (i.2 : A) (j.2 : A))))
        ≫ (ringSpecIso (E 𝒜 j)).inv
      = (ringSpecIso (Efg 𝒜 i j)).inv ≫
          ((GoodPotionIngredient.glueData (ing 𝒜)).t i j ≫
            (GoodPotionIngredient.glueData (ing 𝒜)).f j i) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (sqRight 𝒜 i j).symm

theorem awayι_eq {x : A} {m₁ m₂ : ℕ} (h₁ : x ∈ 𝒜 m₁) (hm₁ : 0 < m₁)
    (h₂ : x ∈ 𝒜 m₂) (hm₂ : 0 < m₂) :
    Proj.awayι 𝒜 x h₁ hm₁ = Proj.awayι 𝒜 x h₂ hm₂ := rfl

def chart (i : Index 𝒜) :
    Spec (CommRingCat.of ((ing 𝒜 i).Potion)) ⟶ AlgebraicGeometry.Proj 𝒜 :=
  (ringSpecIso (E 𝒜 i)).hom ≫ Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2

theorem chart_eq (i : Index 𝒜) :
    chart 𝒜 i
      = (awayIngredientSpecIso 𝒜 i.2.2 i.1.2).hom ≫ Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2 := rfl

def phi : GoodPotionIngredient.Proj (ing 𝒜) ⟶ AlgebraicGeometry.Proj 𝒜 :=
  Multicoequalizer.desc _ _ (fun i => chart 𝒜 i) (by
    rintro ⟨i, j⟩
    show (GoodPotionIngredient.glueData (ing 𝒜)).f i j ≫ chart 𝒜 i
        = ((GoodPotionIngredient.glueData (ing 𝒜)).t i j ≫
            (GoodPotionIngredient.glueData (ing 𝒜)).f j i) ≫ chart 𝒜 j
    rw [chart, chart, ← Category.assoc, ← Category.assoc, sqLeft, sqRight, Category.assoc,
      Category.assoc, Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]
    rfl)

theorem ι_phi (i : Index 𝒜) :
    (GoodPotionIngredient.glueData (ing 𝒜)).ι i ≫ phi 𝒜 = chart 𝒜 i :=
  Multicoequalizer.π_desc _ _ _ _ _

def chartInv (i : Index 𝒜) :
    Spec (CommRingCat.of (Away 𝒜 (i.2 : A))) ⟶ GoodPotionIngredient.Proj (ing 𝒜) :=
  (ringSpecIso (E 𝒜 i)).inv ≫ (GoodPotionIngredient.glueData (ing 𝒜)).ι i

theorem chartInv_compat (i j : Index 𝒜) :
    pullback.fst (Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2) (Proj.awayι 𝒜 (j.2 : A) j.2.2 j.1.2)
        ≫ chartInv 𝒜 i
      = pullback.snd _ _ ≫ chartInv 𝒜 j := by
  rw [← cancel_epi (Proj.pullbackAwayιIso 𝒜 i.2.2 i.1.2 j.2.2 j.1.2
    (rfl : ((i.2 : A) * (j.2 : A)) = (i.2 : A) * (j.2 : A))).inv, ← Category.assoc,
    ← Category.assoc, Proj.pullbackAwayιIso_inv_fst, Proj.pullbackAwayιIso_inv_snd,
    chartInv, chartInv, ← Category.assoc, ← Category.assoc, sqLeftInv, sqRightInv,
    Category.assoc, Category.assoc, Category.assoc,
    ← (GoodPotionIngredient.glueData (ing 𝒜)).glue_condition i j]

def psi : AlgebraicGeometry.Proj 𝒜 ⟶ GoodPotionIngredient.Proj (ing 𝒜) :=
  (Proj.affineOpenCover 𝒜).openCover.glueMorphisms (fun i => chartInv 𝒜 i)
    (fun i j => chartInv_compat 𝒜 i j)

theorem awayι_psi (i : Index 𝒜) :
    Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2 ≫ psi 𝒜 = chartInv 𝒜 i :=
  (Proj.affineOpenCover 𝒜).openCover.ι_glueMorphisms _ _ i

theorem phi_psi : phi 𝒜 ≫ psi 𝒜 = 𝟙 _ := by
  refine Multicoequalizer.hom_ext _ _ _ (fun i => ?_)
  show ((GoodPotionIngredient.glueData (ing 𝒜)).ι i) ≫ phi 𝒜 ≫ psi 𝒜
      = ((GoodPotionIngredient.glueData (ing 𝒜)).ι i) ≫ 𝟙 _
  rw [← Category.assoc, ι_phi, Category.comp_id, chart, Category.assoc, awayι_psi, chartInv,
    Iso.hom_inv_id_assoc]

theorem psi_phi : psi 𝒜 ≫ phi 𝒜 = 𝟙 _ := by
  refine (Proj.affineOpenCover 𝒜).openCover.hom_ext _ _ (fun i => ?_)
  show (Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2) ≫ psi 𝒜 ≫ phi 𝒜
      = (Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2) ≫ 𝟙 _
  rw [← Category.assoc, awayι_psi, Category.comp_id, chartInv, Category.assoc, ι_phi, chart,
    Iso.inv_hom_id_assoc]

def projIso : GoodPotionIngredient.Proj (ing 𝒜) ≅ AlgebraicGeometry.Proj 𝒜 where
  hom := phi 𝒜
  inv := psi 𝒜
  hom_inv_id := phi_psi 𝒜
  inv_hom_id := psi_phi 𝒜

def projIsoSymm : AlgebraicGeometry.Proj 𝒜 ≅ GoodPotionIngredient.Proj (ing 𝒜) :=
  (projIso 𝒜).symm

instance : IsIso (phi 𝒜) := ⟨psi 𝒜, phi_psi 𝒜, psi_phi 𝒜⟩

end ProjIsoA
