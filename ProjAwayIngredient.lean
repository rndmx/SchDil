import ProjComparison
import Project.Potions.GoodPotionIngredient

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousSubmonoid

namespace ProjComparison

section AwayIngredient

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem mem_intGrading {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) :
    f ∈ intGrading 𝒜 (m : ℤ) := by
  have h : intGrading 𝒜 (m : ℤ) = 𝒜 m :=
    gradingOfInjection_apply_ρ 𝒜 Nat.toIntHom m
  rw [h]
  exact hf

theorem isHomogeneousElem_intGrading {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) :
    SetLike.IsHomogeneousElem (intGrading 𝒜) f :=
  ⟨(m : ℤ), mem_intGrading 𝒜 hf⟩

def awaySubmonoid {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) :
    HomogeneousSubmonoid (intGrading 𝒜) :=
  HomogeneousSubmonoid.closure {f} (by
    rintro x (rfl : x = f)
    exact isHomogeneousElem_intGrading 𝒜 hf)

@[simp] theorem awaySubmonoid_toSubmonoid {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) :
    (awaySubmonoid 𝒜 hf).toSubmonoid = Submonoid.powers f := by
  show Submonoid.closure {f} = _
  rw [Submonoid.powers_eq_closure]

theorem awaySubmonoid_isRelevant {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    (awaySubmonoid 𝒜 hf).IsRelevant := by
  haveI : AddGroup.FG ℤ :=
    ⟨⟨{1}, by simpa using AddSubgroup.closure_singleton_int_one_eq_top⟩⟩
  refine elemIsRelevant_of_homogeneous_of_factorisation (𝒜 := intGrading 𝒜) f
    (isHomogeneousElem_intGrading 𝒜 hf) 1 (fun _ => f) (fun _ => (m : ℤ))
    (fun _ => mem_intGrading 𝒜 hf) ?_ 1 (by simp)
  have hrange : Set.range (fun _ : Fin 1 => (m : ℤ)) = {(m : ℤ)} := by
    ext z; simp
  rw [hrange, ← AddSubgroup.zmultiples_eq_closure]
  refine ⟨?_⟩
  rw [Int.index_zmultiples]
  simpa using hm.ne'

def awayIngredient {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    GoodPotionIngredient (intGrading 𝒜) where
  toHomogeneousSubmonoid := awaySubmonoid 𝒜 hf
  relevant := awaySubmonoid_isRelevant 𝒜 hf hm
  fg := by
    rw [awaySubmonoid_toSubmonoid]
    exact ⟨{f}, by simp [Submonoid.powers_eq_closure]⟩

@[simp] theorem awayIngredient_toSubmonoid {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    (awayIngredient 𝒜 hf hm).toSubmonoid = Submonoid.powers f :=
  awaySubmonoid_toSubmonoid 𝒜 hf

noncomputable def awayIngredientEquiv {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    Away 𝒜 f ≃+* (awayIngredient 𝒜 hf hm).Potion :=
  awayEquivPotion 𝒜 f _ (awayIngredient_toSubmonoid 𝒜 hf hm)

noncomputable def awayIngredientSpecIso {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    Spec (CommRingCat.of ((awayIngredient 𝒜 hf hm).Potion)) ≅
      Spec (CommRingCat.of (Away 𝒜 f)) where
  hom := Spec.map (CommRingCat.ofHom (awayIngredientEquiv 𝒜 hf hm).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (awayIngredientEquiv 𝒜 hf hm).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (awayIngredientEquiv 𝒜 hf hm).toRingHom.comp
          (awayIngredientEquiv 𝒜 hf hm).symm.toRingHom = RingHom.id _ from
        RingHom.ext fun a => (awayIngredientEquiv 𝒜 hf hm).apply_symm_apply a]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (awayIngredientEquiv 𝒜 hf hm).symm.toRingHom.comp
          (awayIngredientEquiv 𝒜 hf hm).toRingHom = RingHom.id _ from
        RingHom.ext fun a => (awayIngredientEquiv 𝒜 hf hm).symm_apply_apply a]
    exact Spec.map_id _

end AwayIngredient

end ProjComparison
