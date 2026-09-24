import ChartBar
import Project.Proj.Construction

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

open HomogeneousSubmonoid HomogeneousLocalization AlgebraicGeometry CategoryTheory

namespace ChartEq

variable {ι : Type} {R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

theorem toBarPotion_potionToMul (S T : HomogeneousSubmonoid 𝒜)
    (h : S.bar = (S * T).bar) (z : S.Potion) :
    (potionEquiv h) (toBarPotion S z) = toBarPotion (S * T) (S.potionToMul T z) := by
  induction z using Quotient.inductionOn' with | h z => rfl

theorem potionToMul_bijective (S T : HomogeneousSubmonoid 𝒜)
    (h : S.bar = (S * T).bar) :
    Function.Bijective (S.potionToMul T) := by
  have key : ∀ z : S.Potion,
      (potionEquiv h) (S.equivBarPotion z) = (S * T).equivBarPotion (S.potionToMul T z) :=
    fun z => toBarPotion_potionToMul S T h z
  constructor
  · intro a b hab
    apply S.equivBarPotion.injective
    apply (potionEquiv h).injective
    rw [key a, key b, hab]
  · intro w
    refine ⟨S.equivBarPotion.symm ((potionEquiv h).symm ((S * T).equivBarPotion w)), ?_⟩
    apply (S * T).equivBarPotion.injective
    rw [← key, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

noncomputable def potionMulEquiv (S T : HomogeneousSubmonoid 𝒜) (h : S.bar = (S * T).bar) :
    S.Potion ≃+* (S * T).Potion :=
  RingEquiv.ofBijective (S.potionToMul T) (potionToMul_bijective S T h)

theorem bar_mul_eq_of_bar_eq {S T : HomogeneousSubmonoid 𝒜} (h : S.bar = T.bar) :
    (S * T).bar = S.bar := by
  refine le_antisymm ?_ ?_
  · have hle : S * T ≤ S.bar := by
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submonoid.mem_mul_iff.1 hx
      exact mul_mem (le_bar _ hy) (h ▸ le_bar _ hz)
    simpa using bar_mono _ _ hle
  · simpa using bar_mono _ _ (left_le_mul S T)

end ChartEq
