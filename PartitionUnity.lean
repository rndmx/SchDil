import ChartEq

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

open HomogeneousSubmonoid HomogeneousLocalization

namespace PartitionUnity

variable {ι : Type} {R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

def frac (S : HomogeneousSubmonoid 𝒜) {d : ι} {g f : A} (hg : g ∈ 𝒜 d) (hf : f ∈ 𝒜 d)
    (hfS : f ∈ S) : S.Potion :=
  HomogeneousLocalization.mk ⟨d, ⟨g, hg⟩, ⟨f, hf⟩, hfS⟩

theorem val_frac (S : HomogeneousSubmonoid 𝒜) {d : ι} {g f : A} (hg : g ∈ 𝒜 d) (hf : f ∈ 𝒜 d)
    (hfS : f ∈ S) :
    (frac S hg hf hfS).val = Localization.mk g ⟨f, hfS⟩ := rfl

theorem sum_frac_eq_one {κ : Type*} (S : HomogeneousSubmonoid 𝒜) {d : ι} {f : A}
    (hf : f ∈ 𝒜 d) (hfS : f ∈ S) (J : Finset κ) (g : κ → A)
    (hg : ∀ j : κ, g j ∈ 𝒜 d) (hsum : ∑ j ∈ J, g j = f) :
    ∑ j ∈ J, frac S (hg j) hf hfS = 1 := by
  classical
  have key : ∀ T : Finset κ, (∑ j ∈ T, frac S (hg j) hf hfS).val =
      Localization.mk (∑ j ∈ T, g j) ⟨f, hfS⟩ := by
    intro T
    induction T using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, HomogeneousLocalization.val_zero,
          Localization.mk_zero]
    | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [HomogeneousLocalization.val_add, ih, val_frac, Localization.add_mk_self]
  apply HomogeneousLocalization.val_injective
  rw [key J, hsum, HomogeneousLocalization.val_one]
  exact Localization.mk_self ⟨f, hfS⟩

theorem exists_frac_notMem {κ : Type*} (S : HomogeneousSubmonoid 𝒜) {d : ι} {f : A}
    (hf : f ∈ 𝒜 d) (hfS : f ∈ S) (J : Finset κ) (g : κ → A)
    (hg : ∀ j : κ, g j ∈ 𝒜 d) (hsum : ∑ j ∈ J, g j = f)
    (p : Ideal S.Potion) (hp : p.IsPrime) :
    ∃ j ∈ J, frac S (hg j) hf hfS ∉ p := by
  by_contra hcon
  push_neg at hcon
  have : (1 : S.Potion) ∈ p := by
    rw [← sum_frac_eq_one S hf hfS J g hg hsum]
    exact Ideal.sum_mem _ fun j hj => hcon j hj
  exact hp.ne_top ((Ideal.eq_top_iff_one _).2 this)

end PartitionUnity
