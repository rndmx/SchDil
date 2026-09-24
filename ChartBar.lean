import Project.Potions.GoodPotionIngredient
import Project.HomogeneousSubmonoid.Relevant

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open HomogeneousSubmonoid

namespace ChartBar

variable {ι : Type} {R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

theorem isHomogeneousElem_prod (s : Finset A)
    (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) :
    SetLike.IsHomogeneousElem 𝒜 (∏ x ∈ s, x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using SetLike.isHomogeneousElem_one 𝒜
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact SetLike.IsHomogeneousElem.mul (hs a (Finset.mem_insert_self a s))
        (ih fun x hx => hs x (Finset.mem_insert_of_mem hx))

theorem bar_eq_of_le_bar' (S T : HomogeneousSubmonoid 𝒜) (h1 : S ≤ T.bar) (h2 : T ≤ S.bar) :
    S.bar = T.bar :=
  le_antisymm (by simpa using bar_mono _ _ h1) (by simpa using bar_mono _ _ h2)

theorem dvd_prod_of_mem (s : Finset A) {a : A} (ha : a ∈ s) : a ∣ ∏ x ∈ s, x :=
  Finset.dvd_prod_of_mem id ha

theorem bar_closure_prod_eq (s : Finset A)
    (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) :
    (closure (s : Set A) hs).bar =
      (closure {∏ x ∈ s, x}
        (by rintro y (rfl : y = _); exact isHomogeneousElem_prod s hs)).bar := by
  classical
  set f : A := ∏ x ∈ s, x with hf
  set T : HomogeneousSubmonoid 𝒜 :=
    closure {f} (by rintro y (rfl : y = _); exact isHomogeneousElem_prod s hs) with hT
  refine bar_eq_of_le_bar' _ _ ?_ ?_
  ·
    intro x hx
    refine Submonoid.closure_induction ?_ ?_ ?_ hx
    · intro y hy
      refine (mem_bar _ _).2 ⟨hs y hy, f, ?_, dvd_prod_of_mem s hy⟩
      exact Submonoid.subset_closure rfl
    · exact (mem_bar _ _).2 ⟨SetLike.isHomogeneousElem_one 𝒜, 1, one_mem _, dvd_refl 1⟩
    · rintro y z - - ⟨hy, u, hu, hyu⟩ ⟨hz, w, hw, hzw⟩
      exact (mem_bar _ _).2 ⟨hy.mul hz, u * w, mul_mem hu hw, mul_dvd_mul hyu hzw⟩
  ·
    intro x hx
    refine Submonoid.closure_induction ?_ ?_ ?_ hx
    · rintro y (rfl : y = f)
      refine (mem_bar _ _).2 ⟨isHomogeneousElem_prod s hs, f, ?_, dvd_refl f⟩
      exact Submonoid.prod_mem _ fun a ha => Submonoid.subset_closure ha
    · exact (mem_bar _ _).2 ⟨SetLike.isHomogeneousElem_one 𝒜, 1, one_mem _, dvd_refl 1⟩
    · rintro y z - - ⟨hy, u, hu, hyu⟩ ⟨hz, w, hw, hzw⟩
      exact (mem_bar _ _).2 ⟨hy.mul hz, u * w, mul_mem hu hw, mul_dvd_mul hyu hzw⟩

theorem isHomogeneousElem_pow {a : A} (ha : SetLike.IsHomogeneousElem 𝒜 a) (k : ℕ) :
    SetLike.IsHomogeneousElem 𝒜 (a ^ k) := by
  obtain ⟨d, hd⟩ := ha
  exact ⟨k • d, SetLike.pow_mem_graded k hd⟩

def gen (a : A) (ha : SetLike.IsHomogeneousElem 𝒜 a) : HomogeneousSubmonoid 𝒜 :=
  closure {a} (by rintro y (rfl : y = a); exact ha)

theorem mem_gen_self (a : A) (ha : SetLike.IsHomogeneousElem 𝒜 a) : a ∈ gen a ha :=
  Submonoid.subset_closure rfl

theorem gen_le_of_dvd {a b : A} (ha : SetLike.IsHomogeneousElem 𝒜 a)
    (T : HomogeneousSubmonoid 𝒜)
    (hbT : b ∈ T) (hab : a ∣ b) : gen a ha ≤ T.bar := by
  intro x hx
  refine Submonoid.closure_induction ?_ ?_ ?_ hx
  · rintro y (rfl : y = a)
    exact (mem_bar _ _).2 ⟨ha, b, hbT, hab⟩
  · exact (mem_bar _ _).2 ⟨SetLike.isHomogeneousElem_one 𝒜, 1, one_mem _, dvd_refl 1⟩
  · rintro y z - - ⟨hy, u, hu, hyu⟩ ⟨hz, w, hw, hzw⟩
    exact (mem_bar _ _).2 ⟨hy.mul hz, u * w, mul_mem hu hw, mul_dvd_mul hyu hzw⟩

theorem bar_gen_pow (a : A) (ha : SetLike.IsHomogeneousElem 𝒜 a) {k : ℕ} (hk : 0 < k) :
    (gen a ha).bar = (gen (a ^ k) (isHomogeneousElem_pow ha k)).bar := by
  refine bar_eq_of_le_bar' _ _ ?_ ?_
  · exact gen_le_of_dvd ha _ (mem_gen_self _ (isHomogeneousElem_pow ha k)) (dvd_pow_self a hk.ne')
  · refine gen_le_of_dvd (isHomogeneousElem_pow ha k) _ ?_ (dvd_refl _)
    exact pow_mem (mem_gen_self a ha) k

theorem bar_gen_mul_left (f g : A) (hf : SetLike.IsHomogeneousElem 𝒜 f)
    (hg : SetLike.IsHomogeneousElem 𝒜 g) :
    (gen f hf * gen (f * g) (hf.mul hg)).bar = (gen (f * g) (hf.mul hg)).bar := by
  refine bar_eq_of_le_bar' _ _ ?_ ?_
  ·
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submonoid.mem_mul_iff.1 hx
    have hy' : y ∈ (gen (f * g) (hf.mul hg)).bar :=
      gen_le_of_dvd hf _ (mem_gen_self _ (hf.mul hg)) ⟨g, rfl⟩ hy
    have hz' : z ∈ (gen (f * g) (hf.mul hg)).bar := le_bar _ hz
    exact mul_mem hy' hz'
  · exact le_trans (right_le_mul _ _) (le_bar _)

theorem isHomogeneousElem_prod' {κ : Type*} (s : Finset κ) (g : κ → A)
    (hg : ∀ i, SetLike.IsHomogeneousElem 𝒜 (g i)) :
    SetLike.IsHomogeneousElem 𝒜 (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using SetLike.isHomogeneousElem_one 𝒜
  | insert a s ha ih => rw [Finset.prod_insert ha]; exact (hg a).mul ih

theorem bar_closure_range_eq {κ : Type*} [Fintype κ] (g : κ → A)
    (hg : ∀ i, SetLike.IsHomogeneousElem 𝒜 (g i)) :
    (closure (Set.range g) (by rintro _ ⟨i, rfl⟩; exact hg i)).bar =
      (gen (∏ i : κ, g i) (isHomogeneousElem_prod' Finset.univ g hg)).bar := by
  classical
  refine bar_eq_of_le_bar' _ _ ?_ ?_
  · intro x hx
    refine Submonoid.closure_induction ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      refine (mem_bar _ _).2 ⟨hg i, ∏ j : κ, g j, mem_gen_self _ _, ?_⟩
      exact Finset.dvd_prod_of_mem g (Finset.mem_univ i)
    · exact (mem_bar _ _).2 ⟨SetLike.isHomogeneousElem_one 𝒜, 1, one_mem _, dvd_refl 1⟩
    · rintro y z - - ⟨hy, u, hu, hyu⟩ ⟨hz, w, hw, hzw⟩
      exact (mem_bar _ _).2 ⟨hy.mul hz, u * w, mul_mem hu hw, mul_dvd_mul hyu hzw⟩
  · intro x hx
    refine Submonoid.closure_induction ?_ ?_ ?_ hx
    · rintro y (rfl : y = _)
      refine (mem_bar _ _).2 ⟨isHomogeneousElem_prod' Finset.univ g hg,
        ∏ i : κ, g i, ?_, dvd_refl _⟩
      exact Submonoid.prod_mem _ fun i _ => Submonoid.subset_closure ⟨i, rfl⟩
    · exact (mem_bar _ _).2 ⟨SetLike.isHomogeneousElem_one 𝒜, 1, one_mem _, dvd_refl 1⟩
    · rintro y z - - ⟨hy, u, hu, hyu⟩ ⟨hz, w, hw, hzw⟩
      exact (mem_bar _ _).2 ⟨hy.mul hz, u * w, mul_mem hu hw, mul_dvd_mul hyu hzw⟩

theorem gen_congr' {x y : A} (hx : SetLike.IsHomogeneousElem 𝒜 x)
    (hy : SetLike.IsHomogeneousElem 𝒜 y) (h : x = y) :
    (gen x hx).bar = (gen y hy).bar := by
  subst h; rfl

end ChartBar
