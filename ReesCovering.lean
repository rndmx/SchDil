import ProjComparison
import Project.Dilatation.ReesAlgebra
import Project.HomogeneousSubmonoid.Dagger

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

universe u

open HomogeneousSubmonoid HomogeneousLocalization
open scoped Family Pointwise

namespace ReesCovering

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : Type u} [CommRing A] (F : ι → Ideal A)

variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

instance : AddGroup.FG (ι →₀ ℤ) := by
  refine ⟨⟨Finset.image (fun i => Finsupp.single i (1 : ℤ)) Finset.univ, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  induction x using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | single i n =>
      have : Finsupp.single i n = n • Finsupp.single i (1 : ℤ) := by
        ext j; simp [Finsupp.single_apply]
      rw [this]
      exact zsmul_mem (AddSubgroup.subset_closure (by simp)) n

theorem single_mem_gradingOfInjection (v : ι →₀ ℕ) (y : (F ^ v : Ideal A)) :
    ReesAlgebra.single F v y ∈
      gradingOfInjection (ReesAlgebra.grading F) (ρNatToInt ι) (ρNatToInt ι v) :=
  ReesAlgebra.single_has_degree' F v y

theorem coord_pos_of_relevant_single (v : ι →₀ ℕ) (y : (F ^ v : Ideal A))
    (hrel : ElemIsRelevant
      (𝒜 := gradingOfInjection (ReesAlgebra.grading F) (ρNatToInt ι))
      (ReesAlgebra.single F v y)
      ⟨ρNatToInt ι v, single_mem_gradingOfInjection F v y⟩)
    (hnil : ∀ k : ℕ, (ReesAlgebra.single F v y) ^ k ≠ 0) (i : ι) :
    0 < v i := by
  have h := ProjComparison.coord_pos_of_elemIsRelevant (ReesAlgebra.grading F)
    (d := ρNatToInt ι v) (a := ReesAlgebra.single F v y)
    ⟨ρNatToInt ι v, single_mem_gradingOfInjection F v y⟩
    (single_mem_gradingOfInjection F v y) hrel hnil i
  simpa [ρNatToInt] using h

variable [DecidableEq ι]

def oneVec : ι →₀ ℕ := ∑ i : ι, Finsupp.single i 1

@[simp] theorem oneVec_apply (i : ι) : (oneVec : ι →₀ ℕ) i = 1 := by
  classical
  simp [oneVec, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem oneVec_le {v : ι →₀ ℕ} (h : ∀ i, 0 < v i) : (oneVec : ι →₀ ℕ) ≤ v := by
  intro i
  simpa using h i

theorem familyPow_oneVec (a : ι → A) : a ^ (oneVec : ι →₀ ℕ) = ∏ i : ι, a i := by
  classical
  rw [familyPow_def]
  rw [Finsupp.prod]
  have hsupp : (oneVec : ι →₀ ℕ).support = Finset.univ := by
    ext i; simp
  rw [hsupp]
  exact Finset.prod_congr rfl fun i _ => by simp

theorem prod_mem_familyPow_oneVec {a : ι → A} (ha : ∀ i, a i ∈ F i) :
    (∏ i : ι, a i) ∈ F ^ (oneVec : ι →₀ ℕ) := by
  rw [← familyPow_oneVec]
  exact Ideal.mem_familyPow_of_mem fun i _ => ha i

def prodGen {a : ι → A} (ha : ∀ i, a i ∈ F i) : ReesAlgebra F :=
  ReesAlgebra.single F oneVec ⟨∏ i : ι, a i, prod_mem_familyPow_oneVec F ha⟩

def prodIdeal : Ideal (ReesAlgebra F) :=
  Ideal.span { r | ∃ (a : ι → A) (ha : ∀ i, a i ∈ F i), r = prodGen F ha }

theorem prodGen_mem {a : ι → A} (ha : ∀ i, a i ∈ F i) : prodGen F ha ∈ prodIdeal F :=
  Ideal.subset_span ⟨a, ha, rfl⟩

theorem familyPow_oneVec_eq_span :
    F ^ (oneVec : ι →₀ ℕ) = Ideal.span (∏ i : ι, (F i : Set A)) := by
  classical
  have hsupp : (oneVec : ι →₀ ℕ).support = Finset.univ := by ext i; simp
  rw [familyPow_def, Finsupp.prod, hsupp, ← Ideal.prod_span]
  exact Finset.prod_congr rfl fun i _ => by simp

theorem single_oneVec_mem_prodIdeal (b : A) (hb : b ∈ F ^ (oneVec : ι →₀ ℕ)) :
    ReesAlgebra.single F oneVec ⟨b, hb⟩ ∈ prodIdeal F := by
  classical
  have hspan : b ∈ Ideal.span (∏ i : ι, (F i : Set A)) := familyPow_oneVec_eq_span F ▸ hb
  induction hspan using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := (Set.mem_finset_prod _ _ _).1 hx
      exact Ideal.subset_span ⟨g, fun i => hg (Finset.mem_univ i), rfl⟩
  | zero =>
      rw [show (⟨(0 : A), _⟩ : (F ^ (oneVec : ι →₀ ℕ) : Ideal A)) = 0 from rfl,
        map_zero]
      exact Ideal.zero_mem _
  | add x y hx hy ihx ihy =>
      have hx' : x ∈ F ^ (oneVec : ι →₀ ℕ) := (familyPow_oneVec_eq_span F).symm ▸ hx
      have hy' : y ∈ F ^ (oneVec : ι →₀ ℕ) := (familyPow_oneVec_eq_span F).symm ▸ hy
      rw [show (⟨x + y, _⟩ : (F ^ (oneVec : ι →₀ ℕ) : Ideal A)) =
          (⟨x, hx'⟩ : (F ^ (oneVec : ι →₀ ℕ) : Ideal A)) + ⟨y, hy'⟩ from rfl,
        map_add]
      exact Ideal.add_mem _ (ihx hx') (ihy hy')
  | smul r x hx ihx =>
      have hx' : x ∈ F ^ (oneVec : ι →₀ ℕ) := (familyPow_oneVec_eq_span F).symm ▸ hx
      rw [show (⟨r • x, _⟩ : (F ^ (oneVec : ι →₀ ℕ) : Ideal A)) =
          r • (⟨x, hx'⟩ : (F ^ (oneVec : ι →₀ ℕ) : Ideal A)) from rfl,
        map_smul, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (ihx hx')

theorem single_mem_prodIdeal {v : ι →₀ ℕ} (hv : ∀ i, 0 < v i) (y : (F ^ v : Ideal A)) :
    ReesAlgebra.single F v y ∈ prodIdeal F := by
  classical
  obtain ⟨w, hw⟩ := exists_add_of_le (oneVec_le (v := v) hv)
  subst hw
  have hmem : (y : A) ∈ F ^ (oneVec : ι →₀ ℕ) * F ^ w := by
    rw [← familyPow_add]
    exact y.2
  refine Submodule.mul_induction_on'
    (C := fun z (_ : z ∈ F ^ (oneVec : ι →₀ ℕ) * F ^ w) =>
      ∀ hz : z ∈ F ^ ((oneVec : ι →₀ ℕ) + w),
        ReesAlgebra.single F (oneVec + w) ⟨z, hz⟩ ∈ prodIdeal F)
    ?_ ?_ hmem y.2
  · intro b hb c hc hbc
    rw [show (⟨b * c, hbc⟩ : (F ^ ((oneVec : ι →₀ ℕ) + w) : Ideal A)) =
        ⟨b * c, Ideal.mem_familyPow_add hb hc⟩ from rfl,
      ← ReesAlgebra.single_mul (F := F) oneVec w ⟨b, hb⟩ ⟨c, hc⟩]
    exact Ideal.mul_mem_right _ _ (single_oneVec_mem_prodIdeal F b hb)
  · intro x₁ hx₁ x₂ hx₂ ih₁ ih₂ hsum
    have h₁ : x₁ ∈ F ^ ((oneVec : ι →₀ ℕ) + w) := by rw [familyPow_add]; exact hx₁
    have h₂ : x₂ ∈ F ^ ((oneVec : ι →₀ ℕ) + w) := by rw [familyPow_add]; exact hx₂
    rw [show (⟨x₁ + x₂, hsum⟩ : (F ^ ((oneVec : ι →₀ ℕ) + w) : Ideal A)) =
        (⟨x₁, h₁⟩ : (F ^ ((oneVec : ι →₀ ℕ) + w) : Ideal A)) + ⟨x₂, h₂⟩ from rfl,
      map_add]
    exact Ideal.add_mem _ (ih₁ h₁) (ih₂ h₂)

theorem relevant_mem_radical_prodIdeal {x : ReesAlgebra F}
    (hx : SetLike.IsHomogeneousElem
      (gradingOfInjection (ReesAlgebra.grading F) (ρNatToInt ι)) x)
    (hrel : ElemIsRelevant x hx) :
    x ∈ (prodIdeal F).radical := by
  classical
  by_cases hnil : ∃ k : ℕ, x ^ k = 0
  · obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [hk]; exact Ideal.zero_mem _⟩
  push_neg at hnil
  obtain ⟨d, hd⟩ := hx
  by_cases hd' : d ∈ Set.range (ρNatToInt ι)
  · obtain ⟨v, rfl⟩ := hd'
    rw [ProjComparison.gradingOfInjection_apply_ρ (ReesAlgebra.grading F) (ρNatToInt ι) v,
      ReesAlgebra.grading, LinearMap.mem_range] at hd
    obtain ⟨y, rfl⟩ := hd
    refine Ideal.le_radical (single_mem_prodIdeal F (fun i => ?_) y)
    exact coord_pos_of_relevant_single F v y hrel hnil i
  · exfalso
    rw [ProjComparison.gradingOfInjection_apply_not_mem
      (ReesAlgebra.grading F) (ρNatToInt ι) hd'] at hd
    exact hnil 1 (by simpa using hd)

theorem dagger_le_radical_prodIdeal :
    ((gradingOfInjection (ReesAlgebra.grading F)
      (ρNatToInt ι)) †).toIdeal ≤
      (prodIdeal F).radical := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨hx, hrel⟩
  exact relevant_mem_radical_prodIdeal F hx hrel

theorem relevant_mem_prodIdeal {x : ReesAlgebra F}
    (hx : SetLike.IsHomogeneousElem
      (gradingOfInjection (ReesAlgebra.grading F) (ρNatToInt ι)) x)
    (hrel : ElemIsRelevant x hx) (hnil : ∀ k : ℕ, x ^ k ≠ 0) :
    x ∈ prodIdeal F := by
  classical
  obtain ⟨d, hd⟩ := hx
  by_cases hd' : d ∈ Set.range (ρNatToInt ι)
  · obtain ⟨v, rfl⟩ := hd'
    rw [ProjComparison.gradingOfInjection_apply_ρ (ReesAlgebra.grading F) (ρNatToInt ι) v,
      ReesAlgebra.grading, LinearMap.mem_range] at hd
    obtain ⟨y, rfl⟩ := hd
    exact single_mem_prodIdeal F (fun i => coord_pos_of_relevant_single F v y hrel hnil i) y
  · exfalso
    rw [ProjComparison.gradingOfInjection_apply_not_mem
      (ReesAlgebra.grading F) (ρNatToInt ι) hd'] at hd
    exact hnil 1 (by simpa using hd)

def prodGenSet : Set (ReesAlgebra F) :=
  { r | ∃ (a : ι → A) (ha : ∀ i, a i ∈ F i), r = prodGen F ha }

theorem prodIdeal_eq_span : prodIdeal F = Ideal.span (prodGenSet F) := rfl

theorem prodGenSet_homogeneous :
    ∀ t ∈ prodGenSet F, t ∈ gradingOfInjection (ReesAlgebra.grading F) (ρNatToInt ι)
      (ρNatToInt ι oneVec) := by
  rintro t ⟨a, ha, rfl⟩
  exact ReesAlgebra.single_has_degree' F _ _

end ReesCovering
