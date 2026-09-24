import ReesCovering
import ChartBar
import Project.Blowups.Bl

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

open HomogeneousSubmonoid ReesCovering
open scoped Family

namespace ReesMu

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : Type (u+1)} [CommRing A] (L : ι → Ideal A)
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

def multicenterOf {a : ι → A} (ha : ∀ i, a i ∈ L i) : Multicenter A where
  index := ι
  ideal := L
  elem := a

@[simp] theorem multicenterOf_index {a : ι → A} (ha : ∀ i, a i ∈ L i) :
    (multicenterOf L ha).index = ι := rfl

theorem multicenterOf_largeIdeal {a : ι → A} (ha : ∀ i, a i ∈ L i) (i : ι) :
    (multicenterOf L ha).LargeIdeal i = L i := by
  show L i + Ideal.span {a i} = L i
  rw [Submodule.add_eq_sup]
  exact sup_eq_left.2 (Ideal.span_le.2 (by simpa using ha i))

def muOf {a : ι → A} (ha : ∀ i, a i ∈ L i) : Mu L where
  multicenter := multicenterOf L ha
  fin := inferInstanceAs (Fintype ι)
  Ψ := id
  sec := id
  surj _ := rfl
  cond i := multicenterOf_largeIdeal L ha i

noncomputable local instance : DecidableEq (ReesAlgebra L) := Classical.decEq _

noncomputable def muGens {a : ι → A} (ha : ∀ i, a i ∈ L i) : Finset (ReesAlgebra L) :=
  Finset.image (fun i : ι => ReesAlgebra.single L (Finsupp.single i 1)
    ⟨a i, by rw [familyPow_single]; exact ha i⟩) Finset.univ

theorem prod_muGens_eq {a : ι → A} (ha : ∀ i, a i ∈ L i)
    (hinj : Function.Injective (fun i : ι => ReesAlgebra.single L (Finsupp.single i 1)
      ⟨a i, by rw [familyPow_single]; exact ha i⟩)) :
    ∏ x ∈ muGens L ha, x = prodGen L ha := by
  rw [muGens, Finset.prod_image (fun i _ j _ h => hinj h)]
  rw [ReesAlgebra.single_prod]
  refine ReesAlgebra.single_eq' (F := L) _ _ ?_ _ _ _ _ ?_
  · ext i
    simp [oneVec, Finsupp.finset_sum_apply, Finsupp.single_apply]
  · simp

theorem muGens_coe {a : ι → A} (ha : ∀ i, a i ∈ L i) :
    ((muGens L ha : Finset (ReesAlgebra L)) : Set (ReesAlgebra L)) =
      { x | ∃ i : ι, ReesAlgebra.single L (Finsupp.single i 1)
        ⟨a i, by rw [familyPow_single]; exact ha i⟩ = x } := by
  ext x
  simp [muGens, eq_comm]

theorem muGens_homogeneous {a : ι → A} (ha : ∀ i, a i ∈ L i) :
    ∀ x ∈ (muGens L ha : Set (ReesAlgebra L)),
      SetLike.IsHomogeneousElem (ReesAlgebra.intGrading L) x := by
  intro x hx
  rw [muGens_coe] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ⟨_, ReesAlgebra.single_has_degree' L _ _⟩

theorem clo_mu_eq {a : ι → A} (ha : ∀ i, a i ∈ L i) :
    clo_mu L (muOf L ha) =
      HomogeneousSubmonoid.closure ((muGens L ha : Finset (ReesAlgebra L)) :
        Set (ReesAlgebra L)) (muGens_homogeneous L ha) := by
  apply HomogeneousSubmonoid.toSubmonoid_injective
  show Submonoid.closure _ = Submonoid.closure _
  congr 1
  rw [muGens_coe]
  rfl

theorem clo_mu_bar_eq {a : ι → A} (ha : ∀ i, a i ∈ L i)
    (hinj : Function.Injective (fun i : ι => ReesAlgebra.single L (Finsupp.single i 1)
      ⟨a i, by rw [familyPow_single]; exact ha i⟩)) :
    (clo_mu L (muOf L ha)).bar =
      (ChartBar.gen (prodGen L ha)
        ⟨ρNatToInt ι oneVec, ReesAlgebra.single_has_degree' L _ _⟩).bar := by
  rw [clo_mu_eq L ha]
  have h := ChartBar.bar_closure_prod_eq (𝒜 := ReesAlgebra.intGrading L)
    (muGens L ha) (muGens_homogeneous L ha)
  rw [h]
  congr 1
  apply HomogeneousSubmonoid.toSubmonoid_injective
  show Submonoid.closure _ = Submonoid.closure _
  rw [prod_muGens_eq L ha hinj]

def muGen {a : ι → A} (ha : ∀ i, a i ∈ L i) (i : ι) : ReesAlgebra L :=
  ReesAlgebra.single L (Finsupp.single i 1) ⟨a i, by rw [familyPow_single]; exact ha i⟩

theorem muGen_homogeneous {a : ι → A} (ha : ∀ i, a i ∈ L i) (i : ι) :
    SetLike.IsHomogeneousElem (ReesAlgebra.intGrading L) (muGen L ha i) :=
  ⟨_, ReesAlgebra.single_has_degree' L _ _⟩

theorem prod_muGen_eq {a : ι → A} (ha : ∀ i, a i ∈ L i) :
    ∏ i : ι, muGen L ha i = prodGen L ha := by
  classical
  show ∏ i : ι, ReesAlgebra.single L (Finsupp.single i 1) _ = _
  rw [ReesAlgebra.single_prod]
  refine ReesAlgebra.single_eq' (F := L) _ _ ?_ _ _ _ _ ?_
  · ext i
    simp [oneVec, Finsupp.finset_sum_apply, Finsupp.single_apply]
  · simp

theorem clo_mu_eq_closure_range {a : ι → A} (ha : ∀ i, a i ∈ L i) :
    clo_mu L (muOf L ha) =
      HomogeneousSubmonoid.closure (Set.range (muGen L ha))
        (by rintro _ ⟨i, rfl⟩; exact muGen_homogeneous L ha i) := by
  apply HomogeneousSubmonoid.toSubmonoid_injective
  show Submonoid.closure _ = Submonoid.closure _
  congr 1

theorem clo_mu_bar_eq' {a : ι → A} (ha : ∀ i, a i ∈ L i) :
    (clo_mu L (muOf L ha)).bar =
      (ChartBar.gen (prodGen L ha)
        ⟨ρNatToInt ι oneVec, ReesAlgebra.single_has_degree' L _ _⟩).bar := by
  rw [clo_mu_eq_closure_range L ha]
  have h := ChartBar.bar_closure_range_eq (𝒜 := ReesAlgebra.intGrading L)
    (muGen L ha) (muGen_homogeneous L ha)
  rw [h]
  exact ChartBar.gen_congr' _ _ (prod_muGen_eq L ha)

end ReesMu
