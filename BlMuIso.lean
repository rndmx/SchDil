import BlMuOpen
import ReesChartCover

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

open AlgebraicGeometry CategoryTheory GoodPotionIngredient

namespace BlMuIso

variable {A : Type (u+1)} [CommRing A]
variable {ι : Type} [Fintype ι] (L : ι → Ideal A) [DecidableEq ι]
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

theorem leOfSet_eq :
    BlMuOpen.leOfSet L (BlMuOpen.muSet L) =
      ProjSurj.leOfSet (Set.range (map_index L)) := rfl

theorem surjective_blMuToBl : Function.Surjective (BlMuOpen.blMuToBl L).base := by
  have h2 : Function.Surjective
      (projHomOfLE (BlMuOpen.leOfSet L (BlMuOpen.muSet L))).base := by
    rw [leOfSet_eq]
    exact ReesChartCover.surjective_projHom L
  haveI : IsIso (projToRange (map_index L)) := isIso_projToRange _
  haveI : IsIso ((projToRange (map_index L)).base) := inferInstance
  have h1 : Function.Surjective ((projToRange (map_index L)).base) :=
    (TopCat.homeoOfIso (asIso ((projToRange (map_index L)).base))).surjective
  show Function.Surjective
    ((projToRange (map_index L) ≫ projHomOfLE (BlMuOpen.leOfSet L (BlMuOpen.muSet L))).base)
  rw [Scheme.comp_base]
  exact h2.comp h1

instance isIso_BlMuToBl : IsIso (BlMuToBl L) :=
  BlMuOpen.isIso_of_surjective L
    (by rw [← BlMuOpen.blMuToBl_eq]; exact surjective_blMuToBl L)

noncomputable def blMuIso : BlMu L ≅ Bl L :=
  asIso (BlMuToBl L)

end BlMuIso
