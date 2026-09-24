import PolyptychPanelChart

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) {T : Scheme.{u+1}} (f : T ⟶ X)

def HomOver : Type _ := { g : T ⟶ M.dilatation // g ≫ M.structureMap = f }

theorem pullSubset_of_hom (g : T ⟶ M.dilatation) (hg : g ≫ M.structureMap = f) :
    M.pullSubset f := by
  rw [← hg]
  exact M.pullSubset_of_over_dilatation' g

theorem pullSubset_of_nonempty (h : Nonempty (M.HomOver f)) : M.pullSubset f :=
  h.elim fun g => M.pullSubset_of_hom f g.1 g.2

theorem isEmpty_homOver (h : ¬ M.pullSubset f) : IsEmpty (M.HomOver f) :=
  not_nonempty_iff.mp fun hne => h (M.pullSubset_of_nonempty f hne)

theorem unique_homOver (hCars : IsCars T (Clos.pullback f M.D))
    (hsub : M.pullSubset f) : Nonempty (Unique (M.HomOver f)) := by
  obtain ⟨g, hg, huniq⟩ := M.universal_property T f hCars hsub
  exact ⟨{ default := ⟨g, hg⟩, uniq := fun x => Subtype.ext (huniq x.1 x.2) }⟩

theorem nonempty_homOver_iff (hCars : IsCars T (Clos.pullback f M.D)) :
    Nonempty (M.HomOver f) ↔ M.pullSubset f :=
  ⟨M.pullSubset_of_nonempty f, fun hsub =>
    (M.unique_homOver f hCars hsub).elim fun _ => ⟨default⟩⟩

theorem representability (hCars : IsCars T (Clos.pullback f M.D)) :
    (M.pullSubset f ∧ Nonempty (Unique (M.HomOver f))) ∨
      (¬ M.pullSubset f ∧ IsEmpty (M.HomOver f)) := by
  by_cases hsub : M.pullSubset f
  · exact Or.inl ⟨hsub, M.unique_homOver f hCars hsub⟩
  · exact Or.inr ⟨hsub, M.isEmpty_homOver f hsub⟩

end PreMultiCenter
end SchemeDilatation
