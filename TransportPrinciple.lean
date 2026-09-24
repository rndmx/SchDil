import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import PreClosAndClos

suppress_compilation

universe u v

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry
namespace Scheme
namespace IdealSheafData

variable {X : Scheme.{u}}

theorem le_of_le_on_cover {I J : X.IdealSheafData} {ι : Type v}
    (U : ι → X.affineOpens) (hcov : ∀ x : X, ∃ i, x ∈ (U i).1)
    (h : ∀ i, I.ideal (U i) ≤ J.ideal (U i)) : I ≤ J := by
  rw [le_def]
  intro V
  rw [V.2.ideal_le_iff]
  intro x hxV
  obtain ⟨i, hxi⟩ := hcov x
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter V.2 (U i).2 x ⟨hxV, hxi⟩

  set W : X.affineOpens := X.affineBasicOpen f with hW
  have hWV : W ≤ V := X.affineBasicOpen_le f
  have hWU : W ≤ U i := by
    rw [hW]
    show X.basicOpen f ≤ (U i).1
    rw [hfg]
    exact X.basicOpen_le g
  have hxW : x ∈ W.1 := hxf

  have hle : I.ideal W ≤ J.ideal W := by
    rw [← I.map_ideal hWU, ← J.map_ideal hWU]
    exact Ideal.map_mono (h i)

  have hfac : (X.presheaf.germ V x hxV).hom =
      (X.presheaf.germ W x hxW).hom.comp
        (X.presheaf.map (homOfLE hWV).op).hom := by
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom
      (X.presheaf.germ_res (homOfLE hWV) x hxW).symm
  rw [hfac, ← Ideal.map_map, ← Ideal.map_map, I.map_ideal hWV, J.map_ideal hWV]
  exact Ideal.map_mono hle

end IdealSheafData

namespace Hom

variable {X Y : Scheme.{u}}

theorem ker_le_ker_of_cover {S T : Scheme.{u}} (f : S ⟶ Y) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiCompact g] {ι : Type v}
    (U : ι → Y.affineOpens) (hcov : ∀ y : Y, ∃ i, y ∈ (U i).1)
    (h : ∀ i, RingHom.ker (f.app (U i)).hom ≤ RingHom.ker (g.app (U i)).hom) :
    f.ker ≤ g.ker :=
  IdealSheafData.le_of_le_on_cover U hcov
    (fun i => by rw [Hom.ker_apply, Hom.ker_apply]; exact h i)

theorem ker_le_ker_everywhere {S T : Scheme.{u}} (f : S ⟶ Y) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiCompact g] {ι : Type v}
    (U : ι → Y.affineOpens) (hcov : ∀ y : Y, ∃ i, y ∈ (U i).1)
    (h : ∀ i, RingHom.ker (f.app (U i)).hom ≤ RingHom.ker (g.app (U i)).hom)
    (V : Y.affineOpens) :
    RingHom.ker (f.app V).hom ≤ RingHom.ker (g.app V).hom := by
  have := ker_le_ker_of_cover f g U hcov h
  rw [← Hom.ker_apply f V, ← Hom.ker_apply g V]
  exact this V

end Hom

end Scheme
end AlgebraicGeometry
