import GlobalDilProperties
import MulticenterNonZeroDivisor

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

variable {X : Scheme.{u+1}}

namespace SchemeDilatation

namespace PreMultiCenter

variable (M : PreMultiCenter X)

theorem structureMap_preserves_nonzerodiv
    (γβ : (pull_cov X M.Drep M.dilatation M.structureMap).J)
    {a : M.cov.obj γβ.1} (ha : a ∈ nonZeroDivisors (M.cov.obj γβ.1)) :
    (pull_mor_ring X M.Drep M.dilatation M.structureMap γβ).hom a ∈
      nonZeroDivisors
        ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) := by
  classical
  set mr := Spec.preimage
    ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).map γβ.2 ≫
      inv (M.chartCompare γβ.1)) with hmr
  have hmr_eq : Spec.map mr =
      (pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).map γβ.2 ≫
        inv (M.chartCompare γβ.1) := Spec.map_preimage _
  letI : Algebra (Multicenter.Dilatation (M.localMulticenter γβ.1))
      ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) :=
    mr.hom.toAlgebra
  haveI : IsOpenImmersion
      (Spec ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2) ↘
        Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γβ.1)))) := by
    show IsOpenImmersion (Spec.map (CommRingCat.ofHom mr.hom))
    rw [CommRingCat.ofHom_hom, hmr_eq]
    infer_instance
  have hflat : RingHom.Flat (algebraMap (Multicenter.Dilatation (M.localMulticenter γβ.1))
      ((pull_loc_cov X M.Drep M.dilatation M.structureMap γβ.1).obj γβ.2)) :=
    open_flat_ring _ _
  rw [chart_pull_mor_ring]
  show mr.hom ((algebraMap (M.cov.obj γβ.1)
    (Multicenter.Dilatation (M.localMulticenter γβ.1))) a) ∈ _
  exact hflat.preserves_nonzeroDivisors
    (Multicenter.Dilatation.nonzerodiv_of_nonzerodiv ha)

end PreMultiCenter

end SchemeDilatation
