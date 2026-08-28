import GlobalDilProperties
import MulticenterNonZeroDivisor

/-!
# A dilatation does not create zero-divisors

`PreMultiCenter.structureMap_preserves_nonzerodiv` is the geometric form of
`Multicenter.Dilatation.nonzerodiv_of_nonzerodiv`: on every affine chart of `M.dilatation`
lying over an affine chart `M.cov.obj γ` of `X`, the induced ring map sends
non-zero-divisors to non-zero-divisors.

The proof is the second half of `PreMultiCenter.structureMap_isCars_chart`, with the
distinguished element `(M.localMulticenter γ).elem i` replaced by an arbitrary
non-zero-divisor: `chart_pull_mor_ring` factors the map as the dilatation algebra map
`M.cov.obj γ ⟶ (M.localMulticenter γ)[…]` followed by an open immersion of affines, the
first preserving non-zero-divisors by the ring-level lemma and the second by flatness.

Consequence: a divisor that is already Cartier on `X`, read off the covering `M.cov`,
remains Cartier after pulling back along `M.structureMap`. This is the input to the
`J`-half of the tower formula [Ma23d, Prop. 2.22].
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

variable {X : Scheme.{u+1}}

namespace SchemeDilatation

namespace PreMultiCenter

variable (M : PreMultiCenter X)

/-- On each chart of `M.dilatation`, the structure map preserves non-zero-divisors. -/
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
