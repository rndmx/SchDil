import PolyptychStageIdeal

/-!
# The chart comparison for `υ_{K,J} : 𝔻_K → 𝔻_J`

The exact analogue, for the comparison morphisms `upsilonScheme` of `PolyptychSchemeUpsilon`,
of `IteratedSchemeMultiCore.multiRho` / `multi_chart_cone` for the multiples: a ring
homomorphism `upsRho : chart_γ(𝔻_J) → chart_γ(𝔻_K)` together with the commuting square
`ups_chart_cone`.  This is what lets the two-stage chart computations be run over `𝔻_J`.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter Family
open Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]

/-- The chart of `𝔻_K` is an algebra over the chart of `X` however that base ring is
spelled. -/
instance (priority := low) algDefSpacePair (J K : Finset M.indnumb) (γ : M.cov.J) :
    Algebra ((M.defSpace J).cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ)) :=
  inferInstanceAs (Algebra ((M.defSpace K).cov.obj γ)
    (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ)))

instance algBaseDefSpace (K : Finset M.indnumb) (γ : M.cov.J) :
    Algebra (M.cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ)) :=
  inferInstanceAs (Algebra ((M.defSpace K).cov.obj γ)
    (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ)))

/-- The distinguished element of `𝔻_J` at `j` spans the divisor ideal. -/
theorem defSpace_chart_span (J : Finset M.indnumb) (γ : M.cov.J)
    (j : (M.defSpace J).indnumb) :
    Ideal.span {((M.defSpace J).localMulticenter γ).elem j} =
      ∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γ := by
  letI : Submodule.IsPrincipal ((M.defSpace J).Dideal j γ) := (M.defSpace J).Dprin j γ
  have h1 : Ideal.span {((M.defSpace J).localMulticenter γ).elem j} =
      (M.defSpace J).Dideal j γ :=
    Ideal.span_singleton_generator ((M.defSpace J).Dideal j γ)
  rw [h1]
  rfl

section UpsRho

variable {J K : Finset M.indnumb} (hJK : J ⊆ K) (γ : M.cov.J)

include hJK in
/-- The non-zero-divisor input for the chart comparison `υ_{K,J}`. -/
theorem upsRho_nzd (j : (M.defSpace J).indnumb) :
    algebraMap ((M.defSpace K).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ))
        (((M.defSpace J).localMulticenter γ).elem j) ∈
      nonZeroDivisors (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ)) := by
  classical
  have hprod : algebraMap ((M.defSpace K).cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ))
      (∏ s ∈ J.filter (fun s => j.1 ≤ s), (M.localMulticenter γ).elem s) ∈
      nonZeroDivisors (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ)) := by
    rw [map_prod]
    exact prod_mem fun s hs =>
      M.defSpace_chart_gen_nzd K γ s (hJK (Finset.mem_filter.mp hs).1)
  refine nonZeroDivisors_of_span_singleton_eq ?_ hprod
  have hgen : Ideal.span {((M.defSpace J).localMulticenter γ).elem j} =
      Ideal.span {∏ s ∈ J.filter (fun s => j.1 ≤ s),
        (M.localMulticenter γ).elem s} := by
    rw [M.defSpace_chart_span J γ j, Ideal.span_singleton_finset_prod]
    exact Finset.prod_congr rfl fun s _ => M.local_Dideal_span' γ s
  have h0 := congrArg (Ideal.map (algebraMap ((M.defSpace K).cov.obj γ)
    (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ)) : _ →+* _)) hgen
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton] at h0
  exact h0

include hJK in
/-- The containment input for the chart comparison `υ_{K,J}`. -/
theorem upsRho_gen (j : (M.defSpace J).indnumb) :
    Ideal.map (algebraMap ((M.defSpace K).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ)))
        (M.Yideal j.1 γ) ≤
      Ideal.span {algebraMap ((M.defSpace K).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ))
        (((M.defSpace J).localMulticenter γ).elem j)} := by
  classical
  rw [Ideal.span_singleton_map, M.defSpace_chart_span J γ j]
  refine le_trans (M.defSpace_chart_self_le K γ j.1 (hJK j.2)) (Ideal.map_mono ?_)
  rw [Finset.prod_filter_split hJK (fun s => j.1 ≤ s) (fun s => M.Dideal s γ)]
  exact Ideal.mul_le_right

include hJK in
/-- **The chart comparison ring map** `chart_γ(𝔻_J) → chart_γ(𝔻_K)`. -/
def upsRho :
    Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)
      →ₐ[(M.defSpace J).cov.obj γ]
      Multicenter.Dilatation ((M.defSpace K).localMulticenter γ) :=
  desc ((M.defSpace J).localMulticenter γ) (M.upsRho_nzd hJK γ)
    (fun j => (gen_iff_le ((M.defSpace J).localMulticenter γ) j).mpr
      (M.upsRho_gen hJK γ j))

include hJK in
theorem upsRho_algebraMap (x : M.cov.obj γ) :
    M.upsRho hJK γ (algebraMap ((M.defSpace J).cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) x) =
      algebraMap ((M.defSpace K).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace K).localMulticenter γ)) x :=
  (M.upsRho hJK γ).commutes x

include hJK in
/-- The scheme-level chart comparison. -/
def upsRhoSch : (M.defSpace K).chart γ ⟶ (M.defSpace J).chart γ :=
  Spec.map (CommRingCat.ofHom (M.upsRho hJK γ).toRingHom)

include hJK in
theorem upsRhoSch_chartHom :
    M.upsRhoSch hJK γ ≫ (M.defSpace J).chartHom γ = (M.defSpace K).chartHom γ := by
  rw [upsRhoSch]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact M.upsRho_algebraMap hJK γ a

include hJK in
theorem upsChart_overX :
    ((M.defSpace K).chartTo γ ≫ M.upsilonScheme hJK) ≫ (M.defSpace J).structureMap =
      (M.defSpace K).chartToX γ := by
  rw [Category.assoc, M.upsilonScheme_over hJK,
    (M.defSpace K).structureMap_chart γ]

include hJK in
theorem upsChart_isCars :
    IsCars ((M.defSpace K).chart γ)
      (Clos.pullback ((M.defSpace K).chartToX γ) (M.defSpace J).D) := by
  have heq : (M.defSpace K).chartToX γ =
      (M.defSpace K).chartTo γ ≫ (M.defSpace K).structureMap :=
    ((M.defSpace K).structureMap_chart γ).symm
  rw [heq]
  have hstep : Clos.pullback
      ((M.defSpace K).chartTo γ ≫ (M.defSpace K).structureMap) (M.defSpace J).D =
      pullback_Clos ((M.defSpace K).chartTo γ)
        (Clos.pullback (M.defSpace K).structureMap (M.defSpace J).D) := by
    show pullback_Clos _ (Quotient.mk'' (M.defSpace J).Drep) = _
    rw [pullback_assoc]
    rfl
  rw [hstep]
  haveI : IsOpenImmersion ((M.defSpace K).chartTo γ) :=
    (M.defSpace K).chartTo_isOpenImmersion γ
  haveI : AlgebraicGeometry.Flat ((M.defSpace K).chartTo γ) := inferInstance
  exact pullback_IsCars _ _ _ (M.defSpace_isCars hJK)

include hJK in
theorem upsChart_pullSubset :
    (M.defSpace J).pullSubset ((M.defSpace K).chartToX γ) := by
  have h := (M.defSpace J).pullSubset_of_over_dilatation'
    ((M.defSpace K).chartTo γ ≫ M.upsilonScheme hJK)
  rwa [M.upsChart_overX hJK γ] at h

include hJK in
/-- **The chart cone for `υ_{K,J}`**: on charts, the comparison morphism is `Spec` of the
ring-level `upsRho`. -/
theorem ups_chart_cone :
    (M.defSpace K).chartTo γ ≫ M.upsilonScheme hJK =
      M.upsRhoSch hJK γ ≫ (M.defSpace J).chartTo γ := by
  refine ((M.defSpace J).universal_property ((M.defSpace K).chart γ)
    ((M.defSpace K).chartToX γ) (M.upsChart_isCars hJK γ)
    (M.upsChart_pullSubset hJK γ)).unique ?_ ?_
  · exact M.upsChart_overX hJK γ
  · rw [Category.assoc, (M.defSpace J).structureMap_chart γ,
      show (M.defSpace J).chartToX γ =
        (M.defSpace J).chartHom γ ≫ M.cov.map γ from rfl,
      ← Category.assoc, M.upsRhoSch_chartHom hJK γ]
    show (M.defSpace K).chartHom γ ≫ M.cov.map γ = _
    rfl

end UpsRho

end PreMultiCenter
end SchemeDilatation
