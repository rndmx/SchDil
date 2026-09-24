import GlobalDilProperties
import ClosSumSche

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation
namespace PreMultiCenter
variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (ν θ : M.indnumb → ℕ)

noncomputable def multipleDChartDatum (i : M.indnumb) : ChartDatum X where
  cov := M.cov
  idl γ := (M.Dideal i γ) ^ (ν i)
  compat a b hab := by
    rw [Ideal.map_pow, Ideal.map_pow]
    exact congrArg (· ^ (ν i)) (chartIdeal_agree M.Drep a b hab i)

noncomputable def multiple : PreMultiCenter X where
  indnumb := M.indnumb
  cov := M.cov
  Ysub := M.Ysub
  Dsub i := (M.multipleDChartDatum ν i).glued
  Yover := M.Yover
  Dover i := ⟨(M.multipleDChartDatum ν i).structureMap⟩
  Yideal := M.Yideal
  Dideal i γ := (M.Dideal i γ) ^ (ν i)
  YcondIso := M.YcondIso
  YcondOver := M.YcondOver
  DcondIso i γ := asIso ((M.multipleDChartDatum ν i).chartCompare γ)
  DcondOver i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (M.multipleDChartDatum ν i).chartCompare γ ≫
        pullback.snd ((M.multipleDChartDatum ν i).structureMap) (M.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((M.Dideal i γ) ^ (ν i))))
    exact (M.multipleDChartDatum ν i).chartCompare_snd γ
  Dprin i γ := by
    letI : Submodule.IsPrincipal (M.Dideal i γ) := M.Dprin i γ
    exact ⟨⟨(Submodule.IsPrincipal.generator (M.Dideal i γ)) ^ (ν i), by
      rw [Ideal.submodule_span_eq, ← Ideal.span_singleton_pow,
        Ideal.span_singleton_generator]⟩⟩

@[simp] theorem multiple_Dideal (i : M.indnumb) (γ : M.cov.J) :
    (M.multiple ν).Dideal i γ = (M.Dideal i γ) ^ (ν i) := rfl

@[simp] theorem multiple_Yideal (i : M.indnumb) (γ : M.cov.J) :
    (M.multiple ν).Yideal i γ = M.Yideal i γ := rfl

theorem multiple_gen_nzd (i : M.indnumb) (hi : ν i ≠ 0)
    (γβ : (pull_cov X M.Drep (M.multiple ν).dilatation
      (M.multiple ν).structureMap).J) :
    (pull_mor_ring X M.Drep (M.multiple ν).dilatation
        (M.multiple ν).structureMap γβ).hom ((M.localMulticenter γβ.1).elem i) ∈
      nonZeroDivisors ((pull_loc_cov X M.Drep (M.multiple ν).dilatation
        (M.multiple ν).structureMap γβ.1).obj γβ.2) := by
  obtain ⟨g, hg, hgnzd⟩ := (M.multiple ν).structureMap_isCars_chart i γβ
  have hpow : ((pull_mor_ring X M.Drep (M.multiple ν).dilatation
      (M.multiple ν).structureMap γβ).hom
      ((M.localMulticenter γβ.1).elem i)) ^ (ν i) ∈
      nonZeroDivisors ((pull_loc_cov X M.Drep (M.multiple ν).dilatation
        (M.multiple ν).structureMap γβ.1).obj γβ.2) := by
    refine nonZeroDivisors_of_span_singleton_eq ?_ hgnzd
    rw [← hg]
    show Ideal.span {((pull_mor_ring X M.Drep (M.multiple ν).dilatation
        (M.multiple ν).structureMap γβ).hom
        ((M.localMulticenter γβ.1).elem i)) ^ (ν i)} =
      Ideal.map (pull_mor_ring X M.Drep (M.multiple ν).dilatation
        (M.multiple ν).structureMap γβ).hom ((M.Dideal i γβ.1) ^ (ν i))
    rw [Ideal.map_pow, ← Ideal.span_singleton_pow]
    congr 1
    letI : Submodule.IsPrincipal (M.Dideal i γβ.1) := M.Dprin i γβ.1
    conv_rhs => rw [← Ideal.span_singleton_generator (M.Dideal i γβ.1)]
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [hm, pow_succ] at hpow
  exact (mul_mem_nonZeroDivisors.mp hpow).2

theorem multiple_isCars (hθν : ∀ i, θ i ≤ ν i) :
    IsCars (M.multiple ν).dilatation
      (Clos.pullback (M.multiple ν).structureMap (M.multiple θ).D) := by
  refine ⟨pullback_PreClos X (M.multiple ν).dilatation
      (M.multiple ν).structureMap (M.multiple θ).Drep,
    pullback_IsPreCars_of_charts _ _ _ (fun i γβ => ?_), rfl⟩
  refine ⟨((pull_mor_ring X M.Drep (M.multiple ν).dilatation
      (M.multiple ν).structureMap γβ).hom
      ((M.localMulticenter γβ.1).elem i)) ^ (θ i), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep (M.multiple ν).dilatation
        (M.multiple ν).structureMap γβ).hom ((M.Dideal i γβ.1) ^ (θ i)) = _
    rw [Ideal.map_pow, ← Ideal.span_singleton_pow]
    congr 1
    letI : Submodule.IsPrincipal (M.Dideal i γβ.1) := M.Dprin i γβ.1
    conv_lhs => rw [← Ideal.span_singleton_generator (M.Dideal i γβ.1)]
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  · rcases Nat.eq_zero_or_pos (θ i) with h0 | hpos
    · rw [h0, pow_zero]
      exact Submonoid.one_mem _
    · have hν : ν i ≠ 0 := (lt_of_lt_of_le hpos (hθν i)).ne'
      exact pow_mem (M.multiple_gen_nzd ν i hν γβ) (θ i)

theorem multiple_pullSubset_chart (hθν : ∀ i, θ i ≤ ν i) (i : M.indnumb)
    (γβ : (pull_cov X M.Drep (M.multiple ν).dilatation
      (M.multiple ν).structureMap).J) :
    Ideal.map (pull_mor_ring X M.Drep (M.multiple ν).dilatation
        (M.multiple ν).structureMap γβ).hom (M.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep (M.multiple ν).dilatation
        (M.multiple ν).structureMap γβ).hom ((M.Dideal i γβ.1) ^ (θ i)) := by
  have h1 : Ideal.map (pull_mor_ring X M.Drep (M.multiple ν).dilatation
      (M.multiple ν).structureMap γβ).hom (M.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep (M.multiple ν).dilatation
        (M.multiple ν).structureMap γβ).hom ((M.Dideal i γβ.1) ^ (ν i)) :=
    (M.multiple ν).structureMap_pullSubset i γβ
  exact le_trans h1 (Ideal.map_mono (Ideal.pow_le_pow_right (hθν i)))

theorem multiple_pullSubset (hθν : ∀ i, θ i ≤ ν i) :
    (M.multiple θ).pullSubset (M.multiple ν).structureMap :=
  fun i γβ => M.multiple_pullSubset_chart ν θ hθν i γβ

theorem existsUnique_multipleHom (hθν : ∀ i, θ i ≤ ν i) :
    ∃! φ : (M.multiple ν).dilatation ⟶ (M.multiple θ).dilatation,
      φ ≫ (M.multiple θ).structureMap = (M.multiple ν).structureMap :=
  (M.multiple θ).universal_property (M.multiple ν).dilatation
    (M.multiple ν).structureMap (M.multiple_isCars ν θ hθν)
    (M.multiple_pullSubset ν θ hθν)

noncomputable def multipleHom (hθν : ∀ i, θ i ≤ ν i) :
    (M.multiple ν).dilatation ⟶ (M.multiple θ).dilatation :=
  (M.existsUnique_multipleHom ν θ hθν).choose

@[simp] theorem multipleHom_over (hθν : ∀ i, θ i ≤ ν i) :
    M.multipleHom ν θ hθν ≫ (M.multiple θ).structureMap =
      (M.multiple ν).structureMap :=
  (M.existsUnique_multipleHom ν θ hθν).choose_spec.1

theorem multipleHom_unique (hθν : ∀ i, θ i ≤ ν i)
    (g : (M.multiple ν).dilatation ⟶ (M.multiple θ).dilatation)
    (hg : g ≫ (M.multiple θ).structureMap = (M.multiple ν).structureMap) :
    g = M.multipleHom ν θ hθν :=
  (M.existsUnique_multipleHom ν θ hθν).choose_spec.2 g hg

end PreMultiCenter
end SchemeDilatation
