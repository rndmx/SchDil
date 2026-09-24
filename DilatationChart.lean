import GlobalDilProperties

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

variable {X : Scheme.{u+1}}

namespace SchemeDilatation

namespace PreMultiCenter

variable (M : PreMultiCenter X)

theorem localMulticenter_Yideal_le_Dideal (γ : M.cov.J) (i : M.indnumb) :
    Ideal.map (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ))) (M.Yideal i γ) ≤
      Ideal.map (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ))) (M.Dideal i γ) := by
  letI := M.Dprin i γ
  letI : Submodule.IsPrincipal (M.Dideal i γ) := M.Dprin i γ
  have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal
    (F := M.localMulticenter γ) (Finsupp.single i 1)
  rw [familyPow_single, familyPow_single] at h
  have hle : M.Yideal i γ ≤ (M.localMulticenter γ).LargeIdeal i := by
    show (M.localMulticenter γ).ideal i ≤ _
    unfold Multicenter.LargeIdeal
    rw [Submodule.add_eq_sup]
    exact le_sup_left
  refine le_trans (Ideal.map_mono hle) ?_
  rw [← h, ← Ideal.span_singleton_generator (M.Dideal i γ), Ideal.map_span,
    Set.image_singleton]
  exact le_rfl

theorem exists_chart_factorisation (γ : M.cov.J) {C : CommRingCat.{u+1}}
    (c : Spec C ⟶ M.dilatation) (w : M.cov.obj γ ⟶ C)
    (hcw : c ≫ M.structureMap = Spec.map w ≫ M.cov.map γ) :
    ∃ ψ : CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ)) ⟶ C,
      CommRingCat.ofHom (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ))) ≫ ψ = w := by
  set s : Spec C ⟶ Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ))) :=
    pullback.lift c (Spec.map w) hcw ≫ inv (M.chartCompare γ) with hs
  have hsw : s ≫ M.chartHom γ = Spec.map w := by
    rw [hs, Category.assoc, show inv (M.chartCompare γ) ≫ M.chartHom γ =
        pullback.snd M.structureMap (M.cov.map γ) from by
      rw [← M.chartCompare_snd γ, IsIso.inv_hom_id_assoc], pullback.lift_snd]
  refine ⟨Spec.preimage s, ?_⟩
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage]
  exact hsw

theorem Yideal_le_Dideal_of_over_dilatation (γ : M.cov.J) {C : CommRingCat.{u+1}}
    (c : Spec C ⟶ M.dilatation) (w : M.cov.obj γ ⟶ C)
    (hcw : c ≫ M.structureMap = Spec.map w ≫ M.cov.map γ) (i : M.indnumb) :
    Ideal.map w.hom (M.Yideal i γ) ≤ Ideal.map w.hom (M.Dideal i γ) := by
  obtain ⟨ψ, hψ⟩ := M.exists_chart_factorisation γ c w hcw
  rw [← hψ, CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.map_map]
  exact Ideal.map_mono (M.localMulticenter_Yideal_le_Dideal γ i)

end PreMultiCenter

end SchemeDilatation
