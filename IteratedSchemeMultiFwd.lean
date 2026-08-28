import IteratedSchemeMultiCore

/-!
# [Ma24, Prop. 4.6]: the forward conditions

Verifies the Cartier and containment conditions for the second-stage multicenter
`iterCenter` along the canonical morphism `φ_{ν,θ} : Bl^{Dν} ⟶ Bl^{Dθ}`, and produces the
forward morphism by the universal property.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

section Forward

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (ν θ n : M.indnumb → ℕ)
  (hsum : ∀ i, θ i + n i = ν i)
  (hb : M.CarsOnYAll) (hSt : M.ElemNzdOnQuotAll) (i' : M.indnumb)

include hsum in
/-- `θ ≤ ν` when `θ + n = ν`. -/
theorem le_of_sum : ∀ i, θ i ≤ ν i :=
  fun i => (hsum i) ▸ Nat.le_add_right (θ i) (n i)

include hsum in
/-- `n ≤ ν` when `θ + n = ν`. -/
theorem le_of_sum' : ∀ i, n i ≤ ν i :=
  fun i => (hsum i) ▸ Nat.le_add_left (n i) (θ i)

/-- The factorization of a pull-covering piece of `Bl^{Dν} ×_B chart^θ_γ` through the
chart of `Bl^{Dν}`, compatibly with the multi-index comparison map. -/
theorem iter_piece_factor
    (γβ : (pull_cov (M.multiple θ).dilatation
      (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
      (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))).J) :
    ∃ ψ : CommRingCat.of
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1)) ⟶
        (pull_loc_cov (M.multiple θ).dilatation
          (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
          (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ.1).obj γβ.2,
      pull_mor_ring (M.multiple θ).dilatation
          (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
          (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ =
        CommRingCat.ofHom
          (M.multiRho ν θ (M.le_of_sum ν θ n hsum) γβ.1).toRingHom ≫ ψ ∧
      RingHom.Flat ψ.hom := by
  have hsnd : (pull_loc_cov (M.multiple θ).dilatation
      (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
      (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ.1).map γβ.2 ≫
      pullback.snd (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))
        ((M.iterCenter θ n hb hSt).Drep.cov.map γβ.1) =
      Spec.map (pull_mor_ring (M.multiple θ).dilatation
        (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
        (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ) :=
    (spec_map_pull_mor_ring _ _ γβ).symm
  have hcφ : ((pull_loc_cov (M.multiple θ).dilatation
      (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
      (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ.1).map γβ.2 ≫
      pullback.fst (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))
        ((M.iterCenter θ n hb hSt).Drep.cov.map γβ.1)) ≫
      M.multipleHom ν θ (M.le_of_sum ν θ n hsum) =
      Spec.map (pull_mor_ring (M.multiple θ).dilatation
        (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
        (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ) ≫
      (M.multiple θ).chartTo γβ.1 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd]
    rfl
  have hcw : ((pull_loc_cov (M.multiple θ).dilatation
      (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
      (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ.1).map γβ.2 ≫
      pullback.fst (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))
        ((M.iterCenter θ n hb hSt).Drep.cov.map γβ.1)) ≫
      (M.multiple ν).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ((M.multiple θ).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γβ.1))) ≫
        pull_mor_ring (M.multiple θ).dilatation
          (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
          (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ) ≫
      M.cov.map γβ.1 := by
    rw [← M.multipleHom_over ν θ (M.le_of_sum ν θ n hsum), ← Category.assoc,
      hcφ, Spec.map_comp]
    rw [Category.assoc, Category.assoc, (M.multiple θ).structureMap_chart γβ.1]
    rfl
  obtain ⟨sT, hsT1, hsT2⟩ := (M.multiple ν).exists_chart_factorisation' γβ.1
    _ _ hcw
  haveI : IsOpenImmersion ((M.multiple θ).chartTo γβ.1) :=
    (M.multiple θ).chartTo_isOpenImmersion γβ.1
  haveI : Mono ((M.multiple θ).chartTo γβ.1) := inferInstance
  have hkey : Spec.map (pull_mor_ring (M.multiple θ).dilatation
      (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
      (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ) =
      sT ≫ M.multiRhoSch ν θ (M.le_of_sum ν θ n hsum) γβ.1 := by
    apply Mono.right_cancellation (f := (M.multiple θ).chartTo γβ.1)
    rw [← hcφ]
    simp only [Category.assoc]
    rw [← M.multi_chart_cone ν θ (M.le_of_sum ν θ n hsum) γβ.1,
      reassoc_of% hsT1]
  refine ⟨Spec.preimage sT, ?_, ?_⟩
  · apply Spec.map_injective
    rw [hkey, Spec.map_comp, Spec.map_preimage]
    rfl
  · haveI hc : IsOpenImmersion ((pull_loc_cov (M.multiple θ).dilatation
        (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
        (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ.1).map γβ.2 ≫
        pullback.fst (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))
          ((M.iterCenter θ n hb hSt).Drep.cov.map γβ.1)) :=
      (pull_cov (M.multiple θ).dilatation (M.iterCenter θ n hb hSt).Drep
        (M.multiple ν).dilatation
        (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))).map_prop γβ
    haveI hsc : IsOpenImmersion (sT ≫ (M.multiple ν).chartTo γβ.1) := by
      rw [hsT1]
      exact hc
    haveI hs : IsOpenImmersion sT :=
      IsOpenImmersion.of_comp sT ((M.multiple ν).chartTo γβ.1)
    haveI hflat : AlgebraicGeometry.Flat sT := inferInstance
    haveI hflat2 : AlgebraicGeometry.Flat (Spec.map (Spec.preimage sT)) := by
      rw [Spec.map_preimage]
      exact hflat
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Flat)).mp hflat2

/-- The composite chart map is the algebra map, on the base. -/
theorem iterRho_comp_algebraMap (γ : M.cov.J) :
    ((M.multiRho ν θ (M.le_of_sum ν θ n hsum) γ).toRingHom.comp
      (M.projRho i' θ γ).toRingHom).comp
      (algebraMap ((((M.restrict (fun _ : PUnit => i')).multiple
        (fun _ : PUnit => θ i'))).cov.obj γ)
        (Multicenter.Dilatation (((M.restrict (fun _ : PUnit => i')).multiple
          (fun _ : PUnit => θ i')).localMulticenter γ))) =
    (algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :
        _ →+* _) := by
  ext a
  exact (congrArg (M.multiRho ν θ (M.le_of_sum ν θ n hsum) γ)
    (M.projRho_algebraMap i' θ γ a)).trans
    (M.multiRho_algebraMap ν θ (M.le_of_sum ν θ n hsum) γ a)

/-- Chart form of the containment condition of the multi-index second stage. -/
theorem iterCenter_pullSubset_chart (i : M.indnumb)
    (γβ : (pull_cov (M.multiple θ).dilatation
      (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
      (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))).J) :
    Ideal.map (pull_mor_ring (M.multiple θ).dilatation
        (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
        (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ).hom
        ((M.iterCenter θ n hb hSt).Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring (M.multiple θ).dilatation
        (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
        (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ).hom
        ((M.iterCenter θ n hb hSt).Dideal i γβ.1) := by
  obtain ⟨ψ, hψ, -⟩ := M.iter_piece_factor ν θ n hsum hb hSt γβ
  rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  set f : (M.cov.obj γβ.1) →+*
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1)) :=
    (algebraMap ((M.multiple ν).cov.obj γβ.1)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1)) :
        _ →+* _) with hf
  have hstep : ∀ (I : Ideal (Multicenter.Dilatation
      ((M.multiple θ).localMulticenter γβ.1))),
      Ideal.map ((CommRingCat.Hom.hom ψ).comp
        (M.multiRho ν θ (M.le_of_sum ν θ n hsum) γβ.1).toRingHom) I =
      Ideal.map (CommRingCat.Hom.hom ψ)
        (Ideal.map (M.multiRho ν θ (M.le_of_sum ν θ n hsum) γβ.1).toRingHom
          I) := fun I => (Ideal.map_map _ _).symm
  rw [hstep, hstep]
  refine Ideal.map_mono ?_
  rw [iterCenter_Yideal, iterCenter_Dideal, Ideal.map_map]
  have habs := Multicenter.map_exceptIdeal_le_span
    (G := ((M.restrict (fun _ : PUnit => i)).multiple
      (fun _ : PUnit => θ i)).localMulticenter γβ.1)
    (ρ := (M.multiRho ν θ (M.le_of_sum ν θ n hsum) γβ.1).toRingHom.comp
      (M.projRho i θ γβ.1).toRingHom)
    (α := f) (M.iterRho_comp_algebraMap ν θ n hsum i γβ.1)
    (f ((M.localMulticenter γβ.1).elem i) ^ (n i)) ?_ ?_
  · refine le_trans habs (le_of_eq ?_)
    rw [Ideal.map_pow, Ideal.map_map,
      show ((M.multiRho ν θ (M.le_of_sum ν θ n hsum) γβ.1).toRingHom).comp
        (algebraMap ((M.multiple θ).cov.obj γβ.1)
          (Multicenter.Dilatation ((M.multiple θ).localMulticenter γβ.1))) =
        f from RingHom.ext fun a =>
          M.multiRho_algebraMap ν θ (M.le_of_sum ν θ n hsum) γβ.1 a,
      M.local_Dideal_span' γβ.1 i, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow]
  · -- the center maps into `gen_θ · α^n`
    show Ideal.map f (M.Yideal i γβ.1) ≤ _
    have h1 : Ideal.map f (M.Yideal i γβ.1) ≤
        Ideal.span {f ((M.localMulticenter γβ.1).elem i) ^ (ν i)} :=
      M.chart_M_le_alpha_pow' γβ.1 ν i
    refine le_trans h1 (le_of_eq ?_)
    have hsplit : f ((M.localMulticenter γβ.1).elem i) ^ (ν i) =
        f ((M.localMulticenter γβ.1).elem i) ^ (θ i) *
          f ((M.localMulticenter γβ.1).elem i) ^ (n i) := by
      rw [← pow_add, hsum i]
    rw [hsplit, ← Ideal.span_singleton_mul_span_singleton,
      ← M.hom_multipleGen_span' γβ.1 θ i f,
      Ideal.span_singleton_mul_span_singleton]
    rfl
  · -- the distinguished element of `G_θ` is a non-zero-divisor in `A_γ[G_ν]`
    show f ((((M.restrict (fun _ : PUnit => i)).multiple
      (fun _ : PUnit => θ i)).localMulticenter γβ.1).elem default) ∈ _
    exact M.chart_gen_nzd' γβ.1 ν θ i (M.le_of_sum ν θ n hsum i)

/-- **The containment condition of the multi-index second stage holds along the
canonical morphism** `Bl^{Dν} ⟶ Bl^{Dθ}`. -/
theorem iterCenter_pullSubset :
    (M.iterCenter θ n hb hSt).pullSubset
      (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) :=
  ((M.iterCenter θ n hb hSt).pullSubset_iff _).mpr
    (fun i γβ => M.iterCenter_pullSubset_chart ν θ n hsum hb hSt i γβ)

/-- Chart form of the Cartier condition of the multi-index second stage. -/
theorem iterCenter_isCars_chart (i : M.indnumb)
    (γβ : (pull_cov (M.multiple θ).dilatation
      (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
      (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))).J) :
    ∃ g : (pull_loc_cov (M.multiple θ).dilatation
        (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
        (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ.1).obj γβ.2,
      (pullback_PreClos (M.multiple θ).dilatation
          (M.multiple ν).dilatation
          (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))
          (M.iterCenter θ n hb hSt).Drep).ideal i γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov (M.multiple θ).dilatation
        (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
        (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ.1).obj γβ.2) := by
  obtain ⟨ψ, hψ, hflat⟩ := M.iter_piece_factor ν θ n hsum hb hSt γβ
  refine ⟨ψ.hom ((algebraMap ((M.multiple ν).cov.obj γβ.1)
    (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1)))
      ((M.localMulticenter γβ.1).elem i)) ^ (n i), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring (M.multiple θ).dilatation
        (M.iterCenter θ n hb hSt).Drep (M.multiple ν).dilatation
        (M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) γβ).hom
        ((M.iterCenter θ n hb hSt).Dideal i γβ.1) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [iterCenter_Dideal]
    rw [Ideal.map_pow, Ideal.map_map, RingHom.comp_assoc,
      show ((M.multiRho ν θ (M.le_of_sum ν θ n hsum) γβ.1).toRingHom).comp
        (algebraMap ((M.multiple θ).cov.obj γβ.1)
          (Multicenter.Dilatation ((M.multiple θ).localMulticenter γβ.1))) =
        (algebraMap ((M.multiple ν).cov.obj γβ.1)
          (Multicenter.Dilatation ((M.multiple ν).localMulticenter γβ.1))) from
      RingHom.ext fun a =>
        M.multiRho_algebraMap ν θ (M.le_of_sum ν θ n hsum) γβ.1 a,
      ← Ideal.map_map]
    rw [M.local_Dideal_span' γβ.1 i, Ideal.map_span, Set.image_singleton,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    rfl
  · rw [← map_pow]
    exact hflat.preserves_nonzeroDivisors
      (M.chart_alpha_pow_nzd' γβ.1 ν n i (M.le_of_sum' ν θ n hsum i))

/-- **The Cartier condition of the multi-index second stage holds along the canonical
morphism.** -/
theorem iterCenter_isCars :
    IsCars (M.multiple ν).dilatation
      (Clos.pullback (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))
        (M.iterCenter θ n hb hSt).D) :=
  ⟨pullback_PreClos (M.multiple θ).dilatation (M.multiple ν).dilatation
      (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))
      (M.iterCenter θ n hb hSt).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun i γβ => M.iterCenter_isCars_chart ν θ n hsum hb hSt i γβ), rfl⟩

/-- **The forward morphism of [Ma24, Prop. 4.6]**. -/
theorem existsUnique_iterMultiFwd :
    ∃! g : (M.multiple ν).dilatation ⟶
        (M.iterCenter θ n hb hSt).dilatation,
      g ≫ (M.iterCenter θ n hb hSt).structureMap =
        M.multipleHom ν θ (M.le_of_sum ν θ n hsum) :=
  (M.iterCenter θ n hb hSt).universal_property _
    (M.multipleHom ν θ (M.le_of_sum ν θ n hsum))
    (M.iterCenter_isCars ν θ n hsum hb hSt)
    (M.iterCenter_pullSubset ν θ n hsum hb hSt)

end Forward
end PreMultiCenter

end SchemeDilatation
