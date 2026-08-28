import IteratedSchemeMultiFwd

/-!
# [Ma24, Prop. 4.6]: the backward conditions

Verifies the Cartier and containment conditions for `Bl^{Dν}` along
`Bl^{{nᵢθ*Dᵢ}}_{strict}(Bl^{Dθ}) ⟶ Bl^{Dθ} ⟶ X`, and produces the backward morphism.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

section BackwardMulti

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (ν θ n : M.indnumb → ℕ)
  (hsum : ∀ i, θ i + n i = ν i)
  (hb : M.CarsOnYAll) (hSt : M.ElemNzdOnQuotAll) (γ : M.cov.J) (j : M.indnumb)

/-- The chosen generator of the multi-index second-stage divisor spans the `nⱼ`-th
power of the total-transform ideal. -/
theorem iterCenter_localGen_span :
    Ideal.span {((M.iterCenter θ n hb hSt).localMulticenter γ).elem j} =
      (Ideal.map (algebraMap ((M.multiple θ).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)))
        (M.Dideal j γ)) ^ (n j) := by
  letI : Submodule.IsPrincipal ((Ideal.map (algebraMap ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)))
      (M.Dideal j γ)) ^ (n j)) :=
    (M.iterCenter θ n hb hSt).Dprin j γ
  show Ideal.span {Submodule.IsPrincipal.generator
    ((Ideal.map (algebraMap ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)))
      (M.Dideal j γ)) ^ (n j))} = _
  exact Ideal.span_singleton_generator _

/-- In the multi-index second-stage dilatation, the image of `αⱼ^{θⱼ}` is a
non-zero-divisor. -/
theorem iterChart_alpha_nzd_theta :
    ((algebraMap ((M.iterCenter θ n hb hSt).cov.obj γ)
        (Multicenter.Dilatation
          ((M.iterCenter θ n hb hSt).localMulticenter γ))).comp
      (algebraMap ((M.multiple θ).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ))))
      ((M.localMulticenter γ).elem j) ^ (θ j) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) := by
  set g2 : (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) →+*
      (Multicenter.Dilatation ((M.iterCenter θ n hb hSt).localMulticenter γ)) :=
    (algebraMap ((M.iterCenter θ n hb hSt).cov.obj γ)
      (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) : _ →+* _) with hg2
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) :=
    (algebraMap ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) :
        _ →+* _) with hf
  show (g2.comp f) ((M.localMulticenter γ).elem j) ^ (θ j) ∈ _
  simp only [RingHom.comp_apply]
  have hgen1 : f (((M.multiple θ).localMulticenter γ).elem j) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.multiple θ).localMulticenter γ)) :=
    nonzerodiv_image_single ((M.multiple θ).localMulticenter γ) j
  have hgen1' : g2 (f (((M.multiple θ).localMulticenter γ).elem j)) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) :=
    Multicenter.Dilatation.nonzerodiv_of_nonzerodiv
      (F := (M.iterCenter θ n hb hSt).localMulticenter γ) hgen1
  obtain ⟨u, hu⟩ := M.hom_multipleGen_mem_at γ θ j f
  have h1 : g2 u * (g2 (f ((M.localMulticenter γ).elem j))) ^ (θ j) =
      g2 (f (((M.multiple θ).localMulticenter γ).elem j)) := by
    rw [← map_pow, ← map_mul, hu]
  have h2 : g2 u * (g2 (f ((M.localMulticenter γ).elem j))) ^ (θ j) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) := by
    rw [h1]; exact hgen1'
  exact (mul_mem_nonZeroDivisors.mp h2).2

include hsum in
/-- In the multi-index second-stage dilatation, the image of `αⱼ^{νⱼ}` is a
non-zero-divisor. -/
theorem iterChart_alpha_nzd :
    ((algebraMap ((M.iterCenter θ n hb hSt).cov.obj γ)
        (Multicenter.Dilatation
          ((M.iterCenter θ n hb hSt).localMulticenter γ))).comp
      (algebraMap ((M.multiple θ).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ))))
      ((M.localMulticenter γ).elem j) ^ (ν j) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) := by
  set g2 : (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) →+*
      (Multicenter.Dilatation ((M.iterCenter θ n hb hSt).localMulticenter γ)) :=
    (algebraMap ((M.iterCenter θ n hb hSt).cov.obj γ)
      (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) : _ →+* _) with hg2
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) :=
    (algebraMap ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) :
        _ →+* _) with hf
  show (g2.comp f) ((M.localMulticenter γ).elem j) ^ (ν j) ∈ _
  simp only [RingHom.comp_apply]
  have hθpart : (g2 (f ((M.localMulticenter γ).elem j))) ^ (θ j) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) := by
    have h := M.iterChart_alpha_nzd_theta θ n hb hSt γ j
    simpa only [RingHom.comp_apply] using h
  have hgenH : g2 (((M.iterCenter θ n hb hSt).localMulticenter γ).elem j) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) :=
    nonzerodiv_image_single ((M.iterCenter θ n hb hSt).localMulticenter γ) j
  have hspan2 : Ideal.span
      {((M.iterCenter θ n hb hSt).localMulticenter γ).elem j} =
      Ideal.span {f ((M.localMulticenter γ).elem j) ^ (n j)} := by
    rw [M.iterCenter_localGen_span θ n hb hSt γ j]
    show (Ideal.map f (M.Dideal j γ)) ^ (n j) = _
    rw [M.local_Dideal_span' γ j, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow]
  have hmemH : ((M.iterCenter θ n hb hSt).localMulticenter γ).elem j ∈
      Ideal.span {f ((M.localMulticenter γ).elem j) ^ (n j)} := by
    rw [← hspan2]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmemH
  have h3 : g2 c * (g2 (f ((M.localMulticenter γ).elem j))) ^ (n j) =
      g2 (((M.iterCenter θ n hb hSt).localMulticenter γ).elem j) := by
    rw [← map_pow, ← map_mul, hc]
  have h4 : g2 c * (g2 (f ((M.localMulticenter γ).elem j))) ^ (n j) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) := by
    rw [h3]; exact hgenH
  have hn := (mul_mem_nonZeroDivisors.mp h4).2
  rw [show (ν j : ℕ) = θ j + n j from (hsum j).symm, pow_add]
  exact mul_mem hθpart hn

include hsum in
/-- **The backward containment of [Ma24, Prop. 4.6]**: in the multi-index second-stage
chart, the `j`-th center ideal is contained in the span of `αⱼ^{νⱼ}` — a section of the
center factors through the mono-centered exceptional ideal, which is the second-stage
center by construction. -/
theorem iterChart_M_le :
    Ideal.map ((algebraMap ((M.iterCenter θ n hb hSt).cov.obj γ)
        (Multicenter.Dilatation
          ((M.iterCenter θ n hb hSt).localMulticenter γ))).comp
      (algebraMap ((M.multiple θ).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ))))
        (M.Yideal j γ) ≤
      Ideal.span {((algebraMap ((M.iterCenter θ n hb hSt).cov.obj γ)
        (Multicenter.Dilatation
          ((M.iterCenter θ n hb hSt).localMulticenter γ))).comp
      (algebraMap ((M.multiple θ).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ))))
        ((M.localMulticenter γ).elem j) ^ (ν j)} := by
  set g2 : (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) →+*
      (Multicenter.Dilatation ((M.iterCenter θ n hb hSt).localMulticenter γ)) :=
    (algebraMap ((M.iterCenter θ n hb hSt).cov.obj γ)
      (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γ)) : _ →+* _) with hg2
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) :=
    (algebraMap ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) :
        _ →+* _) with hf
  set fm : (M.cov.obj γ) →+*
      (Multicenter.Dilatation (((M.restrict (fun _ : PUnit => j)).multiple
        (fun _ : PUnit => θ j)).localMulticenter γ)) :=
    (algebraMap ((((M.restrict (fun _ : PUnit => j)).multiple
        (fun _ : PUnit => θ j))).cov.obj γ)
      (Multicenter.Dilatation (((M.restrict (fun _ : PUnit => j)).multiple
        (fun _ : PUnit => θ j)).localMulticenter γ)) : _ →+* _) with hfm
  rw [Ideal.map_le_iff_le_comap]
  intro m hm
  rw [Ideal.mem_comap]
  show (g2.comp f) m ∈ Ideal.span
    {(g2.comp f) ((M.localMulticenter γ).elem j) ^ (ν j)}
  simp only [RingHom.comp_apply]
  -- the mono-centered `z`-step
  have hself : Ideal.map fm ((((M.restrict (fun _ : PUnit => j)).multiple
      (fun _ : PUnit => θ j)).localMulticenter γ).ideal default) ≤
      Ideal.span {fm ((((M.restrict (fun _ : PUnit => j)).multiple
        (fun _ : PUnit => θ j)).localMulticenter γ).elem default)} :=
    Multicenter.self_le (((M.restrict (fun _ : PUnit => j)).multiple
      (fun _ : PUnit => θ j)).localMulticenter γ) default
  have hm2 : fm m ∈ Ideal.span
      {fm ((((M.restrict (fun _ : PUnit => j)).multiple
        (fun _ : PUnit => θ j)).localMulticenter γ).elem default)} :=
    hself (Ideal.mem_map_of_mem _ hm)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hm2
  have hzE : z ∈ (((M.restrict (fun _ : PUnit => j)).multiple
      (fun _ : PUnit => θ j)).localMulticenter γ).exceptIdeal := by
    rw [Multicenter.mem_exceptIdeal]
    show fm ((((M.restrict (fun _ : PUnit => j)).multiple
        (fun _ : PUnit => θ j)).localMulticenter γ).elem default) * z ∈
      Ideal.map fm ((((M.restrict (fun _ : PUnit => j)).multiple
        (fun _ : PUnit => θ j)).localMulticenter γ).ideal default)
    rw [mul_comm, hz]
    exact Ideal.mem_map_of_mem _ hm
  -- transport along the chart comparison
  have hzmulti : (M.projRho j θ γ) z ∈
      ((M.iterCenter θ n hb hSt).localMulticenter γ).ideal j :=
    Ideal.mem_map_of_mem _ hzE
  have htrans : f m = (M.projRho j θ γ) z *
      f (((M.multiple θ).localMulticenter γ).elem j) := by
    have happ := congrArg (M.projRho j θ γ) hz
    rw [map_mul] at happ
    have h1 : (M.projRho j θ γ) (fm m) = f m := M.projRho_algebraMap j θ γ m
    have h2 : (M.projRho j θ γ)
        (fm ((((M.restrict (fun _ : PUnit => j)).multiple
          (fun _ : PUnit => θ j)).localMulticenter γ).elem default)) =
        f (((M.multiple θ).localMulticenter γ).elem j) :=
      M.projRho_algebraMap j θ γ _
    rw [h1, h2] at happ
    exact happ.symm
  -- the exceptional part factors through `αⱼ^{nⱼ}`
  have hselfH : Ideal.map g2
      (((M.iterCenter θ n hb hSt).localMulticenter γ).ideal j) ≤
      Ideal.span {g2 (((M.iterCenter θ n hb hSt).localMulticenter γ).elem j)} :=
    Multicenter.self_le ((M.iterCenter θ n hb hSt).localMulticenter γ) j
  have hz2 : g2 ((M.projRho j θ γ) z) ∈
      Ideal.span {g2 (((M.iterCenter θ n hb hSt).localMulticenter γ).elem j)} :=
    hselfH (Ideal.mem_map_of_mem _ hzmulti)
  have hspan2 : Ideal.span
      {((M.iterCenter θ n hb hSt).localMulticenter γ).elem j} =
      Ideal.span {f ((M.localMulticenter γ).elem j) ^ (n j)} := by
    rw [M.iterCenter_localGen_span θ n hb hSt γ j]
    show (Ideal.map f (M.Dideal j γ)) ^ (n j) = _
    rw [M.local_Dideal_span' γ j, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow]
  have hg2span : Ideal.span
      {g2 (((M.iterCenter θ n hb hSt).localMulticenter γ).elem j)} =
      Ideal.span {g2 (f ((M.localMulticenter γ).elem j)) ^ (n j)} := by
    calc Ideal.span {g2 (((M.iterCenter θ n hb hSt).localMulticenter γ).elem j)}
        = Ideal.map g2 (Ideal.span
            {((M.iterCenter θ n hb hSt).localMulticenter γ).elem j}) := by
          rw [Ideal.map_span, Set.image_singleton]
          rfl
      _ = Ideal.map g2 (Ideal.span
            {f ((M.localMulticenter γ).elem j) ^ (n j)}) := by rw [hspan2]
      _ = Ideal.span {g2 (f ((M.localMulticenter γ).elem j) ^ (n j))} := by
          rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.span {g2 (f ((M.localMulticenter γ).elem j)) ^ (n j)} := by
          rw [map_pow]
  rw [hg2span] at hz2
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hz2
  obtain ⟨u, hu⟩ := M.hom_multipleGen_mem_at γ θ j f
  refine Ideal.mem_span_singleton'.mpr ⟨t * g2 u, ?_⟩
  rw [show (ν j : ℕ) = θ j + n j from (hsum j).symm, pow_add]
  rw [htrans, map_mul, ← ht, ← hu, map_mul, map_pow]
  ring

/-- **Two-stage factorization** for the multi-index second stage: a pull-covering
piece of its dilatation over a chart of `X` factors flatly through the second-stage
chart `(A_γ[G_θ])[H_γ]`. -/
theorem iterBackward_piece_factor
    (γβ : (pull_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
      ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap)).J) :
    ∃ ψ : CommRingCat.of (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γβ.1)) ⟶
        (pull_loc_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
          ((M.iterCenter θ n hb hSt).structureMap ≫
            (M.multiple θ).structureMap) γβ.1).obj γβ.2,
      pull_mor_ring X M.Drep (M.iterCenter θ n hb hSt).dilatation
          ((M.iterCenter θ n hb hSt).structureMap ≫
            (M.multiple θ).structureMap) γβ =
        CommRingCat.ofHom ((algebraMap ((M.iterCenter θ n hb hSt).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((M.iterCenter θ n hb hSt).localMulticenter γβ.1))).comp
          (algebraMap ((M.multiple θ).cov.obj γβ.1)
            (Multicenter.Dilatation
              ((M.multiple θ).localMulticenter γβ.1)))) ≫ ψ ∧
      RingHom.Flat ψ.hom := by
  have hsnd : (pull_loc_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
      ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap) γβ.1).map γβ.2 ≫
      pullback.snd ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap) (M.Drep.cov.map γβ.1) =
      Spec.map (pull_mor_ring X M.Drep (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ) :=
    (spec_map_pull_mor_ring _ _ γβ).symm
  have hcwB : (((pull_loc_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
      ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap) γβ.1).map γβ.2 ≫
      pullback.fst ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap) (M.Drep.cov.map γβ.1)) ≫
      (M.iterCenter θ n hb hSt).structureMap) ≫ (M.multiple θ).structureMap =
      Spec.map (pull_mor_ring X M.Drep (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ) ≫ M.cov.map γβ.1 := by
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc, hsnd]
    rfl
  obtain ⟨sB, hsB1, hsB2⟩ := (M.multiple θ).exists_chart_factorisation' γβ.1
    _ _ hcwB
  have hcwN : ((pull_loc_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
      ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap) γβ.1).map γβ.2 ≫
      pullback.fst ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap) (M.Drep.cov.map γβ.1)) ≫
      (M.iterCenter θ n hb hSt).structureMap =
      Spec.map (Spec.preimage sB) ≫ (M.iterCenter θ n hb hSt).cov.map γβ.1 := by
    rw [Spec.map_preimage]
    exact hsB1.symm
  obtain ⟨sN, hsN1, hsN2⟩ := (M.iterCenter θ n hb hSt).exists_chart_factorisation'
    γβ.1 _ _ hcwN
  refine ⟨Spec.preimage sN, ?_, ?_⟩
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_comp, Spec.map_comp]
    have hsN2' : sN ≫ (M.iterCenter θ n hb hSt).chartHom γβ.1 = sB := by
      rw [hsN2, Spec.map_preimage]
    rw [← hsB2, ← hsN2']
    simp only [Category.assoc]
    rfl
  · haveI hc : IsOpenImmersion ((pull_loc_cov X M.Drep
        (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ.1).map γβ.2 ≫
        pullback.fst ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) (M.Drep.cov.map γβ.1)) :=
      (pull_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap)).map_prop γβ
    haveI hsc : IsOpenImmersion (sN ≫
        (M.iterCenter θ n hb hSt).chartTo γβ.1) := by
      rw [hsN1]
      exact hc
    haveI hsn : IsOpenImmersion sN :=
      IsOpenImmersion.of_comp sN ((M.iterCenter θ n hb hSt).chartTo γβ.1)
    haveI hflat : AlgebraicGeometry.Flat sN := inferInstance
    haveI hflat2 : AlgebraicGeometry.Flat (Spec.map (Spec.preimage sN)) := by
      rw [Spec.map_preimage]
      exact hflat
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Flat)).mp hflat2

include hsum in
/-- Chart form of the backward containment condition. -/
theorem iterBackward_pullSubset_chart (i : M.indnumb)
    (γβ : (pull_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
      ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap)).J) :
    Ideal.map (pull_mor_ring X M.Drep (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ).hom (M.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ).hom
        ((M.Dideal i γβ.1) ^ (ν i)) := by
  obtain ⟨ψ, hψ, -⟩ := M.iterBackward_piece_factor θ n hb hSt γβ
  rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hstep : ∀ (I : Ideal (M.cov.obj γβ.1)),
      Ideal.map ((CommRingCat.Hom.hom ψ).comp
        ((algebraMap ((M.iterCenter θ n hb hSt).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((M.iterCenter θ n hb hSt).localMulticenter γβ.1))).comp
          (algebraMap ((M.multiple θ).cov.obj γβ.1)
            (Multicenter.Dilatation
              ((M.multiple θ).localMulticenter γβ.1))))) I =
      Ideal.map (CommRingCat.Hom.hom ψ)
        (Ideal.map ((algebraMap ((M.iterCenter θ n hb hSt).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((M.iterCenter θ n hb hSt).localMulticenter γβ.1))).comp
          (algebraMap ((M.multiple θ).cov.obj γβ.1)
            (Multicenter.Dilatation
              ((M.multiple θ).localMulticenter γβ.1)))) I) :=
    fun I => (Ideal.map_map _ _).symm
  rw [hstep, hstep]
  refine Ideal.map_mono ?_
  refine le_trans (M.iterChart_M_le ν θ n hsum hb hSt γβ.1 i) ?_
  rw [Ideal.map_pow, M.local_Dideal_span' γβ.1 i, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow]
  exact le_rfl

include hsum in
/-- **The backward containment condition** of [Ma24, Prop. 4.6]. -/
theorem iterBackward_pullSubset :
    (M.multiple ν).pullSubset
      ((M.iterCenter θ n hb hSt).structureMap ≫ (M.multiple θ).structureMap) :=
  ((M.multiple ν).pullSubset_iff _).mpr
    (fun i γβ => M.iterBackward_pullSubset_chart ν θ n hsum hb hSt i γβ)

include hsum in
/-- Chart form of the backward Cartier condition at exponent `ν`. -/
theorem iterBackward_isCars_chart (i : M.indnumb)
    (γβ : (pull_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
      ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap)).J) :
    ∃ g : (pull_loc_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ.1).obj γβ.2,
      (pullback_PreClos X (M.iterCenter θ n hb hSt).dilatation
          ((M.iterCenter θ n hb hSt).structureMap ≫
            (M.multiple θ).structureMap)
          (M.multiple ν).Drep).ideal i γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov X M.Drep
        (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ.1).obj γβ.2) := by
  obtain ⟨ψ, hψ, hflat⟩ := M.iterBackward_piece_factor θ n hb hSt γβ
  refine ⟨ψ.hom (((algebraMap ((M.iterCenter θ n hb hSt).cov.obj γβ.1)
      (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γβ.1))).comp
      (algebraMap ((M.multiple θ).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γβ.1))))
      ((M.localMulticenter γβ.1).elem i) ^ (ν i)), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep
        (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ).hom
        ((M.Dideal i γβ.1) ^ (ν i)) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [M.local_Dideal_span' γβ.1 i, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, RingHom.comp_apply, map_pow]
    rfl
  · exact hflat.preserves_nonzeroDivisors
      (M.iterChart_alpha_nzd ν θ n hsum hb hSt γβ.1 i)

include hsum in
/-- **The backward Cartier condition** of [Ma24, Prop. 4.6]. -/
theorem iterBackward_isCars :
    IsCars (M.iterCenter θ n hb hSt).dilatation
      (Clos.pullback ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap) (M.multiple ν).D) :=
  ⟨pullback_PreClos X (M.iterCenter θ n hb hSt).dilatation
      ((M.iterCenter θ n hb hSt).structureMap ≫ (M.multiple θ).structureMap)
      (M.multiple ν).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun i γβ => M.iterBackward_isCars_chart ν θ n hsum hb hSt i γβ), rfl⟩

include ν hsum in
/-- Chart form of the backward Cartier condition at exponent `θ`. -/
theorem iterBackward_isCars_theta_chart (i : M.indnumb)
    (γβ : (pull_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
      ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap)).J) :
    ∃ g : (pull_loc_cov X M.Drep (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ.1).obj γβ.2,
      (pullback_PreClos X (M.iterCenter θ n hb hSt).dilatation
          ((M.iterCenter θ n hb hSt).structureMap ≫
            (M.multiple θ).structureMap)
          (M.multiple θ).Drep).ideal i γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov X M.Drep
        (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ.1).obj γβ.2) := by
  obtain ⟨ψ, hψ, hflat⟩ := M.iterBackward_piece_factor θ n hb hSt γβ
  refine ⟨ψ.hom (((algebraMap ((M.iterCenter θ n hb hSt).cov.obj γβ.1)
      (Multicenter.Dilatation
        ((M.iterCenter θ n hb hSt).localMulticenter γβ.1))).comp
      (algebraMap ((M.multiple θ).cov.obj γβ.1)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γβ.1))))
      ((M.localMulticenter γβ.1).elem i) ^ (θ i)), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep
        (M.iterCenter θ n hb hSt).dilatation
        ((M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap) γβ).hom
        ((M.Dideal i γβ.1) ^ (θ i)) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [M.local_Dideal_span' γβ.1 i, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, RingHom.comp_apply, map_pow]
    rfl
  · exact hflat.preserves_nonzeroDivisors
      (M.iterChart_alpha_nzd_theta θ n hb hSt γβ.1 i)

include hsum in
/-- The `θ`-level backward Cartier condition. -/
theorem iterBackward_isCars_theta :
    IsCars (M.iterCenter θ n hb hSt).dilatation
      (Clos.pullback ((M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap) (M.multiple θ).D) :=
  ⟨pullback_PreClos X (M.iterCenter θ n hb hSt).dilatation
      ((M.iterCenter θ n hb hSt).structureMap ≫ (M.multiple θ).structureMap)
      (M.multiple θ).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun i γβ => M.iterBackward_isCars_theta_chart ν θ n hsum hb hSt i γβ),
    rfl⟩

include hsum in
/-- **The backward morphism of [Ma24, Prop. 4.6]**. -/
theorem existsUnique_iterMultiBwd :
    ∃! g : (M.iterCenter θ n hb hSt).dilatation ⟶
        (M.multiple ν).dilatation,
      g ≫ (M.multiple ν).structureMap =
        (M.iterCenter θ n hb hSt).structureMap ≫
          (M.multiple θ).structureMap :=
  (M.multiple ν).universal_property _
    ((M.iterCenter θ n hb hSt).structureMap ≫ (M.multiple θ).structureMap)
    (M.iterBackward_isCars ν θ n hsum hb hSt)
    (M.iterBackward_pullSubset ν θ n hsum hb hSt)

end BackwardMulti
end PreMultiCenter

end SchemeDilatation
