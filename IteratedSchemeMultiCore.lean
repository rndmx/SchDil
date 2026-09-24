import SchemeLemma44

suppress_compilation
universe u
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace Multicenter

theorem map_exceptIdeal_le_span {A C : Type (u+1)} [CommRing A] [CommRing C]
    (G : Multicenter A) [Unique G.index]
    (ρ : Multicenter.Dilatation G →+* C) (α : A →+* C)
    (hρα : ρ.comp (algebraMap A (Multicenter.Dilatation G)) = α)
    (g : C)
    (hM : Ideal.map α (G.ideal default) ≤
      Ideal.span {α (G.elem default) * g})
    (hnzd : α (G.elem default) ∈ nonZeroDivisors C) :
    Ideal.map ρ G.exceptIdeal ≤ Ideal.span {g} := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  have hx' := G.mem_exceptIdeal.mp hx
  have h1 : ρ (algebraMap A (Multicenter.Dilatation G) (G.elem default) * x) ∈
      Ideal.map ρ (Ideal.map (algebraMap A (Multicenter.Dilatation G))
        (G.ideal default)) := Ideal.mem_map_of_mem _ hx'
  rw [Ideal.map_map, hρα, map_mul,
    show ρ (algebraMap A (Multicenter.Dilatation G) (G.elem default)) =
      α (G.elem default) from by rw [← hρα]; rfl] at h1
  have h2 := hM h1
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h2
  have hcalc : α (G.elem default) * (ρ x - z * g) = 0 := by
    rw [mul_sub, ← hz]
    ring
  have hx0 := sub_eq_zero.mp
    ((mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd).mp hcalc)
  rw [hx0]
  exact Ideal.mem_span_singleton'.mpr ⟨z, rfl⟩

end Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

section PullSubsetIff

theorem pullSubset_iff {X : Scheme.{u+1}} (M : PreMultiCenter X)
    {T : Scheme.{u+1}} (f : T ⟶ X) :
    M.pullSubset f ↔
      ∀ (i : M.indnumb) (γβ : (pull_cov X M.Drep T f).J),
        Ideal.map (pull_mor_ring X M.Drep T f γβ).hom (M.Yideal i γβ.1) ≤
          Ideal.map (pull_mor_ring X M.Drep T f γβ).hom (M.Dideal i γβ.1) :=
  Iff.rfl

end PullSubsetIff

section RestrictMultiple

variable {X : Scheme.{u+1}} (M : PreMultiCenter X)

theorem restrict_multiple_comm {J : Type} (ι : J → M.indnumb)
    (ν : M.indnumb → ℕ) :
    (M.multiple ν).restrict ι = (M.restrict ι).multiple (fun k => ν (ι k)) := rfl

end RestrictMultiple

section PerIndexRing

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (γ : M.cov.J)

theorem local_Dideal_span' (i : M.indnumb) :
    M.Dideal i γ = Ideal.span {(M.localMulticenter γ).elem i} := by
  letI : Submodule.IsPrincipal (M.Dideal i γ) := M.Dprin i γ
  exact (Ideal.span_singleton_generator (M.Dideal i γ)).symm

theorem multiple_localGen_span' (w : M.indnumb → ℕ) (i : M.indnumb) :
    Ideal.span {((M.multiple w).localMulticenter γ).elem i} =
      (M.Dideal i γ) ^ (w i) := by
  letI : Submodule.IsPrincipal ((M.Dideal i γ) ^ (w i)) :=
    (M.multiple w).Dprin i γ
  show Ideal.span {Submodule.IsPrincipal.generator ((M.Dideal i γ) ^ (w i))} = _
  exact Ideal.span_singleton_generator _

section RingHomTarget

variable {B : Type (u+1)} [CommRing B]

theorem hom_multipleGen_span' (w : M.indnumb → ℕ) (i : M.indnumb)
    (f : (M.cov.obj γ) →+* B) :
    Ideal.span {f (((M.multiple w).localMulticenter γ).elem i)} =
      Ideal.span {f ((M.localMulticenter γ).elem i) ^ (w i)} := by
  have h1 : Ideal.span {f (((M.multiple w).localMulticenter γ).elem i)} =
      Ideal.map f ((M.Dideal i γ) ^ (w i)) := by
    rw [← M.multiple_localGen_span' γ w i, Ideal.map_span, Set.image_singleton]
  rw [h1, Ideal.map_pow, M.local_Dideal_span' γ i, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow]

theorem hom_multipleGen_mem_at (w : M.indnumb → ℕ) (i : M.indnumb)
    (f : (M.cov.obj γ) →+* B) :
    ∃ u : B, u * f ((M.localMulticenter γ).elem i) ^ (w i) =
      f (((M.multiple w).localMulticenter γ).elem i) :=
  Ideal.mem_span_singleton'.mp (by
    rw [← M.hom_multipleGen_span' γ w i f]
    exact Ideal.mem_span_singleton_self _)

theorem hom_multipleGen_mem_at' (w : M.indnumb → ℕ) (i : M.indnumb)
    (f : (M.cov.obj γ) →+* B) :
    ∃ v : B, v * f (((M.multiple w).localMulticenter γ).elem i) =
      f ((M.localMulticenter γ).elem i) ^ (w i) :=
  Ideal.mem_span_singleton'.mp (by
    rw [M.hom_multipleGen_span' γ w i f]
    exact Ideal.mem_span_singleton_self _)

end RingHomTarget

theorem chart_alpha_pow_nzd' (w k : M.indnumb → ℕ) (i : M.indnumb)
    (hkw : k i ≤ w i) :
    (algebraMap ((M.multiple w).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ))
        ((M.localMulticenter γ).elem i)) ^ (k i) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) := by
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :=
    (algebraMap ((M.multiple w).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :
        _ →+* _) with hf
  show f ((M.localMulticenter γ).elem i) ^ (k i) ∈ nonZeroDivisors _
  have hgen : f (((M.multiple w).localMulticenter γ).elem i) ∈
      nonZeroDivisors _ :=
    nonzerodiv_image_single ((M.multiple w).localMulticenter γ) i
  obtain ⟨u, hu⟩ := M.hom_multipleGen_mem_at γ w i f
  have h2 : u * f ((M.localMulticenter γ).elem i) ^ (w i) ∈
      nonZeroDivisors _ := by
    rw [hu]; exact hgen
  have hpow := (mul_mem_nonZeroDivisors.mp h2).2
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hkw
  rw [hm, pow_add] at hpow
  exact (mul_mem_nonZeroDivisors.mp hpow).1

theorem chart_gen_nzd' (w k : M.indnumb → ℕ) (i : M.indnumb) (hkw : k i ≤ w i) :
    algebraMap ((M.multiple w).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ))
        (((M.multiple k).localMulticenter γ).elem i) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) := by
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :=
    (algebraMap ((M.multiple w).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :
        _ →+* _) with hf
  show f (((M.multiple k).localMulticenter γ).elem i) ∈ nonZeroDivisors _
  obtain ⟨v, hv⟩ := M.hom_multipleGen_mem_at' γ k i f
  have h : v * f (((M.multiple k).localMulticenter γ).elem i) ∈
      nonZeroDivisors _ := by
    rw [hv]
    exact M.chart_alpha_pow_nzd' γ w k i hkw
  exact (mul_mem_nonZeroDivisors.mp h).2

theorem chart_M_le_alpha_pow' (w : M.indnumb → ℕ) (i : M.indnumb) :
    Ideal.map (algebraMap ((M.multiple w).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)))
        (M.Yideal i γ) ≤
      Ideal.span {algebraMap ((M.multiple w).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple w).localMulticenter γ))
        ((M.localMulticenter γ).elem i) ^ (w i)} := by
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :=
    (algebraMap ((M.multiple w).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple w).localMulticenter γ)) :
        _ →+* _) with hf
  show Ideal.map f (M.Yideal i γ) ≤
    Ideal.span {f ((M.localMulticenter γ).elem i) ^ (w i)}
  have h1 : Ideal.map f (((M.multiple w).localMulticenter γ).ideal i) ≤
      Ideal.span {f (((M.multiple w).localMulticenter γ).elem i)} :=
    Multicenter.self_le ((M.multiple w).localMulticenter γ) i
  rw [M.hom_multipleGen_span' γ w i f] at h1
  exact h1

end PerIndexRing

section MonoAt

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (i : M.indnumb)
  (θ : M.indnumb → ℕ)

instance restrict_indnumb_unique :
    Unique (M.restrict (fun _ : PUnit => i)).indnumb :=
  inferInstanceAs (Unique PUnit)

def CarsOnYAll : Prop :=
  ∀ j : M.indnumb, (M.restrict (fun _ : PUnit => j)).CarsOnY

def ElemNzdOnQuotAll : Prop :=
  ∀ j : M.indnumb, (M.restrict (fun _ : PUnit => j)).ElemNzdOnQuot

noncomputable def projAt :
    (M.multiple θ).dilatation ⟶
      ((M.multiple θ).restrict (fun _ : PUnit => i)).dilatation :=
  ((M.multiple θ).exists_unique_hom_restrict (fun _ : PUnit => i)).choose

@[simp] theorem projAt_over :
    M.projAt i θ ≫
      ((M.multiple θ).restrict (fun _ : PUnit => i)).structureMap =
      (M.multiple θ).structureMap :=
  ((M.multiple θ).exists_unique_hom_restrict (fun _ : PUnit => i)).choose_spec.1

theorem projAt_unique
    (g : (M.multiple θ).dilatation ⟶
      ((M.multiple θ).restrict (fun _ : PUnit => i)).dilatation)
    (hg : g ≫ ((M.multiple θ).restrict (fun _ : PUnit => i)).structureMap =
      (M.multiple θ).structureMap) : g = M.projAt i θ :=
  ((M.multiple θ).exists_unique_hom_restrict
    (fun _ : PUnit => i)).choose_spec.2 g hg

variable (γ : M.cov.J)

noncomputable instance restrictChartAlgebraBridge :
    Algebra (((M.multiple θ).restrict (fun _ : PUnit => i)).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) :=
  inferInstanceAs (Algebra ((M.multiple θ).cov.obj γ)
    (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)))

theorem projRho_nzd :
    ∀ k, algebraMap
        (((M.multiple θ).restrict (fun _ : PUnit => i)).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ))
        ((((M.multiple θ).restrict (fun _ : PUnit => i)).localMulticenter γ).elem
          k) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) := by
  intro k
  exact nonzerodiv_image_single ((M.multiple θ).localMulticenter γ) i

theorem projRho_gen :
    ∀ k, Ideal.span {algebraMap
        (((M.multiple θ).restrict (fun _ : PUnit => i)).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ))
        ((((M.multiple θ).restrict (fun _ : PUnit => i)).localMulticenter γ).elem
          k)} =
      Ideal.map (algebraMap
        (((M.multiple θ).restrict (fun _ : PUnit => i)).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)))
        ((((M.multiple θ).restrict
          (fun _ : PUnit => i)).localMulticenter γ).LargeIdeal k) := by
  intro k
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) :=
    (algebraMap ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) :
        _ →+* _) with hf
  have hle : Ideal.map f (M.Yideal i γ) ≤
      Ideal.span {f (((M.multiple θ).localMulticenter γ).elem i)} := by
    have h1 : Ideal.map f (M.Yideal i γ) ≤
        Ideal.span {f ((M.localMulticenter γ).elem i) ^ (θ i)} :=
      M.chart_M_le_alpha_pow' γ θ i
    rw [← M.hom_multipleGen_span' γ θ i f] at h1
    exact h1
  show Ideal.span {f (((M.multiple θ).localMulticenter γ).elem i)} =
    Ideal.map f ((M.Yideal i γ) +
      (Ideal.span {((M.multiple θ).localMulticenter γ).elem i} :
        Ideal (M.cov.obj γ)))
  rw [Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact (sup_eq_right.mpr hle).symm

noncomputable def projRho :
    Multicenter.Dilatation
        ((((M.multiple θ).restrict
          (fun _ : PUnit => i))).localMulticenter γ)
      →ₐ[(((M.multiple θ).restrict (fun _ : PUnit => i))).cov.obj γ]
      Multicenter.Dilatation ((M.multiple θ).localMulticenter γ) :=
  desc ((((M.multiple θ).restrict (fun _ : PUnit => i))).localMulticenter γ)
    (M.projRho_nzd i θ γ) (M.projRho_gen i θ γ)

theorem projRho_algebraMap (x : (M.cov.obj γ)) :
    M.projRho i θ γ (algebraMap
      ((((M.multiple θ).restrict (fun _ : PUnit => i))).cov.obj γ)
      (Multicenter.Dilatation
        ((((M.multiple θ).restrict (fun _ : PUnit => i))).localMulticenter γ))
      x) =
    algebraMap ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) x :=
  (M.projRho i θ γ).commutes x

noncomputable def projRhoSch :
    (M.multiple θ).chart γ ⟶
      ((M.multiple θ).restrict (fun _ : PUnit => i)).chart γ :=
  Spec.map (CommRingCat.ofHom (M.projRho i θ γ).toRingHom)

theorem projRhoSch_chartHom :
    M.projRhoSch i θ γ ≫
      ((M.multiple θ).restrict (fun _ : PUnit => i)).chartHom γ =
      (M.multiple θ).chartHom γ := by
  rw [projRhoSch]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact M.projRho_algebraMap i θ γ a

theorem projChart_overX :
    ((M.multiple θ).chartTo γ ≫ M.projAt i θ) ≫
      ((M.multiple θ).restrict (fun _ : PUnit => i)).structureMap =
      (M.multiple θ).chartToX γ := by
  rw [Category.assoc, M.projAt_over i θ, (M.multiple θ).structureMap_chart γ]

theorem projChart_isCars :
    IsCars ((M.multiple θ).chart γ)
      (Clos.pullback ((M.multiple θ).chartToX γ)
        ((M.multiple θ).restrict (fun _ : PUnit => i)).D) := by
  have heq : (M.multiple θ).chartToX γ =
      (M.multiple θ).chartTo γ ≫ (M.multiple θ).structureMap :=
    ((M.multiple θ).structureMap_chart γ).symm
  rw [heq]
  have hstep : Clos.pullback
      ((M.multiple θ).chartTo γ ≫ (M.multiple θ).structureMap)
      ((M.multiple θ).restrict (fun _ : PUnit => i)).D =
      pullback_Clos ((M.multiple θ).chartTo γ)
        (Clos.pullback (M.multiple θ).structureMap
          ((M.multiple θ).restrict (fun _ : PUnit => i)).D) := by
    show pullback_Clos _
      (Quotient.mk'' ((M.multiple θ).restrict (fun _ : PUnit => i)).Drep) = _
    rw [pullback_assoc]
    rfl
  rw [hstep]
  haveI : IsOpenImmersion ((M.multiple θ).chartTo γ) :=
    (M.multiple θ).chartTo_isOpenImmersion γ
  haveI : AlgebraicGeometry.Flat ((M.multiple θ).chartTo γ) := inferInstance
  exact pullback_IsCars _ _ _
    ((M.multiple θ).restrict_isCars (fun _ : PUnit => i))

theorem projChart_pullSubset :
    ((M.multiple θ).restrict (fun _ : PUnit => i)).pullSubset
      ((M.multiple θ).chartToX γ) := by
  have h := (M.restrict (fun _ : PUnit => i)).pullSubset_of_over_dilatation
    (fun _ : PUnit => θ i)
    ((M.multiple θ).chartTo γ ≫ M.projAt i θ)
  have h2 : ((M.multiple θ).chartTo γ ≫ M.projAt i θ) ≫
      ((M.restrict (fun _ : PUnit => i)).multiple
        (fun _ : PUnit => θ i)).structureMap =
      (M.multiple θ).chartToX γ := by
    show ((M.multiple θ).chartTo γ ≫ M.projAt i θ) ≫
      ((M.multiple θ).restrict (fun _ : PUnit => i)).structureMap = _
    exact M.projChart_overX i θ γ
  rw [h2] at h
  exact h

theorem proj_chart_cone :
    (M.multiple θ).chartTo γ ≫ M.projAt i θ =
      M.projRhoSch i θ γ ≫
        ((M.multiple θ).restrict (fun _ : PUnit => i)).chartTo γ := by
  refine (((M.multiple θ).restrict (fun _ : PUnit => i)).universal_property
    ((M.multiple θ).chart γ) ((M.multiple θ).chartToX γ)
    (M.projChart_isCars i θ γ) (M.projChart_pullSubset i θ γ)).unique ?_ ?_
  · exact M.projChart_overX i θ γ
  · rw [Category.assoc,
      ((M.multiple θ).restrict (fun _ : PUnit => i)).structureMap_chart γ,
      show ((M.multiple θ).restrict (fun _ : PUnit => i)).chartToX γ =
        ((M.multiple θ).restrict (fun _ : PUnit => i)).chartHom γ ≫
          M.cov.map γ from rfl,
      ← Category.assoc, M.projRhoSch_chartHom i θ γ]
    show (M.multiple θ).chartHom γ ≫ M.cov.map γ = _
    rfl

noncomputable def strictYChartDatum (hb : M.CarsOnYAll) (hSt : M.ElemNzdOnQuotAll) :
    ChartDatum (M.multiple θ).dilatation where
  cov := (M.multiple θ).dilatationCover
  idl γ := Ideal.map (M.projRho i θ γ).toRingHom
    ((((M.restrict (fun _ : PUnit => i)).multiple
      (fun _ : PUnit => θ i)).localMulticenter γ).exceptIdeal)
  compat {W} _ {γ γ'} a b hab := by
    haveI : IsClosedImmersion ((M.restrict (fun _ : PUnit => i)).Ylift
        (fun _ : PUnit => θ i) (hb i)) :=
      (M.restrict (fun _ : PUnit => i)).Ylift_isClosedImmersion
        (fun _ : PUnit => θ i) (hb i)
    have hab' : (a ≫ M.projRhoSch i θ γ) ≫
        ((M.restrict (fun _ : PUnit => i)).multiple
          (fun _ : PUnit => θ i)).dilatationCover.map γ =
        (b ≫ M.projRhoSch i θ γ') ≫
        ((M.restrict (fun _ : PUnit => i)).multiple
          (fun _ : PUnit => θ i)).dilatationCover.map γ' := by
      show (a ≫ M.projRhoSch i θ γ) ≫
          ((M.multiple θ).restrict (fun _ : PUnit => i)).chartTo γ =
        (b ≫ M.projRhoSch i θ γ') ≫
          ((M.multiple θ).restrict (fun _ : PUnit => i)).chartTo γ'
      rw [Category.assoc, Category.assoc, ← M.proj_chart_cone i θ γ,
        ← M.proj_chart_cone i θ γ', ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ M.projAt i θ) hab
    have h := chartIdeal_agree
      (presentPreClos ((M.restrict (fun _ : PUnit => i)).Ylift
          (fun _ : PUnit => θ i) (hb i))
        ((M.restrict (fun _ : PUnit => i)).multiple
          (fun _ : PUnit => θ i)).dilatationCover)
      (a ≫ M.projRhoSch i θ γ) (b ≫ M.projRhoSch i θ γ') hab' PUnit.unit
    rw [presentPreClos_ideal, presentPreClos_ideal,
      (M.restrict (fun _ : PUnit => i)).presentIdeal_eq_exceptIdeal
        (fun _ : PUnit => θ i) (hb i) (hSt i) γ,
      (M.restrict (fun _ : PUnit => i)).presentIdeal_eq_exceptIdeal
        (fun _ : PUnit => θ i) (hb i) (hSt i) γ'] at h
    have hpa : Spec.preimage (W.isoSpec.inv ≫ a ≫ M.projRhoSch i θ γ) =
        CommRingCat.ofHom (M.projRho i θ γ).toRingHom ≫
          Spec.preimage (W.isoSpec.inv ≫ a) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ a ≫ M.projRhoSch i θ γ =
        (W.isoSpec.inv ≫ a) ≫ M.projRhoSch i θ γ
      rw [Category.assoc]
    have hpb : Spec.preimage (W.isoSpec.inv ≫ b ≫ M.projRhoSch i θ γ') =
        CommRingCat.ofHom (M.projRho i θ γ').toRingHom ≫
          Spec.preimage (W.isoSpec.inv ≫ b) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ b ≫ M.projRhoSch i θ γ' =
        (W.isoSpec.inv ≫ b) ≫ M.projRhoSch i θ γ'
      rw [Category.assoc]
    rw [hpa, hpb, CommRingCat.hom_comp, CommRingCat.hom_comp,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, ← Ideal.map_map,
      ← Ideal.map_map] at h
    exact h

end MonoAt

section IterCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (θ n : M.indnumb → ℕ)
  (hb : M.CarsOnYAll) (hSt : M.ElemNzdOnQuotAll)

noncomputable def iterCenter : PreMultiCenter (M.multiple θ).dilatation where
  indnumb := M.indnumb
  cov := (M.multiple θ).dilatationCover
  Ysub i := (M.strictYChartDatum i θ hb hSt).glued
  Dsub i := (M.transformDChartDatum θ n i).glued
  Yover i := ⟨(M.strictYChartDatum i θ hb hSt).structureMap⟩
  Dover i := ⟨(M.transformDChartDatum θ n i).structureMap⟩
  Yideal i γ := Ideal.map (M.projRho i θ γ).toRingHom
    ((((M.restrict (fun _ : PUnit => i)).multiple
      (fun _ : PUnit => θ i)).localMulticenter γ).exceptIdeal)
  Dideal i γ := (Ideal.map (algebraMap ((M.multiple θ).cov.obj γ)
    (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)))
      (M.Dideal i γ)) ^ (n i)
  YcondIso i γ := asIso ((M.strictYChartDatum i θ hb hSt).chartCompare γ)
  YcondOver i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (M.strictYChartDatum i θ hb hSt).chartCompare γ ≫
        pullback.snd ((M.strictYChartDatum i θ hb hSt).structureMap)
          ((M.multiple θ).dilatationCover.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (M.projRho i θ γ).toRingHom
          ((((M.restrict (fun _ : PUnit => i)).multiple
            (fun _ : PUnit => θ i)).localMulticenter γ).exceptIdeal))))
    exact (M.strictYChartDatum i θ hb hSt).chartCompare_snd γ
  DcondIso i γ := asIso ((M.transformDChartDatum θ n i).chartCompare γ)
  DcondOver i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (M.transformDChartDatum θ n i).chartCompare γ ≫
        pullback.snd ((M.transformDChartDatum θ n i).structureMap)
          ((M.multiple θ).dilatationCover.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((Ideal.map (algebraMap ((M.multiple θ).cov.obj γ)
          (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)))
            (M.Dideal i γ)) ^ (n i))))
    exact (M.transformDChartDatum θ n i).chartCompare_snd γ
  Dprin i γ := by
    letI : Submodule.IsPrincipal (M.Dideal i γ) := M.Dprin i γ
    refine ⟨⟨(algebraMap ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)))
        ((M.localMulticenter γ).elem i) ^ (n i), ?_⟩⟩
    rw [Ideal.submodule_span_eq, ← Ideal.span_singleton_pow]
    congr 1
    conv_lhs => rw [show M.Dideal i γ =
      Ideal.span {(M.localMulticenter γ).elem i} from M.local_Dideal_span' γ i]
    rw [Ideal.map_span, Set.image_singleton]
    rfl

@[simp] theorem iterCenter_Yideal (i : M.indnumb) (γ : M.cov.J) :
    (M.iterCenter θ n hb hSt).Yideal i γ =
      Ideal.map (M.projRho i θ γ).toRingHom
        ((((M.restrict (fun _ : PUnit => i)).multiple
          (fun _ : PUnit => θ i)).localMulticenter γ).exceptIdeal) := rfl

@[simp] theorem iterCenter_Dideal (i : M.indnumb) (γ : M.cov.J) :
    (M.iterCenter θ n hb hSt).Dideal i γ =
      (Ideal.map (algebraMap ((M.multiple θ).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)))
          (M.Dideal i γ)) ^ (n i) := rfl

end IterCenter

section MultiRho

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (ν θ : M.indnumb → ℕ)
  (hθν : ∀ i, θ i ≤ ν i) (γ : M.cov.J)

noncomputable instance multiChartAlgebraBridge :
    Algebra ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :=
  inferInstanceAs (Algebra ((M.multiple ν).cov.obj γ)
    (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))

include hθν in
theorem multiRho_nzd :
    ∀ i, algebraMap ((M.multiple θ).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))
        (((M.multiple θ).localMulticenter γ).elem i) ∈
      nonZeroDivisors
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :=
  fun i => M.chart_gen_nzd' γ ν θ i (hθν i)

include hθν in
theorem multiRho_gen :
    ∀ i, Ideal.span {algebraMap ((M.multiple θ).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ))
        (((M.multiple θ).localMulticenter γ).elem i)} =
      Ideal.map (algebraMap ((M.multiple θ).cov.obj γ)
        (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)))
        (((M.multiple θ).localMulticenter γ).LargeIdeal i) := by
  intro i
  set f : (M.cov.obj γ) →+*
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :=
    (algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) :
        _ →+* _) with hf
  have hle : Ideal.map f (M.Yideal i γ) ≤
      Ideal.span {f (((M.multiple θ).localMulticenter γ).elem i)} := by
    have h1 : Ideal.map f (M.Yideal i γ) ≤
        Ideal.span {f ((M.localMulticenter γ).elem i) ^ (ν i)} :=
      M.chart_M_le_alpha_pow' γ ν i
    have h2 : Ideal.span {f ((M.localMulticenter γ).elem i) ^ (ν i)} ≤
        Ideal.span {f ((M.localMulticenter γ).elem i) ^ (θ i)} :=
      Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow _ (hθν i))
    have h3 := le_trans h1 h2
    rw [← M.hom_multipleGen_span' γ θ i f] at h3
    exact h3
  show Ideal.span {f (((M.multiple θ).localMulticenter γ).elem i)} =
    Ideal.map f ((M.Yideal i γ) +
      (Ideal.span {((M.multiple θ).localMulticenter γ).elem i} :
        Ideal (M.cov.obj γ)))
  rw [Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact (sup_eq_right.mpr hle).symm

noncomputable def multiRho :
    Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)
      →ₐ[(M.multiple θ).cov.obj γ]
      Multicenter.Dilatation ((M.multiple ν).localMulticenter γ) :=
  desc ((M.multiple θ).localMulticenter γ) (M.multiRho_nzd ν θ hθν γ)
    (M.multiRho_gen ν θ hθν γ)

theorem multiRho_algebraMap (x : (M.cov.obj γ)) :
    M.multiRho ν θ hθν γ (algebraMap ((M.multiple θ).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple θ).localMulticenter γ)) x) =
    algebraMap ((M.multiple ν).cov.obj γ)
      (Multicenter.Dilatation ((M.multiple ν).localMulticenter γ)) x :=
  (M.multiRho ν θ hθν γ).commutes x

noncomputable def multiRhoSch :
    (M.multiple ν).chart γ ⟶ (M.multiple θ).chart γ :=
  Spec.map (CommRingCat.ofHom (M.multiRho ν θ hθν γ).toRingHom)

theorem multiRhoSch_chartHom :
    M.multiRhoSch ν θ hθν γ ≫ (M.multiple θ).chartHom γ =
      (M.multiple ν).chartHom γ := by
  rw [multiRhoSch]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact M.multiRho_algebraMap ν θ hθν γ a

theorem multiChart_overX :
    ((M.multiple ν).chartTo γ ≫ M.multipleHom ν θ hθν) ≫
      (M.multiple θ).structureMap = (M.multiple ν).chartToX γ := by
  rw [Category.assoc, M.multipleHom_over ν θ hθν,
    (M.multiple ν).structureMap_chart γ]

include hθν in
theorem multiChart_isCars :
    IsCars ((M.multiple ν).chart γ)
      (Clos.pullback ((M.multiple ν).chartToX γ) (M.multiple θ).D) := by
  have heq : (M.multiple ν).chartToX γ =
      (M.multiple ν).chartTo γ ≫ (M.multiple ν).structureMap :=
    ((M.multiple ν).structureMap_chart γ).symm
  rw [heq]
  have hstep : Clos.pullback
      ((M.multiple ν).chartTo γ ≫ (M.multiple ν).structureMap)
      (M.multiple θ).D =
      pullback_Clos ((M.multiple ν).chartTo γ)
        (Clos.pullback (M.multiple ν).structureMap (M.multiple θ).D) := by
    show pullback_Clos _ (Quotient.mk'' (M.multiple θ).Drep) = _
    rw [pullback_assoc]
    rfl
  rw [hstep]
  haveI : IsOpenImmersion ((M.multiple ν).chartTo γ) :=
    (M.multiple ν).chartTo_isOpenImmersion γ
  haveI : AlgebraicGeometry.Flat ((M.multiple ν).chartTo γ) := inferInstance
  exact pullback_IsCars _ _ _ (M.multiple_isCars ν θ hθν)

include hθν in
theorem multiChart_pullSubset :
    (M.multiple θ).pullSubset ((M.multiple ν).chartToX γ) := by
  have h := M.pullSubset_of_over_dilatation θ
    ((M.multiple ν).chartTo γ ≫ M.multipleHom ν θ hθν)
  rw [Category.assoc, M.multipleHom_over ν θ hθν,
    (M.multiple ν).structureMap_chart γ] at h
  exact h

theorem multi_chart_cone :
    (M.multiple ν).chartTo γ ≫ M.multipleHom ν θ hθν =
      M.multiRhoSch ν θ hθν γ ≫ (M.multiple θ).chartTo γ := by
  refine ((M.multiple θ).universal_property ((M.multiple ν).chart γ)
    ((M.multiple ν).chartToX γ) (M.multiChart_isCars ν θ hθν γ)
    (M.multiChart_pullSubset ν θ hθν γ)).unique ?_ ?_
  · exact M.multiChart_overX ν θ hθν γ
  · rw [Category.assoc, (M.multiple θ).structureMap_chart γ,
      show (M.multiple θ).chartToX γ =
        (M.multiple θ).chartHom γ ≫ M.cov.map γ from rfl,
      ← Category.assoc, M.multiRhoSch_chartHom ν θ hθν γ]
    show (M.multiple ν).chartHom γ ≫ M.cov.map γ = _
    rfl

end MultiRho

end PreMultiCenter

end SchemeDilatation
