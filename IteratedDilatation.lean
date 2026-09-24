import Tower

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

section EmptyCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X)

theorem isCars_id_of_isEmpty (h : IsEmpty M.indnumb) :
    IsCars X (Clos.pullback (𝟙 X) M.D) :=
  ⟨pullback_PreClos X X (𝟙 X) M.Drep,
   ⟨⟨fun i _ => h.elim i⟩, fun i _ => h.elim i⟩, rfl⟩

theorem pullSubset_id_of_isEmpty (h : IsEmpty M.indnumb) :
    M.pullSubset (𝟙 X) := fun i _ => h.elim i

theorem existsUnique_section_of_isEmpty (h : IsEmpty M.indnumb) :
    ∃! s : X ⟶ M.dilatation, s ≫ M.structureMap = 𝟙 X :=
  M.universal_property X (𝟙 X) (M.isCars_id_of_isEmpty h) (M.pullSubset_id_of_isEmpty h)

theorem structureMap_isIso_of_isEmpty (h : IsEmpty M.indnumb) :
    IsIso M.structureMap := by
  obtain ⟨s, hs, -⟩ := M.existsUnique_section_of_isEmpty h
  refine ⟨s, ?_, hs⟩
  exact (M.universal_property M.dilatation M.structureMap
    M.structureMap_isCars M.structureMap_pullSubset).unique
    (by rw [Category.assoc, hs, Category.comp_id]) (Category.id_comp _)

end EmptyCenter

section Iterated

noncomputable def iterDil :
    (k : ℕ) → (X : Scheme.{u+1}) → (M : PreMultiCenter X) →
    (Fin k ≃ M.indnumb) → Σ' (T : Scheme.{u+1}), T ⟶ X
  | 0, X, _, _ => ⟨X, 𝟙 X⟩
  | (k+1), X, M, σ =>
      ⟨(iterDil k ((M.restrict (fun _ : PUnit => σ 0)).dilatation)
          ((M.restrict (fun j : Fin k => σ j.succ)).baseChange
            (M.restrict (fun _ : PUnit => σ 0)).structureMap)
              (Equiv.refl _)).1,
       (iterDil k ((M.restrict (fun _ : PUnit => σ 0)).dilatation)
          ((M.restrict (fun j : Fin k => σ j.succ)).baseChange
            (M.restrict (fun _ : PUnit => σ 0)).structureMap)
              (Equiv.refl _)).2 ≫
         (M.restrict (fun _ : PUnit => σ 0)).structureMap⟩

example (X : Scheme.{u+1}) (M : PreMultiCenter X) (σ : Fin 1 ≃ M.indnumb) :
    (iterDil 1 X M σ).1 = (M.restrict (fun _ : PUnit => σ 0)).dilatation := rfl

theorem iterDil_spec : ∀ (k : ℕ) (X : Scheme.{u+1}) (M : PreMultiCenter X)
    (σ : Fin k ≃ M.indnumb),
    ∃ e : M.dilatation ≅ (iterDil k X M σ).1,
      e.hom ≫ (iterDil k X M σ).2 = M.structureMap ∧
      ∀ g : M.dilatation ⟶ (iterDil k X M σ).1,
        g ≫ (iterDil k X M σ).2 = M.structureMap → g = e.hom := by
  intro k
  induction k with
  | zero =>
    intro X M σ
    have hempty : IsEmpty M.indnumb := ⟨fun i => (σ.symm i).elim0⟩
    obtain ⟨s, hs, -⟩ := M.existsUnique_section_of_isEmpty hempty
    have h1 : M.structureMap ≫ s = 𝟙 M.dilatation :=
      (M.universal_property M.dilatation M.structureMap
        M.structureMap_isCars M.structureMap_pullSubset).unique
        (by rw [Category.assoc, hs, Category.comp_id]) (Category.id_comp _)
    refine ⟨⟨M.structureMap, s, h1, hs⟩, Category.comp_id _, fun g hg => ?_⟩
    show g = M.structureMap
    rw [← hg]
    exact (Category.comp_id g).symm
  | succ k ih =>
    intro X M σ
    have hIK : ∀ i, (∃ j : PUnit, (fun _ : PUnit => σ 0) j = i) ∨
        ∃ j : Fin k, (fun j : Fin k => σ j.succ) j = i := by
      intro i
      obtain ⟨n, rfl⟩ : ∃ n, σ n = i := ⟨σ.symm i, Equiv.apply_symm_apply σ i⟩
      rcases Fin.eq_zero_or_eq_succ n with h0 | ⟨j, rfl⟩
      · exact Or.inl ⟨PUnit.unit, by rw [h0]⟩
      · exact Or.inr ⟨j, rfl⟩
    obtain ⟨e', he'over, he'uniq⟩ := ih ((M.restrict (fun _ : PUnit => σ 0)).dilatation)
      ((M.restrict (fun j : Fin k => σ j.succ)).baseChange
        (M.restrict (fun _ : PUnit => σ 0)).structureMap) (Equiv.refl _)
    refine ⟨(M.towerIso (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ) hIK) ≪≫ e',
      ?_, ?_⟩
    · rw [Iso.trans_hom, Category.assoc]
      have hstep : e'.hom ≫ (iterDil (k+1) X M σ).2 =
          M.towerToX (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ) := by
        show e'.hom ≫ (_ ≫ (M.restrict (fun _ : PUnit => σ 0)).structureMap) = _
        rw [← Category.assoc, he'over]
      rw [hstep]
      exact M.towerIso_hom_over (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ) hIK
    · intro g hg
      have hh : ((M.towerIso (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ) hIK).inv
            ≫ g) ≫ (iterDil (k+1) X M σ).2 =
          M.towerToX (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ) := by
        rw [Category.assoc, hg, ← M.towerIso_hom_over (fun _ : PUnit => σ 0)
          (fun j : Fin k => σ j.succ) hIK, ← Category.assoc, Iso.inv_hom_id,
          Category.id_comp]
      have hoverB : ((M.towerIso (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ)
            hIK).inv ≫ g) ≫
          (iterDil k ((M.restrict (fun _ : PUnit => σ 0)).dilatation)
            ((M.restrict (fun j : Fin k => σ j.succ)).baseChange
              (M.restrict (fun _ : PUnit => σ 0)).structureMap) (Equiv.refl _)).2 =
          M.towerToBase (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ) :=
        ((M.restrict (fun _ : PUnit => σ 0)).universal_property
          (M.tower (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ))
          (M.towerToX (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ))
          (M.tower_isCars_base (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ))
          (M.tower_pullSubset_base (fun _ : PUnit => σ 0)
            (fun j : Fin k => σ j.succ))).unique
          (by rw [Category.assoc]; exact hh) rfl
      have hhe := he'uniq _ hoverB
      show g = ((M.towerIso (fun _ : PUnit => σ 0) (fun j : Fin k => σ j.succ) hIK)
        ≪≫ e').hom
      rw [Iso.trans_hom, ← hhe, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end Iterated

section Named

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) {k : ℕ} (σ : Fin k ≃ M.indnumb)

noncomputable def iterSch : Scheme.{u+1} := (iterDil k X M σ).1

noncomputable def iterMap : M.iterSch σ ⟶ X := (iterDil k X M σ).2

noncomputable def iterIso : M.dilatation ≅ M.iterSch σ :=
  (iterDil_spec k X M σ).choose

@[simp] theorem iterIso_hom_over :
    (M.iterIso σ).hom ≫ M.iterMap σ = M.structureMap :=
  (iterDil_spec k X M σ).choose_spec.1

theorem iterIso_unique (g : M.dilatation ⟶ M.iterSch σ)
    (hg : g ≫ M.iterMap σ = M.structureMap) : g = (M.iterIso σ).hom :=
  (iterDil_spec k X M σ).choose_spec.2 g hg

end Named

end PreMultiCenter

end SchemeDilatation
