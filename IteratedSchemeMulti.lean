import IteratedSchemeMultiBwd

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

section MainIsoMulti

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (ν θ n : M.indnumb → ℕ)
  (hsum : ∀ i, θ i + n i = ν i)
  (hb : M.CarsOnYAll) (hSt : M.ElemNzdOnQuotAll)

noncomputable def iterMultiFwd :
    (M.multiple ν).dilatation ⟶ (M.iterCenter θ n hb hSt).dilatation :=
  (M.existsUnique_iterMultiFwd ν θ n hsum hb hSt).choose

@[simp] theorem iterMultiFwd_over :
    M.iterMultiFwd ν θ n hsum hb hSt ≫
      (M.iterCenter θ n hb hSt).structureMap =
      M.multipleHom ν θ (M.le_of_sum ν θ n hsum) :=
  (M.existsUnique_iterMultiFwd ν θ n hsum hb hSt).choose_spec.1

noncomputable def iterMultiBwd :
    (M.iterCenter θ n hb hSt).dilatation ⟶ (M.multiple ν).dilatation :=
  (M.existsUnique_iterMultiBwd ν θ n hsum hb hSt).choose

@[simp] theorem iterMultiBwd_over :
    M.iterMultiBwd ν θ n hsum hb hSt ≫ (M.multiple ν).structureMap =
      (M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap :=
  (M.existsUnique_iterMultiBwd ν θ n hsum hb hSt).choose_spec.1

theorem iterMultiFwd_comp_iterMultiBwd :
    M.iterMultiFwd ν θ n hsum hb hSt ≫ M.iterMultiBwd ν θ n hsum hb hSt =
      𝟙 _ := by
  have e₁ : (M.iterMultiFwd ν θ n hsum hb hSt ≫
      M.iterMultiBwd ν θ n hsum hb hSt) ≫ (M.multiple ν).structureMap =
      (M.multiple ν).structureMap := by
    rw [Category.assoc, M.iterMultiBwd_over ν θ n hsum hb hSt,
      ← Category.assoc, M.iterMultiFwd_over ν θ n hsum hb hSt,
      M.multipleHom_over ν θ (M.le_of_sum ν θ n hsum)]
  exact ((M.multiple ν).universal_property (M.multiple ν).dilatation
    (M.multiple ν).structureMap (M.multiple ν).structureMap_isCars
    (M.multiple ν).structureMap_pullSubset).unique e₁ (Category.id_comp _)

theorem iterMultiBwd_over_base :
    M.iterMultiBwd ν θ n hsum hb hSt ≫
      M.multipleHom ν θ (M.le_of_sum ν θ n hsum) =
      (M.iterCenter θ n hb hSt).structureMap := by
  have e₁ : (M.iterMultiBwd ν θ n hsum hb hSt ≫
      M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) ≫
      (M.multiple θ).structureMap =
      (M.iterCenter θ n hb hSt).structureMap ≫
        (M.multiple θ).structureMap := by
    rw [Category.assoc, M.multipleHom_over ν θ (M.le_of_sum ν θ n hsum),
      M.iterMultiBwd_over ν θ n hsum hb hSt]
  exact ((M.multiple θ).universal_property
    (M.iterCenter θ n hb hSt).dilatation
    ((M.iterCenter θ n hb hSt).structureMap ≫ (M.multiple θ).structureMap)
    (M.iterBackward_isCars_theta ν θ n hsum hb hSt)
    (M.pullSubset_of_over_dilatation θ
      ((M.iterCenter θ n hb hSt).structureMap))).unique e₁ rfl

theorem iterMultiBwd_comp_iterMultiFwd :
    M.iterMultiBwd ν θ n hsum hb hSt ≫ M.iterMultiFwd ν θ n hsum hb hSt =
      𝟙 _ := by
  have e₁ : (M.iterMultiBwd ν θ n hsum hb hSt ≫
      M.iterMultiFwd ν θ n hsum hb hSt) ≫
      (M.iterCenter θ n hb hSt).structureMap =
      (M.iterCenter θ n hb hSt).structureMap := by
    rw [Category.assoc, M.iterMultiFwd_over ν θ n hsum hb hSt,
      M.iterMultiBwd_over_base ν θ n hsum hb hSt]
  exact ((M.iterCenter θ n hb hSt).universal_property
    (M.iterCenter θ n hb hSt).dilatation
    (M.iterCenter θ n hb hSt).structureMap
    (M.iterCenter θ n hb hSt).structureMap_isCars
    (M.iterCenter θ n hb hSt).structureMap_pullSubset).unique e₁
    (Category.id_comp _)

noncomputable def iterMultiSchemeIso :
    (M.multiple ν).dilatation ≅ (M.iterCenter θ n hb hSt).dilatation where
  hom := M.iterMultiFwd ν θ n hsum hb hSt
  inv := M.iterMultiBwd ν θ n hsum hb hSt
  hom_inv_id := M.iterMultiFwd_comp_iterMultiBwd ν θ n hsum hb hSt
  inv_hom_id := M.iterMultiBwd_comp_iterMultiFwd ν θ n hsum hb hSt

@[simp] theorem iterMultiSchemeIso_hom_over :
    (M.iterMultiSchemeIso ν θ n hsum hb hSt).hom ≫
      (M.iterCenter θ n hb hSt).structureMap =
      M.multipleHom ν θ (M.le_of_sum ν θ n hsum) :=
  M.iterMultiFwd_over ν θ n hsum hb hSt

theorem iterMultiSchemeIso_unique
    (g : (M.multiple ν).dilatation ⟶ (M.iterCenter θ n hb hSt).dilatation)
    (hg : g ≫ (M.iterCenter θ n hb hSt).structureMap =
      M.multipleHom ν θ (M.le_of_sum ν θ n hsum)) :
    g = (M.iterMultiSchemeIso ν θ n hsum hb hSt).hom :=
  ((M.existsUnique_iterMultiFwd ν θ n hsum hb hSt).unique hg
    (M.iterMultiFwd_over ν θ n hsum hb hSt)).trans rfl

end MainIsoMulti

section Lemma45

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [DecidableEq M.indnumb]
  (ν : M.indnumb → ℕ) (i : M.indnumb) (c : ℕ)
  (hb : M.CarsOnYAll) (hSt : M.ElemNzdOnQuotAll)

theorem single_sum :
    ∀ j, ν j + (Pi.single i c : M.indnumb → ℕ) j =
      (ν + (Pi.single i c : M.indnumb → ℕ)) j :=
  fun _ => rfl

noncomputable def iterateSingleIso :
    (M.multiple (ν + (Pi.single i c : M.indnumb → ℕ))).dilatation ≅
      (M.iterCenter ν ((Pi.single i c : M.indnumb → ℕ)) hb hSt).dilatation :=
  M.iterMultiSchemeIso (ν + (Pi.single i c : M.indnumb → ℕ)) ν ((Pi.single i c : M.indnumb → ℕ))
    (M.single_sum ν i c) hb hSt

@[simp] theorem iterateSingleIso_hom_over :
    (M.iterateSingleIso ν i c hb hSt).hom ≫
      (M.iterCenter ν ((Pi.single i c : M.indnumb → ℕ)) hb hSt).structureMap =
      M.multipleHom (ν + (Pi.single i c : M.indnumb → ℕ)) ν
        (M.le_of_sum (ν + (Pi.single i c : M.indnumb → ℕ)) ν ((Pi.single i c : M.indnumb → ℕ))
          (M.single_sum ν i c)) :=
  M.iterMultiSchemeIso_hom_over (ν + (Pi.single i c : M.indnumb → ℕ)) ν ((Pi.single i c : M.indnumb → ℕ))
    (M.single_sum ν i c) hb hSt

end Lemma45
end PreMultiCenter

end SchemeDilatation
