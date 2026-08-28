import PreMultiCenter

/-!
# Base change of a multicenter

Given `M : PreMultiCenter X` and `f : T ⟶ X`, this file constructs the base-changed
multicenter `M.baseChange f : PreMultiCenter T`, whose centers and divisors are
`Y_i ×_X T` and `D_i ×_X T`.

This is the datum appearing on the right-hand side of the tower formula
[Ma23d, Prop. 2.22]: for `J ⊆ I` with `K = I \ J`, the `I`-dilatation of `X` is the
`K`-dilatation of the `J`-dilatation of `X`, taken along the centers base-changed
to `Bl_J X`.

Everything is defined so that `(M.baseChange f).Yrep` and `(M.baseChange f).Drep` are
*definitionally* the already-available `pullback_PreClos` of `M.Yrep` and `M.Drep`
(see `baseChange_Yrep` and `baseChange_Drep`, both `rfl`). Consequently the existing
`pull_cov` / `pull_mor_ring` / `pull_ideal` API applies to `M.baseChange f` unchanged.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

section BaseChangeComp

variable {X T T' : Scheme.{u+1}}

/-- Base change of closed-subscheme data is transitive.

The two sides carry genuinely different affine coverings of `T'` -- one obtained by
refining `Z.cov` twice, the other by refining it once -- so this is an isomorphism of
`PreClos` data, not an equality. `relStructure` only records the family of closed
subschemes up to isomorphism over the base, so it is exactly the pasting isomorphism
`(S ×[X] T) ×[T] T' ≅ S ×[X] T'`. -/
def pullback_PreClos_comp (Z : PreClos X) (p : T ⟶ X) (g : T' ⟶ T) :
    relStructure (pullback_PreClos T T' g (pullback_PreClos X T p Z))
      (pullback_PreClos X T' (g ≫ p) Z) where
  indnumb_equiv := Equiv.refl _
  subscheme_iso i := pullbackLeftPullbackSndIso (Z.subscheme i ↘ X) p g
  subscheme_iso_over i := by
    rw [Scheme.Hom.isOver_iff]
    exact pullbackLeftPullbackSndIso_hom_snd _ _ _

/-- Base change is transitive in `Clos`: pulling back along `p` and then along `g` is
pulling back along `g ≫ p`. -/
theorem pullback_Clos_comp (Z : Clos X) (p : T ⟶ X) (g : T' ⟶ T) :
    pullback_Clos g (pullback_Clos p Z) = pullback_Clos (g ≫ p) Z := by
  induction Z using Quotient.inductionOn with | h Z =>
  exact Quotient.sound ⟨pullback_PreClos_comp Z p g⟩

end BaseChangeComp

namespace SchemeDilatation

variable {X : Scheme.{u+1}} {T : Scheme.{u+1}}

namespace PreMultiCenter

variable (M : PreMultiCenter X) (f : T ⟶ X)

/-- The covering of `T` used by `M.baseChange f` does not depend on whether it is read
off the centers or off the divisors: `Yrep` and `Drep` share the covering `M.cov`. -/
theorem pull_cov_Yrep_eq_Drep :
    pull_cov X M.Yrep T f = pull_cov X M.Drep T f := rfl

/-- Base change of a multicenter along `f : T ⟶ X`: the centers and divisors are
`Y_i ×_X T` and `D_i ×_X T`, and the ideals are the ideals of `M` pushed forward along
the induced ring maps on the pulled-back affine covering. -/
def baseChange : PreMultiCenter T where
  indnumb := M.indnumb
  cov := pull_cov X M.Yrep T f
  Ysub i := pullback (M.Ysub i ↘ X) f
  Dsub i := pullback (M.Dsub i ↘ X) f
  Yover i := ⟨pullback.snd _ _⟩
  Dover i := ⟨pullback.snd _ _⟩
  Yideal i γβ := pull_ideal X M.Yrep T f γβ i
  Dideal i γβ := pull_ideal X M.Drep T f γβ i
  YcondIso i γβ := pullback_PreClos_condiso X γβ i
  YcondOver i γβ := pullback_PreClos_condover X γβ i
  DcondIso i γβ := pullback_PreClos_condiso (Z := M.Drep) X γβ i
  DcondOver i γβ := pullback_PreClos_condover (Z := M.Drep) X γβ i
  Dprin i γβ := by
    apply Submodule.IsPrincipal.map_ringHom
    exact M.Dprin i γβ.1

@[simp] theorem baseChange_indnumb : (M.baseChange f).indnumb = M.indnumb := rfl

@[simp] theorem baseChange_cov : (M.baseChange f).cov = pull_cov X M.Yrep T f := rfl

/-- The centers of `M.baseChange f` are the base-changed centers of `M`. -/
@[simp] theorem baseChange_Yrep :
    (M.baseChange f).Yrep = pullback_PreClos X T f M.Yrep := rfl

/-- The divisors of `M.baseChange f` are the base-changed divisors of `M`. -/
@[simp] theorem baseChange_Drep :
    (M.baseChange f).Drep = pullback_PreClos X T f M.Drep := rfl

@[simp] theorem baseChange_Y : (M.baseChange f).Y = pullback_Clos f M.Y := rfl

@[simp] theorem baseChange_D : (M.baseChange f).D = pullback_Clos f M.D := rfl

@[simp] theorem baseChange_Yideal (i : M.indnumb) (γβ : (M.baseChange f).cov.J) :
    (M.baseChange f).Yideal i γβ =
      Ideal.map (pull_mor_ring X M.Yrep T f γβ).hom (M.Yideal i γβ.1) := rfl

@[simp] theorem baseChange_Dideal (i : M.indnumb) (γβ : (M.baseChange f).cov.J) :
    (M.baseChange f).Dideal i γβ =
      Ideal.map (pull_mor_ring X M.Drep T f γβ).hom (M.Dideal i γβ.1) := rfl

/-- The local multicenter of the base change has, as ideals, the images of the local
ideals of `M`. -/
theorem baseChange_localMulticenter_ideal (γβ : (M.baseChange f).cov.J)
    (i : M.indnumb) :
    ((M.baseChange f).localMulticenter γβ).ideal i =
      Ideal.map (pull_mor_ring X M.Yrep T f γβ).hom
        ((M.localMulticenter γβ.1).ideal i) := rfl

/-- The distinguished element of the local multicenter of the base change generates the
image of the ideal generated by the distinguished element of `M`. It is only pinned down
up to a unit, so this is stated as an equality of ideals. -/
theorem baseChange_localMulticenter_elem_span (γβ : (M.baseChange f).cov.J)
    (i : M.indnumb) :
    Ideal.span {((M.baseChange f).localMulticenter γβ).elem i} =
      Ideal.map (pull_mor_ring X M.Drep T f γβ).hom
        (Ideal.span {(M.localMulticenter γβ.1).elem i}) := by
  letI hbc : ((M.baseChange f).Dideal i γβ).IsPrincipal := (M.baseChange f).Dprin i γβ
  letI hM : (M.Dideal i γβ.1).IsPrincipal := M.Dprin i γβ.1
  have e₁ : Ideal.span {((M.baseChange f).localMulticenter γβ).elem i} =
      (M.baseChange f).Dideal i γβ := Ideal.span_singleton_generator _
  have e₂ : Ideal.span {(M.localMulticenter γβ.1).elem i} = M.Dideal i γβ.1 :=
    Ideal.span_singleton_generator _
  rw [e₁, e₂, baseChange_Dideal]

section BaseChangeComp

variable {T' : Scheme.{u+1}}

/-- Base change of a multicenter is transitive, up to the canonical comparison of
closed-subscheme data. -/
def baseChangeComp (p : T ⟶ X) (g : T' ⟶ T) :
    relStructure ((M.baseChange p).baseChange g) (M.baseChange (g ≫ p)) where
  RY := pullback_PreClos_comp M.Yrep p g
  RD := pullback_PreClos_comp M.Drep p g
  eq_equiv := rfl

theorem baseChange_comp_Y (p : T ⟶ X) (g : T' ⟶ T) :
    ((M.baseChange p).baseChange g).Y = (M.baseChange (g ≫ p)).Y :=
  Quotient.sound ⟨(M.baseChangeComp p g).RY⟩

theorem baseChange_comp_D (p : T ⟶ X) (g : T' ⟶ T) :
    ((M.baseChange p).baseChange g).D = (M.baseChange (g ≫ p)).D :=
  Quotient.sound ⟨(M.baseChangeComp p g).RD⟩

/-- The divisors of `M` pulled back to `T'` in two steps agree with the divisors of the
multicenter base-changed to `T'` in one step. -/
theorem pullback_Clos_baseChange_D (p : T ⟶ X) (g : T' ⟶ T) :
    pullback_Clos g (pullback_Clos p M.D) = (M.baseChange (g ≫ p)).D := by
  rw [pullback_Clos_comp, baseChange_D]

end BaseChangeComp

end PreMultiCenter

end SchemeDilatation
