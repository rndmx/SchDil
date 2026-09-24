import BaseChange
import GlobalDilProperties
import DilToBlowup

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory Limits SchemeDilatation

namespace SchemeDilatation

namespace Mono

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [Unique M.indnumb]

local notation "i₀" => (default : M.indnumb)

section UniversalProperty

theorem universal_property (T : Scheme.{u+1}) (f : T ⟶ X)
    (hCars : IsCars T (Clos.pullback f M.D))
    (hsub : M.pullSubset f) :
    ∃! g : T ⟶ M.dilatation, g ≫ M.structureMap = f :=
  M.universal_property T f hCars hsub

theorem hom_subsingleton (T : Scheme.{u+1}) (f : T ⟶ X)
    (hCars : IsCars T (Clos.pullback f M.D))
    (hsub : M.pullSubset f)
    (g g' : T ⟶ M.dilatation)
    (hg : g ≫ M.structureMap = f) (hg' : g' ≫ M.structureMap = f) :
    g = g' := by
  obtain ⟨_, _, huniq⟩ := M.universal_property T f hCars hsub
  rw [huniq g hg, huniq g' hg']

end UniversalProperty

section ExceptionalDivisor

theorem exceptional_isCars :
    IsCars M.dilatation (Clos.pullback M.structureMap M.D) :=
  M.structureMap_isCars

theorem exceptional_eq (hZD : centerSubDivisor M) :
    Clos.pullback M.structureMap M.Y =
      Clos.pullback M.structureMap M.D :=
  exceptional_pullback_eq M hZD

noncomputable def exceptionalIso (hZD : centerSubDivisor M) :
    pullback (M.Ysub i₀ ↘ X) M.structureMap ≅
      pullback (M.Dsub i₀ ↘ X) M.structureMap :=
  SchemeDilatation.exceptionalIso M hZD i₀

theorem exceptionalIso_over (hZD : centerSubDivisor M) :
    Scheme.Hom.IsOver (exceptionalIso M hZD).hom M.dilatation :=
  SchemeDilatation.exceptionalIso_over M hZD i₀

theorem structureMap_pullSubset : M.pullSubset M.structureMap :=
  M.structureMap_pullSubset

end ExceptionalDivisor

section Functoriality

variable {X' : Scheme.{u+1}} (M' : PreMultiCenter X') [Unique M'.indnumb]
  (f : X' ⟶ X)
  (RD : relStructure (pullback_PreClos X X' f M.Drep) M'.Drep)
  (hY : ∀ (i : M.indnumb) (γ' : M'.cov.J),
    (pullback_PreClos X X' f M.Yrep).reindexIdeal M'.cov i γ' ≤
      M'.Yideal (RD.indnumb_equiv i) γ' ⊔
        M'.Dideal (RD.indnumb_equiv i) γ')

include RD hY in
theorem existsUnique_functorialityHom :
    ∃! g : M'.dilatation ⟶ M.dilatation,
      g ≫ M.structureMap = M'.structureMap ≫ f :=
  M.existsUnique_functorialityHom M' f RD hY

noncomputable def functorialityHom : M'.dilatation ⟶ M.dilatation :=
  M.functorialityHom M' f RD hY

@[simp] theorem functorialityHom_over :
    functorialityHom M M' f RD hY ≫ M.structureMap = M'.structureMap ≫ f :=
  M.functorialityHom_over M' f RD hY

theorem functorialityHom_unique (g : M'.dilatation ⟶ M.dilatation)
    (hg : g ≫ M.structureMap = M'.structureMap ≫ f) :
    g = functorialityHom M M' f RD hY :=
  M.functorialityHom_unique M' f RD hY g hg

end Functoriality

section BaseChange

variable {X' : Scheme.{u+1}} (f : X' ⟶ X)

noncomputable def baseChangeIso
    (hcars : IsCars (pullback M.structureMap f)
      (Clos.pullback (pullback.snd M.structureMap f)
        (M.baseChange f).D)) :
    (M.baseChange f).dilatation ≅ pullback M.structureMap f :=
  M.baseChangeIso f hcars

noncomputable def flatBaseChangeIso [AlgebraicGeometry.Flat f] :
    (M.baseChange f).dilatation ≅ pullback M.structureMap f :=
  M.flatBaseChangeIso f

theorem baseChangeHom_property [AlgebraicGeometry.Flat f]
    (P : MorphismProperty Scheme.{u+1})
    [P.IsStableUnderBaseChange] [P.RespectsIso] (hf : P f) :
    P (PreMultiCenter.baseChangeHom M f) :=
  PreMultiCenter.baseChangeHom_property M f P hf

end BaseChange

end Mono

end SchemeDilatation
