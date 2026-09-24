import ClosMathlibBridge
import SchemeMathlibForm

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

namespace SchemeDilatation

variable {X : Scheme.{u+1}}

theorem fromSpec_image_top {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ''ᵁ ⊤ = U :=
  Opens.ext (by simp)

noncomputable def PreMultiCenter.ofClosedImmersions {ι : Type}
    (Ysub Dsub : ι → Scheme.{u+1})
    [∀ i, Scheme.Over (Ysub i) X] [∀ i, Scheme.Over (Dsub i) X]
    (hY : ∀ i, IsClosedImmersion (Ysub i ↘ X))
    (hD : ∀ i, IsClosedImmersion (Dsub i ↘ X))
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X)
    (hprin : ∀ i γ, (famIdeal Dsub hD cov i γ).IsPrincipal) :
    PreMultiCenter X where
  indnumb := ι
  cov := cov
  Ysub := Ysub
  Dsub := Dsub
  Yideal := famIdeal Ysub hY cov
  Dideal := famIdeal Dsub hD cov
  YcondIso := (PreClos.ofFamily Ysub hY cov).condiso
  YcondOver := (PreClos.ofFamily Ysub hY cov).condover
  DcondIso := (PreClos.ofFamily Dsub hD cov).condiso
  DcondOver := (PreClos.ofFamily Dsub hD cov).condover
  Dprin := hprin

@[simp] theorem PreMultiCenter.ofClosedImmersions_Ysub {ι : Type}
    (Ysub Dsub : ι → Scheme.{u+1})
    [∀ i, Scheme.Over (Ysub i) X] [∀ i, Scheme.Over (Dsub i) X]
    (hY : ∀ i, IsClosedImmersion (Ysub i ↘ X))
    (hD : ∀ i, IsClosedImmersion (Dsub i ↘ X))
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X)
    (hprin : ∀ i γ, (famIdeal Dsub hD cov i γ).IsPrincipal) :
    (PreMultiCenter.ofClosedImmersions Ysub Dsub hY hD cov hprin).Ysub = Ysub := rfl

@[simp] theorem PreMultiCenter.ofClosedImmersions_Dsub {ι : Type}
    (Ysub Dsub : ι → Scheme.{u+1})
    [∀ i, Scheme.Over (Ysub i) X] [∀ i, Scheme.Over (Dsub i) X]
    (hY : ∀ i, IsClosedImmersion (Ysub i ↘ X))
    (hD : ∀ i, IsClosedImmersion (Dsub i ↘ X))
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X)
    (hprin : ∀ i γ, (famIdeal Dsub hD cov i γ).IsPrincipal) :
    (PreMultiCenter.ofClosedImmersions Ysub Dsub hY hD cov hprin).Dsub = Dsub := rfl

noncomputable def PreMultiCenter.ofLocallyPrincipal {ι : Type} [Finite ι]
    (Ysub Dsub : ι → Scheme.{u+1})
    [∀ i, Scheme.Over (Ysub i) X] [∀ i, Scheme.Over (Dsub i) X]
    (hY : ∀ i, IsClosedImmersion (Ysub i ↘ X))
    (hD : ∀ i, IsClosedImmersion (Dsub i ↘ X))
    (hloc : ∀ i, IsLocallyPrincipalOver (Dsub i ↘ X)) :
    PreMultiCenter X :=
  haveI : ∀ i, IsClosedImmersion (Dsub i ↘ X) := hD
  PreMultiCenter.ofClosedImmersions Ysub Dsub hY hD
    (principalCover (fun i => Dsub i ↘ X) hloc)
    (fun i x => by
      refine famIdeal_isPrincipal Dsub hD _ i x ?_
      rw [fromSpec_image_top]
      exact isPrincipal_principalOpen (fun i => Dsub i ↘ X) hloc x i)

@[simp] theorem PreMultiCenter.ofLocallyPrincipal_Ysub {ι : Type} [Finite ι]
    (Ysub Dsub : ι → Scheme.{u+1})
    [∀ i, Scheme.Over (Ysub i) X] [∀ i, Scheme.Over (Dsub i) X]
    (hY : ∀ i, IsClosedImmersion (Ysub i ↘ X))
    (hD : ∀ i, IsClosedImmersion (Dsub i ↘ X))
    (hloc : ∀ i, IsLocallyPrincipalOver (Dsub i ↘ X)) :
    (PreMultiCenter.ofLocallyPrincipal Ysub Dsub hY hD hloc).Ysub = Ysub := rfl

@[simp] theorem PreMultiCenter.ofLocallyPrincipal_Dsub {ι : Type} [Finite ι]
    (Ysub Dsub : ι → Scheme.{u+1})
    [∀ i, Scheme.Over (Ysub i) X] [∀ i, Scheme.Over (Dsub i) X]
    (hY : ∀ i, IsClosedImmersion (Ysub i ↘ X))
    (hD : ∀ i, IsClosedImmersion (Dsub i ↘ X))
    (hloc : ∀ i, IsLocallyPrincipalOver (Dsub i ↘ X)) :
    (PreMultiCenter.ofLocallyPrincipal Ysub Dsub hY hD hloc).Dsub = Dsub := rfl

end SchemeDilatation
