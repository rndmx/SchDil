import PreClosClosedImmersion

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

variable {X : Scheme.{u+1}}

def PreClos.subset (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X)
    (eqcovW : W.cov = cov) (eqcovZ : Z.cov = cov) : Prop :=
  ∀ (i : W.indnumb) (γ : cov.J),
    (show (δ : cov.J) → Ideal (cov.obj δ) from eqcovZ ▸ Z.ideal (e i)) γ ≤
      (show (δ : cov.J) → Ideal (cov.obj δ) from eqcovW ▸ W.ideal i) γ

def PreClos.subset' (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X) : Prop :=
  ∀ (eqcovW : W.cov = cov) (eqcovZ : Z.cov = cov) (i : W.indnumb) (γ : cov.J),
    (show (δ : cov.J) → Ideal (cov.obj δ) from eqcovZ ▸ Z.ideal (e i)) γ ≤
      (show (δ : cov.J) → Ideal (cov.obj δ) from eqcovW ▸ W.ideal i) γ

theorem PreClos.subset_iff_subset' (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X)
    (eqcovW : W.cov = cov) (eqcovZ : Z.cov = cov) :
    PreClos.subset W Z e cov eqcovW eqcovZ ↔ PreClos.subset' W Z e cov := by
  constructor
  · intro h hW' hZ' i γ
    rw [Subsingleton.elim hW' eqcovW, Subsingleton.elim hZ' eqcovZ]
    exact h i γ
  · intro h
    exact h eqcovW eqcovZ

def Clos.subset (W Z : Clos X) {ιW ιZ : Type} (e : ιW ≃ ιZ) : Prop :=
  ∃ (Wrep Zrep : PreClos X) (hiW : Wrep.indnumb = ιW) (hiZ : Zrep.indnumb = ιZ)
    (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X)
    (eqcovW : Wrep.cov = cov) (eqcovZ : Zrep.cov = cov),
    (Quotient.mk'' Wrep : Clos X) = W ∧ (Quotient.mk'' Zrep : Clos X) = Z ∧
    PreClos.subset Wrep Zrep
      ((Equiv.cast hiW).trans (e.trans (Equiv.cast hiZ).symm)) cov eqcovW eqcovZ
