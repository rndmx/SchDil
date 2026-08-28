import PolyptychSchemeUpsilon
import SchemeFact51

/-!
# The intermediate deformation space carrying the panel `(𝔻_J)ᵢ`

For Theorem 3.7 (`theo-iso-panelization`) of Dubouloz-Mayeux, *A polyptych of
multi-centered deformation spaces*, the second-stage centers on `𝔻_J` are the panels
`(𝔻_J)ᵢ`, `i ∈ I ∖ J`, whose chart ideals are `ker(F_J(i)^*)`.  By the kernel formula
these are

`(Mᵢ / ∏_{s ∈ J≥i} d_s) + Σ_{j ∈ J} (M_j ∩ Mᵢ) / ∏_{s ∈ J≥j} d_s`.

Because the index set is *totally ordered* and the centers are monotone, `M_j ∩ Mᵢ` is
simply `M_{min(i,j)}` — again one of the *given* centers.  Hence the displayed ideal is
the `genFracIdeal` (the ideal of Fact 5.1) of the multicenter

`panelBase M J i = { (X_{min(i,k)}, Σ_{s ∈ J≥k} D_s) }_{k ∈ J ∪ {i}}`,

all of whose centers are contained in `Xᵢ` (`panelBase_centersOver`).  So on
`𝔻(panelBase M J i)` the panel is the *lift of `Xᵢ`* of `SchemeFact51`, a globally defined
closed immersion — which is exactly what is needed to glue the chart ideals on `𝔻_J`
(the `ChartDatum.compat` obligation, inherited through `chartIdeal_agree` as in
`IteratedSchemeMultiCore.strictYChartDatum`).

The index set `J ∪ {i}` is realised as `Option ↥J`, so that the distinguished index
reduces definitionally (`min i i` does not).

This file builds `panelBase`, the associated `panelInt` (its `1`-st multiple, the form in
which `SchemeFact51` is stated), and the comparison morphism
`panelProj : 𝔻_J → 𝔻(panelInt)` through which everything is transported.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]

/-- The divisor index of the panel multicenter: `i` at the distinguished index, `j`
elsewhere. -/
def panelKey (J : Finset M.indnumb) (i : M.indnumb) :
    Option {j // j ∈ J} → M.indnumb
  | none => i
  | some j => j.1

/-- The center index of the panel multicenter: `Xᵢ` at the distinguished index,
`X_{min(i,j)} = X_j ∩ Xᵢ` elsewhere. -/
def panelCtr (J : Finset M.indnumb) (i : M.indnumb) :
    Option {j // j ∈ J} → M.indnumb
  | none => i
  | some j => min i j.1

@[simp] theorem panelKey_none (J : Finset M.indnumb) (i : M.indnumb) :
    M.panelKey J i none = i := rfl

@[simp] theorem panelKey_some (J : Finset M.indnumb) (i : M.indnumb)
    (j : {j // j ∈ J}) : M.panelKey J i (some j) = j.1 := rfl

@[simp] theorem panelCtr_none (J : Finset M.indnumb) (i : M.indnumb) :
    M.panelCtr J i none = i := rfl

@[simp] theorem panelCtr_some (J : Finset M.indnumb) (i : M.indnumb)
    (j : {j // j ∈ J}) : M.panelCtr J i (some j) = min i j.1 := rfl

theorem panelCtr_le (J : Finset M.indnumb) (i : M.indnumb)
    (k : Option {j // j ∈ J}) : M.panelCtr J i k ≤ i := by
  cases k with
  | none => exact le_rfl
  | some j => exact min_le_left i j.1

/-- **The intermediate multicenter for the panel `(𝔻_J)ᵢ`**: index `J ∪ {i}`, centers
`X_{min(i,k)} = Xₖ ∩ Xᵢ`, divisors `Σ_{s ∈ J≥k} D_s`. -/
def panelBase (J : Finset M.indnumb) (i : M.indnumb) : PreMultiCenter X where
  indnumb := Option {j // j ∈ J}
  cov := M.cov
  Ysub k := M.Ysub (M.panelCtr J i k)
  Dsub k := (M.defDChartDatum J (M.panelKey J i k)).glued
  Yover k := M.Yover (M.panelCtr J i k)
  Dover k := ⟨(M.defDChartDatum J (M.panelKey J i k)).structureMap⟩
  Yideal k γ := M.Yideal (M.panelCtr J i k) γ
  Dideal k γ := ∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s), M.Dideal s γ
  YcondIso k γ := M.YcondIso (M.panelCtr J i k) γ
  YcondOver k γ := M.YcondOver (M.panelCtr J i k) γ
  DcondIso k γ := asIso ((M.defDChartDatum J (M.panelKey J i k)).chartCompare γ)
  DcondOver k γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
    show (M.defDChartDatum J (M.panelKey J i k)).chartCompare γ ≫
        pullback.snd ((M.defDChartDatum J (M.panelKey J i k)).structureMap)
          (M.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s), M.Dideal s γ)))
    exact (M.defDChartDatum J (M.panelKey J i k)).chartCompare_snd γ
  Dprin k γ := by
    classical
    refine ⟨⟨∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s),
      (M.Dprin s γ).generator, ?_⟩⟩
    · rw [Ideal.submodule_span_eq, Ideal.span_singleton_finset_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      letI : Submodule.IsPrincipal (M.Dideal s γ) := M.Dprin s γ
      exact (Ideal.span_singleton_generator (M.Dideal s γ)).symm

@[simp] theorem panelBase_Yideal (J : Finset M.indnumb) (i : M.indnumb)
    (k : (M.panelBase J i).indnumb) (γ : M.cov.J) :
    (M.panelBase J i).Yideal k γ = M.Yideal (M.panelCtr J i k) γ := rfl

@[simp] theorem panelBase_Dideal (J : Finset M.indnumb) (i : M.indnumb)
    (k : (M.panelBase J i).indnumb) (γ : M.cov.J) :
    (M.panelBase J i).Dideal k γ =
      ∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s), M.Dideal s γ := rfl

@[simp] theorem panelBase_cov (J : Finset M.indnumb) (i : M.indnumb) :
    (M.panelBase J i).cov = M.cov := rfl

/-- The distinguished index `i` of `panelBase M J i`. -/
def panelIdx (J : Finset M.indnumb) (i : M.indnumb) : (M.panelBase J i).indnumb := none

@[simp] theorem panelBase_Ysub_panelIdx (J : Finset M.indnumb) (i : M.indnumb) :
    (M.panelBase J i).Ysub (M.panelIdx J i) = M.Ysub i := rfl

@[simp] theorem panelBase_Yideal_panelIdx (J : Finset M.indnumb) (i : M.indnumb)
    (γ : M.cov.J) :
    (M.panelBase J i).Yideal (M.panelIdx J i) γ = M.Yideal i γ := rfl

/-- **All centers of `panelBase M J i` lie in `Xᵢ`** — the hypothesis `CentersOver` of
`SchemeFact51`, which is what makes `Xᵢ` lift to `𝔻(panelBase M J i)`. -/
theorem panelBase_centersOver (hM : M.MonoDatum) (J : Finset M.indnumb) (i : M.indnumb) :
    (M.panelBase J i).CentersOver (M.panelIdx J i) := by
  intro k γ
  exact hM γ (M.panelCtr_le J i k)

/-- The form in which `SchemeFact51` is stated: the `1`-st multiple. -/
def panelInt (J : Finset M.indnumb) (i : M.indnumb) : PreMultiCenter X :=
  (M.panelBase J i).multiple (fun _ => 1)

@[simp] theorem panelInt_Yideal (J : Finset M.indnumb) (i : M.indnumb)
    (k : (M.panelBase J i).indnumb) (γ : M.cov.J) :
    (M.panelInt J i).Yideal k γ = M.Yideal (M.panelCtr J i k) γ := rfl

@[simp] theorem panelInt_Dideal (J : Finset M.indnumb) (i : M.indnumb)
    (k : (M.panelBase J i).indnumb) (γ : M.cov.J) :
    (M.panelInt J i).Dideal k γ =
      (∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s), M.Dideal s γ) ^ 1 := rfl

section Proj

variable (J : Finset M.indnumb) (i : M.indnumb)

/-- The Cartier condition for `𝔻_J → 𝔻(panelInt)`, chart level. -/
theorem panelProj_isCars_chart (k : (M.panelBase J i).indnumb)
    (γβ : (pull_cov X M.Drep (M.defSpace J).dilatation
      (M.defSpace J).structureMap).J) :
    ∃ g : (pull_loc_cov X M.Drep (M.defSpace J).dilatation
        (M.defSpace J).structureMap γβ.1).obj γβ.2,
      (pullback_PreClos X (M.defSpace J).dilatation
          (M.defSpace J).structureMap (M.panelInt J i).Drep).ideal k γβ =
        Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov X M.Drep (M.defSpace J).dilatation
        (M.defSpace J).structureMap γβ.1).obj γβ.2) := by
  classical
  refine ⟨(pull_mor_ring X M.Drep (M.defSpace J).dilatation
      (M.defSpace J).structureMap γβ).hom
      (∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s),
        ((M.localMulticenter γβ.1).elem s)), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep (M.defSpace J).dilatation
        (M.defSpace J).structureMap γβ).hom
        ((∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s), M.Dideal s γβ.1) ^ 1) = _
    rw [pow_one, M.defSpace_Dideal_map_span J γβ.1 _ (M.panelKey J i k)]
    rfl
  · rw [map_prod]
    exact prod_mem fun s hs =>
      M.defSpace_gen_nzd J s (Finset.mem_filter.mp hs).1 γβ

/-- The Cartier condition for `𝔻_J → 𝔻(panelInt)`. -/
theorem panelProj_isCars :
    IsCars (M.defSpace J).dilatation
      (Clos.pullback (M.defSpace J).structureMap (M.panelInt J i).D) :=
  ⟨pullback_PreClos X (M.defSpace J).dilatation
      (M.defSpace J).structureMap (M.panelInt J i).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun k γβ => M.panelProj_isCars_chart J i k γβ),
    rfl⟩

/-- For the distinguished index, `J≥i` is `J≥j₀` where `j₀ = min J≥i`. -/
theorem panelKey_filter_eq (hne : (J.filter (fun s => i ≤ s)).Nonempty) :
    ∃ j₀ ∈ J, i ≤ j₀ ∧
      J.filter (fun s => j₀ ≤ s) = J.filter (fun s => i ≤ s) := by
  classical
  refine ⟨(J.filter (fun s => i ≤ s)).min' hne,
    (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1,
    (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2, ?_⟩
  ext s
  simp only [Finset.mem_filter]
  refine ⟨fun h => ⟨h.1, le_trans (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2 h.2⟩,
    fun h => ⟨h.1, Finset.min'_le _ s (Finset.mem_filter.mpr ⟨h.1, h.2⟩)⟩⟩

/-- The containment condition for `𝔻_J → 𝔻(panelInt)`, chart level. -/
theorem panelProj_pullSubset_chart (hM : M.MonoDatum) (k : (M.panelBase J i).indnumb)
    (γβ : (pull_cov X M.Drep (M.defSpace J).dilatation
      (M.defSpace J).structureMap).J) :
    Ideal.map (pull_mor_ring X M.Drep (M.defSpace J).dilatation
        (M.defSpace J).structureMap γβ).hom (M.Yideal (M.panelCtr J i k) γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep (M.defSpace J).dilatation
        (M.defSpace J).structureMap γβ).hom
        ((∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s), M.Dideal s γβ.1) ^ 1) := by
  classical
  rw [pow_one]
  cases k with
  | none =>
    by_cases hne : (J.filter (fun s => i ≤ s)).Nonempty
    · obtain ⟨j₀, hj₀J, hij₀, hfil⟩ := M.panelKey_filter_eq J i hne
      have h1 := (M.defSpace J).structureMap_pullSubset ⟨j₀, hj₀J⟩ γβ
      have h2 : (∏ s ∈ J.filter (fun s => j₀ ≤ s), M.Dideal s γβ.1) =
          ∏ s ∈ J.filter (fun s => M.panelKey J i none ≤ s), M.Dideal s γβ.1 := by
        rw [panelKey_none, hfil]
      rw [← h2]
      exact le_trans (Ideal.map_mono (hM γβ.1 hij₀)) h1
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [show J.filter (fun s => M.panelKey J i none ≤ s) = ∅ from hne,
        Finset.prod_empty, Ideal.one_eq_top, Ideal.map_top]
      exact le_top
  | some j =>
    have h1 := (M.defSpace J).structureMap_pullSubset ⟨j.1, j.2⟩ γβ
    exact le_trans (Ideal.map_mono (hM γβ.1 (min_le_right i j.1))) h1

/-- The containment condition for `𝔻_J → 𝔻(panelInt)`. -/
theorem panelProj_pullSubset (hM : M.MonoDatum) :
    (M.panelInt J i).pullSubset (M.defSpace J).structureMap :=
  ((M.panelInt J i).pullSubset_iff (M.defSpace J).structureMap).mpr
    (fun k γβ => M.panelProj_pullSubset_chart J i hM k γβ)

/-- **The comparison morphism `𝔻_J → 𝔻(panelInt M J i)`** through which the panel
`(𝔻_J)ᵢ` is pulled back. -/
theorem existsUnique_panelProj (hM : M.MonoDatum) :
    ∃! φ : (M.defSpace J).dilatation ⟶ (M.panelInt J i).dilatation,
      φ ≫ (M.panelInt J i).structureMap = (M.defSpace J).structureMap :=
  (M.panelInt J i).universal_property (M.defSpace J).dilatation
    (M.defSpace J).structureMap (M.panelProj_isCars J i)
    (M.panelProj_pullSubset J i hM)

/-- The comparison morphism `𝔻_J → 𝔻(panelInt M J i)`. -/
def panelProj (hM : M.MonoDatum) :
    (M.defSpace J).dilatation ⟶ (M.panelInt J i).dilatation :=
  (M.existsUnique_panelProj J i hM).choose

@[simp] theorem panelProj_over (hM : M.MonoDatum) :
    M.panelProj J i hM ≫ (M.panelInt J i).structureMap =
      (M.defSpace J).structureMap :=
  (M.existsUnique_panelProj J i hM).choose_spec.1

theorem panelProj_unique (hM : M.MonoDatum)
    (g : (M.defSpace J).dilatation ⟶ (M.panelInt J i).dilatation)
    (hg : g ≫ (M.panelInt J i).structureMap = (M.defSpace J).structureMap) :
    g = M.panelProj J i hM :=
  (M.existsUnique_panelProj J i hM).choose_spec.2 g hg

end Proj

end PreMultiCenter
end SchemeDilatation
