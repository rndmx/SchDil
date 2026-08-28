import MulticenterSingleDivisor
import StrictTransformPresent

/-!
# The canonical closed immersion of [Ma24, §5], and Fact 5.1 at the scheme level

The setup opening §5 of [Ma24] fixes closed subschemes `Y₀, …, Y_k ⊆ X`, a divisor `D`
meeting each `Yᵢ` in a Cartier divisor, and `Y₀ ⊆ Yᵢ` for every `i`; it then observes
that `Y₀ ⟶ X` lifts to a canonical **closed immersion**

  `Y₀ ⟶ Bl^{s₀D,…,s_kD}_{Y₀,…,Y_k} X`,

and Fact 5.1 computes, in the affine case, the ideal cutting it out: it is
`⟨M₀/a^{s₀}, …, M_k/a^{s_k}⟩`.

This file proves both, for an arbitrary `PreMultiCenter M` and an arbitrary index `i₀`
(no single-divisor assumption is needed).  The two standing hypotheses are stated on the
charts:

* `CentersOver` — `M.Yideal i γ ≤ M.Yideal i₀ γ`, the ideal-reversed `Y_{i₀} ⊆ Yᵢ`;
* `CarsOnCenter` — each `Dᵢ` restricts to a Cartier divisor on `Y_{i₀}`;
* `ElemNzdOnCenter` — its ring form on the charts of `X`.

Results:

* `Y0lift` — the unique lift `Y_{i₀} ⟶ Bl^{sD}_Y X`.  Its containment condition is free:
  every `Yᵢ` sits inside `Y_{i₀}`, whose ideal dies on its own charts
  (`Yideal_pull_eq_bot`), so the `pullSubset` condition is `⊥ ≤ _`.
* `Y0lift_isClosedImmersion` — **the §5 preamble claim**, by [Ma24, Prop. 4.3]:
  `ℓ ≫ θ` is the closed immersion `Y_{i₀} ↪ X` and `θ` is separated, being affine.
* `presentIdeal_Y0lift` — **Fact 5.1 at the scheme level**: on the dilatation charts,
  the chart ideal of `ℓ` is exactly `Multicenter.genFracIdeal`, the ideal that
  `MulticenterSingleDivisor.lean` proves is `ker (descTo)`.

The last one follows the pattern of the mono-centered `(P!)` of Lemma 4.4: the chart
piece `Spec (A_γ/M_{i₀})` of the center maps to the dilatation chart through the Fact 5.1
map `descTo` (`chartOfCenter_kappa`), the resulting cone `center_cone_eq` is an instance
of the universal property applied to a flat map over `Y_{i₀}`, and the comparison
`centerToPullback` into `Y_{i₀} ×_B chart_γ` is an isomorphism.  Feeding that and
`genFracQuotEquiv` into `spec_presentation_ideal_unique` identifies the two presentations.
-/

suppress_compilation
universe u
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

section SchemeFact51

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (i₀ : M.indnumb)
  (s : M.indnumb → ℕ)

/-- **General-index form of the vanishing of the center on its own charts**: the ideal of
`Y_{i₀}` dies in the canonical covering of `Y_{i₀} ×_X U_γ`. -/
theorem Yideal_pull_eq_bot
    (γβ : (pull_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X)).J) :
    Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
      (M.Yideal i₀ γβ.1) = ⊥ := by
  have hover := M.YcondOver i₀ γβ.1
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  have hsnd : pullback.snd (M.Ysub i₀ ↘ X) (M.Drep.cov.map γβ.1) =
      (M.YcondIso i₀ γβ.1).inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))) := by
    show pullback.snd (M.Ysub i₀ ↘ X) (M.cov.map γβ.1) = _
    rw [← hover, Iso.inv_hom_id_assoc]
  set ψ := Spec.preimage
    ((pull_loc_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ.1).map γβ.2 ≫
      (M.YcondIso i₀ γβ.1).inv) with hψ
  have hfact : pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ =
      CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1)) ≫ ψ := by
    apply Spec.map_injective
    rw [spec_map_pull_mor_ring, Spec.map_comp, hψ, Spec.map_preimage, hsnd,
      Category.assoc]
  rw [hfact, CommRingCat.hom_comp, ← Ideal.map_map,
    show (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))).hom =
      Ideal.Quotient.mk (M.Yideal i₀ γβ.1) from rfl,
    Ideal.map_quotient_self, Ideal.map_bot]

/-- The §5 hypothesis `Y_{i₀} ⊆ Yᵢ`, in chart form (note the reversal: the ideal of the
smaller subscheme is the bigger one). -/
def CentersOver : Prop :=
  ∀ (i : M.indnumb) (γ : M.cov.J), M.Yideal i γ ≤ M.Yideal i₀ γ

/-- The §5 hypothesis that every `Dᵢ` restricts to a Cartier divisor on `Y_{i₀}`, in
chart form on the canonical covering of `Y_{i₀} ×_X U_γ`. -/
def CarsOnCenter : Prop :=
  ∀ (i : M.indnumb) (γβ : (pull_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X)).J),
    ∃ g : (pull_loc_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ.1).obj γβ.2,
      Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
        (M.Dideal i γβ.1) = Ideal.span {g} ∧
      g ∈ nonZeroDivisors
        ((pull_loc_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ.1).obj γβ.2)

include s in
/-- Under the standing hypothesis, every multiple `sᵢDᵢ` also restricts to a Cartier
divisor on `Y_{i₀}`. -/
theorem Y0lift_isCars (hb : M.CarsOnCenter i₀) :
    IsCars (M.Ysub i₀) (Clos.pullback (M.Ysub i₀ ↘ X) (M.multiple s).D) := by
  refine ⟨pullback_PreClos X (M.Ysub i₀) (M.Ysub i₀ ↘ X) (M.multiple s).Drep,
    pullback_IsPreCars_of_charts _ _ _ (fun i γβ => ?_), rfl⟩
  obtain ⟨g, hg, hgnzd⟩ := hb i γβ
  refine ⟨g ^ s i, ?_, pow_mem hgnzd _⟩
  show Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
      ((M.Dideal i γβ.1) ^ (s i)) = _
  rw [Ideal.map_pow, hg, Ideal.span_singleton_pow]

/-- Chart form of the containment condition for the lift of `Y_{i₀}`. -/
theorem Y0lift_pullSubset_chart (hY : M.CentersOver i₀) (i : M.indnumb)
    (γβ : (pull_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X)).J) :
    Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
        (M.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ).hom
        ((M.Dideal i γβ.1) ^ (s i)) := by
  refine le_trans (Ideal.map_mono (hY i γβ.1)) ?_
  rw [M.Yideal_pull_eq_bot i₀ γβ]
  exact bot_le

/-- The containment condition for the lift of `Y_{i₀}`: free, because every center is
contained in `Y_{i₀}`, whose ideal dies on its own charts. -/
theorem Y0lift_pullSubset (hY : M.CentersOver i₀) :
    (M.multiple s).pullSubset (M.Ysub i₀ ↘ X) :=
  fun i γβ => M.Y0lift_pullSubset_chart i₀ s hY i γβ

/-- **The canonical closed immersion of [Ma24, §5]**: `Y_{i₀} ⟶ X` lifts uniquely to
`Bl^{sD}_Y X`. -/
theorem existsUnique_Y0lift (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀) :
    ∃! ℓ : M.Ysub i₀ ⟶ (M.multiple s).dilatation,
      ℓ ≫ (M.multiple s).structureMap = M.Ysub i₀ ↘ X :=
  (M.multiple s).universal_property (M.Ysub i₀) (M.Ysub i₀ ↘ X)
    (M.Y0lift_isCars i₀ s hb) (M.Y0lift_pullSubset i₀ s hY)

/-- The canonical lift `Y_{i₀} ⟶ Bl^{sD}_Y X`. -/
def Y0lift (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀) :
    M.Ysub i₀ ⟶ (M.multiple s).dilatation :=
  (M.existsUnique_Y0lift i₀ s hY hb).choose

@[simp] theorem Y0lift_over (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀) :
    M.Y0lift i₀ s hY hb ≫ (M.multiple s).structureMap = M.Ysub i₀ ↘ X :=
  (M.existsUnique_Y0lift i₀ s hY hb).choose_spec.1

theorem Y0lift_unique (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀)
    (g : M.Ysub i₀ ⟶ (M.multiple s).dilatation)
    (hg : g ≫ (M.multiple s).structureMap = M.Ysub i₀ ↘ X) :
    g = M.Y0lift i₀ s hY hb :=
  (M.existsUnique_Y0lift i₀ s hY hb).choose_spec.2 g hg

/-- **[Ma24, §5 preamble, via Prop. 4.3]**: the canonical lift is a closed immersion. -/
instance Y0lift_isClosedImmersion (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀) :
    IsClosedImmersion (M.Y0lift i₀ s hY hb) := by
  haveI h1 : IsClosedImmersion
      (M.Y0lift i₀ s hY hb ≫ (M.multiple s).structureMap) := by
    rw [M.Y0lift_over i₀ s hY hb]
    exact M.Yrep.subscheme_isClosedImmersion i₀
  haveI ha : IsAffineHom (M.multiple s).structureMap :=
    (M.multiple s).structureMap_isAffineHom
  haveI h2 : IsSeparated (M.multiple s).structureMap :=
    IsSeparated.of_isAffineHom _
  exact IsClosedImmersion.of_comp (M.Y0lift i₀ s hY hb) (M.multiple s).structureMap

/-- The §5 hypothesis that each `Dᵢ` meets `Y_{i₀}` in a Cartier divisor, in the ring
form used on the charts of `X`. -/
def ElemNzdOnCenter : Prop :=
  ∀ (i : M.indnumb) (γ : M.cov.J),
    Ideal.Quotient.mk (M.Yideal i₀ γ) ((M.localMulticenter γ).elem i) ∈
      nonZeroDivisors ((M.cov.obj γ) ⧸ M.Yideal i₀ γ)

include s in
/-- The chosen generator of `Dᵢ^{sᵢ}` is also a non-zero-divisor modulo the ideal of
`Y_{i₀}`. -/
theorem multiple_localGen_nzd_center (hSt : M.ElemNzdOnCenter i₀)
    (i : M.indnumb) (γ : M.cov.J) :
    Ideal.Quotient.mk (((M.multiple s).localMulticenter γ).ideal i₀)
        (((M.multiple s).localMulticenter γ).elem i) ∈
      nonZeroDivisors ((((M.multiple s).cov.obj γ)) ⧸
        ((M.multiple s).localMulticenter γ).ideal i₀) := by
  show Ideal.Quotient.mk (M.Yideal i₀ γ)
      (((M.multiple s).localMulticenter γ).elem i) ∈
    nonZeroDivisors ((M.cov.obj γ) ⧸ M.Yideal i₀ γ)
  have hbD : (M.localMulticenter γ).elem i ∈ M.Dideal i γ := by
    letI : Submodule.IsPrincipal (M.Dideal i γ) := M.Dprin i γ
    rw [← Ideal.span_singleton_generator (M.Dideal i γ)]
    exact Ideal.mem_span_singleton_self _
  have hmem : (M.localMulticenter γ).elem i ^ (s i) ∈
      Ideal.span {((M.multiple s).localMulticenter γ).elem i} := by
    rw [M.multiple_localGen_span' γ s i]
    exact Ideal.pow_mem_pow hbD (s i)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have h1 : Ideal.Quotient.mk (M.Yideal i₀ γ)
      ((M.localMulticenter γ).elem i ^ (s i)) ∈
      nonZeroDivisors ((M.cov.obj γ) ⧸ M.Yideal i₀ γ) := by
    rw [map_pow]
    exact pow_mem (hSt i γ) (s i)
  rw [← hc, map_mul] at h1
  exact (mul_mem_nonZeroDivisors.mp h1).2

/-- The chart-level hypotheses of [Ma24, Fact 5.1] hold on every chart. -/
theorem chart_hsub (hY : M.CentersOver i₀) (γ : M.cov.J) :
    ∀ i, ((M.multiple s).localMulticenter γ).ideal i ≤
      ((M.multiple s).localMulticenter γ).ideal i₀ :=
  fun i => hY i γ

/-- The chart piece of the center `Y_{i₀}`. -/
def chartOfCenter (γ : M.cov.J) : Scheme.{u+1} :=
  Spec (CommRingCat.of ((M.cov.obj γ) ⧸ M.Yideal i₀ γ))

/-- Its open immersion into the center. -/
def chartOfCenter_to (γ : M.cov.J) : M.chartOfCenter i₀ γ ⟶ M.Ysub i₀ :=
  (M.YcondIso i₀ γ).hom ≫ pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ)

instance chartOfCenter_to_flat (γ : M.cov.J) :
    AlgebraicGeometry.Flat (M.chartOfCenter_to i₀ γ) := by
  haveI h1 : IsOpenImmersion (pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ)) := by
    haveI := M.cov.map_prop γ
    infer_instance
  haveI : AlgebraicGeometry.Flat (pullback.fst (M.Ysub i₀ ↘ X) (M.cov.map γ)) :=
    inferInstance
  haveI : AlgebraicGeometry.Flat (M.YcondIso i₀ γ).hom := inferInstance
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

theorem chartOfCenter_to_overX (γ : M.cov.J) :
    M.chartOfCenter_to i₀ γ ≫ (M.Ysub i₀ ↘ X) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γ))) ≫
        M.cov.map γ := by
  have hover := M.YcondOver i₀ γ
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  rw [chartOfCenter_to, Category.assoc, pullback.condition, ← Category.assoc, hover]

/-- **The chart map `κ` of [Ma24, Fact 5.1]**: `Spec (A_γ/M_{i₀}) ⟶ Bl^{sD}`-chart,
given by the universal-property map `descTo` of `MulticenterSingleDivisor.lean`. -/
def chartOfCenter_kappa (hY : M.CentersOver i₀) (hSt : M.ElemNzdOnCenter i₀)
    (γ : M.cov.J) :
    M.chartOfCenter i₀ γ ⟶ (M.multiple s).chart γ :=
  Spec.map (CommRingCat.ofHom
    ((Multicenter.descTo ((M.multiple s).localMulticenter γ) i₀
      (M.chart_hsub i₀ s hY γ)
      (fun i => M.multiple_localGen_nzd_center i₀ s hSt i γ)).toRingHom))

theorem chartOfCenter_kappa_chartHom (hY : M.CentersOver i₀)
    (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    M.chartOfCenter_kappa i₀ s hY hSt γ ≫ (M.multiple s).chartHom γ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γ))) := by
  rw [chartOfCenter_kappa]
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact ((Multicenter.descTo ((M.multiple s).localMulticenter γ) i₀
    (M.chart_hsub i₀ s hY γ)
    (fun i => M.multiple_localGen_nzd_center i₀ s hSt i γ)).commutes a)

/-- Anything factoring through `Y_{i₀}` kills its ideal. -/
theorem pull_Yideal_eq_bot_of_factor {T : Scheme.{u+1}} (u : T ⟶ M.Ysub i₀)
    (γβ : (pull_cov X M.Drep T (u ≫ (M.Ysub i₀ ↘ X))).J) :
    Ideal.map (pull_mor_ring X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ).hom
      (M.Yideal i₀ γβ.1) = ⊥ := by
  have hover := M.YcondOver i₀ γβ.1
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  set pmap : pullback (u ≫ (M.Ysub i₀ ↘ X)) (M.Drep.cov.map γβ.1) ⟶
      pullback (M.Ysub i₀ ↘ X) (M.Drep.cov.map γβ.1) :=
    pullback.map _ _ _ _ u (𝟙 _) (𝟙 _) (by rw [Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp]) with hpmap
  have hsnd : pullback.snd (u ≫ (M.Ysub i₀ ↘ X)) (M.Drep.cov.map γβ.1) =
      pmap ≫ (M.YcondIso i₀ γβ.1).inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))) := by
    have h1 : pmap ≫ pullback.snd (M.Ysub i₀ ↘ X) (M.Drep.cov.map γβ.1) =
        pullback.snd (u ≫ (M.Ysub i₀ ↘ X)) (M.Drep.cov.map γβ.1) := by
      rw [hpmap, pullback.lift_snd, Category.comp_id]
    have h2 : pullback.snd (M.Ysub i₀ ↘ X) (M.Drep.cov.map γβ.1) =
        (M.YcondIso i₀ γβ.1).inv ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))) := by
      show pullback.snd (M.Ysub i₀ ↘ X) (M.cov.map γβ.1) = _
      rw [← hover, Iso.inv_hom_id_assoc]
    rw [← h1, h2]
  set ψ := Spec.preimage
    ((pull_loc_cov X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ.1).map γβ.2 ≫ pmap ≫
      (M.YcondIso i₀ γβ.1).inv) with hψ
  have hfact : pull_mor_ring X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ =
      CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1)) ≫ ψ := by
    apply Spec.map_injective
    rw [spec_map_pull_mor_ring, Spec.map_comp, hψ, Spec.map_preimage, hsnd]
    simp only [Category.assoc]
  rw [hfact, CommRingCat.hom_comp, ← Ideal.map_map,
    show (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))).hom =
      Ideal.Quotient.mk (M.Yideal i₀ γβ.1) from rfl,
    Ideal.map_quotient_self, Ideal.map_bot]

/-- Chart form of the containment condition for anything factoring through
`Y_{i₀}`. -/
theorem pullSubset_of_factor_center_chart (hY : M.CentersOver i₀)
    {T : Scheme.{u+1}} (u : T ⟶ M.Ysub i₀) (i : M.indnumb)
    (γβ : (pull_cov X M.Drep T (u ≫ (M.Ysub i₀ ↘ X))).J) :
    Ideal.map (pull_mor_ring X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ).hom
        (M.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep T (u ≫ (M.Ysub i₀ ↘ X)) γβ).hom
        ((M.Dideal i γβ.1) ^ (s i)) := by
  refine le_trans (Ideal.map_mono (hY i γβ.1)) ?_
  rw [M.pull_Yideal_eq_bot_of_factor i₀ u γβ]
  exact bot_le

theorem pullSubset_of_factor_center (hY : M.CentersOver i₀)
    {T : Scheme.{u+1}} (u : T ⟶ M.Ysub i₀) :
    (M.multiple s).pullSubset (u ≫ (M.Ysub i₀ ↘ X)) :=
  fun i γβ => M.pullSubset_of_factor_center_chart i₀ s hY u i γβ

theorem isCars_of_factor_center (hb : M.CarsOnCenter i₀)
    {T : Scheme.{u+1}} (u : T ⟶ M.Ysub i₀) [AlgebraicGeometry.Flat u] :
    IsCars T (Clos.pullback (u ≫ (M.Ysub i₀ ↘ X)) (M.multiple s).D) := by
  have hstep : Clos.pullback (u ≫ (M.Ysub i₀ ↘ X)) (M.multiple s).D =
      pullback_Clos u (Clos.pullback (M.Ysub i₀ ↘ X) (M.multiple s).D) := by
    show pullback_Clos (u ≫ (M.Ysub i₀ ↘ X))
      (Quotient.mk'' (M.multiple s).Drep) = _
    rw [pullback_assoc]
    rfl
  rw [hstep]
  exact pullback_IsCars T u _ (M.Y0lift_isCars i₀ s hb)

theorem existsUnique_lift_of_factor_center (hY : M.CentersOver i₀)
    (hb : M.CarsOnCenter i₀) {T : Scheme.{u+1}} (u : T ⟶ M.Ysub i₀)
    [AlgebraicGeometry.Flat u] :
    ∃! g : T ⟶ (M.multiple s).dilatation,
      g ≫ (M.multiple s).structureMap = u ≫ (M.Ysub i₀ ↘ X) :=
  (M.multiple s).universal_property T (u ≫ (M.Ysub i₀ ↘ X))
    (M.isCars_of_factor_center i₀ s hb u)
    (M.pullSubset_of_factor_center i₀ s hY u)

/-- **The cone equality**: the two natural maps from the chart of `Y_{i₀}` to
`Bl^{sD}_Y X` agree — through the lift `ℓ`, and through the Fact 5.1 quotient map. -/
theorem center_cone_eq (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀)
    (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    M.chartOfCenter_to i₀ γ ≫ M.Y0lift i₀ s hY hb =
      M.chartOfCenter_kappa i₀ s hY hSt γ ≫ (M.multiple s).chartTo γ := by
  refine ((M.existsUnique_lift_of_factor_center i₀ s hY hb
    (M.chartOfCenter_to i₀ γ)).unique ?_ ?_)
  · rw [Category.assoc, M.Y0lift_over i₀ s hY hb]
  · rw [Category.assoc, (M.multiple s).structureMap_chart γ]
    show M.chartOfCenter_kappa i₀ s hY hSt γ ≫
      (M.multiple s).chartHom γ ≫ M.cov.map γ = _
    rw [← Category.assoc, M.chartOfCenter_kappa_chartHom i₀ s hY hSt γ,
      ← M.chartOfCenter_to_overX i₀ γ]

/-- The comparison `Spec (A_γ/M_{i₀}) ⟶ Y_{i₀} ×_B chart_γ`. -/
def centerToPullback (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀)
    (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    M.chartOfCenter i₀ γ ⟶
      pullback (M.Y0lift i₀ s hY hb) ((M.multiple s).chartTo γ) :=
  pullback.lift (M.chartOfCenter_to i₀ γ) (M.chartOfCenter_kappa i₀ s hY hSt γ)
    (M.center_cone_eq i₀ s hY hb hSt γ)

/-- The inverse comparison, through `Y_{i₀} ×_X U_γ`. -/
def pullbackToCenter (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀)
    (γ : M.cov.J) :
    pullback (M.Y0lift i₀ s hY hb) ((M.multiple s).chartTo γ) ⟶
      M.chartOfCenter i₀ γ :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (M.multiple s).chartHom γ)
    (by
      rw [← M.Y0lift_over i₀ s hY hb, ← Category.assoc, pullback.condition,
        Category.assoc, (M.multiple s).structureMap_chart γ,
        show (M.multiple s).chartToX γ =
          (M.multiple s).chartHom γ ≫ M.cov.map γ from rfl, ← Category.assoc]) ≫
    (M.YcondIso i₀ γ).inv

theorem pullbackToCenter_comp_centerToPullback (hY : M.CentersOver i₀)
    (hb : M.CarsOnCenter i₀) (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    M.pullbackToCenter i₀ s hY hb γ ≫ M.centerToPullback i₀ s hY hb hSt γ =
      𝟙 _ := by
  haveI : Mono ((M.multiple s).chartTo γ) := by
    haveI := (M.multiple s).chartTo_isOpenImmersion γ
    infer_instance
  have hfst : M.pullbackToCenter i₀ s hY hb γ ≫ M.chartOfCenter_to i₀ γ =
      pullback.fst (M.Y0lift i₀ s hY hb) ((M.multiple s).chartTo γ) := by
    rw [pullbackToCenter, chartOfCenter_to, Category.assoc, Iso.inv_hom_id_assoc,
      pullback.lift_fst]
  apply pullback.hom_ext
  · rw [Category.assoc, centerToPullback, pullback.lift_fst, Category.id_comp]
    exact hfst
  · rw [Category.assoc, centerToPullback, pullback.lift_snd, Category.id_comp]
    apply Mono.right_cancellation (f := (M.multiple s).chartTo γ)
    rw [Category.assoc, ← M.center_cone_eq i₀ s hY hb hSt γ, ← Category.assoc,
      hfst]
    exact pullback.condition

theorem centerToPullback_comp_pullbackToCenter (hY : M.CentersOver i₀)
    (hb : M.CarsOnCenter i₀) (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    M.centerToPullback i₀ s hY hb hSt γ ≫ M.pullbackToCenter i₀ s hY hb γ =
      𝟙 _ := by
  have hover := M.YcondOver i₀ γ
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  rw [pullbackToCenter, ← Category.assoc, Iso.comp_inv_eq, Category.id_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, centerToPullback, pullback.lift_fst]
    rfl
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, centerToPullback,
      pullback.lift_snd, M.chartOfCenter_kappa_chartHom i₀ s hY hSt γ, hover]

instance centerToPullback_isIso (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀)
    (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    IsIso (M.centerToPullback i₀ s hY hb hSt γ) :=
  ⟨M.pullbackToCenter i₀ s hY hb γ,
    M.centerToPullback_comp_pullbackToCenter i₀ s hY hb hSt γ,
    M.pullbackToCenter_comp_centerToPullback i₀ s hY hb hSt γ⟩

/-- The `Spec`-level form of the Fact 5.1 quotient identification. -/
def chartOfCenter_genIso (hY : M.CentersOver i₀) (hSt : M.ElemNzdOnCenter i₀)
    (γ : M.cov.J) :
    M.chartOfCenter i₀ γ ≅
      Spec (CommRingCat.of
        ((Multicenter.Dilatation ((M.multiple s).localMulticenter γ)) ⧸
          ((M.multiple s).localMulticenter γ).genFracIdeal)) where
  hom := Spec.map (CommRingCat.ofHom
    ((Multicenter.genFracQuotEquiv ((M.multiple s).localMulticenter γ) i₀
      (M.chart_hsub i₀ s hY γ)
      (fun i => M.multiple_localGen_nzd_center i₀ s hSt i γ)).toRingEquiv.toRingHom))
  inv := Spec.map (CommRingCat.ofHom
    ((Multicenter.genFracQuotEquiv ((M.multiple s).localMulticenter γ) i₀
      (M.chart_hsub i₀ s hY γ)
      (fun i =>
        M.multiple_localGen_nzd_center i₀ s hSt i γ)).toRingEquiv.symm.toRingHom))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((Multicenter.genFracQuotEquiv ((M.multiple s).localMulticenter γ) i₀
          (M.chart_hsub i₀ s hY γ)
          (fun i => M.multiple_localGen_nzd_center i₀ s hSt i
            γ)).toRingEquiv.toRingHom).comp
        ((Multicenter.genFracQuotEquiv ((M.multiple s).localMulticenter γ) i₀
          (M.chart_hsub i₀ s hY γ)
          (fun i => M.multiple_localGen_nzd_center i₀ s hSt i
            γ)).toRingEquiv.symm.toRingHom) = RingHom.id _ from
        RingHom.ext fun x =>
          (Multicenter.genFracQuotEquiv ((M.multiple s).localMulticenter γ) i₀
            (M.chart_hsub i₀ s hY γ)
            (fun i => M.multiple_localGen_nzd_center i₀ s hSt i
              γ)).toRingEquiv.apply_symm_apply x]
    show Spec.map (𝟙 _) = 𝟙 _
    rw [Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((Multicenter.genFracQuotEquiv ((M.multiple s).localMulticenter γ) i₀
          (M.chart_hsub i₀ s hY γ)
          (fun i => M.multiple_localGen_nzd_center i₀ s hSt i
            γ)).toRingEquiv.symm.toRingHom).comp
        ((Multicenter.genFracQuotEquiv ((M.multiple s).localMulticenter γ) i₀
          (M.chart_hsub i₀ s hY γ)
          (fun i => M.multiple_localGen_nzd_center i₀ s hSt i
            γ)).toRingEquiv.toRingHom) = RingHom.id _ from
        RingHom.ext fun x =>
          (Multicenter.genFracQuotEquiv ((M.multiple s).localMulticenter γ) i₀
            (M.chart_hsub i₀ s hY γ)
            (fun i => M.multiple_localGen_nzd_center i₀ s hSt i
              γ)).toRingEquiv.symm_apply_apply x]
    show Spec.map (𝟙 _) = 𝟙 _
    rw [Spec.map_id]

@[simp] theorem chartOfCenter_genIso_hom (hY : M.CentersOver i₀)
    (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    (M.chartOfCenter_genIso i₀ s hY hSt γ).hom = Spec.map (CommRingCat.ofHom
      ((Multicenter.genFracQuotEquiv ((M.multiple s).localMulticenter γ) i₀
        (M.chart_hsub i₀ s hY γ)
        (fun i =>
          M.multiple_localGen_nzd_center i₀ s hSt i γ)).toRingEquiv.toRingHom)) :=
  rfl

theorem chartOfCenter_genIso_mk (hY : M.CentersOver i₀)
    (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    (M.chartOfCenter_genIso i₀ s hY hSt γ).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (((M.multiple s).localMulticenter γ).genFracIdeal))) =
      M.chartOfCenter_kappa i₀ s hY hSt γ := by
  rw [chartOfCenter_genIso_hom, chartOfCenter_kappa, ← Spec.map_comp]
  congr 1

/-- **The scheme-level form of [Ma24, Fact 5.1]**: on the dilatation charts of
`Bl^{sD}_Y X`, the chart ideal of the canonical closed immersion `Y_{i₀} ↪ Bl^{sD}_Y X`
is exactly the ideal `⟨Mᵢ/aᵢ⟩` of Fact 5.1. -/
theorem presentIdeal_Y0lift (hY : M.CentersOver i₀) (hb : M.CarsOnCenter i₀)
    (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    presentIdeal (M.Y0lift i₀ s hY hb) ((M.multiple s).dilatationCover) γ =
      ((M.multiple s).localMulticenter γ).genFracIdeal := by
  refine spec_presentation_ideal_unique
    (pullback.snd (M.Y0lift i₀ s hY hb)
      ((M.multiple s).dilatationCover.map γ)) _ _
    (presentIso (M.Y0lift i₀ s hY hb) ((M.multiple s).dilatationCover) γ)
    ((asIso (M.centerToPullback i₀ s hY hb hSt γ)).symm ≪≫
      M.chartOfCenter_genIso i₀ s hY hSt γ)
    (presentIso_eq (M.Y0lift i₀ s hY hb) ((M.multiple s).dilatationCover) γ)
    ?_
  rw [Iso.trans_hom, Category.assoc, M.chartOfCenter_genIso_mk i₀ s hY hSt γ,
    Iso.symm_hom, asIso_inv]
  symm
  rw [IsIso.inv_comp_eq]
  show M.chartOfCenter_kappa i₀ s hY hSt γ =
    M.centerToPullback i₀ s hY hb hSt γ ≫
      pullback.snd (M.Y0lift i₀ s hY hb) ((M.multiple s).chartTo γ)
  rw [centerToPullback, pullback.lift_snd]

end SchemeFact51

end PreMultiCenter

end SchemeDilatation
