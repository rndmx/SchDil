import PolyptychBwd

/-!
# The paper's literal formulations

Everything in this file is a *restatement* of results already proved, in the exact form
in which Dubouloz-Mayeux, *A polyptych of multi-centered deformation spaces* writes them.
Nothing here is used elsewhere; it exists so that the formal statements can be compared
with the paper line by line.

* `Polyptych.Mono.min_ideal` — on a totally ordered index set with order-reversing
  centers, `M_{min(i,j)} = M_i ∩ M_j`, which is why the paper's intersections never leave
  the given family of centers.
* `Polyptych.anchorPow`, `Polyptych.paperIdeal` — the ideal
  `(M_i/∏_{s∈J≥i} d_s) + Σ_{j∈J} (M_j ∩ M_i)/∏_{s∈J≥j} d_s`
  of `lem:KerfJi-inclusion`, written with the paper's first summand (the denominator
  `∏_{s∈J≥i} d_s` is realised by `anchorPow`, i.e. by `j₀ = min J≥i` when `J≥i ≠ ∅` and
  by the empty exponent otherwise).
* `Polyptych.paperIdeal_eq_panelSubIdeal` — it agrees with the `panelSubIdeal` used in
  the development.
* `Polyptych.paperIdeal_le_ker` — **Lemma `lem:KerfJi-inclusion`**, literally.
* `Polyptych.ker_panelHom_eq_paper` — **Proposition `prop:Kernel-formula`**, literally.
* `panelStage_Yideal_eq_paper` — the centers of the scheme-level panel datum are that
  same ideal, *unconditionally* (no dilatation-regularity needed).
* `Assumption31`, `panelizationIsoPaper` — **Theorem 3.7** with the paper's hypotheses
  bundled as they are stated there.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter Family
open Polyptych

namespace Polyptych

variable {A : Type (u+1)} [CommRing A] {I : Type} [LinearOrder I] [Fintype I]
variable (M : I → Ideal A) (d : I → A)

/-- On a totally ordered index set with order-reversing centers, `M_{min(i,j)}` **is** the
intersection `M_i ∩ M_j`. -/
theorem Mono.min_ideal (hM : Mono M) (i j : I) : M (min i j) = M i ⊓ M j := by
  rcases le_total i j with h | h
  · rw [min_eq_left h]
    exact (inf_eq_left.mpr (hM h)).symm
  · rw [min_eq_right h]
    exact (inf_eq_right.mpr (hM h)).symm

section AnchorPow

variable (J : Finset I) (i : I)

/-- The exponent realising the denominator `∏_{s ∈ J≥i} d_s` inside `R_J`: `single j₀ 1`
for `j₀ = min J≥i` when `J≥i ≠ ∅`, and `0` otherwise. -/
def anchorPow : (restCenter M d J).index →₀ ℕ :=
  if h : (J.filter (fun s => i ≤ s)).Nonempty then
    Finsupp.single (⟨(J.filter (fun s => i ≤ s)).min' h,
      (Finset.mem_filter.mp (Finset.min'_mem _ h)).1⟩ :
      (restCenter M d J).index) 1
  else 0

theorem anchorPow_pos (h : (J.filter (fun s => i ≤ s)).Nonempty) :
    anchorPow M d J i =
      Finsupp.single (⟨(J.filter (fun s => i ≤ s)).min' h,
        (Finset.mem_filter.mp (Finset.min'_mem _ h)).1⟩ :
        (restCenter M d J).index) 1 := by
  rw [anchorPow]
  exact dif_pos h

theorem anchorPow_zero (h : ¬ (J.filter (fun s => i ≤ s)).Nonempty) :
    anchorPow M d J i = 0 := by
  rw [anchorPow]
  exact dif_neg h

/-- The distinguished element attached to `anchorPow` is exactly `∏_{s ∈ J≥i} d_s`. -/
theorem restCenter_elemPow_anchorPow :
    (restCenter M d J).elem ^ (anchorPow M d J i) = elemOf d J i := by
  classical
  by_cases h : (J.filter (fun s => i ≤ s)).Nonempty
  · rw [anchorPow_pos M d J i h, familyPow_single]
    show elemOf d J ((J.filter (fun s => i ≤ s)).min' h) = elemOf d J i
    simp only [elemOf]
    congr 1
    ext s
    simp only [Finset.mem_filter]
    exact ⟨fun hs => ⟨hs.1, le_trans
        (Finset.mem_filter.mp (Finset.min'_mem _ h)).2 hs.2⟩,
      fun hs => ⟨hs.1, Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs.1, hs.2⟩)⟩⟩
  · rw [anchorPow_zero M d J i h, familyPow_zero]
    rw [Finset.not_nonempty_iff_eq_empty] at h
    show (1 : A) = elemOf d J i
    simp only [elemOf, h, Finset.prod_empty]

/-- `M i` lies in the large-ideal power attached to `anchorPow`, so the fractions
`m/∏_{s∈J≥i} d_s` with `m ∈ M i` make sense in `R_J`. -/
theorem mem_largeIdealPow_anchorPow (hM : Mono M) {m : A} (hm : m ∈ M i) :
    m ∈ ((restCenter M d J).LargeIdeal ^ (anchorPow M d J i) : Ideal A) := by
  classical
  by_cases h : (J.filter (fun s => i ≤ s)).Nonempty
  · rw [anchorPow_pos M d J i h]
    refine (restCenter M d J).mem_largeIdealPow_single _ ?_
    show m ∈ M ((J.filter (fun s => i ≤ s)).min' h)
    exact hM (Finset.mem_filter.mp (Finset.min'_mem _ h)).2 hm
  · rw [anchorPow_zero M d J i h, familyPow_zero, Ideal.one_eq_top]
    trivial

end AnchorPow

/-- **The ideal of `lem:KerfJi-inclusion`, in the paper's form**:
`(M i / ∏_{s∈J≥i} d_s) + Σ_{j∈J} (M j ∩ M i)/∏_{s∈J≥j} d_s`. -/
def paperIdeal (J : Finset I) (i : I) : Ideal (Ring M d J) :=
  Ideal.span {x : Ring M d J | ∃ (m : A)
      (hx : m ∈ ((restCenter M d J).LargeIdeal ^ (anchorPow M d J i) : Ideal A)),
      m ∈ M i ∧ x = Dilatation.frac (anchorPow M d J i) ⟨m, hx⟩} ⊔
    ⨆ j : (restCenter M d J).index, Ideal.span
      {x : Ring M d J | ∃ (m : A) (hm : m ∈ M j.1) (_ : m ∈ M i),
        x = Dilatation.frac (Finsupp.single j 1)
          ⟨m, (restCenter M d J).mem_largeIdealPow_single j hm⟩}

/-- The paper's first summand `M i/∏_{s∈J≥i} d_s` lands in `panelSubIdeal`. -/
theorem frac_anchorPow_mem_panelSubIdeal (hM : Mono M) (J : Finset I) (i : I) {m : A}
    (hx : m ∈ ((restCenter M d J).LargeIdeal ^ (anchorPow M d J i) : Ideal A))
    (hmi : m ∈ M i) :
    Dilatation.frac (anchorPow M d J i) ⟨m, hx⟩ ∈ panelSubIdeal M d J i := by
  classical
  by_cases h : (J.filter (fun s => i ≤ s)).Nonempty
  · set j₀ : (restCenter M d J).index :=
      ⟨(J.filter (fun s => i ≤ s)).min' h,
        (Finset.mem_filter.mp (Finset.min'_mem _ h)).1⟩ with hj₀
    have hmj : m ∈ M j₀.1 :=
      hM (Finset.mem_filter.mp (Finset.min'_mem _ h)).2 hmi
    rw [(restCenter M d J).frac_exp_congr (anchorPow M d J i)
      (Finsupp.single j₀ 1) (anchorPow_pos M d J i h) m hx
      ((restCenter M d J).mem_largeIdealPow_single j₀ hmj)]
    exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem j₀
      (Ideal.subset_span ⟨m, hmj, hmi, rfl⟩))
  · have h0 : m ∈ ((restCenter M d J).LargeIdeal ^
        (0 : (restCenter M d J).index →₀ ℕ) : Ideal A) := by simp
    rw [(restCenter M d J).frac_exp_congr (anchorPow M d J i) 0
        (anchorPow_zero M d J i h) m hx h0,
      (restCenter M d J).frac_zero_eq_algebraMap m h0]
    exact Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hmi)

/-- **The paper's ideal is the `panelSubIdeal` used in this development.** -/
theorem paperIdeal_eq_panelSubIdeal (hM : Mono M) (J : Finset I) (i : I) :
    paperIdeal M d J i = panelSubIdeal M d J i := by
  classical
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
  · rw [Ideal.span_le]
    rintro x ⟨m, hx, hmi, rfl⟩
    exact frac_anchorPow_mem_panelSubIdeal M d hM J i hx hmi
  · rw [Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap]
    have hx := mem_largeIdealPow_anchorPow M d J i hM hm
    rw [(restCenter M d J).algebraMap_eq_pow_mul_frac (anchorPow M d J i) m hx]
    exact Ideal.mul_mem_left _ _ (Submodule.mem_sup_left
      (Ideal.subset_span ⟨m, hx, hm, rfl⟩))

/-- **Lemma `lem:KerfJi-inclusion`**, in the paper's form. -/
theorem paperIdeal_le_ker (hC : Cartier M d) (hM : Mono M) (J : Finset I) (i : I) :
    paperIdeal M d J i ≤ RingHom.ker (panelHom M d hC J i) := by
  rw [paperIdeal_eq_panelSubIdeal M d hM J i]
  exact panelSubIdeal_le_ker M d hC J i

/-- **Proposition `prop:Kernel-formula`**, in the paper's form:
`ker(F_J(i)^*) = (M i/∏_{s∈J≥i} d_s) + Σ_{j∈J} (M j ∩ M i)/∏_{s∈J≥j} d_s`. -/
theorem ker_panelHom_eq_paper (hC : Cartier M d) (hM : Mono M) (J : Finset I) (i : I)
    (hiJ : i ∉ J) (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    RingHom.ker (panelHom M d hC J i) = paperIdeal M d J i := by
  rw [paperIdeal_eq_panelSubIdeal M d hM J i]
  exact ker_panelHom_eq hC hM J i hiJ hR1 hR2

/-- The paper's second summand, written with `M_{min(i,j)}`: on a totally ordered index
set with order-reversing centers the intersection `M_j ∩ M_i` **is** the center
`M_{min(i,j)}`, which is what lets `panelBase` use only the *given* centers. -/
theorem paperIdeal_summand_min (hM : Mono M) (J : Finset I) (i : I)
    (j : (restCenter M d J).index) :
    Ideal.span {x : Ring M d J | ∃ (m : A) (hm : m ∈ M j.1) (_ : m ∈ M i),
        x = Dilatation.frac (Finsupp.single j 1)
          ⟨m, (restCenter M d J).mem_largeIdealPow_single j hm⟩} =
      Ideal.span {x : Ring M d J | ∃ (m : A) (hmin : m ∈ M (min i j.1)),
        x = Dilatation.frac (Finsupp.single j 1)
          ⟨m, (restCenter M d J).mem_largeIdealPow_single j
            (hM (min_le_right i j.1) hmin)⟩} := by
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, hm, hmi, rfl⟩
    exact ⟨m, by rw [Mono.min_ideal M hM i j.1]; exact ⟨hmi, hm⟩, rfl⟩
  · rintro ⟨m, hmin, rfl⟩
    rw [Mono.min_ideal M hM i j.1] at hmin
    exact ⟨m, hmin.2, hmin.1, rfl⟩

end Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb]

section PaperForm

variable (J : Finset M.indnumb) (hC : M.CartierDatum) (hb : M.CarsOnCenterAll)
  (hM : M.MonoDatum)

/-- **The centers of the scheme-level panel datum, unconditionally**: without assuming
dilatation-regularity they are already the ideal of `lem:KerfJi-inclusion` (transported
by the chart bridge).  Dilatation-regularity is what upgrades this to
`ker (F_J(i)^*)` (`panelStage_Yideal_eq`). -/
theorem panelStage_Yideal_eq_panelSubIdeal
    (i : (M.panelStage J hC hb hM).indnumb) (γ : M.cov.J) :
    (M.panelStage J hC hb hM).Yideal i γ =
      Ideal.map (M.chartEquiv J γ).toRingHom
        (Polyptych.panelSubIdeal (M.chartM γ) (M.chartd γ) J i.1) := by
  classical
  show Ideal.map (M.panelChartRho J i.1 γ hM).toRingHom
      (((M.panelInt J i.1).localMulticenter γ).genFracIdeal) = _
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, Multicenter.genFracIdeal]
    refine iSup_le fun k => ?_
    rw [Ideal.span_le]
    rintro x ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    cases k with
    | some j =>
      have hmj : m ∈ M.Yideal j.1 γ := hM γ (min_le_right i.1 j.1) hm
      have hmi : m ∈ M.Yideal i.1 γ := hM γ (min_le_left i.1 j.1) hm
      have hspan := M.panelFrac_span_eq J i.1 γ hM (some j) j m hm hmj rfl
      have hmem : M.chartEquiv J γ (Dilatation.frac (Finsupp.single j 1)
          ⟨m, (Polyptych.restCenter (M.chartM γ) (M.chartd γ)
            J).mem_largeIdealPow_single j hmj⟩) ∈
          Ideal.map (M.chartEquiv J γ).toRingHom
            (Polyptych.panelSubIdeal (M.chartM γ) (M.chartd γ) J i.1) :=
        Ideal.mem_map_of_mem _ (Submodule.mem_sup_right
          (Submodule.mem_iSup_of_mem j (Ideal.subset_span ⟨m, hmj, hmi, rfl⟩)))
      refine (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)) ?_
      rw [← hspan]
      exact Ideal.mem_span_singleton_self _
    | none =>
      by_cases hne : (J.filter (fun s => i.1 ≤ s)).Nonempty
      · obtain ⟨j₀, hj₀J, hij₀, hfil⟩ := M.panelKey_filter_eq J i.1 hne
        have hmj : m ∈ M.Yideal j₀ γ := hM γ hij₀ hm
        have hspan := M.panelFrac_span_eq J i.1 γ hM none ⟨j₀, hj₀J⟩ m hm hmj hfil.symm
        have hmem : M.chartEquiv J γ (Dilatation.frac (Finsupp.single
            (⟨j₀, hj₀J⟩ : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) 1)
            ⟨m, (Polyptych.restCenter (M.chartM γ) (M.chartd γ)
              J).mem_largeIdealPow_single ⟨j₀, hj₀J⟩ hmj⟩) ∈
            Ideal.map (M.chartEquiv J γ).toRingHom
              (Polyptych.panelSubIdeal (M.chartM γ) (M.chartd γ) J i.1) :=
          Ideal.mem_map_of_mem _ (Submodule.mem_sup_right
            (Submodule.mem_iSup_of_mem ⟨j₀, hj₀J⟩
              (Ideal.subset_span ⟨m, hmj, hm, rfl⟩)))
        refine (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)) ?_
        rw [← hspan]
        exact Ideal.mem_span_singleton_self _
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hunit : IsUnit (((M.panelInt J i.1).localMulticenter γ).elem none) := by
          rw [← Ideal.span_singleton_eq_top, M.panelInt_chart_span J i.1 γ none,
            show J.filter (fun s => M.panelKey J i.1 none ≤ s) = ∅ from hne,
            Finset.prod_empty, Ideal.one_eq_top]
        have hunitC : IsUnit (algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
            (((M.panelInt J i.1).localMulticenter γ).elem none)) :=
          hunit.map (algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
        obtain ⟨v, hv⟩ := hunitC
        have hG := M.panelChartRho_frac J i.1 γ hM (Finsupp.single none 1)
          ⟨m, ((M.panelInt J i.1).localMulticenter γ).mem_largeIdealPow_single none hm⟩
        rw [familyPow_single] at hG
        have hmemC : algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m ∈
            Ideal.map (M.chartEquiv J γ).toRingHom
              (Polyptych.panelSubIdeal (M.chartM γ) (M.chartd γ) J i.1) := by
          have hkey : (M.chartEquiv J γ).toRingHom (algebraMap (M.cov.obj γ)
              (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) m) =
              algebraMap ((M.defSpace J).cov.obj γ)
                (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m :=
            M.chartEquiv_algebraMap J γ m
          rw [← hkey]
          exact Ideal.mem_map_of_mem _
            (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hm))
        refine (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmemC)) ?_
        refine Ideal.mem_span_singleton'.mpr ⟨↑v⁻¹, ?_⟩
        rw [← hG, ← hv, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_mul]
        rfl
  · rw [Ideal.map_le_iff_le_comap, Polyptych.panelSubIdeal]
    refine sup_le ?_ (iSup_le fun j => ?_)
    · rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have hkey : (M.chartEquiv J γ).toRingHom (algebraMap (M.cov.obj γ)
          (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) m) =
          algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m :=
        M.chartEquiv_algebraMap J γ m
      have hG := M.panelChartRho_frac J i.1 γ hM (Finsupp.single none 1)
        ⟨m, ((M.panelInt J i.1).localMulticenter γ).mem_largeIdealPow_single none hm⟩
      rw [familyPow_single] at hG
      rw [hkey, ← hG]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _
        (((M.panelInt J i.1).localMulticenter γ).frac_mem_genFracIdeal none hm))
    · rw [Ideal.span_le]
      rintro x ⟨m, hmj, hmi, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]
      have hmk : m ∈ M.Yideal (min i.1 j.1) γ := by
        rcases le_total i.1 j.1 with h | h
        · rw [min_eq_left h]; exact hmi
        · rw [min_eq_right h]; exact hmj
      have hspan := M.panelFrac_span_eq J i.1 γ hM (some j) j m hmk hmj rfl
      have hmem : M.panelChartRho J i.1 γ hM (Dilatation.frac
          (Finsupp.single (some j) 1)
          ⟨m, ((M.panelInt J i.1).localMulticenter γ).mem_largeIdealPow_single
            (some j) hmk⟩) ∈
          Ideal.map (M.panelChartRho J i.1 γ hM).toRingHom
            (((M.panelInt J i.1).localMulticenter γ).genFracIdeal) :=
        Ideal.mem_map_of_mem _
          (((M.panelInt J i.1).localMulticenter γ).frac_mem_genFracIdeal (some j) hmk)
      refine (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)) ?_
      rw [hspan]
      exact Ideal.mem_span_singleton_self _

/-- **The centers of `𝔻𝔻_J` are the paper's ideal**, unconditionally. -/
theorem panelStage_Yideal_eq_paper
    (i : (M.panelStage J hC hb hM).indnumb) (γ : M.cov.J) :
    (M.panelStage J hC hb hM).Yideal i γ =
      Ideal.map (M.chartEquiv J γ).toRingHom
        (Polyptych.paperIdeal (M.chartM γ) (M.chartd γ) J i.1) := by
  rw [M.panelStage_Yideal_eq_panelSubIdeal J hC hb hM i γ,
    Polyptych.paperIdeal_eq_panelSubIdeal (M.chartM γ) (M.chartd γ) (hM γ) J i.1]

end PaperForm

/-- **Assumption 3.1** at scheme level, bundled: `X_i ∩ D_{i'}` is a Cartier divisor in
`X_i` for all `i, i'`, expressed on the charts of `X` (`CartierDatum`) and on the
canonical covering of `X_i ×_X U_γ` (`CarsOnCenterAll`). -/
structure Assumption31 : Prop where
  cartier : M.CartierDatum
  cars : M.CarsOnCenterAll

/-- **Theorem 3.7**, with the paper's hypotheses: a deformation datum on `X` (its centers
order-reversing, `hM`) satisfying Assumption 3.1 (`hA`) and dilatation-regular with
respect to `J` (`hreg`) has `Θ_J : 𝔻𝔻_J → 𝔻_I` an isomorphism. -/
def panelizationIsoPaper (J : Finset M.indnumb) (hA : M.Assumption31)
    (hM : M.MonoDatum) (hreg : M.DilRegular J) :
    M.panelSpace J hA.cartier hA.cars hM ≅ (M.defSpace Finset.univ).dilatation :=
  M.panelizationIso J hA.cartier hA.cars hM hreg

/-- The center of `panelBase` at index `k` is the intersection `X_i ∩ X_{key k}`: on a
totally ordered index set with order-reversing centers, `M_{min(i,j)} = M_i ∩ M_j`, so the
ideal appearing in `lem:KerfJi-inclusion` is again one of the *given* centers. -/
theorem chartM_panelCtr (hM : M.MonoDatum) (J : Finset M.indnumb) (i : M.indnumb)
    (γ : M.cov.J) (k : Option {j // j ∈ J}) :
    M.chartM γ (M.panelCtr J i k) =
      M.chartM γ i ⊓ M.chartM γ (M.panelKey J i k) := by
  cases k with
  | none => exact (inf_idem _).symm
  | some j => exact Polyptych.Mono.min_ideal (M.chartM γ) (hM γ) i j.1

end PreMultiCenter
end SchemeDilatation
