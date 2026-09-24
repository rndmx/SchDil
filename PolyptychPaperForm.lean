import PolyptychBwd

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter Family
open Polyptych

namespace Polyptych

variable {A : Type (u+1)} [CommRing A] {I : Type} [LinearOrder I] [Fintype I]
variable (M : I → Ideal A) (d : I → A)

theorem Mono.min_ideal (hM : Mono M) (i j : I) : M (min i j) = M i ⊓ M j := by
  rcases le_total i j with h | h
  · rw [min_eq_left h]
    exact (inf_eq_left.mpr (hM h)).symm
  · rw [min_eq_right h]
    exact (inf_eq_right.mpr (hM h)).symm

section AnchorPow

variable (J : Finset I) (i : I)

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

def paperIdeal (J : Finset I) (i : I) : Ideal (Ring M d J) :=
  Ideal.span {x : Ring M d J | ∃ (m : A)
      (hx : m ∈ ((restCenter M d J).LargeIdeal ^
        (anchorPow M d J i) : Ideal A)),
      m ∈ M i ∧ x = Dilatation.frac (anchorPow M d J i) ⟨m, hx⟩} ⊔
    ⨆ j : (restCenter M d J).index, Ideal.span
      {x : Ring M d J | ∃ (m : A) (hm : m ∈ M j.1) (_ : m ∈ M i),
        x = Dilatation.frac (Finsupp.single j 1)
          ⟨m, (restCenter M d J).mem_largeIdealPow_single j hm⟩}

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

theorem paperIdeal_le_ker (J : Finset I) (i : I) :
    paperIdeal M d J i ≤ RingHom.ker (panelHom M d J i) := by
  have key : ∀ (ν : (restCenter M d J).index →₀ ℕ) (m : A)
      (hm : m ∈ (restCenter M d J).LargeIdeal ^ ν), m ∈ M i →
      panelHom M d J i (Dilatation.frac ν ⟨m, hm⟩) = 0 := by
    intro ν m hm hmi
    have hspec := (restCenter M d J).quotHom_frac_spec (M i) ν ⟨m, hm⟩
    have hzero : algebraMap A ((A ⧸ M i)[(restCenter M d J).quotCenter (M i)])
        ((⟨m, hm⟩ : (restCenter M d J).LargeIdeal ^ ν) : A) = 0 := by
      show algebraMap (A ⧸ M i) _ (Ideal.Quotient.mk (M i) m) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmi, map_zero]
    rw [hzero] at hspec
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff
      ((restCenter M d J).quotHom_elemPow_nzd (M i) ν)).mp hspec
  refine sup_le ?_ (iSup_le fun j => ?_)
  · rw [Ideal.span_le]
    rintro x ⟨m, hx, hmi, rfl⟩
    exact key _ m hx hmi
  · rw [Ideal.span_le]
    rintro x ⟨m, hm, hmi, rfl⟩
    exact key _ m _ hmi

theorem ker_panelHom_eq_paper (J : Finset I) (i : I) (hCi : CartierAt M d J i)
    (hM : Mono M) (hiJ : i ∉ J) (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    RingHom.ker (panelHom M d J i) = paperIdeal M d J i := by
  rw [paperIdeal_eq_panelSubIdeal M d hM J i]
  exact ker_panelHom_eq J i hCi hM hiJ hR1 hR2

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

variable (J : Finset M.indnumb) (hC : M.CartierDatum) (hM : M.MonoDatum)

include hC hM in
theorem panelStage_Yideal_eq_paper (hreg : M.DilRegular J)
    (i : (M.panelStage J).indnumb) (γ : M.cov.J) :
    (M.panelStage J).Yideal i γ =
      Ideal.map (M.chartEquiv J γ).toRingHom
        (Polyptych.paperIdeal (M.chartM γ) (M.chartd γ) J i.1) := by
  have hiJ : i.1 ∉ J := (Finset.mem_sdiff.mp i.2).2
  rw [M.panelStage_Yideal_eq J i γ,
    Polyptych.ker_panelHom_eq_paper (M.chartM γ) (M.chartd γ) J i.1 ((hC γ).at J i.1) (hM γ) hiJ
      (hreg γ i.1 hiJ).1 (hreg γ i.1 hiJ).2]

end PaperForm

structure Assumption31 : Prop where
  cartier : M.CartierDatum

def panelizationIsoPaper (J : Finset M.indnumb) (hA : M.Assumption31)
    (hM : M.MonoDatum) (hreg : M.DilRegular J) :
    M.panelSpace J ≅ (M.defSpace Finset.univ).dilatation :=
  M.panelizationIso J hA.cartier hM hreg

theorem chartM_panelCtr (hM : M.MonoDatum) (J : Finset M.indnumb) (i : M.indnumb)
    (γ : M.cov.J) (k : Option {j // j ∈ J}) :
    M.chartM γ (M.panelCtr J i k) =
      M.chartM γ i ⊓ M.chartM γ (M.panelKey J i k) := by
  cases k with
  | none => exact (inf_idem _).symm
  | some j => exact Polyptych.Mono.min_ideal (M.chartM γ) (hM γ) i j.1

end PreMultiCenter
end SchemeDilatation

namespace Polyptych

variable {A : Type (u+1)} [CommRing A] {I : Type} [LinearOrder I] [Fintype I]
variable {M : I → Ideal A} {d : I → A}

noncomputable def paperQuotEquiv (J : Finset I) (i : I) (hCi : CartierAt M d J i)
    (hM : Mono M) (hiJ : i ∉ J) (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    (Ring M d J ⧸ paperIdeal M d J i) ≃ₐ[A] Ring (resM M i) (resd M d i) J :=
  (Ideal.quotientEquivAlgOfEq A (paperIdeal_eq_panelSubIdeal M d hM J i)).trans
    (panelSubQuotEquiv J i hCi hM hiJ hR1 hR2)

end Polyptych
