import PolyptychKernel
import MulticenterSingleDivisor

suppress_compilation

universe u

open Family Multicenter Dilatation

namespace Polyptych

variable {A : Type (u+1)} [CommRing A] {I : Type} [LinearOrder I] [Fintype I]
variable (M : I → Ideal A) (d : I → A)

def elemOf (J : Finset I) (j : I) : A :=
  ∏ s ∈ J.filter (fun s => j ≤ s), d s

def restCenter (J : Finset I) : Multicenter A where
  index := {j // j ∈ J}
  ideal j := M j.1
  elem j := elemOf d J j.1

@[simp] lemma restCenter_ideal (J : Finset I) (j : {j // j ∈ J}) :
    (restCenter M d J).ideal j = M j.1 := rfl

@[simp] lemma restCenter_elem (J : Finset I) (j : {j // j ∈ J}) :
    (restCenter M d J).elem j = elemOf d J j.1 := rfl

abbrev Ring (J : Finset I) : Type (u+1) := A[restCenter M d J]

def Cartier : Prop :=
  ∀ i i' : I, Ideal.Quotient.mk (M i) (d i') ∈ nonZeroDivisors (A ⧸ M i)

def CartierAt (J : Finset I) (i : I) : Prop :=
  ∀ j ∈ J, Ideal.Quotient.mk (M i) (d j) ∈ nonZeroDivisors (A ⧸ M i)

variable {M d}

theorem Cartier.at (hC : Cartier M d) (J : Finset I) (i : I) : CartierAt M d J i :=
  fun j _ => hC i j

lemma elemOf_quot_nzd {J : Finset I} {i : I} (hCi : CartierAt M d J i)
    (j : (restCenter M d J).index) :
    Ideal.Quotient.mk (M i) ((restCenter M d J).elem j) ∈ nonZeroDivisors (A ⧸ M i) := by
  show Ideal.Quotient.mk (M i) (∏ s ∈ J.filter (fun s => j.1 ≤ s), d s) ∈ _
  rw [map_prod]
  exact prod_mem fun s hs => hCi s (Finset.mem_filter.mp hs).1

variable (M d)

noncomputable def panelHom (J : Finset I) (i : I) :
    (Ring M d J) →ₐ[A] (A ⧸ M i)[(restCenter M d J).quotCenter (M i)] :=
  (restCenter M d J).quotHom (M i)

theorem ker_panelHom {J : Finset I} {i : I} (hCi : CartierAt M d J i) :
    RingHom.ker (panelHom M d J i) =
      (restCenter M d J).kerFracIdeal (M i) :=
  (restCenter M d J).ker_quotHom (M i) (elemOf_quot_nzd hCi)

theorem panelHom_surjective (J : Finset I) (i : I) :
    Function.Surjective (panelHom M d J i) :=
  (restCenter M d J).quotHom_surjective (M i)

def panelSubIdeal (J : Finset I) (i : I) : Ideal (Ring M d J) :=
  Ideal.map (algebraMap A (Ring M d J)) (M i) ⊔
    ⨆ j : (restCenter M d J).index, Ideal.span
      {x : Ring M d J | ∃ (m : A) (hm : m ∈ M j.1) (_ : m ∈ M i),
        x = Dilatation.frac (Finsupp.single j 1)
          ⟨m, (restCenter M d J).mem_largeIdealPow_single j hm⟩}

theorem panelSubIdeal_le_ker_at {J : Finset I} {i : I} (hCi : CartierAt M d J i) :
    panelSubIdeal M d J i ≤ RingHom.ker (panelHom M d J i) := by
  rw [ker_panelHom M d hCi]
  refine sup_le ?_ (iSup_le fun j => ?_)
  · rw [Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap]
    have h0 : m ∈ (restCenter M d J).LargeIdeal ^ (0 : (restCenter M d J).index →₀ ℕ) := by
      simp
    rw [← (restCenter M d J).frac_zero_eq_algebraMap m h0]
    exact (restCenter M d J).frac_mem_kerFracIdeal (M i) 0 m h0 hm
  · rw [Ideal.span_le]
    rintro x ⟨m, hm, hmi, rfl⟩
    exact (restCenter M d J).frac_mem_kerFracIdeal (M i) _ m _ hmi

theorem panelSubIdeal_le_ker (hC : Cartier M d) (J : Finset I) (i : I) :
    panelSubIdeal M d J i ≤ RingHom.ker (panelHom M d J i) :=
  panelSubIdeal_le_ker_at M d (hC.at J i)

section Upsilon

lemma d_dvd_elemOf (K : Finset I) (s : I) (hs : s ∈ K) : d s ∣ elemOf d K s := by
  classical
  refine Finset.dvd_prod_of_mem _ ?_
  simp only [Finset.mem_filter]
  exact ⟨hs, le_rfl⟩

lemma algebraMap_d_nzd (K : Finset I) (s : I) (hs : s ∈ K) :
    algebraMap A (Ring M d K) (d s) ∈ nonZeroDivisors (Ring M d K) := by
  obtain ⟨c, hc⟩ := d_dvd_elemOf d K s hs
  have h := nonzerodiv_image_single (restCenter M d K) ⟨s, hs⟩
  rw [restCenter_elem, hc, map_mul] at h
  exact (mul_mem_nonZeroDivisors.mp h).1

lemma elemOf_dvd_of_subset {J K : Finset I} (hJK : J ⊆ K) (j : I) :
    elemOf d J j ∣ elemOf d K j := by
  classical
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro s hs
  simp only [Finset.mem_filter] at hs ⊢
  exact ⟨hJK hs.1, hs.2⟩

lemma algebraMap_elemOf_nzd {J K : Finset I} (hJK : J ⊆ K) (j : I) :
    algebraMap A (Ring M d K) (elemOf d J j) ∈ nonZeroDivisors (Ring M d K) := by
  classical
  simp only [elemOf, map_prod]
  refine prod_mem fun s hs => algebraMap_d_nzd M d K s ?_
  exact hJK (Finset.mem_filter.mp hs).1

lemma upsilon_gen {J K : Finset I} (hJK : J ⊆ K) (j : (restCenter M d J).index) :
    Ideal.map (algebraMap A (Ring M d K)) ((restCenter M d J).ideal j) ≤
      Ideal.span {algebraMap A (Ring M d K) ((restCenter M d J).elem j)} := by
  have hj : j.1 ∈ K := hJK j.2
  refine le_trans (Multicenter.self_le (restCenter M d K) ⟨j.1, hj⟩) ?_
  obtain ⟨c, hc⟩ := elemOf_dvd_of_subset d hJK j.1
  rw [restCenter_elem, hc, map_mul]
  exact Ideal.span_singleton_le_span_singleton.mpr ⟨_, rfl⟩

noncomputable def upsilon {J K : Finset I} (hJK : J ⊆ K) :
    (Ring M d J) →ₐ[A] (Ring M d K) :=
  desc (restCenter M d J)
    (fun j => algebraMap_elemOf_nzd M d hJK j.1)
    (fun j => (gen_iff_le (restCenter M d J) j).mpr (upsilon_gen M d hJK j))

@[simp] lemma upsilon_algebraMap {J K : Finset I} (hJK : J ⊆ K) (a : A) :
    upsilon M d hJK (algebraMap A (Ring M d J) a) = algebraMap A (Ring M d K) a :=
  (upsilon M d hJK).commutes a

end Upsilon

end Polyptych
