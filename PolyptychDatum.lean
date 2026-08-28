import PolyptychKernel
import MulticenterSingleDivisor

/-!
# Deformation data and their multi-centered deformation spaces (affine model)

Local affine models of the section "Local affine models" of Dubouloz-Mayeux, *A polyptych
of multi-centered deformation spaces* (arXiv:2411.15606).

A *deformation datum* on `Spec A` indexed by a finite totally ordered set `I` is a family of
ideals `M i` of `A` with `M i ≤ M i'` whenever `i ≤ i'` (so that `Xᵢ = Spec(A/Mᵢ)` is
order-reversing), together with elements `d i` of `A` (so that `Dᵢ = div(dᵢ)`).

For a subset `J ⊆ I` the deformation space `𝔻_J` is the spectrum of

`R_J = A[{ M_j / ∏_{s ∈ J≥j} d_s }_{j ∈ J}]`,

the multi-centered dilatation along `restCenter M d J`.  The closed immersion
`F_J(i) : (𝔻_J)ᵢ → 𝔻_J` corresponds to the surjection `panelHom` obtained by reducing the
datum modulo `M i`; its kernel is computed by `PolyptychKernel.ker_quotHom` under
Assumption 3.1 (`Cartier` below).

Main contents:
* `restCenter`, `elemOf` — the multicenter `{(M_j, ∏_{s∈J≥j} d_s)}_{j∈J}`;
* `Cartier` — Assumption 3.1 at ring level: `d i'` is a non-zero-divisor mod `M i`;
* `panelHom`, `ker_panelHom` — `F_J(i)^*` and the description of its kernel;
* `panelSubIdeal`, `panelSubIdeal_le_ker` — the inclusion lemma `lem:KerfJi-inclusion`;
* `upsilon` — the comparison morphism `υ_{K,J} : R_J → R_K` for `J ⊆ K`.
-/

suppress_compilation

universe u

open Family Multicenter Dilatation

namespace Polyptych

variable {A : Type (u+1)} [CommRing A] {I : Type} [LinearOrder I] [Fintype I]
variable (M : I → Ideal A) (d : I → A)

/-- `∏_{s ∈ J, j ≤ s} d_s`, the divisor attached to the index `j` inside `𝔻_J`. -/
def elemOf (J : Finset I) (j : I) : A := ∏ s ∈ J.filter (fun s => j ≤ s), d s

/-- The multicenter `{(M_j, ∏_{s∈J≥j} d_s)}_{j∈J}` on `A` defining `𝔻_J`. -/
def restCenter (J : Finset I) : Multicenter A where
  index := {j // j ∈ J}
  ideal j := M j.1
  elem j := elemOf d J j.1

@[simp] lemma restCenter_ideal (J : Finset I) (j : {j // j ∈ J}) :
    (restCenter M d J).ideal j = M j.1 := rfl

@[simp] lemma restCenter_elem (J : Finset I) (j : {j // j ∈ J}) :
    (restCenter M d J).elem j = elemOf d J j.1 := rfl

/-- `R_J = A[{M_j/∏_{s∈J≥j} d_s}]`. -/
abbrev Ring (J : Finset I) : Type (u+1) := A[restCenter M d J]

/-- **Assumption 3.1** at ring level: `Xᵢ ∩ D_{i'}` is Cartier in `Xᵢ`, i.e. the image of
`d i'` in `A ⧸ M i` is a non-zero-divisor, for all `i, i'`. -/
def Cartier : Prop :=
  ∀ i i' : I, Ideal.Quotient.mk (M i) (d i') ∈ nonZeroDivisors (A ⧸ M i)

variable {M d}

/-- Under Assumption 3.1 every distinguished element of `restCenter M d J` stays a
non-zero-divisor modulo `M i`. -/
lemma elemOf_quot_nzd (hC : Cartier M d) (J : Finset I) (i : I)
    (j : (restCenter M d J).index) :
    Ideal.Quotient.mk (M i) ((restCenter M d J).elem j) ∈ nonZeroDivisors (A ⧸ M i) := by
  show Ideal.Quotient.mk (M i) (∏ s ∈ J.filter (fun s => j.1 ≤ s), d s) ∈ _
  rw [map_prod]
  exact prod_mem fun s _ => hC i s

variable (M d)

/-- `F_J(i)^*`: the reduction of the deformation space `𝔻_J` modulo `M i`, the surjection
defining the panel `(𝔻_J)ᵢ`. -/
noncomputable def panelHom (hC : Cartier M d) (J : Finset I) (i : I) :
    (Ring M d J) →ₐ[A] (A ⧸ M i)[(restCenter M d J).quotCenter (M i)] :=
  (restCenter M d J).quotHom (M i) (elemOf_quot_nzd hC J i)

/-- **Lemma `lem:Kerf_Ji-Cartier`**: the kernel of `F_J(i)^*` consists of the fractions
whose numerator lies in `M i`. -/
theorem ker_panelHom (hC : Cartier M d) (J : Finset I) (i : I) :
    RingHom.ker (panelHom M d hC J i) =
      (restCenter M d J).kerFracIdeal (M i) :=
  (restCenter M d J).ker_quotHom (M i) (elemOf_quot_nzd hC J i)

/-- **`F_J(i)^*` is surjective** (`eq:f_ij-def`): the panel `(𝔻_J)ᵢ` is a closed
subscheme of `𝔻_J`. -/
theorem panelHom_surjective (hC : Cartier M d) (J : Finset I) (i : I) :
    Function.Surjective (panelHom M d hC J i) :=
  (restCenter M d J).quotHom_surjective (M i) (elemOf_quot_nzd hC J i)

/-- The ideal `(M i/∏_{s∈J≥i} d_s) + Σ_{j∈J} (M_j ∩ M i)/∏_{s∈J≥j} d_s` of `R_J` appearing
in the inclusion lemma `lem:KerfJi-inclusion`.  The first summand is recorded here as
`σ_J^*(M i)` together with the `j`-th terms: when `J≥i` is nonempty the fraction
`M i/∏_{s∈J≥i} d_s` is the `j₀`-term for `j₀ = min J≥i` (since `M i = M j₀ ∩ M i` and
`J≥i = J≥j₀`), and when `J≥i` is empty it is `σ_J^*(M i)`. -/
def panelSubIdeal (J : Finset I) (i : I) : Ideal (Ring M d J) :=
  Ideal.map (algebraMap A (Ring M d J)) (M i) ⊔
    ⨆ j : (restCenter M d J).index, Ideal.span
      {x : Ring M d J | ∃ (m : A) (hm : m ∈ M j.1) (_ : m ∈ M i),
        x = Dilatation.frac (Finsupp.single j 1)
          ⟨m, (restCenter M d J).mem_largeIdealPow_single j hm⟩}

/-- **Lemma `lem:KerfJi-inclusion`**. -/
theorem panelSubIdeal_le_ker (hC : Cartier M d) (J : Finset I) (i : I) :
    panelSubIdeal M d J i ≤ RingHom.ker (panelHom M d hC J i) := by
  rw [ker_panelHom M d hC J i]
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

section Upsilon

/-- `d_s` divides `∏_{s' ∈ K≥s} d_{s'}` when `s ∈ K`. -/
lemma d_dvd_elemOf (K : Finset I) (s : I) (hs : s ∈ K) : d s ∣ elemOf d K s := by
  classical
  refine Finset.dvd_prod_of_mem _ ?_
  simp only [Finset.mem_filter]
  exact ⟨hs, le_rfl⟩

/-- Every `d_s`, `s ∈ K`, becomes a non-zero-divisor in `R_K`. -/
lemma algebraMap_d_nzd (K : Finset I) (s : I) (hs : s ∈ K) :
    algebraMap A (Ring M d K) (d s) ∈ nonZeroDivisors (Ring M d K) := by
  obtain ⟨c, hc⟩ := d_dvd_elemOf d K s hs
  have h := nonzerodiv_image_single (restCenter M d K) ⟨s, hs⟩
  rw [restCenter_elem, hc, map_mul] at h
  exact (mul_mem_nonZeroDivisors.mp h).1

/-- For `J ⊆ K`, the `J`-divisor of `j` divides the `K`-divisor of `j`. -/
lemma elemOf_dvd_of_subset {J K : Finset I} (hJK : J ⊆ K) (j : I) :
    elemOf d J j ∣ elemOf d K j := by
  classical
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro s hs
  simp only [Finset.mem_filter] at hs ⊢
  exact ⟨hJK hs.1, hs.2⟩

/-- `σ_K^*` sends the `J`-divisors to non-zero-divisors of `R_K`. -/
lemma algebraMap_elemOf_nzd {J K : Finset I} (hJK : J ⊆ K) (j : I) :
    algebraMap A (Ring M d K) (elemOf d J j) ∈ nonZeroDivisors (Ring M d K) := by
  classical
  simp only [elemOf, map_prod]
  refine prod_mem fun s hs => algebraMap_d_nzd M d K s ?_
  exact hJK (Finset.mem_filter.mp hs).1

/-- The universal-property containment for `υ_{K,J}`. -/
lemma upsilon_gen {J K : Finset I} (hJK : J ⊆ K) (j : (restCenter M d J).index) :
    Ideal.map (algebraMap A (Ring M d K)) ((restCenter M d J).ideal j) ≤
      Ideal.span {algebraMap A (Ring M d K) ((restCenter M d J).elem j)} := by
  have hj : j.1 ∈ K := hJK j.2
  refine le_trans (Multicenter.self_le (restCenter M d K) ⟨j.1, hj⟩) ?_
  obtain ⟨c, hc⟩ := elemOf_dvd_of_subset d hJK j.1
  rw [restCenter_elem, hc, map_mul]
  exact Ideal.span_singleton_le_span_singleton.mpr ⟨_, rfl⟩

/-- **The comparison morphism `υ_{K,J} : R_J → R_K`** of `lem:nu_IJ`, for `J ⊆ K`. -/
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
