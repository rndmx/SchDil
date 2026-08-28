import MulticenterRing
import MulticenterTower

/-!
# The monopoly isomorphism for dilatations of rings: [Ma24, Prop. 2.36]

For a finite multicenter `{[Mᵢ, aᵢ]}_{i ∈ I}` on `A`, put `a := ∏ᵢ aᵢ` and
`N := ∑ᵢ (Mᵢ · ∏_{j ≠ i} aⱼ)`. Then there is a unique isomorphism of `A`-algebras

  `A[{Mᵢ/aᵢ}] ≃ₐ[A] A[N/a]`.

`M.monopoly` is the mono-centered multicenter `[N, a]`. The proof is by the universal
property on both sides: for any `A`-algebra `B`, the two sets of conditions are
equivalent —

* `prodElem_nzd_iff`: `f(∏ aᵢ)` is a non-zero-divisor iff every `f(aᵢ)` is;
* `monopoly_map_le_iff`: given that, `f(N)B ⊆ f(a)B` iff `f(Mᵢ)B ⊆ f(aᵢ)B` for all `i`
  (one direction multiplies by `∏_{j≠i} aⱼ`, the other cancels it).

Both `desc` maps then exist, and their composites are identities by
`lemma_exists_unique_morphism'`. These condition-transfer lemmas are stated for an
arbitrary `A`-algebra `B` so they can be reused chart-wise at the scheme level
([Ma24, Prop. 3.34]).
-/

suppress_compilation

universe u

open Family

namespace Multicenter

section Monopoly

variable {A : Type (u+1)} [CommRing A] (M : Multicenter A)
variable [Fintype M.index] [DecidableEq M.index]

/-- The product of all distinguished elements except the `i`-th. -/
def coElem (i : M.index) : A := ∏ j ∈ Finset.univ.erase i, M.elem j

/-- The product of all distinguished elements. -/
def prodElem : A := ∏ j, M.elem j

lemma elem_mul_coElem (i : M.index) : M.elem i * M.coElem i = M.prodElem :=
  Finset.mul_prod_erase Finset.univ M.elem (Finset.mem_univ i)

/-- The monopoly multicenter `[∑ᵢ (Mᵢ · ∏_{j≠i} aⱼ), ∏ᵢ aᵢ]` of [Ma24, Prop. 2.36]. -/
def monopoly : Multicenter A where
  index := PUnit
  ideal _ := ⨆ i, M.ideal i * Ideal.span {M.coElem i}
  elem _ := M.prodElem

@[simp] lemma monopoly_ideal (u : PUnit) :
    M.monopoly.ideal u = ⨆ i, M.ideal i * Ideal.span {M.coElem i} := rfl

@[simp] lemma monopoly_elem (u : PUnit) : M.monopoly.elem u = M.prodElem := rfl

section ConditionTransfer

variable {B : Type (u+1)} [CommRing B] [Algebra A B]

/-- `f(∏ aᵢ)` is a non-zero-divisor iff every `f(aᵢ)` is. -/
lemma prodElem_nzd_iff :
    algebraMap A B M.prodElem ∈ nonZeroDivisors B ↔
      ∀ i, algebraMap A B (M.elem i) ∈ nonZeroDivisors B := by
  constructor
  · intro h i
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hprod : x * algebraMap A B M.prodElem = 0 := by
      rw [← M.elem_mul_coElem i, map_mul, ← mul_assoc, hx, zero_mul]
    exact mem_nonZeroDivisors_iff_right.mp h x hprod
  · intro h
    rw [prodElem, map_prod]
    exact Submonoid.prod_mem _ (fun i _ => h i)

lemma coElem_nzd (h : ∀ i, algebraMap A B (M.elem i) ∈ nonZeroDivisors B) (i : M.index) :
    algebraMap A B (M.coElem i) ∈ nonZeroDivisors B := by
  rw [coElem, map_prod]
  exact Submonoid.prod_mem _ (fun j _ => h j)

/-- Under the non-zero-divisor hypothesis, the monopoly containment is equivalent to the
family of mono-centered containments. -/
lemma monopoly_map_le_iff (h : ∀ i, algebraMap A B (M.elem i) ∈ nonZeroDivisors B) :
    Ideal.map (algebraMap A B) (M.monopoly.ideal PUnit.unit) ≤
        Ideal.span {algebraMap A B M.prodElem} ↔
      ∀ i, Ideal.map (algebraMap A B) (M.ideal i) ≤
        Ideal.span {algebraMap A B (M.elem i)} := by
  constructor
  · intro hle i
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    -- f m * f (coElem i) lands in span {f prodElem}
    have hmem : algebraMap A B (m * M.coElem i) ∈
        Ideal.span {algebraMap A B M.prodElem} := by
      refine hle (Ideal.mem_map_of_mem _ ?_)
      rw [monopoly_ideal]
      exact (le_iSup (fun i => M.ideal i * Ideal.span {M.coElem i}) i)
        (Ideal.mul_mem_mul hm (Ideal.mem_span_singleton_self _))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    -- c * f(prodElem) = f m * f (coElem i); cancel f (coElem i)
    have hcancel : (c * algebraMap A B (M.elem i) - algebraMap A B m) *
        algebraMap A B (M.coElem i) = 0 := by
      rw [sub_mul, mul_assoc, ← map_mul, M.elem_mul_coElem i, hc, map_mul, sub_self]
    have hzero := (mul_right_mem_nonZeroDivisors_eq_zero_iff
      (M.coElem_nzd h i)).mp hcancel
    rw [Ideal.mem_comap]
    exact Ideal.mem_span_singleton'.mpr ⟨c, by
      have := sub_eq_zero.mp hzero
      rw [mul_comm] at this
      rw [mul_comm]
      exact this.symm ▸ rfl⟩
  · intro hall
    rw [monopoly_ideal, (Ideal.gc_map_comap (algebraMap A B)).l_iSup]
    refine iSup_le (fun i => ?_)
    rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
    calc Ideal.map (algebraMap A B) (M.ideal i) *
          Ideal.span {algebraMap A B (M.coElem i)}
        ≤ Ideal.span {algebraMap A B (M.elem i)} *
          Ideal.span {algebraMap A B (M.coElem i)} :=
          Ideal.mul_mono_left (hall i)
      _ = Ideal.span {algebraMap A B (M.elem i) * algebraMap A B (M.coElem i)} :=
          Ideal.span_singleton_mul_span_singleton _ _
      _ = Ideal.span {algebraMap A B M.prodElem} := by rw [← map_mul, M.elem_mul_coElem]

end ConditionTransfer

section Equivalence

/-- Every `f(aᵢ)` is a non-zero-divisor in `A[M.monopoly]`. -/
lemma elem_nzd_in_monopolyDil (i : M.index) :
    algebraMap A A[M.monopoly] (M.elem i) ∈ nonZeroDivisors A[M.monopoly] :=
  (M.prodElem_nzd_iff.mp (nonzerodiv_image_single M.monopoly PUnit.unit)) i

/-- The monopoly containment holds in `A[M.monopoly]` (its own defining condition). -/
lemma monopoly_self_le :
    Ideal.map (algebraMap A A[M.monopoly]) (M.monopoly.ideal PUnit.unit) ≤
      Ideal.span {algebraMap A A[M.monopoly] M.prodElem} :=
  (gen_iff_le M.monopoly PUnit.unit).mp
    (reciprocal_for_univ M.monopoly (AlgHom.id A A[M.monopoly]) PUnit.unit)

omit [Fintype M.index] [DecidableEq M.index] in
/-- The mono-centered containments hold in `A[M]` (its own defining conditions). -/
lemma self_le (i : M.index) :
    Ideal.map (algebraMap A A[M]) (M.ideal i) ≤
      Ideal.span {algebraMap A A[M] (M.elem i)} :=
  (gen_iff_le M i).mp (reciprocal_for_univ M (AlgHom.id A A[M]) i)

/-- The canonical map `A[M] →ₐ[A] A[M.monopoly]`. -/
noncomputable def toMonopoly : A[M] →ₐ[A] A[M.monopoly] :=
  desc M (M.elem_nzd_in_monopolyDil)
    (fun i => (gen_iff_le M i).mpr
      ((M.monopoly_map_le_iff M.elem_nzd_in_monopolyDil).mp M.monopoly_self_le i))

/-- Every `f(aᵢ)` — hence `f(∏ aᵢ)` — is a non-zero-divisor in `A[M]`. -/
lemma prodElem_nzd_in_dil :
    algebraMap A A[M] M.prodElem ∈ nonZeroDivisors A[M] :=
  M.prodElem_nzd_iff.mpr (fun i => nonzerodiv_image_single M i)

/-- The canonical map `A[M.monopoly] →ₐ[A] A[M]`. -/
noncomputable def fromMonopoly : A[M.monopoly] →ₐ[A] A[M] :=
  desc M.monopoly (fun _ => M.prodElem_nzd_in_dil)
    (fun _ => (gen_iff_le M.monopoly _).mpr
      ((M.monopoly_map_le_iff (fun i => nonzerodiv_image_single M i)).mpr M.self_le))

lemma fromMonopoly_comp_toMonopoly :
    (M.fromMonopoly.comp M.toMonopoly) = AlgHom.id A A[M] :=
  lemma_exists_unique_morphism' M (fun i => nonzerodiv_image_single M i)
    (fun i => reciprocal_for_univ M (AlgHom.id A A[M]) i) _ _

lemma toMonopoly_comp_fromMonopoly :
    (M.toMonopoly.comp M.fromMonopoly) = AlgHom.id A A[M.monopoly] :=
  lemma_exists_unique_morphism' M.monopoly
    (fun _ => nonzerodiv_image_single M.monopoly PUnit.unit)
    (fun u => reciprocal_for_univ M.monopoly (AlgHom.id A A[M.monopoly]) u) _ _

/-- **[Ma24, Prop. 2.36], the monopoly isomorphism for rings**: for a finite
multicenter, `A[{Mᵢ/aᵢ}ᵢ] ≃ₐ[A] A[(∑ᵢ Mᵢ·∏_{j≠i}aⱼ) / ∏ᵢ aᵢ]`. -/
noncomputable def monopolyEquiv : A[M] ≃ₐ[A] A[M.monopoly] :=
  AlgEquiv.ofAlgHom M.toMonopoly M.fromMonopoly
    M.toMonopoly_comp_fromMonopoly M.fromMonopoly_comp_toMonopoly

/-- The monopoly isomorphism is the unique `A`-algebra map — [Ma24, Prop. 2.36]'s
"unique isomorphism". -/
lemma monopolyEquiv_unique (χ : A[M] →ₐ[A] A[M.monopoly]) :
    χ = (M.monopolyEquiv : A[M] →ₐ[A] A[M.monopoly]) :=
  lemma_exists_unique_morphism' M M.elem_nzd_in_monopolyDil
    (fun i => reciprocal_for_univ M M.toMonopoly i) _ _

end Equivalence

end Monopoly

end Multicenter
