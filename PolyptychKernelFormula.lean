import PolyptychExpand

/-!
# The kernel formula (`prop:Kernel-formula`)

This file proves the ring-level Proposition `prop:Kernel-formula` of Dubouloz-Mayeux,
*A polyptych of multi-centered deformation spaces* (arXiv:2411.15606): under Assumption 3.1
together with the two conditions `(R₁)` and `(R₂)` of Definition `assutheopan3`, the
inclusion of `lem:KerfJi-inclusion` is an equality,

`ker (F_J(i)^*) = (M i / ∏_{s ∈ J≥i} d s) + Σ_{j ∈ J} (M j ∩ M i) / ∏_{s ∈ J≥j} d s`.

The proof follows the paper.  A fraction `ℓ / a^ν` in the kernel has `ℓ ∈ L^ν ∩ M i`
(`Multicenter.ker_quotHom`).  Induction on the total degree of `ν` peels off the indices
`j ∈ J` with `j < i`: for such a `j` the ideal `M j` is contained in `M i`, so the
`M j`-part of the expansion lands in the target ideal outright, while the `d`-part can be
cancelled because `∏_{s ∈ J≥j} d s` is a non-zero-divisor modulo `M i` (Assumption 3.1).
This reduces to multi-indices `ν` supported in `J > i`, where the expansion
`L^ν = Σ_{α+β=ν} (∏ M_j^{α_j}) (a^β)` together with `(R₂)` distributes the intersection
with `M i` over the sum, and `(R₁)` rewrites each term `(∏ M_j^{α_j}) ∩ M i` as
`(∏_{j > j₀} M_j^{α_j}) M_{j₀}^{α_{j₀}-1} M i`, whose fractions visibly lie in the
`j₀`-th generator `(M_{j₀} ∩ M i)/∏_{s ∈ J≥j₀} d s`.
-/

suppress_compilation

universe u

open Family Multicenter Dilatation

namespace Multicenter

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A)

/-- `∏ Mⱼ^{αⱼ} ≤ ∏ Lⱼ^{αⱼ}`. -/
lemma idealPow_le_largeIdealPow (α : F.index →₀ ℕ) :
    F.ideal ^ α ≤ F.LargeIdeal ^ α := by
  classical
  induction hn : finsuppDeg α using Nat.strong_induction_on generalizing α with
  | _ n ih =>
    subst hn
    rcases eq_or_ne α 0 with rfl | hα
    · simp only [familyPow_zero]
      exact le_rfl
    · obtain ⟨j, α', rfl⟩ := exists_single_add_of_ne_zero α hα
      rw [familyPow_add, familyPow_add, familyPow_single, familyPow_single]
      have h1 : F.ideal j ≤ F.LargeIdeal j := by
        rw [LargeIdeal, Submodule.add_eq_sup]; exact le_sup_left
      exact Ideal.mul_mono h1
        (ih _ (by rw [finsuppDeg_single_add]; omega) α' rfl)

end Multicenter

namespace Polyptych

variable {A : Type (u+1)} [CommRing A] {I : Type} [LinearOrder I] [Fintype I]

/-- The index type of `restCenter M d J`. -/
abbrev Idx (J : Finset I) : Type := {j // j ∈ J}

variable (M : I → Ideal A) (d : I → A)

/-- `∏_{j} (M j)^{α j}`. -/
def mprod {J : Finset I} (α : Idx J →₀ ℕ) : Ideal A := α.prod fun j k => M j.1 ^ k

/-- `∏_{j} (d j)^{β j}`. -/
def dprod {J : Finset I} (β : Idx J →₀ ℕ) : A := β.prod fun j k => d j.1 ^ k

@[simp] lemma mprod_zero {J : Finset I} : mprod M (0 : Idx J →₀ ℕ) = ⊤ := by
  simp only [mprod, Finsupp.prod_zero_index, Ideal.one_eq_top]

@[simp] lemma dprod_zero {J : Finset I} : dprod d (0 : Idx J →₀ ℕ) = 1 := by
  simp only [dprod, Finsupp.prod_zero_index]

lemma dprod_add {J : Finset I} (β β' : Idx J →₀ ℕ) :
    dprod d (β + β') = dprod d β * dprod d β' := by
  classical
  simp only [dprod]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

/-- **Condition `(R₁)`** of Definition `assutheopan3`: for a nonzero multi-index supported
in `J > i` with least element `j₀`,
`(∏_j M_j^{α_j}) ∩ M i = (∏_{j > j₀} M_j^{α_j}) M_{j₀}^{α_{j₀}-1} M i`. -/
def CondR1 (J : Finset I) (i : I) : Prop :=
  ∀ (j₀ : Idx J) (α : Idx J →₀ ℕ), i < j₀.1 →
    (∀ j ∈ α.support, i < j.1 ∧ j₀ ≤ j) →
    mprod M (Finsupp.single j₀ 1 + α) ⊓ M i = mprod M α * M i

/-- **Condition `(R₂)`** of Definition `assutheopan3`: when `J≥i` is nonempty,
intersecting with `M i` distributes over sums of ideals `(∏_j M_j^{α_j})(∏_j d_j^{β_j})`
with the `α`'s supported in `J > i`.  (As in the paper, the condition is only imposed when
`J≥i ≠ ∅`; note that `(R₁)` is vacuous in that case, since it quantifies over `j₀ ∈ J`
with `i < j₀`.) -/
def CondR2 (J : Finset I) (i : I) : Prop :=
  (J.filter (fun s => i ≤ s)).Nonempty →
  ∀ (E : Type) (α β : E → (Idx J →₀ ℕ)),
    (∀ e, ∀ j ∈ (α e).support, i < j.1) →
    (⨆ e, mprod M (α e) * Ideal.span {dprod d (β e)}) ⊓ M i =
      ⨆ e, (mprod M (α e) ⊓ M i) * Ideal.span {dprod d (β e)}

section Aux

/-- Splitting off a chosen index of a multi-index. -/
lemma exists_single_one_add {ι : Type*} [DecidableEq ι] (ν : ι →₀ ℕ) (j : ι)
    (h : ν j ≠ 0) : ∃ ν' : ι →₀ ℕ, ν = Finsupp.single j 1 + ν' ∧ ν'.support ⊆ ν.support := by
  refine ⟨Finsupp.single j (ν j - 1) + ν.erase j, ?_, ?_⟩
  · rw [← add_assoc, ← Finsupp.single_add, show 1 + (ν j - 1) = ν j from by omega]
    exact (Finsupp.single_add_erase j ν).symm
  · intro a ha
    rcases Finset.mem_union.mp (Finsupp.support_add ha) with h1 | h1
    · have : a = j := by simpa using Finsupp.support_single_subset h1
      subst this
      exact Finsupp.mem_support_iff.mpr h
    · rw [Finsupp.support_erase] at h1
      exact Finset.mem_of_mem_erase h1

/-- Every family power of the distinguished elements of `restCenter M d J` is a product of
powers of the `d j`, `j ∈ J`. -/
lemma elemPow_eq_dprod (J : Finset I) (β : (restCenter M d J).index →₀ ℕ) :
    ∃ γ : Idx J →₀ ℕ, (restCenter M d J).elem ^ β = dprod d γ := by
  classical
  set S : Submonoid A :=
    { carrier := {x : A | ∃ γ : Idx J →₀ ℕ, x = dprod d γ}
      one_mem' := ⟨0, (dprod_zero d).symm⟩
      mul_mem' := by
        rintro x y ⟨γ, rfl⟩ ⟨γ', rfl⟩
        exact ⟨γ + γ', (dprod_add d γ γ').symm⟩ } with hS
  have hd : ∀ j : Idx J, d j.1 ∈ S := by
    intro j
    refine ⟨Finsupp.single j 1, ?_⟩
    simp only [dprod]
    rw [Finsupp.prod_single_index (by simp), pow_one]
  have helem : ∀ j : Idx J, (restCenter M d J).elem j ∈ S := by
    intro j
    show (∏ s ∈ J.filter (fun s => j.1 ≤ s), d s) ∈ S
    exact prod_mem fun s hs => hd ⟨s, (Finset.mem_filter.mp hs).1⟩
  have hmem : (restCenter M d J).elem ^ β ∈ S := by
    rw [familyPow_def]
    exact prod_mem fun j _ => pow_mem (helem j) _
  exact hmem

/-- A generator of the second summand of `panelSubIdeal`. -/
lemma frac_single_mem_panelSubIdeal (J : Finset I) (i : I)
    (j : (restCenter M d J).index) (m : A)
    (hmj : m ∈ M j.1) (hmi : m ∈ M i)
    (h : m ∈ ((restCenter M d J).LargeIdeal ^ (Finsupp.single j 1) : Ideal A)) :
    Dilatation.frac (F := restCenter M d J) (Finsupp.single j 1) ⟨m, h⟩ ∈
      panelSubIdeal M d J i :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem j
    (Ideal.subset_span ⟨m, hmj, hmi, rfl⟩))

/-- The image of `M i` lies in `panelSubIdeal`. -/
lemma algebraMap_mem_panelSubIdeal (J : Finset I) (i : I) {m : A} (hm : m ∈ M i) :
    algebraMap A (Ring M d J) m ∈ panelSubIdeal M d J i :=
  Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hm)

end Aux

/-- The centers of a deformation datum are monotone: `M a ≤ M b` for `a ≤ b`, i.e. the
closed subschemes `X i` decrease as `i` grows. -/
def Mono (M : I → Ideal A) : Prop := ∀ ⦃a b : I⦄, a ≤ b → M a ≤ M b

section Main

variable {M d}

/-- **Proposition `prop:Kernel-formula`**, hard inclusion: under Assumption 3.1 and the
conditions `(R₁)`, `(R₂)`, every fraction with numerator in `M i` lies in
`panelSubIdeal`. -/
theorem kerFracIdeal_le_panelSubIdeal (hC : Cartier M d) (hM : Mono M)
    (J : Finset I) (i : I) (hiJ : i ∉ J)
    (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    (restCenter M d J).kerFracIdeal (M i) ≤ panelSubIdeal M d J i := by
  classical
  set F := restCenter M d J with hF
  letI : LinearOrder F.index := inferInstanceAs (LinearOrder {j : I // j ∈ J})
  set P := panelSubIdeal M d J i with hP
  have key : ∀ (n : ℕ) (ν : F.index →₀ ℕ), finsuppDeg ν = n →
      F.LargeIdeal ^ ν ⊓ M i ≤ F.fracPullback ν P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro ν hn
      by_cases hlow : ∃ j ∈ ν.support, j.1 < i
      · -- Case 1: some index of `J` below `i` occurs in `ν`
        obtain ⟨j, hjs, hji⟩ := hlow
        obtain ⟨ν', rfl, -⟩ :=
          exists_single_one_add ν j (Finsupp.mem_support_iff.mp hjs)
        have hdeg : finsuppDeg ν' < n := by
          rw [← hn, finsuppDeg_single_add]; omega
        have IH := ih _ hdeg ν' rfl
        have hMji : M j.1 ≤ M i := hM (le_of_lt hji)
        -- the `M j`-part
        have hpart1 : F.ideal j * F.LargeIdeal ^ ν' ≤
            F.fracPullback (Finsupp.single j 1 + ν') P := by
          refine Ideal.mul_le.2 fun m hm y hy => ?_
          have hmL : m ∈ F.LargeIdeal ^ (Finsupp.single j 1 : F.index →₀ ℕ) :=
            F.mem_largeIdealPow_single j hm
          refine ⟨Ideal.mem_familyPow_add hmL hy, ?_⟩
          rw [F.frac_mul _ _ m y hmL hy]
          exact Ideal.mul_mem_right _ _
            (frac_single_mem_panelSubIdeal M d J i j m hm (hMji hm) hmL)
        -- the divisor part
        have hone : ∀ (helem : F.elem j ∈
            F.LargeIdeal ^ (Finsupp.single j 1 : F.index →₀ ℕ)),
            Dilatation.frac (F := F) (Finsupp.single j 1 : F.index →₀ ℕ)
              ⟨F.elem j, helem⟩ = 1 := by
          intro helem
          have h1 : (1 : A) * F.elem ^ (Finsupp.single j 1 : F.index →₀ ℕ) ∈
              (F.LargeIdeal ^ (Finsupp.single j 1 : F.index →₀ ℕ) : Ideal A) := by
            simp only [one_mul, familyPow_single]
            exact F.elem_mem_LargeIdeal j
          have h2 := F.frac_pow_mul (Finsupp.single j 1) 1 h1
          rw [map_one] at h2
          refine Eq.trans ?_ h2
          congr 1
          exact Subtype.ext (show F.elem j =
            1 * F.elem ^ (Finsupp.single j 1 : F.index →₀ ℕ) from by
              rw [one_mul, familyPow_single])
        have hpart2 : ∀ q : A, q ∈ F.LargeIdeal ^ ν' → F.elem j * q ∈ M i →
            F.elem j * q ∈ F.fracPullback (Finsupp.single j 1 + ν') P := by
          intro q hq hmem
          have hqi : q ∈ M i := by
            have h0 : Ideal.Quotient.mk (M i) (F.elem j) *
                Ideal.Quotient.mk (M i) q = 0 := by
              rw [← map_mul]
              exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
            exact Ideal.Quotient.eq_zero_iff_mem.mp
              ((mul_left_mem_nonZeroDivisors_eq_zero_iff
                (elemOf_quot_nzd hC J i j)).mp h0)
          obtain ⟨hq', hqP'⟩ := IH ⟨hq, hqi⟩
          have helem : F.elem j ∈
              F.LargeIdeal ^ (Finsupp.single j 1 : F.index →₀ ℕ) := by
            rw [familyPow_single]
            exact F.elem_mem_LargeIdeal j
          refine ⟨Ideal.mem_familyPow_add helem hq, ?_⟩
          rw [F.frac_mul _ _ _ q helem hq, hone helem, one_mul]
          exact hqP'
        rintro ℓ ⟨hℓ, hℓi⟩
        rw [familyPow_add, familyPow_single] at hℓ
        have hsup : F.LargeIdeal j * F.LargeIdeal ^ ν' =
            F.ideal j * F.LargeIdeal ^ ν' ⊔ Ideal.span {F.elem j} * F.LargeIdeal ^ ν' := by
          show (F.ideal j + Ideal.span {F.elem j}) * F.LargeIdeal ^ ν' = _
          rw [add_mul, Submodule.add_eq_sup]
        obtain ⟨p, hp, t, ht, hpt⟩ := Submodule.mem_sup.mp (hsup ▸ hℓ)
        have hpP : p ∈ F.fracPullback (Finsupp.single j 1 + ν') P := hpart1 hp
        have hpMi : p ∈ M i := hMji (Ideal.mul_le_right hp)
        obtain ⟨q, hq, rfl⟩ := Multicenter.mem_span_singleton_mul_iff.mp ht
        have htMi : F.elem j * q ∈ M i := by
          rw [show F.elem j * q = ℓ - p from by rw [← hpt]; ring]
          exact Ideal.sub_mem _ hℓi hpMi
        rw [← hpt]
        exact Ideal.add_mem _ hpP (hpart2 q hq htMi)
      · -- Case 2: the support of `ν` lies in `J > i`
        push_neg at hlow
        have hsupp : ∀ j ∈ ν.support, i < j.1 := by
          intro j hj
          rcases lt_trichotomy i j.1 with h | h | h
          · exact h
          · exact absurd (h ▸ j.2) hiJ
          · exact absurd (hlow j hj) (not_le.mpr h)
        rcases eq_or_ne ν 0 with rfl | hν0
        · -- `ν = 0`: the fraction is just the image of its numerator
          rintro ℓ ⟨-, hℓi⟩
          have h0 : ℓ ∈ (F.LargeIdeal ^ (0 : F.index →₀ ℕ) : Ideal A) := by simp
          refine ⟨h0, ?_⟩
          rw [F.frac_zero_eq_algebraMap ℓ h0]
          exact algebraMap_mem_panelSubIdeal M d J i hℓi
        have hguard : (J.filter (fun s => i ≤ s)).Nonempty := by
          obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hν0
          exact ⟨j.1, Finset.mem_filter.mpr ⟨j.2, le_of_lt (hsupp j hj)⟩⟩
        set E := {p : (F.index →₀ ℕ) × (F.index →₀ ℕ) // p.1 + p.2 = ν} with hE
        have hγ : ∀ e : E, ∃ γ : F.index →₀ ℕ, F.elem ^ e.1.2 = dprod d γ :=
          fun e => elemPow_eq_dprod M d J e.1.2
        choose γ hγspec using hγ
        have hsuppα : ∀ (e : E), ∀ j ∈ (e.1.1).support, i < j.1 := by
          intro e j hj
          refine hsupp j (Finsupp.mem_support_iff.mpr ?_)
          have hν : e.1.1 j + e.1.2 j = ν j := by
            have h : (e.1.1 + e.1.2) j = ν j := by rw [e.2]
            simpa using h
          have := Finsupp.mem_support_iff.mp hj
          omega
        have hexp : F.LargeIdeal ^ ν ≤
            ⨆ e : E, mprod M (e.1.1) * Ideal.span {dprod d (γ e)} := by
          refine le_trans (F.largeIdealPow_le_span_expSet ν) ?_
          rw [Ideal.span_le]
          rintro x ⟨α, β, a, hαβ, ha, rfl⟩
          refine Submodule.mem_iSup_of_mem (⟨(α, β), hαβ⟩ : E) ?_
          rw [hγspec ⟨(α, β), hαβ⟩]
          exact Ideal.mul_mem_mul ha (Ideal.mem_span_singleton_self _)
        have hR2' := hR2 hguard E (fun e => e.1.1) γ hsuppα
        refine le_trans (le_trans (inf_le_inf_right (M i) hexp) (le_of_eq hR2')) ?_
        refine iSup_le fun e => ?_
        obtain ⟨⟨α, β⟩, hαβ⟩ := e
        have hsα : ∀ j ∈ α.support, i < j.1 := hsuppα ⟨(α, β), hαβ⟩
        have hg : F.elem ^ β = dprod d (γ ⟨(α, β), hαβ⟩) := hγspec ⟨(α, β), hαβ⟩
        show (mprod M α ⊓ M i) * Ideal.span {dprod d (γ ⟨(α, β), hαβ⟩)} ≤
          F.fracPullback ν P
        rw [← hg, ← hαβ]
        by_cases hα : α = 0
        · -- the purely divisorial term
          rw [hα, mprod_zero, top_inf_eq, zero_add]
          refine Ideal.mul_le.2 fun m hm s hs => ?_
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
          have hpow : F.elem ^ β ∈ F.LargeIdeal ^ β :=
            Ideal.mem_familyPow_of_mem (fun k _ => F.elem_mem_LargeIdeal k)
          have hmem : m * F.elem ^ β ∈ F.LargeIdeal ^ β :=
            Ideal.mul_mem_left _ _ hpow
          have hbase : m * F.elem ^ β ∈ F.fracPullback β P := by
            refine ⟨hmem, ?_⟩
            rw [F.frac_pow_mul β m hmem]
            exact algebraMap_mem_panelSubIdeal M d J i hm
          rw [show m * (c * F.elem ^ β) = c * (m * F.elem ^ β) from by ring]
          exact Ideal.mul_mem_left _ _ hbase
        · -- a term with a nonzero `M`-part: apply `(R₁)`
          have hne : α.support.Nonempty := Finsupp.support_nonempty_iff.mpr hα
          set j₀ := α.support.min' hne with hj₀def
          have hj₀mem : j₀ ∈ α.support := Finset.min'_mem _ _
          have hj₀i : i < j₀.1 := hsα j₀ hj₀mem
          obtain ⟨α', hα'eq, hα'sub⟩ :=
            exists_single_one_add α j₀ (Finsupp.mem_support_iff.mp hj₀mem)
          have hα'cond : ∀ j ∈ α'.support, i < j.1 ∧ j₀ ≤ j := fun j hj =>
            ⟨hsα j (hα'sub hj), Finset.min'_le _ _ (hα'sub hj)⟩
          have hrw : mprod M α ⊓ M i = mprod M α' * M i := by
            rw [hα'eq]; exact hR1 j₀ α' hj₀i hα'cond
          rw [hrw, hα'eq]
          refine Ideal.mul_le.2 fun x hx s hs => ?_
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
          suffices hsuf : x * F.elem ^ β ∈
              F.fracPullback (Finsupp.single j₀ 1 + α' + β) P by
            rw [show x * (c * F.elem ^ β) = c * (x * F.elem ^ β) from by ring]
            exact Ideal.mul_mem_left _ _ hsuf
          refine Submodule.mul_induction_on hx ?_ ?_
          · intro a ha m hm
            have hmMj : m ∈ M j₀.1 := hM (le_of_lt hj₀i) hm
            have hmL : m ∈ (F.LargeIdeal ^
                (Finsupp.single j₀ 1 : F.index →₀ ℕ) : Ideal A) :=
              F.mem_largeIdealPow_single j₀ hmMj
            have haL : a ∈ F.LargeIdeal ^ α' :=
              F.idealPow_le_largeIdealPow α' ha
            have hbL : F.elem ^ β ∈ F.LargeIdeal ^ β :=
              Ideal.mem_familyPow_of_mem (fun k _ => F.elem_mem_LargeIdeal k)
            have hyL : a * F.elem ^ β ∈ F.LargeIdeal ^ (α' + β) :=
              Ideal.mem_familyPow_add haL hbL
            rw [show a * m * F.elem ^ β = m * (a * F.elem ^ β) from by ring,
              add_assoc]
            refine ⟨Ideal.mem_familyPow_add hmL hyL, ?_⟩
            rw [F.frac_mul _ _ m _ hmL hyL]
            exact Ideal.mul_mem_right _ _
              (frac_single_mem_panelSubIdeal M d J i j₀ m hmMj hm hmL)
          · intro x y hx' hy'
            rw [add_mul]
            exact Ideal.add_mem _ hx' hy'
  rw [Multicenter.kerFracIdeal, Ideal.span_le]
  rintro x ⟨ν, m, hm, hmT, rfl⟩
  exact F.frac_mem_of_mem_fracPullback hm
    (key (finsuppDeg ν) ν rfl ⟨hm, hmT⟩)

/-- **Proposition `prop:Kernel-formula`**: under Assumption 3.1 and `(R₁)`, `(R₂)`, the
inclusion `lem:KerfJi-inclusion` is an equality. -/
theorem ker_panelHom_eq (hC : Cartier M d) (hM : Mono M)
    (J : Finset I) (i : I) (hiJ : i ∉ J)
    (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    RingHom.ker (panelHom M d hC J i) = panelSubIdeal M d J i := by
  rw [ker_panelHom M d hC J i]
  exact le_antisymm (kerFracIdeal_le_panelSubIdeal hC hM J i hiJ hR1 hR2)
    (by rw [← ker_panelHom M d hC J i]; exact panelSubIdeal_le_ker M d hC J i)

end Main

end Polyptych
