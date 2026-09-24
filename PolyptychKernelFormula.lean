import PolyptychExpand

suppress_compilation

universe u

open Family Multicenter Dilatation

namespace Multicenter

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A)

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

abbrev Idx (J : Finset I) : Type := {j // j ∈ J}

variable (M : I → Ideal A) (d : I → A)

def mprod {J : Finset I} (α : Idx J →₀ ℕ) : Ideal A :=
  α.prod fun j k => M j.1 ^ k

def dprod {J : Finset I} (β : Idx J →₀ ℕ) : A :=
  β.prod fun j k => d j.1 ^ k

@[simp] lemma mprod_zero {J : Finset I} : mprod M (0 : Idx J →₀ ℕ) = ⊤ := by
  simp only [mprod, Finsupp.prod_zero_index, Ideal.one_eq_top]

@[simp] lemma dprod_zero {J : Finset I} : dprod d (0 : Idx J →₀ ℕ) = 1 := by
  simp only [dprod, Finsupp.prod_zero_index]

lemma dprod_add {J : Finset I} (β β' : Idx J →₀ ℕ) :
    dprod d (β + β') = dprod d β * dprod d β' := by
  classical
  simp only [dprod]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

def CondR1 (J : Finset I) (i : I) : Prop :=
  ∀ (j₀ : Idx J) (α : Idx J →₀ ℕ), i < j₀.1 → α j₀ ≠ 0 →
    (∀ j ∈ α.support, i < j.1 ∧ j₀ ≤ j) →
    mprod M α ⊓ M i = mprod M (α.erase j₀) * M j₀.1 ^ (α j₀ - 1) * M i

lemma mprod_eq_mprod_erase_mul_pow {J : Finset I} (α : Idx J →₀ ℕ) (j₀ : Idx J) :
    mprod M α = mprod M (α.erase j₀) * M j₀.1 ^ (α j₀) := by
  classical
  simp only [mprod]
  rw [← Finsupp.mul_prod_erase' α j₀ (fun j k => M j.1 ^ k) (fun _ => pow_zero _), mul_comm]

theorem CondR1.peeled {J : Finset I} {i : I} (h : CondR1 M J i)
    (j₀ : Idx J) (α : Idx J →₀ ℕ)
    (hi : i < j₀.1) (hα : ∀ j ∈ α.support, i < j.1 ∧ j₀ ≤ j) :
    mprod M (Finsupp.single j₀ 1 + α) ⊓ M i = mprod M α * M i := by
  classical
  set β : Idx J →₀ ℕ := Finsupp.single j₀ 1 + α with hβdef
  have hβj₀ : β j₀ = α j₀ + 1 := by
    rw [hβdef, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  have hne : β j₀ ≠ 0 := by rw [hβj₀]; omega
  have hother : ∀ j, j ≠ j₀ → β j = α j := by
    intro j hj
    rw [hβdef, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hj), zero_add]
  have hsupp : ∀ j ∈ β.support, i < j.1 ∧ j₀ ≤ j := by
    intro j hjm
    by_cases hj : j = j₀
    · subst hj; exact ⟨hi, le_rfl⟩
    · refine hα j ?_
      rw [Finsupp.mem_support_iff] at hjm ⊢
      rwa [hother j hj] at hjm
  have herase : β.erase j₀ = α.erase j₀ := by
    ext j
    by_cases hj : j = j₀
    · subst hj; simp
    · rw [Finsupp.erase_ne hj, Finsupp.erase_ne hj, hother j hj]
  have hkey := h j₀ β hi hne hsupp
  rw [herase, hβj₀, Nat.add_sub_cancel,
    ← mprod_eq_mprod_erase_mul_pow M α j₀] at hkey
  exact hkey

def CondR2 (J : Finset I) (i : I) : Prop :=
  (J.filter (fun s => i ≤ s)).Nonempty →
  ∀ (E : Type) (α β : E → (Idx J →₀ ℕ)),
    (∀ e, ∀ j ∈ (α e).support, i < j.1) →
    (⨆ e, mprod M (α e) * Ideal.span {dprod d (β e)}) ⊓ M i =
      ⨆ e, (mprod M (α e) ⊓ M i) * Ideal.span {dprod d (β e)}

section Aux

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

lemma frac_single_mem_panelSubIdeal (J : Finset I) (i : I)
    (j : (restCenter M d J).index) (m : A)
    (hmj : m ∈ M j.1) (hmi : m ∈ M i)
    (h : m ∈ ((restCenter M d J).LargeIdeal ^ (Finsupp.single j 1) : Ideal A)) :
    Dilatation.frac (F := restCenter M d J) (Finsupp.single j 1) ⟨m, h⟩ ∈
      panelSubIdeal M d J i :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem j
    (Ideal.subset_span ⟨m, hmj, hmi, rfl⟩))

lemma algebraMap_mem_panelSubIdeal (J : Finset I) (i : I) {m : A} (hm : m ∈ M i) :
    algebraMap A (Ring M d J) m ∈ panelSubIdeal M d J i :=
  Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hm)

end Aux

def Mono (M : I → Ideal A) : Prop := ∀ ⦃a b : I⦄, a ≤ b → M a ≤ M b

section Main

variable {M d}

theorem kerFracIdeal_le_panelSubIdeal (J : Finset I) (i : I) (hCi : CartierAt M d J i)
    (hM : Mono M) (hiJ : i ∉ J)
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
      ·
        obtain ⟨j, hjs, hji⟩ := hlow
        obtain ⟨ν', rfl, -⟩ :=
          exists_single_one_add ν j (Finsupp.mem_support_iff.mp hjs)
        have hdeg : finsuppDeg ν' < n := by
          rw [← hn, finsuppDeg_single_add]; omega
        have IH := ih _ hdeg ν' rfl
        have hMji : M j.1 ≤ M i := hM (le_of_lt hji)
        have hpart1 : F.ideal j * F.LargeIdeal ^ ν' ≤
            F.fracPullback (Finsupp.single j 1 + ν') P := by
          refine Ideal.mul_le.2 fun m hm y hy => ?_
          have hmL : m ∈ F.LargeIdeal ^ (Finsupp.single j 1 : F.index →₀ ℕ) :=
            F.mem_largeIdealPow_single j hm
          refine ⟨Ideal.mem_familyPow_add hmL hy, ?_⟩
          rw [F.frac_mul _ _ m y hmL hy]
          exact Ideal.mul_mem_right _ _
            (frac_single_mem_panelSubIdeal M d J i j m hm (hMji hm) hmL)
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
                (elemOf_quot_nzd hCi j)).mp h0)
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
      ·
        push_neg at hlow
        have hsupp : ∀ j ∈ ν.support, i < j.1 := by
          intro j hj
          rcases lt_trichotomy i j.1 with h | h | h
          · exact h
          · exact absurd (h ▸ j.2) hiJ
          · exact absurd (hlow j hj) (not_le.mpr h)
        rcases eq_or_ne ν 0 with rfl | hν0
        ·
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
        ·
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
        ·
          have hne : α.support.Nonempty := Finsupp.support_nonempty_iff.mpr hα
          set j₀ := α.support.min' hne with hj₀def
          have hj₀mem : j₀ ∈ α.support := Finset.min'_mem _ _
          have hj₀i : i < j₀.1 := hsα j₀ hj₀mem
          obtain ⟨α', hα'eq, hα'sub⟩ :=
            exists_single_one_add α j₀ (Finsupp.mem_support_iff.mp hj₀mem)
          have hα'cond : ∀ j ∈ α'.support, i < j.1 ∧ j₀ ≤ j := fun j hj =>
            ⟨hsα j (hα'sub hj), Finset.min'_le _ _ (hα'sub hj)⟩
          have hrw : mprod M α ⊓ M i = mprod M α' * M i := by
            rw [hα'eq]; exact CondR1.peeled M hR1 j₀ α' hj₀i hα'cond
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

theorem ker_panelHom_eq (J : Finset I) (i : I) (hCi : CartierAt M d J i)
    (hM : Mono M) (hiJ : i ∉ J)
    (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    RingHom.ker (panelHom M d J i) = panelSubIdeal M d J i := by
  rw [ker_panelHom M d hCi]
  exact le_antisymm (kerFracIdeal_le_panelSubIdeal J i hCi hM hiJ hR1 hR2)
    (by rw [← ker_panelHom M d hCi]; exact panelSubIdeal_le_ker_at M d hCi)

end Main

end Polyptych
