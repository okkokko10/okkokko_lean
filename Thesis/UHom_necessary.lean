import Mathlib



variable {α β γ : Type*} (f : α → β)


#check ZeroHom -- name inspired

class UHom (f : α → β) where
  prf b₁ b₂ : {x₁ // f x₁ = b₁} ≃ {x₂ // f x₂ = b₂}
-- [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

@[simp]
theorem UHom.main
  [f_upr : UHom f]
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  : PMF.map f (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
    ext x
    open scoped Classical in

    simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
    -- simp_rw [←Set.indicator_apply]
    set b := (↑(Fintype.card β) : ENNReal)
    set a := (↑(Fintype.card α) : ENNReal)
    have a_pos : a ≠ 0 := by simp [a]
    have b_pos : b ≠ 0 := by simp [b]
    have a_fin : a ≠ ⊤ := by simp [a]
    have b_fin : b ≠ ⊤ := by simp [b]
    rw [←ENNReal.mul_left_inj a_pos a_fin]
    rw [←ENNReal.mul_left_inj b_pos b_fin]
    simp only [← ENNReal.tsum_mul_right, ite_mul, zero_mul]
    ring_nf
    rw [ENNReal.inv_mul_cancel (by assumption) (by assumption)]
    rw [ENNReal.mul_inv_cancel_right (by assumption) (by assumption)]
    simp only [one_mul]
    rw [tsum_eq_sum' (s := Finset.univ) (by norm_num)]
    suffices (∑ i, if x = f i then (Fintype.card β) else 0) = (Fintype.card α) by
      unfold a b
      rw [←this]
      simp only [Nat.cast_sum, Nat.cast_ite, CharP.cast_eq_zero]
    -- change (∑ i ∈ Finset.univ, if i ∈ {i | f i = x} then Fintype.card β else 0) = Fintype.card α
    have := Finset.sum_ite_mem Finset.univ {i | x = f i} (fun _ ↦ Fintype.card β)
    convert this
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.univ_inter, Finset.sum_const, smul_eq_mul]
    simp_rw [Eq.comm (a := x)]
    rw [←Fintype.card_subtype]
    rw [←Fintype.card_prod]
    apply Fintype.card_congr
    calc
      _ ≃ (y : β) × { i // f i = y } := by
        exact (Equiv.sigmaFiberEquiv f).symm
      _ ≃ (y : β) × { i // f i = x } := by
        refine Equiv.sigmaCongr (Equiv.refl _) ?_
        intro b
        exact (UHom.prf b x)
      _ ≃ (β) × { i // f i = x } := by
        exact Equiv.sigmaEquivProd β { i // f i = x }
      _ ≃ { i // f i = x } × β := by exact Equiv.prodComm β { i // f i = x }





lemma PMF'.subadditivity {α ι : Type*} (p : PMF α) (s : ι → (α → Prop)) :
  (p.map (fun a ↦ ∃i, s i a)) True ≤ ∑' (i : ι), (p.map (s i)) True := by
  open scoped Classical in
  simp only [PMF.map_apply, eq_iff_iff, true_iff]
  rw [ENNReal.tsum_comm]
  gcongr 1 with r
  by_cases h : ∃i, s i r
  ·
    simp only [h, ↓reduceIte]
    obtain ⟨i,v_s⟩ := h
    apply le_trans ?_ (ENNReal.le_tsum i)
    simp only [v_s, ↓reduceIte, le_refl]
  simp only [h, ↓reduceIte, zero_le]



lemma PMF'.mem_uniform_card
  {α : Type*} [Fintype α] [Nonempty α]
  (Z : Finset α)
  : (PMF.map (fun x ↦ x ∈ Z) (PMF.uniformOfFintype α)) True = Z.card / (Fintype.card (α)) := by
    open scoped Classical in
    simp only [PMF.map_apply, eq_iff_iff, true_iff, PMF.uniformOfFintype_apply]
    rw [←Finset.toFinset_coe Z]
    simp_rw [Set.mem_toFinset]
    simp_rw [←Set.indicator_apply (↑Z : Set α) (fun _ ↦ (↑(Fintype.card α) : ENNReal)⁻¹)]
    rw [←tsum_subtype]
    simp only [SetLike.coe_sort_coe, ENNReal.tsum_const, ENat.card_eq_coe_fintype_card,
      Fintype.card_coe, ENat.toENNReal_coe, Finset.toFinset_coe]
    rfl

variable {M α β : Type}
  [AddGroup M]
  [AddGroup α]
  [AddCommGroup β] -- Gemini: this must be commutative, otherwise α →+ β won't necessarily form a monoid
  [Fintype M] [Nonempty M]
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]




variable (φ : M → α →+ β)
variable (ψ : α → M →+ β)
open scoped Classical in

theorem lemma_5_3_key
  (hφ : ∀x y, φ x y = ψ y x )
  (ψ_surj : ∀s ≠ 0, Function.Surjective (ψ s))
  (Z : Finset β)
  (hZ : 0 ∉ Z)
  : (PMF.uniformOfFintype M).map (fun A ↦ ∃v, v ∈ (φ A).range ∧ v ∈ Z) (True)
    ≤ Fintype.card α * Z.card / Fintype.card β
  := by
  conv_lhs => {
    simp only [AddMonoidHom.mem_range, exists_exists_eq_and]
    simp only [bind_pure_comp]
    change (PMF.uniformOfFintype M |>.map (fun m ↦ ∃ a, (φ m) a ∈ Z)) True
  }
  conv_rhs => {
      change (Fintype.card α : ENat) * Z.card / (Fintype.card β : ENNReal)
      rw [mul_div_assoc,
        ←ENat.card_eq_coe_fintype_card,
        ←ENNReal.tsum_one,
        ←ENNReal.tsum_mul_right,
        one_mul]
    }
  open scoped Classical in

  refine le_trans (PMF'.subadditivity (PMF.uniformOfFintype M) _) ?_
  suffices ∀a, (PMF.map (fun m ↦ (φ m) a ∈ Z) (PMF.uniformOfFintype M)) True ≤ (Z.card) / (Fintype.card (β)) by
    -- this "suffices" only provides structure.
    gcongr 1 with a
    exact this a
  intro a
  by_cases! ha : a = 0
  ·
    rw [ha]
    simp_rw [map_zero, hZ]

    simp only [PMF.map_apply, eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, tsum_zero,
      zero_le]


  simp_rw [hφ]
  specialize ψ_surj a ha
  set ρ := ψ a
  change (PMF.map ((· ∈ Z) ∘ ρ) (PMF.uniformOfFintype M)) True ≤ _
  simp_rw [←PMF.map_comp]
  rw [@UHom.main M β ρ ?_]
  rw [PMF'.mem_uniform_card]
  exact UHom.addHomOfSurjective ρ ψ_surj
