import Thesis.A_Matrix

-- lemma 5.3 seems like it uses a claim that with Prime q, for nonzero s, the distribution A ↦ As is uniform
variable {n m q : ℕ} [NeZero n] [NeZero m] [q_prime : Fact <| Nat.Prime q]

example (q : ℕ) (q_prime : Fact <| Nat.Prime q) : Field (ZMod q) := by infer_instance


-- wait, equivalences preserve uniform distribution

theorem A_Matrix.uniform_of_uniform_vecMul_const
    (s : Fin n → ZMod q)
    : (@A_Matrix.uniform n m q _ |>.map ( f:= fun A : A_Matrix n m q ↦ A.transpose.mulVec s) sorry).toMeasure
      = ProbabilityTheory.uniformOn (@Set.univ _) := sorry

-- theorem ZMod_uniform_of_const_mul_uniform {q : ℕ} [NeZero q]
-- #check ZMod.AddAutEquivUnits
-- #check ZMod.ringEquivOfPrime -- that's cool. maybe irrelevant


-- #check ProbabilityTheory.uniformOn
#check PMF.uniformOfFinset
#check Set.BijOn
#check PMF.seq

-- open PMF

-- maybe also for multisets?
lemma bijection_preserves_uniformOfFinset.{u} {α β : Type u}
  [DecidableEq α]
  [DecidableEq β]
  (s : Finset α) (hs : s.Nonempty) (t : Finset β) (ht : t.Nonempty) -- only one nonempty is needed, the other is implied by hf
  (f : α → β) (hf : Set.BijOn f s t)
  : PMF.map f (PMF.uniformOfFinset s hs) = (PMF.uniformOfFinset t ht) := by
    ext y
    -- change (PMF.map f (PMF.uniformOfFinset s hs)) x = (PMF.uniformOfFinset t ht) x


    rw [PMF.map_apply f (PMF.uniformOfFinset s hs) y]
    -- #check PMF.uniformOfFinset_apply_of_mem
    -- by_cases h : x ∈ t
    -- ·
    --   simp [h]
    --   sorry
    have : Nonempty α := ⟨hs.choose⟩


    by_cases h : y ∈ t
    ·
      have := hf.image_eq
      #check Set.MapsTo
      simp only [PMF.uniformOfFinset_apply]
      simp only [h, ↓reduceIte]



      #check Set.LeftInvOn
      obtain ⟨x,xw⟩ : ∃x, ∀x', y = f x' ↔ x' = x := by sorry
      simp only [xw, tsum_ite_eq]
      have : x ∈ s := by
        have := xw x
        simp only [iff_true] at this
        have := (hf.injOn)
        sorry
      simp only [this, ↓reduceIte, inv_inj, Nat.cast_inj]
      exact Set.BijOn.finsetCard_eq f hf

    rw [PMF.uniformOfFinset_apply_of_notMem _ h]
    simp only [PMF.uniformOfFinset_apply, ENNReal.tsum_eq_zero, ite_eq_right_iff, ENNReal.inv_eq_zero,
      ENNReal.natCast_ne_top, imp_false]
    intro x yfx
    contrapose! h
    rw [yfx]
    exact hf.mapsTo h


-- #exit
open scoped Classical in
@[simp, local aesop safe apply]
theorem bijection_preserves_uniformOfFintype {α β : Type*}
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β] -- only one nonempty is needed, the other is implied by hf
  -- [DecidableEq α] [DecidableEq β]
  {f : α → β} (hf : f.Bijective)
  : (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  ext y
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  let f' := Equiv.ofBijective f hf
  have qq a : a = f'.symm y ↔ y = f a := by
    rw [Eq.comm]
    exact Equiv.symm_apply_eq (Equiv.ofBijective f hf) (x := y) (y := a)
  simp_rw [←qq _]
  simp only [tsum_ite_eq, inv_inj, Nat.cast_inj]
  exact Fintype.card_congr f'

section uniform_preserving

variable {G : Type*} [Group G] [Fintype G] [Nonempty G] (a : G)

set_option trace.aesop true
open scoped Classical in
@[simp]
lemma PMF.map_ofMultiset {α β : Type*}
  (s : Multiset α) (hs : s ≠ 0)
  (f : α → β)
  : PMF.map f (PMF.ofMultiset s hs) = (PMF.ofMultiset (Multiset.map f s) (hs ∘ Multiset.map_eq_zero.mp)) := by
    ext x
    simp only [PMF.map_apply, PMF.ofMultiset_apply, Multiset.card_map]
    suffices
      (∑' (i : α), if x = f i then (Multiset.count i s : ENNReal) else 0) =
        (Multiset.count x (Multiset.map f s) : ENNReal) by
      have := congrArg (· * (s.card : ENNReal)⁻¹) this
      simp only at this
      rw [←ENNReal.tsum_mul_right] at this
      simp only [ite_mul, zero_mul] at this
      simp_all only [ne_eq]
      exact this
    rw [tsum_eq_sum (s := s.toFinset)]
    rotate_left
    · intro b a
      simp_all only [ne_eq, Multiset.mem_toFinset, not_false_eq_true, Multiset.count_eq_zero_of_notMem,
        CharP.cast_eq_zero, ite_self]
    suffices
      (∑ b ∈ s.toFinset, if x = f b then (Multiset.count b s) else 0) =
        (Multiset.count x (Multiset.map f s)) by
        rw [←this]
        simp only [Nat.cast_sum, Nat.cast_ite, CharP.cast_eq_zero]
    simp only [Multiset.count_map]
    simp_rw [← Multiset.count_filter (p := (x = f ·))]
    set w :=  (Multiset.filter (x = f ·) s)
    rw [Multiset.sum_count_eq_card]
    subst w
    simp only [Multiset.mem_filter, Multiset.mem_toFinset, and_imp]
    tauto

set_option trace.aesop true
open scoped Classical in
-- @[simp]
lemma PMF.uniformOfFintype_eq_ofMultiset_univ {α : Type*}
  [Fintype α] [ne : Nonempty α]
  : PMF.uniformOfFintype α = PMF.ofMultiset (Finset.univ.val) (fun uni ↦
    Finset.ne_empty_of_mem (Finset.mem_univ ne.some) (Finset.val_eq_zero.mp uni)) := by
    ext x : 1
    simp_all only [uniformOfFintype_apply, ofMultiset_apply, Multiset.count_univ, Nat.cast_one, Finset.card_val,
      Finset.card_univ, one_div]


@[to_additive, simp, local aesop safe apply]
theorem upre.Group.mulLeft : PMF.map (a * ·) (PMF.uniformOfFintype _) = PMF.uniformOfFintype _ := by
  have := (Group.mulLeft_bijective a)
  -- simp_all only [Multiset.bijective_iff_map_univ_eq_univ, bijection_preserves_uniformOfFintype]
  exact bijection_preserves_uniformOfFintype this



end uniform_preserving
#exit

@[simp]
lemma A_Matrix.uniform_of_transpose_uniform (n m q : ℕ) [NeZero m] [NeZero q] :
      PMF.map Matrix.transpose (PMF.uniformOfFintype (A_Matrix n m q)) = PMF.uniformOfFintype (A_Matrix m n q):= by
      change PMF.map (Matrix.transposeAddEquiv _ _ _ ·) _ = _
      apply bijection_preserves_uniformOfFintype
      exact AddEquiv.bijective (Matrix.transposeAddEquiv (Fin n) (Fin m) (ZMod q))

theorem A_Matrix.uniform_of_uniform_vecMul_const' {n m q : ℕ} [NeZero n][NeZero m] [q_prime : Fact <| Nat.Prime q]
    (s : Fin n → ZMod q)
    : do {
      let A ← PMF.uniformOfFintype (A_Matrix n m q)
      return A.transpose.mulVec s
    } = (PMF.uniformOfFintype (Fin m → ZMod q))
      := by

        simp only [bind_pure_comp]
        rw [PMF.monad_map_eq_map]
        change PMF.map ((Matrix.mulVec · s) ∘ Matrix.transpose) _ = _
        rw [←PMF.map_comp]
        simp only [uniform_of_transpose_uniform]


          -- _ = (do
          --     let A ← PMF.uniformOfFintype (A_Matrix m n q)
          --     have B := Matrix.of.symm A
          --     pure (A.mulVec s)
          -- )
          --     := by
          --       #check Matrix.ofAddEquiv
          --       #check Matrix.mulVec_eq_sum
          --       sorry
        -- simp only [bind_pure_comp]
        -- simp_rw [Matrix.mulVec_eq_sum]
        -- simp only [op_smul_eq_smul]
        -- change
        --   (fun a ↦ ∑ x, s x • (fun y ↦ Matrix.transpose a x y)) <$> _ = _
        -- simp_rw [Matrix.transpose_apply]
        -- conv => {
        --   left; left; intro A; right; intro x; right; intro y

        --   rw [←Matrix.of_symm_apply A]
        -- }



          -- _ = PMF.uniformOfFintype (Fin m → ZMod q) := by sorry
        -- simp only [bind_pure_comp, map_pure]
        -- rw [bind_pure_comp]

        -- change
        --   (PMF.map (fun A ↦ (Matrix.transpose A).mulVec s)
        --         (PMF.uniformOfFintype (A_Matrix n m q))).toMeasure =
        --     (PMF.uniformOfFintype (Fin m → ZMod q)).toMeasure
        -- rw [←PMF.toMeasure_map]


        sorry
