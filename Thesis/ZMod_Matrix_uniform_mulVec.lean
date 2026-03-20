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

lemma bijection_preserves_uniformOfFintype.{u} {α β : Type u}
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β] -- only one nonempty is needed, the other is implied by hf
  [DecidableEq α] [DecidableEq β]
  (f : α → β) (hf : f.Bijective)
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



lemma A_Matrix.uniform_of_transpose_uniform (n m q : ℕ) [NeZero m] [NeZero q] :
      Matrix.transpose <$> PMF.uniformOfFintype (A_Matrix n m q) = PMF.uniformOfFintype (A_Matrix m n q):= by
      change (Matrix.transposeAddEquiv _ _ _ ·) <$> _ = _
      apply bijection_preserves_uniformOfFintype
      exact AddEquiv.bijective (Matrix.transposeAddEquiv (Fin n) (Fin m) (ZMod q))




theorem A_Matrix.uniform_of_uniform_vecMul_const' {n m q : ℕ} [NeZero n][NeZero m] [q_prime : Fact <| Nat.Prime q]
    (s : Fin n → ZMod q)
    : do {
      let A ← PMF.uniformOfFintype (A_Matrix n m q)
      return A.transpose.mulVec s
    } = (PMF.uniformOfFintype (Fin m → ZMod q))
      := by
        calc
          _ =
          (do
              let A ← PMF.uniformOfFintype (A_Matrix n m q)
              let B : Matrix (Fin m) (Fin n) (ZMod q) := Matrix.transpose A
              pure (B.mulVec s)
          )
              := by rfl
          _ = (do
              let B ← do {
                let A ← PMF.uniformOfFintype (A_Matrix n m q)
                pure A.transpose
                }
              pure (B.mulVec s)
          )
              := by
                simp only [bind_pure_comp, map_pure]
          _ = (do
              let B ← PMF.uniformOfFintype (A_Matrix m n q)
              pure (B.mulVec s)
          )
              := by
                have := uniform_of_transpose_uniform n m q
                simp only [bind_pure_comp, map_pure, ← this, Functor.map_map]
                rfl
          -- _ = (do
          --     let A ← PMF.uniformOfFintype (A_Matrix m n q)
          --     have B := Matrix.of.symm A
          --     pure (A.mulVec s)
          -- )
          --     := by
          --       #check Matrix.ofAddEquiv
          --       #check Matrix.mulVec_eq_sum
          --       sorry
        simp only [bind_pure_comp]
        simp_rw [Matrix.mulVec_eq_sum]
        simp only [op_smul_eq_smul]
        change
          (fun a ↦ ∑ x, s x • (fun y ↦ Matrix.transpose a x y)) <$> _ = _
        simp_rw [Matrix.transpose_apply]
        conv => {
          left; left; intro A; right; intro x; right; intro y

          rw [←Matrix.of_symm_apply A]
        }



          -- _ = PMF.uniformOfFintype (Fin m → ZMod q) := by sorry
        -- simp only [bind_pure_comp, map_pure]
        -- rw [bind_pure_comp]

        -- change
        --   (PMF.map (fun A ↦ (Matrix.transpose A).mulVec s)
        --         (PMF.uniformOfFintype (A_Matrix n m q))).toMeasure =
        --     (PMF.uniformOfFintype (Fin m → ZMod q)).toMeasure
        -- rw [←PMF.toMeasure_map]


        sorry
