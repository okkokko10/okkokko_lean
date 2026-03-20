import Thesis.A_Matrix

variable {n m q : ℕ} [NeZero n] [NeZero m] [q_prime : Fact <| Nat.Prime q]

theorem A_Matrix.uniform_of_uniform_vecMul_const
    (s : Fin n → ZMod q)
    : (@A_Matrix.uniform n m q _ |>.map ( f:= fun A : A_Matrix n m q ↦ A.transpose.mulVec s) sorry).toMeasure
      = ProbabilityTheory.uniformOn (@Set.univ _) := sorry

-- theorem ZMod_uniform_of_const_mul_uniform {q : ℕ} [NeZero q]
#check ZMod.AddAutEquivUnits
#check ZMod.ringEquivOfPrime -- that's cool. maybe irrelevant

-- the lemma seems like it uses a claim that with Prime q, for nonzero s, the distribution A ↦ As is uniform

#check ProbabilityTheory.uniformOn
example (q : ℕ) (q_prime : Fact <| Nat.Prime q) : Field (ZMod q) := by infer_instance


lemma A_Matrix.uniform_of_transpose_uniform (n m q : ℕ) [NeZero m] [NeZero q] :
      Matrix.transpose <$> PMF.uniformOfFintype (A_Matrix n m q) = PMF.uniformOfFintype (A_Matrix m n q):= by
      ext A
      -- simp only [PMF.uniformOfFintype_apply]
      change (PMF.map Matrix.transpose (PMF.uniformOfFintype (A_Matrix n m q)) ) A = _
      rw [PMF.map_apply Matrix.transpose ((PMF.uniformOfFintype (A_Matrix n m q))) A]
      rw [tsum_fintype]
      --simp_rw [←Matrix.transposeᵣ_eq]
      have tra b : A = Matrix.transpose b ↔ A.transpose = b := by -- I wonder why this doesn't exist
        rw [←Matrix.transpose_inj,Matrix.transpose_transpose b]
      simp_rw [tra]
      -- we've now shown that only one index in the sum is nonzero
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      -- set_option trace.Meta.synthInstance true in
      change PMF.uniformOfFintype _ _ = PMF.uniformOfFintype _ _ -- for some reason this change has an effect
      simp only [PMF.uniformOfFintype_apply]
      simp only [inv_inj, Nat.cast_inj]
      exact Fintype.card_congr (Matrix.transposeAddEquiv _ _ _).toEquiv

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
