import Thesis.Hypotheses
import Thesis.A_Matrix
import Thesis.Statistic
import Thesis.A_Matrix_Lattice
import Thesis.SmoothingParameter
-- for proving
import Thesis.Lemma_2_6

open scoped ProbabilityTheory NNReal

def lemma_5_3_statement {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : Prop :=
  𝓛.minimum_distance_sup (A.Λ_main') ≥ q/4

theorem lemma_5_3       {n m q : ℕ} [NeZero q] (q_prime : Nat.Prime q) (m_hyp : mHyp m n q)
  : ℙ (lemma_5_3_statementᶜ : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ)) := sorry

def lemma_5_3_relationship {q : N → Q} [∀n, NeZero (q n)] {m : N → M} (A : (n : N) → (A_Matrix n (m n) (q n)))
  (s : (n : N) → ℝ≥0) (ε : (n : N) → ℝ≥0) [∀n, NeZero (ε n)]
  := ∀n : N, 𝓛.smoothing_parameter ((A n).Λ_ortho') (ε n) ≤ s n

def lemma_5_3_also_statement {q : N → Q} [∀n, NeZero (q n)] {m : N → M} (A : (n : N) → (A_Matrix n (m n) (q n)))
  (s : (n : N) → ℝ≥0) :=
  ∃ (ε : (n : N) → ℝ≥0) (_ : negligible ε) (_ : ∀n, NeZero (ε n)), -- change
  lemma_5_3_relationship A s ε

theorem lemma_5_3_also {q : N → Q} [∀n, NeZero (q n)] {m : N → M} (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  (A : (n : N) → (A_Matrix n (m n) (q n)))(hA : ∀n, lemma_5_3_statement (A n))
  (s : (n : N) → ℝ≥0) (hs : s =ω (sqrt_log ∘ m))
  : lemma_5_3_also_statement A s := by

  -- have := Lemma_2_6_then'' (m := m)

  -- let ⟨ε, negl_ε, ε_pos, so⟩ := Lemma_2_6_then'' (ι := (Fin <| m ·)) ?_ (fun n ↦ (A n).Λ_ortho') (s) ?_

  -- change
  --   ∃ ε,
  --     ∃ (_ : negligible ε) (ε_pos : ∀ (n : N), NeZero (ε n)),
  --       ∀ (n : N), (A n).Λ_ortho'.smoothing_parameter (ε n) ≤ s n

  -- have ww n ε (_ : NeZero ε) :
  --   (A n).Λ_ortho'.smoothing_parameter ε = (A n).Λ_main'.smoothing_parameter ε

  -- #check 2 • (𝓛.dualLattice <| (A 0).Λ_ortho')

  -- #check IsZLattice
  -- #check Lemma_2_6_then''
  -- #check A_Matrix.Λ_dual'
  -- let ⟨ε, negl_ε, ε_pos, so⟩ := Lemma_2_6_then' (ι := (Fin <| m ·)) ?_ (fun n ↦ (A n).Λ_ortho') (s) ?_
  -- use ε, negl_ε, ε_pos
  -- intro n
  -- specialize so n
  -- -- simp only [Function.comp_apply] at so
  -- specialize hA n
  -- set ww := 𝓛.smoothing_parameter (A n).Λ_ortho' (ε n)
  -- -- change ww ≤ _ at so
  -- apply le_trans so


  -- unfold lemma_5_3_statement at hA
  -- -- nth_rw 2 [A_Matrix.Λ_dual] at so





  -- sorry
  -- sorry
  -- have m_top := mHyp'_tendsTo _ _ q_prime m_hyp
  -- #check Asymptotics.IsLittleO.comp_tendsto
  -- unfold ω_sqrt_log at *
  -- #check Asymptotics.IsBigO.trans_isLittleO
  -- have : s =O[Filter.atTop] (s ∘ m) := by sorry
  -- -- refine IsBigO.trans_isLittleO ?_ ?_

  sorry
