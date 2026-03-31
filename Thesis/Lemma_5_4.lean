import Thesis.Hypotheses
import Thesis.A_Matrix
import Thesis.Statistic
import Thesis.StatisticalDistance
import Thesis.Zqn
import Thesis.Gaussians

import Thesis.Lemma_5_1
import Thesis.Lemma_5_2
import Thesis.Lemma_5_3
import Thesis.ForallBut

open ProbabilityTheory MeasureTheory
open scoped NNReal

-- hmm, in Corollary 5.4, "statistically close" describes what happens as n varies, but A is conditioned on n. this means statistically_close does not fit
-- what does it mean?

-- the distribution of the syndrome is statistically close to uniform
-- statistically close = statistical distance is negligible in n
-- blackboard: (A, Ax mod q) ≈ (A, y)     f m ≥ ...
-- is it expressed that the distribution sampled from (A : Uniform,e : Gaussian) to (A, Ae mod q), is compared to the distribution (A : Uniform, y: Uniform),
--  and these distributions have type [ProbabilityMeasure ()]
#check let n :=5; let m := 7; let q := 10;
  ProbabilityMeasure ((A_Matrix n m q) × (Fin n → ZMod q))



-- example (q : ℕ → ℕ) (m : ℕ → ℕ)

-- this collection of subsets have all but 2q^-n values
def corollary_5_4_condition {q : ℕ → ℕ} [∀n, NeZero (q n)] {m : ℕ → ℕ} (subsets : (n : ℕ) → Set (A_Matrix n (m n) (q n)))
  := ForAllBut' subsets 2


def corollary_5_4_statement (q : ℕ → ℕ) [∀n, NeZero (q n)]  (m : ℕ → ℕ)
  (A : (n : ℕ) → A_Matrix n (m n) (q n)) (s : ℕ → ℝ≥0) (s_pos : ∀n, NeZero (s n)) :=
    statisticallyClose
      (fun n ↦ (A n).syndromeDistributed (intGaussian (m n) (s n)))
      (fun n ↦ uniform_over_Zqn n (q n))

/-- an example for the proof -/
def corollary_5_4.valid_subsets (q : N → Q) [∀n, NeZero (q n)] (m : N → M)
  : (n : N) → Set (A_Matrix n (m n) (q n)) := by
    intro n
    let w := (lemma_5_1_statement : Set (A_Matrix n (m n) (q n)))
    let ww := (lemma_5_3_statement : Set (A_Matrix n (m n) (q n)))
    exact ww ∩ w
    -- have ww n := fun (A : A_Matrix n (m n) (q n)) ↦ ∀(s : (n : N) → ℝ≥0) (hs : s =ω (sqrt_log ∘ m)), (lemma_5_3_also_statement A (s n))


def corollary_5_4.valid_subsets_spec (q : N → Q) [∀n, NeZero (q n)] (m : N → M) [∀n, NeZero (m n)]  (q_hyp : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  : corollary_5_4_condition (valid_subsets q m) := by
    unfold corollary_5_4_condition valid_subsets
    change ForAllBut' (fun n A ↦ lemma_5_3_statement (n := n) A ∧ lemma_5_1_statement (n := n) A) 2
    rw [←one_add_one_eq_two]
    refine ForAllBut'.and ?_ ?_
    · exact fun n ↦ lemma_5_3 (q_hyp n) (m_hyp n)
    · exact fun n ↦ lemma_5_1 (q_hyp n) (m_hyp n)

-- added that m can't be 0
theorem corollary_5_4 (q : ℕ → ℕ) [∀n, NeZero (q n)] (m : ℕ → ℕ) [∀n, NeZero (m n)] (q_hyp : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  : ∃(subsets : (n : ℕ) → Set (A_Matrix n (m n) (q n)))(_ : corollary_5_4_condition subsets),
  ∀(A : (n : ℕ) → (A_Matrix n (m n) (q n)))(_ : ∀n, A n ∈ subsets n),
  ∀(s : ℕ → ℝ≥0)(hs : (NNReal.toReal ∘ s) =ω (sqrt_log ∘ m)) (s_pos : ∀n, NeZero (s n)) , -- ≥ω is the same as =ω, right?
  corollary_5_4_statement q m A s s_pos
  := by
  refine ⟨corollary_5_4.valid_subsets q m, corollary_5_4.valid_subsets_spec _ _ q_hyp m_hyp, ?_⟩
  intro A A_spec s s_LittleO s_pos

  have A_mem n := Set.mem_inter_iff _ _ _ |>.mp (A_spec n)
  have key_5_1 n : lemma_5_1_statement (A n) := (A_mem n).right
  obtain ⟨ε, negl_ε, ε_pos,key_5_3⟩ : (lemma_5_3_also_statement A s) :=
    have ee n: lemma_5_3_statement (A n) := (A_mem n).left
    lemma_5_3_also q_hyp m_hyp A ee s s_LittleO s_pos

  clear A_spec s_LittleO

  unfold lemma_5_3_relationship at key_5_3
  let sε {n m q : ℕ} {_ : NeZero q} (A : A_Matrix n m q) (ε) {_ : NeZero ε} (s) := (A).Λ_ortho'.smoothing_parameter (ε) ≤ s
  change ∀ᶠ (n : ℕ) in Filter.atTop, sε (A n) (ε n) (s n) at key_5_3

  unfold corollary_5_4_statement
  set synd_dist := (fun n ↦ (A n).syndromeDistributed (intGaussian (m n) (s n)))
  set uni := fun n ↦ uniform_over_Zqn n (q n)



  have key_5_2
    : ∀ᶠ (n : N) in Filter.atTop, statisticalDistance (synd_dist n) (uni n) ≤ 2 * ε n
    := by
      apply Filter.Eventually.mp key_5_3
      apply Filter.Eventually.of_forall
      intro n key_5_2_statement
      exact lemma_5_2 (A n) (key_5_1 n) (ε n) sorry (s n) key_5_2_statement

  have m_top : id ≤ m := by exact mHyp'_ge_id m q q_hyp m_hyp
  apply negligible_over.toNegligible ?_ m_top


  apply negligible_over.of_EventuallyLE key_5_2
  change negligible_over ((2 : ℝ≥0) • ε) m
  exact negligible_over.smul negl_ε



-- maybe also do this?
theorem corollary_5_4_prob (q : N → ℕ) [∀n, NeZero (q n)]  (m : N → ℕ) (q_hyp : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  (s : N → ℝ≥0)(s_growth : s =ω (sqrt_log ∘ m)) (s_pos : ∀n, NeZero (s n)) :
  let A_is n := ProbabilityTheory.uniformOn_isProbabilityMeasure ( s:= (Set.univ : Set (A_Matrix n (m n) (q n)))) sorry sorry
  let A n : ProbabilityMeasure _ := ⟨_,A_is n⟩
  let x := fun n ↦ (intGaussian (m n) (s n))
  let A_x n := ProbabilityMeasure.prod (A n) (x n)
  let A_Ax n := ProbabilityMeasure.map (A_x n) (f :=
    fun ⟨A,x⟩ ↦ (⟨A,A.syndromeMap x⟩ : _ × _)
    ) sorry


  False := sorry

-- set_option linter.unusedTactic false

-- theorem pos_of_pos_mul_pos {a b : Real} (a_pos : 0 < a) (b_pos : 0 < b) : 0 < a * b := by simp_all only [mul_pos_iff_of_pos_left]
-- example  {a b : Real} (a_pos : 0 < a) (b_pos : 0 < b) (a_lt_b : a < b) : sorry := by
--   #check pos_of_pos_mul_pos a_pos b_pos
--   #check pos_of_pos_mul_pos a_pos a_pos
--   #check pos_of_pos_mul_pos b_pos a_pos
--   #check pos_of_pos_mul_pos b_pos a_lt_b
--   sorry
