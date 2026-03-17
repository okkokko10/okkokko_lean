import Thesis.Hypotheses
import Thesis.A_Matrix
import Thesis.Statistic
import Thesis.StatisticalDistance
import Thesis.Zqn
import Thesis.Gaussians

import Thesis.Lemma_5_1
import Thesis.Lemma_5_2
import Thesis.Lemma_5_3

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
def corollary_5_4_condition {q : N → Q} [∀n, NeZero (q n)] {m : N → M} (subsets : (n : N) → Set (A_Matrix n (m n) (q n)))
  := (∀n, ℙ (subsets n)ᶜ ≤ 2 * ((q n) ^ (- n : ℝ)))


def corollary_5_4_statement (q : N → Q) [∀n, NeZero (q n)]  (m : N → M)
  (A : (n : N) → A_Matrix n (m n) (q n)) (s : N → ℝ≥0) (s_pos : ∀n, NeZero (s n)) :=
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


def corollary_5_4.valid_subsets_spec (q : N → Q) [∀n, NeZero (q n)] (m : N → M) (q_hyp : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  : corollary_5_4_condition (valid_subsets q m) := by
    unfold corollary_5_4_condition
    intro n
    unfold valid_subsets
    simp only
    have o1 : (ℙ (lemma_5_1_statementᶜ : Set (A_Matrix n (m n) (q n))) ≤ (q n) ^ (-n : ℝ))
      := lemma_5_1 (q_hyp n) (m_hyp n)
    have o3 : (ℙ (lemma_5_3_statementᶜ : Set (A_Matrix n (m n) (q n))) ≤ (q n) ^ (-n : ℝ))
      := lemma_5_3 (q_hyp n) (m_hyp n)
    trans  (ℙ (lemma_5_3_statementᶜ : Set (A_Matrix n (m n) (q n))) + ℙ (lemma_5_1_statementᶜ : Set (A_Matrix n (m n) (q n))))
    rw [Set.compl_inter]
    exact measure_union_le lemma_5_3_statementᶜ lemma_5_1_statementᶜ
    rw [two_mul]
    exact add_le_add o3 o1

-- added that m can't be 0
theorem corollary_5_4 (q : N → Q) [∀n, NeZero (q n)] (m : N → M) [∀n, NeZero (m n)] (q_hyp : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  : ∃(subsets : (n : N) → Set (A_Matrix n (m n) (q n)))(_ : corollary_5_4_condition subsets),
  ∀(A : (n : N) → (A_Matrix n (m n) (q n)))(_ : ∀n, A n ∈ subsets n),
  ∀(s : N → ℝ≥0)(_ : s =ω (sqrt_log ∘ m)) (s_pos : ∀n, NeZero (s n)) , -- ≥ω is the same as =ω, right?
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
  change ∀ (n : N), sε (A n) (ε n) (s n) at key_5_3

  unfold corollary_5_4_statement
  set synd_dist := (fun n ↦ (A n).syndromeDistributed (intGaussian (m n) (s n)))
  set uni := fun n ↦ uniform_over_Zqn n (q n)


  have key_5_2 n := lemma_5_2 (A n) (key_5_1 n) (ε n) sorry (s n) (key_5_3 n)
  change ∀n, statisticalDistance (synd_dist n) (uni n) ≤ 2 * ε n at key_5_2
  apply negligible.of_le key_5_2
  change negligible ((2 : ℝ≥0) • ε)
  exact negligible.smul negl_ε

-- maybe also do this?
theorem corollary_5_4_prob (q : N → Q) [∀n, NeZero (q n)]  (m : N → M) (q_hyp : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  (s : N → ℝ≥0)(s_growth : s =ω (sqrt_log ∘ m)) (s_pos : ∀n, NeZero (s n)) :
  let A_is n := ProbabilityTheory.uniformOn_isProbabilityMeasure ( s:= (Set.univ : Set (A_Matrix n (m n) (q n)))) sorry sorry
  let A n : ProbabilityMeasure _ := ⟨_,A_is n⟩
  let x := fun n ↦ (intGaussian (m n) (s n))
  let A_x n := ProbabilityMeasure.prod (A n) (x n)
  let A_Ax n := ProbabilityMeasure.map (A_x n) (f :=
    fun ⟨A,x⟩ ↦ (⟨A,A.syndromeMap x⟩ : _ × _)
    ) sorry


  False := sorry
