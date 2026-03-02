import Thesis.Hypotheses
import Thesis.A_Matrix
import Thesis.Statistic
import Thesis.Zqn
import Thesis.Gaussians


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
  := (∀n, ℙ (subsets n) ≤ 2 * ((q n) ^ (- n : ℝ)))


def corollary_5_4_statement (q : N → Q) [∀n, NeZero (q n)]  (m : N → M)
  (A : (n : N) → A_Matrix n (m n) (q n)) (s : N → ℝ≥0) (s_pos : ∀n, NeZero (s n)) :=
    statistically_close
      (fun n ↦ (A n).syndrome_distributed (int_gaussian (m n) (s n)))
      (fun n ↦ uniform_over_Zqn n (q n))


theorem corollary_5_4 (q : N → Q) [∀n, NeZero (q n)]  (m : N → M) (q_hyp : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  : ∃(subsets : (n : N) → Set (A_Matrix n (m n) (q n)))(_ : corollary_5_4_condition subsets),
  ∀(A : (n : N) → (A_Matrix n (m n) (q n)))(_ : ∀n, A n ∈ subsets n),
  ∀(s : N → ℝ≥0)(_ : s =ω (sqrt_log ∘ m)) (s_pos : ∀n, NeZero (s n)) , -- ≥ω is the same as =ω, right?
  corollary_5_4_statement q m A s s_pos
  := by


  sorry
