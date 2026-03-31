import Thesis.A_Matrix
import Thesis.Hypotheses
import Thesis.ForallBut

open ProbabilityTheory

/-- "the subset-sums of the columns of A generate Zqn" -/
def lemma_5_1_statement {n m q : ℕ} (A : A_Matrix n m q) : Prop :=
  A.syndrome_map '' {e | ∀i, e i = 0 ∨ e i = 1} = Set.univ

-- the form seems complete
-- wait, is q_prime
theorem lemma_5_1 {n m q : ℕ} [NeZero q]  (q_prime : Nat.Prime q) (m_hyp : mHyp m n q) : ForAllBut (@lemma_5_1_statement n m q ) 1 := sorry
