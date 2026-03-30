import Mathlib
-- Lemma 5.3: 2 ^ (-m) ≤ q ^ (-2*n)
def mHyp (m n q : ℕ) : Prop := (2 * n * Real.logb 2 q) ≤ m

abbrev N := ℕ
abbrev M := ℕ
abbrev Q := ℕ

section hypotheses
def mHyp' (m : N → M) (q : N → Q) : Prop := ∀n, (2 * n * Real.logb 2 (q n)) ≤ m n


lemma mHyp'_ge_id (m : N → M) (q : N → Q) (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q) : id ≤ m :=
  by
  unfold mHyp' at m_hyp
  intro n
  dsimp only [id_eq]
  specialize m_hyp n
  rify
  apply le_trans ?_ m_hyp
  trans  2 * ↑n * 1
  · linarith only
  gcongr 1
  rw [←Real.log_div_log]
  rw [one_le_div (by positivity)]
  have : 2 ≤ (q n : ℝ) := by
    norm_num
    exact Nat.Prime.two_le (q_prime n)
  apply Real.log_le_log (by norm_num) this


lemma mHyp'_tendsTo (m : N → M) (q : N → Q) (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  : Filter.Tendsto m Filter.atTop Filter.atTop := sorry -- use [mHyp'_ge_id]

end hypotheses
