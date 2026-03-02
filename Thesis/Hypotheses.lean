import Mathlib

def mHyp (m n q : ℕ) : Prop := (2 * n * Real.log q) ≤ m

abbrev N := ℕ
abbrev M := ℕ
abbrev Q := ℕ

section hypotheses

def mHyp' (m : N → M) (q : N → Q) : Prop := ∀n, (2 * n * Real.log (q n)) ≤ m n


lemma mHyp'_ge_id (m : N → M) (q : N → Q) (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q) : id ≤ m :=
  by
  unfold mHyp' at m_hyp
  intro n
  dsimp only [id_eq]
  specialize m_hyp n
  rify
  apply le_trans ?_ m_hyp
  trans  ↑n * 2 * Real.log 2
  · clear * -
    suffices 1 ≤ 2 * Real.log 2 by
      convert_to ↑n * 1 ≤ ↑n * (2 * Real.log 2)
      · group
      · group
      refine mul_le_mul (le_refl _) this (zero_le_one' ℝ) (Nat.cast_nonneg' n)
    linarith only [Real.log_two_gt_d9]
  have tt : Real.log (2) ≤ Real.log ↑(q n) := by
    apply Real.log_le_log zero_lt_two
    simp only [Nat.ofNat_le_cast]
    apply Nat.Prime.two_le (q_prime n)
  ring_nf
  refine mul_le_mul ?_ (by rfl) zero_le_two (by positivity)
  refine mul_le_mul (by rfl) tt (by positivity) (Nat.cast_nonneg' n)

lemma mHyp'_tendsTo (m : N → M) (q : N → Q) (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  : Filter.Tendsto m Filter.atTop Filter.atTop := sorry -- use [mHyp'_ge_id]

end hypotheses
