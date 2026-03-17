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

theorem lemma_5_3_also {q : N → Q} [∀n, NeZero (q n)] {m : N → M} [m_pos : ∀n, NeZero (m n)] (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  (A : (n : N) → (A_Matrix n (m n) (q n)))(hA : ∀n, lemma_5_3_statement (A n))
  (s : (n : N) → ℝ≥0) (hs : s =ω (sqrt_log ∘ m)) (s_pos : ∀n, NeZero (s n))
  : lemma_5_3_also_statement A s := by

  unfold lemma_5_3_also_statement lemma_5_3_relationship

  -- problem: 2_6 has the dimension match the sequence index, but that doesn't appear here.
  have nonem n: Nonempty (Fin (m n)) :=by
    exact instNonemptyOfInhabited



  -- let Λ n : 𝓛 (Fin (n)) := m_minv n ▸ (A (minv n)).Λ_ortho'
  let Λ n : 𝓛 (_) := by
    exact (A (n)).Λ_ortho'


  -- let Λ' n : 𝓛 (Fin (mminv n)) := by
  --   exact Λ (minv n)

  let s' (n : ℕ) : ℝ≥0 :=  (s n) / 4


  obtain ⟨ε,negl_ε, ε_pos, so⟩ := Lemma_2_6_then'' (m := m) (mHyp'_ge_id m q q_prime m_hyp) (m_pos) Λ s' sorry
  -- subst Λ'
  refine ⟨(ε),?_,?_,?_⟩

  sorry
  -- simp only [Function.comp_apply]
  exact fun n ↦ ε_pos (n)
  -- simp only [Function.comp_apply]
  intro n

  specialize (so) n
  subst Λ
  simp_all only
  apply le_trans so
  suffices 1/4 ≤ (A n).Λ_ortho'.dualLattice.minimum_distance_sup by
    rw [div_le_comm₀]
    unfold s'
    trans 1/4
    ·
      simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, NNReal.le_inv_iff_mul_le]
      ring_nf
      exact mul_inv_le_one
    · exact this
    exact (𝓛.minimum_distance_sup.positive _).pos
    exact NeZero.pos (s n)






  clear so negl_ε ε_pos ε
  unfold lemma_5_3_statement at hA
  simp_rw [A_Matrix.Λ_dual'] at hA
  specialize hA n

  have : (q n • (A n).Λ_ortho'.dualLattice).minimum_distance_sup = q n * ((A n).Λ_ortho'.dualLattice).minimum_distance_sup := by
    -- prove in other file
    sorry
  rw [this] at hA
  clear this

  -- simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, NNReal.inv_le, ge_iff_le]
  simp at hA
  set q'  := ((q n) : ℝ≥0)
  set md := (A n).Λ_ortho'.dualLattice.minimum_distance_sup
  have : 0 < q' := by exact NeZero.pos q'


  have : q' * (1 / 4) ≤ q' * md := by
    simp only [one_div]
    exact hA
  set fo := (1/4 : ℝ≥0)
  (expose_names; exact le_of_mul_le_mul_left this this_1)
