import Thesis.Hypotheses
import Thesis.A_Matrix
import Thesis.Statistic
import Thesis.A_Matrix_Lattice
import Thesis.SmoothingParameter
-- for proving
import Thesis.Lemma_2_6

open scoped ProbabilityTheory NNReal

def lemma_5_3_statement {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : Prop :=
  q/4 ≤ 𝓛.minimum_distance_sup (A.Λ_main')



#check PMF.bind


-- clarification: "for some v ∈ Z", is this a uniform random variable?
theorem lemma_5_3       {n m q : ℕ} [NeZero q] [NeZero m] (q_prime : Nat.Prime q) (m_hyp : mHyp m n q)
  : ℙ (lemma_5_3_statementᶜ : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ)) := by

    -- change ℙ (({A | ¬ lemma_5_3_statement A}) : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ))
    suffices ∃s : Set <| A_Matrix n m q, ℙ sᶜ ≤ (q ^ (- n : ℝ)) ∧ ∀A, s A → (lemma_5_3_statement A)  by
      obtain ⟨s,amo, spec⟩ := this
      trans ℙ sᶜ

      have spe A :  (¬ lemma_5_3_statement A) → (¬ s A) := by exact fun a a_1 ↦ a (spec A a_1)
      have spe' :  (lemma_5_3_statement : Set <| A_Matrix n m q)ᶜ ≤ (sᶜ) := by exact spe
      exact MeasureTheory.OuterMeasureClass.measure_mono ℙ spe
      exact amo

    have w (A : A_Matrix n m q) : lemma_5_3_statement A ↔ (∀x ∈ A.Λ_main', x ≠ 0 → q/4 ≤ ‖x‖) := by
      exact 𝓛.minimum_distance.greater_iff _
    have w (A : A_Matrix n m q) : lemma_5_3_statement A := by -- invalid, for planning
      apply 𝓛.minimum_distance.greater_iff _ |>.mpr

      unfold A_Matrix.Λ_main' A_Matrix.Λ_main'' A_Matrix.syndromes
      simp only [ne_eq]
      intro x
      unfold coeSubmodule
      simp only [Submodule.mem_map, Submodule.mem_comap, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, Submodule.subtype_apply, Subtype.exists, exists_and_right,
        exists_eq_right, forall_exists_index]
      change
        ∀ (xZm : x ∈ Casts.Zn (Fin m)),
          Casts.ZnToZqn (⟨x, xZm⟩) ∈ A_Matrix.syndromes (Matrix.transpose A) →
            ¬x = 0 → ↑q / 4 ≤ ‖x‖₊
      unfold A_Matrix.syndromes

      simp only [LinearMap.mem_range, Subtype.exists, forall_exists_index]
      intro xZm y yZn sw xn0
      sorry

    have w (A : A_Matrix n m q) : ¬ lemma_5_3_statement A := by -- invalid, for planning
      unfold lemma_5_3_statement
      rw [(𝓛.minimum_distance.greater_iff A.Λ_main' (r := q/4))]

      unfold A_Matrix.Λ_main' A_Matrix.Λ_main'' A_Matrix.syndromes
      simp only [ne_eq]
      -- intro x
      unfold coeSubmodule
      simp only [Submodule.mem_map, Submodule.mem_comap, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, Submodule.subtype_apply, Subtype.exists, exists_and_right,
        exists_eq_right, forall_exists_index]
      simp only [LinearMap.mem_range, Subtype.exists, forall_exists_index, not_forall,
        Classical.not_imp, not_le, exists_and_right]
      #check Field

      #check Matrix.mulVec_eq_sum

      -- change
      --   ∀ (xZm : x ∈ Casts.Zn (Fin m)),
      --     Casts.ZnToZqn (⟨x, xZm⟩) ∈ A_Matrix.syndromes (Matrix.transpose A) →
      --       ¬x = 0 → ↑q / 4 ≤ ‖x‖₊
      -- unfold A_Matrix.syndromes

      -- simp only [LinearMap.mem_range, Subtype.exists, forall_exists_index]
      -- intro xZm y yZn sw xn0








      sorry






    sorry
-- #exit
def lemma_5_3_relationship {q : N → Q} [∀n, NeZero (q n)] {m : N → M} (A : (n : N) → (A_Matrix n (m n) (q n)))
  (s : (n : N) → ℝ≥0) (ε : (n : N) → ℝ≥0) [∀n, NeZero (ε n)]
  := ∀ᶠ (n : N) in Filter.atTop, 𝓛.smoothing_parameter ((A n).Λ_ortho') (ε n) ≤ s n

def lemma_5_3_also_statement {q : N → Q} [∀n, NeZero (q n)] {m : N → M} (A : (n : N) → (A_Matrix n (m n) (q n)))
  (s : (n : N) → ℝ≥0) :=
  ∃ (ε : (n : N) → ℝ≥0) (_ : negligible_over ε m) (_ : ∀n, NeZero (ε n)), -- change
  lemma_5_3_relationship A s ε

theorem lemma_5_3_also {q : N → Q} [∀n, NeZero (q n)] {m : N → M} [m_pos : ∀n, NeZero (m n)] (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  (A : (n : N) → (A_Matrix n (m n) (q n)))(hA : ∀n, lemma_5_3_statement (A n))
  (s : (n : N) → ℝ≥0) (hs : (NNReal.toReal ∘ s) =ω (sqrt_log ∘ m)) (s_pos : ∀n, NeZero (s n))
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
  have hs' : ((NNReal.toReal ∘ s') =ω (sqrt_log ∘ m)) := by
    have : NNReal.toReal ∘ s' = ( fun n ↦ 4⁻¹ * (NNReal.toReal ∘ s) n) := by
      unfold s'
      funext x
      simp only [Function.comp_apply, NNReal.coe_div, NNReal.coe_ofNat]
      exact div_eq_inv_mul _ 4
    rw [this]
    apply Asymptotics.IsLittleO.const_mul_right
    bound
    exact hs

  obtain ⟨ε,negl_ε, ε_pos, so⟩ := Lemma_2_6_then''' (m := m) (mHyp'_ge_id m q q_prime m_hyp) (m_pos) Λ s' hs'
  -- subst Λ'
  refine ⟨(ε),?_,?_,?_⟩
  exact negl_ε
  -- simp only [Function.comp_apply]
  exact fun n ↦ ε_pos (n)
  -- simp only [Function.comp_apply]
  apply Filter.Eventually.mp so
  apply Filter.Eventually.of_forall
  intro n so'
  subst Λ
  simp_all only
  apply le_trans so'
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


  clear so' so negl_ε ε_pos ε
  unfold lemma_5_3_statement at hA
  simp_rw [A_Matrix.Λ_dual'] at hA
  specialize hA n
  open scoped Pointwise in
  have : ((q n : ℝ) • (A n).Λ_ortho'.dualLattice).minimum_distance_sup = q n * ((A n).Λ_ortho'.dualLattice).minimum_distance_sup := by
    set q' := (q n : ℝ≥0)
    change ((q' : ℝ) • (A n).Λ_ortho'.dualLattice).minimum_distance_sup = q' * _
    symm
    apply 𝓛.minimum_distance.smulHom
  rw [this] at hA
  clear this


  set q'  := ((q n) : ℝ≥0)
  set md := (A n).Λ_ortho'.dualLattice.minimum_distance_sup
  have q'_pos: 0 < q' := by exact NeZero.pos q'


  have : q' * (1 / 4) ≤ q' * md := by
    simp only [one_div]
    exact hA
  set fo := (1/4 : ℝ≥0)
  exact le_of_mul_le_mul_left this q'_pos
