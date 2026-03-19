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
instance A_Matrix.instFintype {n m q : ℕ} [NeZero q] : Fintype (A_Matrix n m q) := Matrix.instFintypeOfDecidableEq (ZMod q)


variable {ι : Type*} [Fintype ι] [DecidableEq ι] in
variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem 𝓛.minimum_distance.greater_iff [Nonempty ι] [NormedAddCommGroup (ι → ℝ)]
  (r : ℝ≥0)
  : r ≤ (𝓛.minimum_distance Λ) ↔ ∀x ∈ Λ, x ≠ 0 → r ≤ ‖x‖₊ := by sorry
-- clarification: "for some v ∈ Z", is this a uniform random variable?

theorem lemma_5_3       {n m q : ℕ} [NeZero q] (q_prime : Nat.Prime q) (m_hyp : mHyp m n q)
  : ℙ (lemma_5_3_statementᶜ : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ)) := by

    let ua := PMF.uniformOfFintype (A_Matrix n m q)
    have eq_measure : ua.toMeasure = A_Matrix.uniform.toMeasure  := by
      unfold ua
      #check PMF.toMeasure_uniformOfFintype_apply
      ext s ms
      have : Fintype s := by
        sorry

      rw [PMF.toMeasure_uniformOfFintype_apply s ms]
      unfold A_Matrix.uniform
      simp only [MeasureTheory.ProbabilityMeasure.coe_mk]
      rw [ProbabilityTheory.uniformOn]

      sorry


    -- unfold MeasurableSpace.volume
    change MeasureTheory.volume (lemma_5_3_statementᶜ : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ))
    change A_Matrix.uniform.toMeasure (lemma_5_3_statementᶜ : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ))
    -- rw [←eq_measure]
    -- simp only [PMF.toMeasure_uniformOfFintype_apply]
    -- #check PMF.toMeasure_bind_apply

    let cha : PMF (Bool) := do {
      let A ← ua
      return q/4 ≤ A.Λ_main'.minimum_distance_sup
    }
    -- suffices cha (Bool.false) ≤ (q ^ (- n : ℝ)) by
    --   unfold cha at this
    --   simp at this


    --   sorry
    -- unfold cha
    -- simp only [bind_pure_comp]

    let cube : Finset (Fin m → ℤ) := sorry
    have nec : cube.Nonempty := sorry

    let cha2 (s : Fin n → ZMod q) : PMF (Bool) := do {
      let A ← ua;
      let v' := A.transpose.mulVec s;
      let v ← PMF.uniformOfFinset cube nec;
      have := ∀i, v i = v' i

      return q/4 ≤ A.Λ_main'.minimum_distance_sup
    }

    unfold lemma_5_3_statement
    simp only [ge_iff_le]





    sorry

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
