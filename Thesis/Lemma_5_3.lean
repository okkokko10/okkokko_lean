import Thesis.Hypotheses
import Thesis.A_Matrix
import Thesis.Statistic
import Thesis.A_Matrix_Lattice
import Thesis.SmoothingParameter
-- for proving
import Thesis.Lemma_2_6
import Thesis.Uniform_mulVec

open scoped ProbabilityTheory NNReal
open ProbabilityTheory MeasureTheory

def lemma_5_3_statement {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : Prop :=
  q/4 ≤ 𝓛.minimum_distance_sup (A.Λ_main')



#check PMF.bind
-- theorem coeSubmodule_mem
--   {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
--   {A : Submodule R M} (B : Submodule R A)
--   (x)
--   : x ∈ coeSubmodule B
--   := sorry


noncomputable def Casts.ZnToZqn_surjective {ι : Type*} {q : ℕ}
  : Function.Surjective (@Casts.ZnToZqn ι q) := by
    -- simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.surjective_comp]
    -- intro w
    -- use fun i ↦ (w i).cast
    -- funext i
    -- simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply,
    --   algebraMap_int_eq, eq_intCast, ZMod.intCast_cast, ZMod.cast_id', id_eq]
    sorry

def A_Matrix.syndromes_def' {n m q : ℕ} (A : A_Matrix n m q)
  : A.syndromes = (Matrix.mulVecLin A).toAddMonoidHom.range.toIntSubmodule
  := by
  unfold syndromes syndromeMap
  simp only
  rw [LinearMap.range_comp]
  rw [LinearMap.range_eq_top_of_surjective _ Casts.ZnToZqn_surjective]
  simp only [Submodule.map_top, AddMonoidHom.coe_toIntLinearMap_range]
-- #check ProbabilityTheory.uniformOn
#check A_Matrix.uniform
theorem A_Matrix.uniformProb_change
  {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [DiscreteMeasurableSpace α]
  :
  PMF.toMeasure (PMF.uniformOfFintype α) =
  ProbabilityTheory.uniformOn (Set.univ) := by
    let := ProbabilityTheory.uniformOn_isProbabilityMeasure (s := @Set.univ α) (Set.finite_univ)
      (Set.nonempty_iff_univ_nonempty.mp inferInstance)
    symm
    ext s ms
    simp
    rw [ProbabilityTheory.uniformOn]
    #check PMF.toPMF_dirac
    #check MeasureTheory.Measure.count
    #check MeasureTheory.OuterMeasure.dirac
    -- rw [←PMF.toPMF_eq_iff_toMeasure_eq]
    -- ext x
    -- rw [PMF.toPMF]
    sorry
#check PMF.toPMF_eq_iff_toMeasure_eq
#check PMF.toMeasure

-- ⊢ ℙ lemma_5_3_statementᶜ ≤ (lemma_5_3_statement <$> PMF.uniformOfFintype (A_Matrix n m q)) False



-- TODO: change (q ^ (- n : ℝ)) to (q ^ n)⁻¹ everywhere
-- clarification: "for some v ∈ Z", is this a uniform random variable?
theorem lemma_5_3       {n m q : ℕ} [NeZero q] [NeZero m] (q_prime : Nat.Prime q) (m_hyp : mHyp m n q)
  : ℙ (lemma_5_3_statementᶜ : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ)) := by
    have : Fact (Nat.Prime q) := .mk q_prime
    rw [show (q : ENNReal) ^ (-(n : ℝ)) = (q^n : ENNReal)⁻¹ by sorry]

    -- change ℙ (({A | ¬ lemma_5_3_statement A}) : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ))
    -- suffices ∃s : Set <| A_Matrix n m q, ℙ sᶜ ≤ (q ^ (- n : ℝ)) ∧ ∀A, s A → (lemma_5_3_statement A)  by
    --   obtain ⟨s,amo, spec⟩ := this
    --   trans ℙ sᶜ

    --   have spe A :  (¬ lemma_5_3_statement A) → (¬ s A) := by exact fun a a_1 ↦ a (spec A a_1)
    --   have spe' :  (lemma_5_3_statement : Set <| A_Matrix n m q)ᶜ ≤ (sᶜ) := by exact spe
    --   exact MeasureTheory.OuterMeasureClass.measure_mono ℙ spe
    --   exact amo


    let C : Set (Fin m → ℝ) := {x : Fin m → ℝ | ¬(x ≠ 0 → ↑q / 4 ≤ ‖x‖₊) }
    let Z : Set ↥(Casts.Zn (Fin m)) := {x :  ↥(Casts.Zn (Fin m)) | ↑x ∈ C}
    let Z'c : Set (Fin m → ZMod q) := Set.kernImage (⇑Casts.ZnToZqn) Zᶜ



    have statement_simplified (A : A_Matrix n m q) : lemma_5_3_statement A ↔ ↑((Matrix.transpose A).mulVecLin.toAddMonoidHom.range) ⊆ Z'c := by -- invalid, for planning
      change lemma_5_3_statement A ↔ ↑(Matrix.transpose A).mulVecLin.toAddMonoidHom.range.toIntSubmodule ⊆ Z'c
      rw [←A_Matrix.syndromes_def']
      unfold lemma_5_3_statement
      rw [(𝓛.minimum_distance.greater_iff A.Λ_main' (r := q/4))]
      convert_to (∀ x ∈ A.Λ_main', x ∉ C) ↔ _
      · unfold C; simp only [ne_eq, Classical.not_imp, not_le, Set.mem_setOf_eq, not_and, not_lt]
      unfold A_Matrix.Λ_main'
      unfold coeSubmodule
      set czqn := Casts.ZnToZqn
      set Λ_in_Zn := (Submodule.comap czqn A.Λ_main'')
      simp only [Submodule.mem_map, Submodule.subtype_apply, Subtype.exists, exists_and_right,
        exists_eq_right, forall_exists_index]
      convert_to (∀ (x : Casts.Zn (Fin m)), x ∈ Λ_in_Zn → (↑x) ∉ C) ↔ _
      · simp only [Subtype.forall]
      change ↑Λ_in_Zn ⊆ Zᶜ ↔ _
      unfold Λ_in_Zn
      rw [Submodule.comap_coe, ←Set.subset_kernImage_iff]
      rfl

    let sorryProp : Prop := sorry

    have Z'c_def' : Z'c = (Casts.ZnToZqn '' Z)ᶜ := by
      ext x
      unfold Z'c
      set czqn := Casts.ZnToZqn
      rw [←Set.singleton_subset_iff]
      rw [Set.subset_kernImage_iff]
      rw [Set.subset_compl_comm]
      have : Set.InjOn czqn Z := sorry

      sorry
    open scoped Classical in
    let Z' : Finset (Fin m → ZMod q) := (Z'cᶜ).toFinset

    have hZ' : 0 ∉ Z' := by sorry


    have statement_simplified' (A : A_Matrix n m q)
      : (¬lemma_5_3_statement A) ↔ ∃v, v ∈ ↑((Matrix.transpose A).mulVecLin.toAddMonoidHom.range) ∧ v ∈ Z' := by
      simp_rw [statement_simplified]
      set ppp := (Matrix.transpose A).mulVecLin.toAddMonoidHom.range
      unfold Z'
      rw [Set.subset_def]
      simp only [SetLike.mem_coe, not_forall,  Set.toFinset_compl,
        Finset.mem_compl, Set.mem_toFinset]
      simp only [exists_prop]

    suffices (do {
      let A ← PMF.uniformOfFintype (A_Matrix n m q)
      return ¬lemma_5_3_statement A
    } : PMF Prop ) (True) ≤ (q ^ n : ENNReal)⁻¹ by
      apply le_trans ?_ this
      simp only [bind_pure_comp]
      sorry
    simp_rw [statement_simplified']
    #check lemma_5_3_key'
    apply le_trans (lemma_5_3_key' Z' hZ')
    simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_pow]

    -- simp only [ENNReal.le_inv_iff_mul_le]
    -- suffices ((q ^ n * Z'.card) * q ^ n) ≤ (q ^ m) by
    --   sorry
    have q_pos : (q : ENNReal) ≠ 0 := sorry
    have q_fin : (q : ENNReal) ≠ ⊤ := sorry



    have Z'_card: Z'.card ≤ (q/2 : ENNReal) ^ m := by sorry
    suffices ↑q ^ n *  (q/2 : ENNReal) ^ m / (↑q ^ m) ≤ (↑q ^ n : ENNReal)⁻¹ by
      apply le_trans ?_ this
      gcongr
    clear * - q_pos q_fin m_hyp
    suffices ↑q ^ n *  (1/2 : ENNReal) ^ m ≤ (↑q ^ n : ENNReal)⁻¹ by
      apply le_trans ?_ this
      apply le_of_eq
      rw [mul_div_assoc]
      congr 1
      simp_rw [ENNReal.div_eq_inv_mul]
      simp [mul_pow]
      rw [mul_comm, mul_assoc]
      rw [ENNReal.mul_inv_cancel ?_ ?_]
      · simp only [mul_one]
      · simp only [ne_eq, pow_eq_zero_iff', q_pos, false_and, not_false_eq_true]
      · simp only [ne_eq, ENNReal.pow_eq_top_iff, q_fin, false_and, not_false_eq_true]

    simp only [one_div, ENNReal.le_inv_iff_mul_le]
    rw [mul_comm, ←mul_assoc]
    refine ENNReal.le_inv_iff_mul_le.mp ?_
    rw [←ENNReal.inv_pow,inv_inv]
    rw [←pow_add]
    rw [←two_mul]


    apply ENNReal.log_le_log_iff.mp
    simp_rw [ENNReal.log_pow]
    simp only [EReal.natCast_mul, Nat.cast_ofNat]
    suffices 2 * ↑n * Real.log (q) ≤ ↑m * ENNReal.log 2 by
      rw [ENNReal.log_pos_real']
      simp only [ENNReal.toReal_natCast, ge_iff_le]
      exact this
      simp only [ENNReal.toReal_natCast, Nat.cast_pos]
      exact Nat.pos_of_neZero q
    rw [ENNReal.log_pos_real' (by simp only [ENNReal.toReal_ofNat, Nat.ofNat_pos])]
    simp only [ENNReal.toReal_ofNat]
    suffices (2 * n * (Real.log ↑q)) ≤ m * (Real.log 2) by
      apply EReal.coe_le_coe
      exact this


    unfold mHyp at m_hyp
    -- apply le_trans m_hyp

    -- TODO: mHyp is wrong





    sorry


#check pdf.IsUniform

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
