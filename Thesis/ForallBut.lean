import Thesis.A_Matrix
open ProbabilityTheory


-- #check ℙ (lemma_5_1_statementᶜ : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ)) := sorry

open scoped ENNReal NNReal

abbrev Scale := ℝ≥0∞


noncomputable def ForAllBut.count (n m q : ℕ) := ((↑q ^ n : ENNReal)⁻¹ * (↑q ^ m) ^ n)
theorem ForAllBut.count_eq (n m q : ℕ) [NeZero q]
  : count n m q = (Fintype.card (A_Matrix n m q)) * (q ^ n : ENNReal)⁻¹  := by
  have : Fintype.card (A_Matrix n m q) = (q ^ m) ^ n := by
    unfold A_Matrix
    rw [Fintype.card_congr (Matrix.of.symm)]
    simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [this]
  unfold count
  rw [mul_comm]
  norm_cast


def ForAllBut (n m q : ℕ) (statement : A_Matrix n m q → Prop) (scale : Scale) := (Set.encard statementᶜ) ≤ scale * (ForAllBut.count n m q)



def ForAllBut.def_encard {n m q : ℕ} {statement : A_Matrix n m q → Prop} {scale : Scale}
  : ForAllBut n m q statement scale ↔ (Set.encard statementᶜ) ≤ scale * (ForAllBut.count n m q) := by
    rfl

def ForAllBut.def_encard' {n m q : ℕ} {statement : A_Matrix n m q → Prop} {scale : Scale}
  : ForAllBut n m q statement scale ↔ (Set.encard statementᶜ) * (q ^ n) ≤ scale *  (q ^ m) ^ n   := by sorry

-- def ForAllBut.def_encard'' {n m q : ℕ} {statement : A_Matrix n m q → Prop} {scale : Scale}
--   : ForAllBut n m q statement scale ↔ (Set.encard statementᶜ) * (q ^ n) ≤ scale *  (q ^ m) ^ n   := by sorry






theorem ForAllBut.and {n m q : ℕ}
  {statement₁ : A_Matrix n m q → Prop} {scale₁ : Scale}
  {statement₂ : A_Matrix n m q → Prop} {scale₂ : Scale}
  (h₁ : ForAllBut n m q statement₁ scale₁)
  (h₂ : ForAllBut n m q statement₂ scale₂)
  :
  ForAllBut n m q (fun A ↦ statement₁ A ∧ statement₂ A) (scale₁ + scale₂)
  :=by
    change  ForAllBut n m q (statement₁ ∩ statement₂ : Set _) (scale₁ + scale₂)
    rw [def_encard] at *
    rw [Set.compl_inter]
    have := Set.encard_union_le statement₁ᶜ statement₂ᶜ
    have := ENat.toENNReal_le.mpr this
    apply le_trans (this)
    norm_num
    ring_nf
    gcongr


#check Filter.Eventually.mp


theorem ForAllBut.mp {n m q : ℕ}
  {statement₁ : A_Matrix n m q → Prop} {scale : Scale}
  {statement₂ : A_Matrix n m q → Prop}
  (h₁ : ForAllBut n m q statement₁ scale)
  (h : ∀A, statement₁ A → statement₂ A)
  :
  ForAllBut n m q (statement₂) scale := by
    rw [def_encard] at *
    have : (setOf statement₁) ⊆ (setOf statement₂) := h
    apply le_trans ?_ h₁
    have := Set.compl_subset_compl.mpr this
    simp only [ENat.toENNReal_le, ge_iff_le]
    exact Set.encard_le_encard this


def ForAllBut' (m q : ℕ → ℕ) (statements : (n : ℕ) → A_Matrix n (m n) (q n) → Prop) (scale : Scale) :=
  ∀n, ForAllBut n (m n) (q n) (statements n) scale

theorem ForAllBut'.and
  {m q : ℕ → ℕ}
  {statements₁ : (n : ℕ) → A_Matrix n (m n) (q n) → Prop} {scale₁ : Scale}
  {statements₂ : (n : ℕ) → A_Matrix n (m n) (q n) → Prop} {scale₂ : Scale}
  (h₁ : ForAllBut' m q statements₁ scale₁)
  (h₂ : ForAllBut' m q statements₂ scale₂)
  : ForAllBut' m q (fun n A ↦ statements₁ n A ∧ statements₂ n A) (scale₁ + scale₂)
  := fun n ↦ ForAllBut.and (h₁ n) (h₂ n)


theorem ForAllBut'.mp
  {m q : ℕ → ℕ}
  {statements₁ : (n : ℕ) → A_Matrix n (m n) (q n) → Prop} {scale : Scale}
  {statements₂ : (n : ℕ) → A_Matrix n (m n) (q n) → Prop}
  (h₁ : ForAllBut' m q statements₁ scale)
  (h : ∀n A, statements₁ n A → statements₂ n A)
  : ForAllBut' m q statements₂ scale
  := fun n ↦ ForAllBut.mp (h₁ n) (h n)


section measure

open MeasureTheory

theorem uniformOn_card {α : Type*} [MeasurableSpace α] [Fintype α]
  {s : Set α } (hs : MeasurableSet s)
  : uniformOn Set.univ s = s.encard / Fintype.card α := by
    simp only [uniformOn_univ, Measure.count_apply hs]

lemma uniform_card' {n m q : ℕ} [NeZero q]
  {statement :  A_Matrix n m q → Prop}
  : ℙ statement = (Set.encard statement) / Fintype.card (A_Matrix n m q) := by
    apply uniformOn_card
    trivial




lemma ForAllBut.measure_card {n m q : ℕ} [NeZero q]
  {statement : A_Matrix n m q → Prop} {scale : Scale}
  : ℙ (statementᶜ) ≤ scale * (q ^ n : ENNReal)⁻¹ ↔ (Set.encard statementᶜ) ≤ scale * (ForAllBut.count n m q)
  :=by
  have q_pos: q ≠ 0 := by exact Ne.symm (NeZero.ne' q)
  -- unfold ForAllBut
  rw [uniform_card']
  set ss := Set.encard statementᶜ
  rw [ENNReal.div_eq_inv_mul]
  have : Fintype.card (A_Matrix n m q) = (q ^ m) ^ n := by
    unfold A_Matrix
    rw [Fintype.card_congr (Matrix.of.symm)]
    simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [this]
  conv_lhs => {
    simp only [Nat.cast_pow]
    rw [ENNReal.inv_mul_le_iff (by simp only [ne_eq, pow_eq_zero_iff', Nat.cast_eq_zero, q_pos,
      false_and, not_false_eq_true]) (by simp only [ne_eq, ENNReal.pow_eq_top_iff,
      ENNReal.natCast_ne_top, false_and, not_false_eq_true])]
    rw [mul_comm,mul_assoc]
    simp only
  }
  unfold count
  simp only

def ForAllBut.def_measure {n m q : ℕ} [NeZero q] {statement : A_Matrix n m q → Prop} {scale : Scale}
  : ForAllBut n m q statement scale ↔ ℙ (statementᶜ) ≤ scale * (q ^ n : ENNReal)⁻¹ := by
    symm
    apply ForAllBut.measure_card

end measure


section PMF

-- from Uniform_mulVec
private lemma PMF'.mem_uniform_card_
  {α : Type*} [Fintype α] [Nonempty α]
  (Z : Finset α)
  : (PMF.map (fun x ↦ x ∈ Z) (PMF.uniformOfFintype α)) True = Z.card / (Fintype.card (α)) := by
    open scoped Classical in
    simp only [PMF.map_apply, eq_iff_iff, true_iff, PMF.uniformOfFintype_apply]
    rw [←Finset.toFinset_coe Z]
    simp_rw [Set.mem_toFinset]
    simp_rw [←Set.indicator_apply (↑Z : Set α) (fun _ ↦ (↑(Fintype.card α) : ENNReal)⁻¹)]
    rw [←tsum_subtype]
    simp only [SetLike.coe_sort_coe, ENNReal.tsum_const, ENat.card_eq_coe_fintype_card,
      Fintype.card_coe, ENat.toENNReal_coe, Finset.toFinset_coe]
    rfl

def ForAllBut.def_PMF {n m q : ℕ} [NeZero q] {statement : A_Matrix n m q → Prop} {scale : Scale}
  : ForAllBut n m q statement scale ↔
    (do {
      let A ← PMF.uniformOfFintype (A_Matrix n m q)
      return (¬statement A)
    } : PMF Prop) (True) ≤ scale * (q ^ n : ENNReal)⁻¹ := by
    -- rw [def_encard]
    open scoped Classical in
    have : (fun a ↦ ¬statement a) = (fun a ↦ a ∈ Finset.univ.filter (¬statement ·)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    conv_rhs => {
      simp only [bind_pure_comp]
      rw [PMF.monad_map_eq_map]
      rw [this]
      rw [PMF'.mem_uniform_card_ ]

    }
    rw [def_encard']


    sorry
