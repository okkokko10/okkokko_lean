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


def ForAllBut {n m q : ℕ} (statement : A_Matrix n m q → Prop) (scale : Scale := 1) := (Set.encard statementᶜ) ≤ scale * (ForAllBut.count n m q)



def ForAllBut.def_encard {n m q : ℕ} {statement : A_Matrix n m q → Prop} {scale : Scale}
  : ForAllBut statement scale ↔ (Set.encard statementᶜ) ≤ scale * (ForAllBut.count n m q) := by
    rfl

def ForAllBut.def_encard' {n m q : ℕ} {statement : A_Matrix n m q → Prop} {scale : Scale}
  : ForAllBut statement scale ↔ (Set.encard statementᶜ) * (q ^ n) ≤ scale *  (q ^ m) ^ n   := by sorry

-- def ForAllBut.def_encard'' {n m q : ℕ} {statement : A_Matrix n m q → Prop} {scale : Scale}
--   : ForAllBut statement scale ↔ (Set.encard statementᶜ) * (q ^ n) ≤ scale *  (q ^ m) ^ n   := by sorry






theorem ForAllBut.and {n m q : ℕ}
  {statement₁ : A_Matrix n m q → Prop} {scale₁ : Scale}
  {statement₂ : A_Matrix n m q → Prop} {scale₂ : Scale}
  (h₁ : ForAllBut statement₁ scale₁)
  (h₂ : ForAllBut statement₂ scale₂)
  :
  ForAllBut (fun A ↦ statement₁ A ∧ statement₂ A) (scale₁ + scale₂)
  :=by
    change  ForAllBut (statement₁ ∩ statement₂ : Set _) (scale₁ + scale₂)
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
  (h : ∀A, statement₁ A → statement₂ A)
  (h₁ : ForAllBut statement₁ scale)
  :
  ForAllBut (statement₂) scale := by
    rw [def_encard] at *
    have : (setOf statement₁) ⊆ (setOf statement₂) := h
    apply le_trans ?_ h₁
    have := Set.compl_subset_compl.mpr this
    simp only [ENat.toENNReal_le, ge_iff_le]
    exact Set.encard_le_encard this


def ForAllBut' {m q : ℕ → ℕ} (statements : (n : ℕ) → A_Matrix n (m n) (q n) → Prop) (scale : Scale) :=
  ∀n, ForAllBut (statements n) scale

theorem ForAllBut'.and
  {m q : ℕ → ℕ}
  {statements₁ : (n : ℕ) → A_Matrix n (m n) (q n) → Prop} {scale₁ : Scale}
  {statements₂ : (n : ℕ) → A_Matrix n (m n) (q n) → Prop} {scale₂ : Scale}
  (h₁ : ForAllBut' statements₁ scale₁)
  (h₂ : ForAllBut' statements₂ scale₂)
  : ForAllBut' (fun n A ↦ statements₁ n A ∧ statements₂ n A) (scale₁ + scale₂)
  := fun n ↦ ForAllBut.and (h₁ n) (h₂ n)


theorem ForAllBut'.mp
  {m q : ℕ → ℕ}
  {statements₁ : (n : ℕ) → A_Matrix n (m n) (q n) → Prop} {scale : Scale}
  {statements₂ : (n : ℕ) → A_Matrix n (m n) (q n) → Prop}
  (h : ∀n A, statements₁ n A → statements₂ n A)
  (h₁ : ForAllBut' statements₁ scale)
  : ForAllBut' statements₂ scale
  := fun n ↦ ForAllBut.mp (h n) (h₁ n)


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
  : ForAllBut statement scale ↔ ℙ (statementᶜ) ≤ scale * (q ^ n : ENNReal)⁻¹ := by
    symm
    apply ForAllBut.measure_card

def ForAllBut.def_measure_one {n m q : ℕ} [NeZero q] {statement : A_Matrix n m q → Prop}
  : ForAllBut statement 1 ↔ ℙ (statementᶜ) ≤ (q ^ n : ENNReal)⁻¹ := by
    rw [←one_mul (q ^ n : ENNReal)⁻¹]
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
  : ForAllBut statement scale ↔
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

end PMF

#check Classical.axiomOfChoice
#check Classical.skolem

def ForAllButSeq {m : ℕ → ℕ} {q : ℕ → ℕ}
 (statementA : ((n : ℕ) → (A_Matrix n (m n) (q n))) → Prop) (scale : Scale)
 := ∃(subsets : (n : ℕ) → (A_Matrix n (m n) (q n)) → Prop)(_ : ForAllBut' subsets scale),
  ∀(A : (n : ℕ) → (A_Matrix n (m n) (q n)))(_ : ∀n, subsets n (A n)), statementA (A)


-- todo: define vacuous

def ForAllBut.nonvacuous (n m q : ℕ) (scale : Scale) : Prop :=
  ∀{statement : A_Matrix n m q → Prop} (_ : ForAllBut statement scale), ∃x, statement x

theorem ForAllBut.nonvacuous.not_empty {n m q : ℕ} {scale : Scale}
  (nv : nonvacuous n m q scale)
  : ¬ ForAllBut (∅ : Set (A_Matrix n m q)) scale
  := fun a ↦ match nv a with | Exists.intro _ w => w

/-- when scale is high enough that it becomes "for all but 100%" -/
def ForAllBut.vacuous (n m q : ℕ) (scale : Scale) : Prop :=
  ∀{statement : A_Matrix n m q → Prop}, ForAllBut statement scale

theorem ForAllBut.vacuous_or_nonvacuous (n m q : ℕ) (scale : Scale)
  : ForAllBut.vacuous n m q scale ∨ ForAllBut.nonvacuous n m q scale := sorry

theorem ForAllBut.vacuous_nontrivial
  {n m q : ℕ} {statement : A_Matrix n m q → Prop} {scale : Scale}
  (h : ForAllBut.nonvacuous n m q scale → ForAllBut statement scale)
  : ForAllBut statement scale := by
    cases ForAllBut.vacuous_or_nonvacuous n m q scale with
    | inl w => exact w
    | inr w => exact h w

theorem ForAllBut'.toSeq
  {m q : ℕ → ℕ}
  {statements : (n : ℕ) → A_Matrix n (m n) (q n) → Prop} {scale : Scale}
  (h : ForAllBut' statements scale)
  : ForAllButSeq (fun As ↦ ∀i, statements i (As i)) scale
  := ⟨statements, h, fun _ a ↦ a⟩



theorem ForAllBut'.ofSeq
  {m q : ℕ → ℕ}
  {statements : (n : ℕ) → A_Matrix n (m n) (q n) → Prop} {scale : Scale}
  (hh : ForAllButSeq (fun As ↦ ∀i, statements i (As i)) scale)
  : ForAllBut' statements scale

  := by
    -- in indices where it's vacuous, replace the given set with univ

    obtain ⟨subsets,sp, w⟩ := hh
    intro n
    refine ForAllBut.vacuous_nontrivial (fun nv ↦ ?_)
    specialize sp n
    let A : (n : ℕ) → A_Matrix n (m n) (q n) := sorry
    specialize w A sorry
    sorry

theorem ForAllButSeq.mp
  {m q : ℕ → ℕ}
  {statements₁ : ((n : ℕ) → A_Matrix n (m n) (q n)) → Prop} {scale : Scale}
  {statements₂ : ((n : ℕ) → A_Matrix n (m n) (q n)) → Prop}
  (h : ∀s, statements₁ s → statements₂ s)
  (h₁ : ForAllButSeq statements₁ scale)
  : ForAllButSeq statements₂ scale
  := by
    obtain ⟨subsets,sp, w⟩ := h₁
    use subsets, sp
    intro As As_s
    exact h _ (w _ As_s)


theorem ForAllButSeq.mp'
  {m q : ℕ → ℕ}
  {statements₁ : (n : ℕ) → A_Matrix n (m n) (q n) → Prop} {scale : Scale}
  {statements₂ : ((n : ℕ) → A_Matrix n (m n) (q n)) → Prop}
  (h : ∀ (As : (n : ℕ) → A_Matrix n (m n) (q n)), (∀ (i : ℕ), statements₁ i (As i)) → statements₂ As)
  (h₁ : ForAllBut' statements₁ scale)
  : ForAllButSeq statements₂ scale
  := mp h (h₁.toSeq)

-- idea: could ForAllButSeq be ae?

#check MeasureTheory.OuterMeasure

#check Filter.Frequently
#check MeasureTheory.ae
open MeasureTheory

-- fp := fun (b : Prop) ↦ if b then (⊤ : ENNReal) else 0
-- this maps ∧ to * and ∨ to +, and → to ≤
-- also, fp ∘ Set.nonempty is (⊤ : Measure)

#check BooleanAlgebra

-- example (p : Prop) : Nat
section PropTop
-- set_option trace.Meta.synthInstance true
-- def PropENNReal (p : Prop) [Decidable p] := if p then (⊤ : ENNReal) else 0
-- def PropTop (p : Prop) [Decidable p] {α : Type*} [Zero α] := if p then (⊤ : ENNReal) else 0

-- #check (⊤ : ENNReal) * 0
-- #check ENNReal.top_mul
#check ENNReal
#check WithTop.top_mul'
#check WithTop.instSemigroupWithZero
#check Top
#check (⊤ : Prop)
#check TopHom
#check BoundedOrderHom

-- set_option trace.Meta.Tactic.simp true



-- @[coe]
noncomputable def propTop {β : Type*} [Bot β] [Top β] (p : Prop) : β := open scoped Classical in if p then ⊤ else ⊥

-- variable (β) in
-- -- @[coe]
-- noncomputable def propTop' : BoundedOrderHom Prop β where
--   toFun p := open scoped Classical in if p then ⊤ else ⊥
--   monotone' a b ab := by
--     simp_all only [le_Prop_eq]
--     split
--     next h => simp_all only [forall_const, ↓reduceIte, le_refl]
--     next h => simp_all only [IsEmpty.forall_iff, bot_le]
--   map_top' := by simp only [«Prop».top_eq_true, ↓reduceIte]
--   map_bot' := by simp only [«Prop».bot_eq_false, ↓reduceIte]
-- noncomputable def propTopPi (α : Type*) : BoundedOrderHom (α → Prop) (α → β) := sorry
-- noncomputable def propTop'' := propTop' (WithTop β)
#check OrderTop
-- #check isBot_zero




variable  {β : Type*} [Bot β] [Top β]

@[simp]
theorem propTop.false_bot : (propTop False : β) = ⊥ := by
  unfold propTop
  simp only [↓reduceIte]

@[simp]
theorem propTop.true_top : (propTop True : β) = ⊤  := by
  unfold propTop
  simp only [↓reduceIte]

variable {β : Type*} [PartialOrder β] [BoundedOrder β] [Nontrivial β]

@[simp]
theorem propTop.le_iff (a b : Prop) : (propTop a : β) ≤ propTop b ↔ (a → b) := by
  unfold propTop
  apply Iff.intro -- aesop
  · intro a_1 a_2
    simp_all only [↓reduceIte, top_le_iff, ite_eq_left_iff, bot_ne_top, imp_false, not_not]
  · intro a_1
    split
    next h => simp_all only [forall_const, ↓reduceIte, le_refl]
    next h => simp_all only [IsEmpty.forall_iff, bot_le]



@[simp]
theorem propTop.top_iff {p : Prop} : (propTop p : β) = ⊤ ↔ p := by
  unfold propTop
  simp only [ite_eq_left_iff, bot_ne_top, imp_false, not_not]

@[simp]
theorem propTop.bot_iff {p : Prop} : (propTop p : β) = ⊥ ↔ (¬ p) := by
  unfold propTop
  simp only [ite_eq_right_iff, top_ne_bot, imp_false]

section ENNReal
@[simp]
theorem propTop.zero_iff {p : Prop} : (propTop p : ENNReal) = 0 ↔ (¬ p) := bot_iff


theorem propTop.and_mul (a b : Prop) : (propTop (a ∧ b) : ENNReal) = propTop a * propTop b := by
  unfold propTop
  simp_all only [bot_eq_zero', mul_ite, ite_mul, ne_eq, ENNReal.top_ne_zero, not_false_eq_true, ENNReal.mul_top,
    zero_mul, mul_zero] -- aesop
  split
  next h => simp_all only [↓reduceIte]
  next h =>
    simp_all only [not_and, right_eq_ite_iff, ENNReal.zero_ne_top, imp_false]
    intro a_1
    simp_all only [not_true_eq_false, imp_false, not_false_eq_true]

theorem propTop.or_plus (a b : Prop) : (propTop (a ∨ b) : ENNReal) = propTop a + propTop b := by
  unfold propTop
  simp_all only [bot_eq_zero'] -- aesop
  split
  next h =>
    cases h with
    | inl h_1 => simp_all only [↓reduceIte, top_add]
    | inr h_2 => simp_all only [↓reduceIte, add_top]
  next h => simp_all only [not_or, ↓reduceIte, add_zero]


theorem propTop.monotone (a b : Prop) (h : a → b) : (propTop a : ENNReal) ≤ propTop b := by
  unfold propTop
  simp_all only [bot_eq_zero'] -- aesop
  split
  next h_1 => simp_all only [forall_const, ↓reduceIte, le_refl]
  next h_1 => simp_all only [IsEmpty.forall_iff, zero_le]

@[simp]
theorem propTop.exists_sum {ι : Type*} (a : ι → Prop) : ∑'i, (propTop (a i)) = (propTop (∃i, a i) : ENNReal) := by
  -- unfold propTop
  by_cases! h : ∃ i, a i
  · simp only [h, true_top]
    refine ENNReal.tsum_eq_top_of_eq_top ?_
    simp_all only [top_iff]
  simp only [h, false_bot, bot_eq_zero', tsum_zero, exists_false]


set_option trace.Meta.synthInstance true in
example : (0 : ENNReal) = ⊥ := rfl
end ENNReal


end PropTop

-- todo: think about
-- #check Fintype
-- #check Finite
-- and
-- #check Decidable



-- #check (⊤ : OuterMeasure _)
#check (⊤ : Measure _)
#check OuterMeasure.top_apply
-- noncomputable def ForAllBut_Measure  {n m q : ℕ} (scale : Scale := 1) : OuterMeasure ((A_Matrix n m q → Prop))
--   := OuterMeasure.comap (ForAllBut (scale := scale)) ⊤

-- noncomputable def ForAllBut.measure'  {n m q : ℕ} (scale : Scale := 1)
--   (nv : nonvacuous n m q scale)
--   : OuterMeasure ((A_Matrix n m q)) where
--   measureOf s := propTop (ForAllBut s scale)
--   empty := by
--     rw [propTop.zero_iff]
--     exact nv.not_empty
--   mono {s₁ s₂} hs := by
--     rw [propTop.le_iff]
--     exact mp hs
--   iUnion_nat s pdi := by
--     simp only [propTop.exists_sum, propTop.le_iff]
--     intro w
--     -- NO
--     -- it's false
--     sorry


#check MeasureTheory.Measure
