import OkkokkoLeanTwo.Basic
import OkkokkoLeanTwo.CoverDecomposes.Basic
import OkkokkoLeanTwo.CoverDecomposes.Monotone
import OkkokkoLeanTwo.Addition.FuncSum

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}


section addition
@[simp]
theorem ComposeCover.add (sa : ι → Set X) (sb : ι' → Set X)
  : ComposeCover sa + ComposeCover sb = ComposeCover (Sum.elim sa sb) := by
  unfold ComposeCover
  funext x
  simp only [Pi.add_apply]
  rw [←ENat.card_sum]
  apply ENat.card_congr
  symm
  exact Equiv.subtypeSum


theorem CoverDecomposes.add {a b : X → ℕ∞} {sa : ι → _} {sb : ι' → _}
  (ah : CoverDecomposes a F sa) (bh : CoverDecomposes b F sb)
  : CoverDecomposes (a + b) F (Sum.elim sa sb)
  := by
  rw [CoverDecomposes.def'] at *
  refine ⟨?_,?_⟩
  · simp only [Set.Sum.elim_range, Set.union_subset_iff, ah.left, bh.left, and_self]
  rw [bh.right, ah.right]
  clear * -
  exact ComposeCover.add sa sb

-- hm, this has three different senses of addition pointwise, union, ⊕
theorem CoverDecomposes.add.union {F' : Set (Set X)} {a b : X → ℕ∞} {sa : ι → _} {sb : ι' → _}
  (ah : CoverDecomposes a F sa) (bh : CoverDecomposes b F' sb)
  : CoverDecomposes (a + b) (F ∪ F') (Sum.elim sa sb)
  := by
  apply add
  apply ah.F_monotone_union_left
  apply bh.F_monotone_union_right

-- this might be unnecessary, since using Set.Sum.elim_range and F_range get the same result
theorem CoverDecomposes.add.minimal {F' : Set (Set X)} {a b : X → ℕ∞} {sa : ι → _} {sb : ι' → _}
  (ah : CoverDecomposes a F sa) (bh : CoverDecomposes b F' sb)
  : CoverDecomposes (a + b) (ah.range ∪ bh.range) (Sum.elim sa sb)
  := by
  -- alternate:
  -- apply add
  -- apply F_monotone Set.subset_union_left ah.F_range
  -- apply F_monotone Set.subset_union_right bh.F_range
  rw [←Set.Sum.elim_range]
  apply F_range
  apply add.union ah bh

-- todo: CoverDecomposes structure, to give additivity.

theorem CoverDecomposesIn.add {a b : X → ℕ∞}
  (ah : CoverDecomposesIn a ι F) (bh : CoverDecomposesIn b ι' F)
  : CoverDecomposesIn (a + b) (ι ⊕ ι') F
  := ⟨_, CoverDecomposes.add ah.choose_spec bh.choose_spec⟩
theorem CoverDecomposesIn.add.union {F' : Set (Set X)} {a b : X → ℕ∞}
  (ah : CoverDecomposesIn a ι F) (bh : CoverDecomposesIn b ι' F')
  : CoverDecomposesIn (a + b) (ι ⊕ ι') (F ∪ F')
  := ⟨_, CoverDecomposes.add (ah.choose_spec.F_monotone_union_left) (bh.choose_spec.F_monotone_union_right)⟩


noncomputable instance instEquivPairInfinite [Infinite ι] : (ι ⊕ ι) ≃ ι := by
  apply Nonempty.some
  apply Cardinal.eq.mp
  simp only [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.add_mk_eq_max, max_self]
noncomputable instance instEquivProdInfinite [Infinite ι] : (ι × ι) ≃ ι := by
  apply Nonempty.some
  apply Cardinal.eq.mp
  simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mul_mk_eq_max, max_self]

-- theorem MultiCover.coe_CoverDecomposesIn (a : MultiCover ι F)


-- #check HAdd -- try for different ι
#check AddSubsemigroup
#check AddSubmonoid

def CoverDecomposesIn.subsemigroup (ι : Type v) (F : Set (Set X)) [Infinite ι] : AddSubsemigroup (X → ℕ∞) where
  carrier := MultiCover ι F
  add_mem' {a b} ha hb := by
    apply by_equiv (instEquivPairInfinite) |>.mp
    apply add ha hb

theorem CoverDecomposesIn.zero (n : ∅ ∈ F) : CoverDecomposesIn 0 ι F
  := by
  unfold CoverDecomposesIn
  use fun _ ↦ ∅
  unfold CoverDecomposes
  simp only [n, implies_true, true_and]
  unfold ComposeCover
  ext x
  simp only [Pi.zero_apply, Set.mem_empty_iff_false, ENat.card_false]


def CoverDecomposesIn.submonoid (n : ∅ ∈ F) [Infinite ι] : AddSubmonoid (X → ℕ∞) where
  carrier := MultiCover ι F
  add_mem' {a b} ha hb := by
    apply by_equiv (instEquivPairInfinite) |>.mp
    apply add ha hb
  zero_mem' := zero n

theorem CoverDecomposes.mul {a b : X → ℕ∞} {sa : ι → _} {sb : ι' → _}
  (Fh : ∀(f)(g), (f ∈ F) → (g ∈ F) → f ∩ g ∈ F)
  (ah : CoverDecomposes a F sa) (bh : CoverDecomposes b F sb)
  : CoverDecomposes (a * b) F ((fun (ii' : ι × ι') ↦ sa ii'.1 ∩ sb ii'.2))
  := by -- multiplication of two sets is their union, and multiplication is bilinear.

  rw [CoverDecomposes.def'] at *
  constructor
  intro f w
  simp only [Set.mem_range, Prod.exists] at w
  obtain ⟨i, i', w⟩ := w

  have sai: sa i ∈ F := by simp only [Set.mem_range, exists_apply_eq_apply, ah.left _]
  have sbi: sb i' ∈ F := by simp only [Set.mem_range, exists_apply_eq_apply, bh.left _]
  exact Set.mem_of_eq_of_mem (id (Eq.symm w)) (Fh (sa i) (sb i') sai sbi)
  rw [bh.right, ah.right]
  clear ah bh
  unfold ComposeCover
  simp only [Set.mem_inter_iff]
  funext x
  simp only [Pi.mul_apply]
  rw [←ENat.card_prod _ _]
  apply ENat.card_congr
  symm
  let P i := x ∈ sa i
  let Q i := x ∈ sb i
  change { i : ι × ι' // P i.1 ∧ Q i.2 } ≃ Subtype P × Subtype Q
  apply Equiv.subtypeProdEquivProd

theorem CoverDecomposesIn.mul {a b : X → ℕ∞}
  (Fh : ∀(f)(g), (f ∈ F) → (g ∈ F) → f ∩ g ∈ F)
  (ah : CoverDecomposesIn a ι F) (bh : CoverDecomposesIn b ι' F)
  : CoverDecomposesIn (a * b) (ι × ι') F

  := ⟨_, CoverDecomposes.mul Fh ah.choose_spec bh.choose_spec⟩

open scoped Classical in
theorem ComposeCover.singleton (s : Set X) (I : ι)
  : (ComposeCover fun i ↦ if i = I then s else ∅) = s.indicator 1
  := by
  rw [ComposeCover.def]
  simp only [Set.mem_ite_empty_right]
  funext x
  simp only [Set.indicator, Pi.one_apply]
  split
  simp_all only [and_true, ENat.card_eq_coe_fintype_card, Fintype.card_unique, Nat.cast_one]
  simp_all only [and_false, ENat.card_false]

open scoped Classical in
theorem ComposeCover.of_finset (s : ι → Set X) (Is : Finset ι)
  : (ComposeCover fun i ↦ if i ∈ Is then s i else ∅) = ∑i ∈ Is, (s i).indicator 1
  := by sorry
open scoped Classical in
theorem ComposeCover.of_fintype [Fintype ι] (s : ι → Set X)
  : (ComposeCover s) = ∑i, (s i).indicator 1
  := by sorry


-- todo: a coercion
/-- the extension of a set: its indicator function -/
theorem CoverDecomposesIn.indicator_mem (n : ∅ ∈ F) [inst : Nonempty ι] {s : Set X}
  (hs : s ∈ F)
  : CoverDecomposesIn (Set.indicator s 1) ι F
  := by
  unfold CoverDecomposesIn
  let I : ι := inst.some
  open scoped Classical in
  use fun i ↦ if i = I then s else ∅
  rw [CoverDecomposes.def']
  constructor
  {
  intro x w
  simp_all only [Set.mem_range, I]
  obtain ⟨w, h⟩ := w
  subst h
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only
  }
  symm
  exact ComposeCover.singleton _ _


-- it is sufficient that a #ι subset of F can partition the space
theorem CoverDecomposesIn.one_mem (u : Set.univ ∈ F) (n : ∅ ∈ F) [inst : Nonempty ι] : CoverDecomposesIn 1 ι F
  := by
  have : (1 : X → ℕ∞) = Set.univ.indicator 1 := by simp only [Set.indicator_univ]
  rw [this]
  exact indicator_mem n u

def CoverDecomposesIn.subsemiring (u : Set.univ ∈ F) (n : ∅ ∈ F) [Infinite ι]
  (Fh : ∀(f)(g), (f ∈ F) → (g ∈ F) → f ∩ g ∈ F)
  : Subsemiring (X → ℕ∞) where
  carrier := MultiCover ι F
  add_mem' {a b} ha hb := by
    apply by_equiv instEquivPairInfinite |>.mp
    apply add ha hb
  zero_mem' := zero n
  mul_mem' {a b} ha hb := by

    apply by_equiv instEquivProdInfinite |>.mp

    apply mul Fh ha hb
  one_mem' := one_mem u n


example : Semigroup (Set X) where
  mul a b := a ∩ b
  mul_assoc a b c := by
    change a ∩ b ∩ c = a ∩ (b ∩ c)
    exact Set.inter_assoc a b c

end addition
