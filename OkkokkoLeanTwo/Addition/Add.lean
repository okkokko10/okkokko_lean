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


theorem CoverDecomposes.from_series (series: ι → Set X)
  : CoverDecomposes (ComposeCover series) (Set.range series) series
  := by
  rw [CoverDecomposes.def']
  simp only [subset_refl, and_self]

theorem CoverDecomposes.F_range {func : X → ℕ∞} {F : Set (Set X)} {series: ι → Set X}
  (cd : CoverDecomposes func F series) : CoverDecomposes func (Set.range series) series
  := by
  convert from_series _
  exact eq cd

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

#check ENat.instWellFoundedRelation
#check WellFoundedRelation



#check LinearMap

instance perm.setoid : Setoid ((ι : Type v) × (ι → X)) where
  r a b := perm a.snd b.snd
  iseqv := {
    refl x := perm.refl x.snd
    symm := perm.symm
    trans := perm.trans
  }
instance perm.restrict.setoid (p : X → Prop) : Setoid ((ι : Type v) × (ι → X)) where
  r a b := perm.restrict p a.snd b.snd
  iseqv := {
    refl _ := perm.refl _
    symm := perm.symm
    trans := perm.trans
  }
#check Quotient perm.setoid
#check Quotient.map₂
-- #check Cardinal

--todo: idea: perm.restrict is "don't care about 0" quotients with perm

noncomputable def perm.get_equiv {a : ι → X} {b : ι' → X} (p : perm a b) : ι ≃ ι' := p.choose

-- note : Empty.elim is what I was looking for.

noncomputable instance perm.instZero : Zero (Quotient (@perm.setoid X)) where
  zero := ⟦⟨Empty, Empty.elim⟩⟧
noncomputable instance perm.instAdd : Add (Quotient (@perm.setoid X)) where
  add := Quotient.map₂ (fun a b ↦ ⟨a.1 ⊕ b.1, Sum.elim a.2 b.2⟩) (by
    simp only
    intro a1 a2 ⟨ae,ac⟩ b1 b2 ⟨be,bc⟩
    change perm _ _
    refine ⟨?_,?_⟩
    simp only
    exact ae.sumCongr be
    simp only [id_eq]
    simp_all only
    obtain ⟨fst, snd⟩ := a1
    obtain ⟨fst_1, snd_1⟩ := a2
    obtain ⟨fst_2, snd_2⟩ := b1
    obtain ⟨fst_3, snd_3⟩ := b2
    simp_all only
    ext x : 1
    simp_all only [Function.comp_apply, Equiv.sumCongr_apply]
    cases x with
    | inl val => simp_all only [Sum.elim_inl, Function.comp_apply, Sum.map_inl]
    | inr val_1 => simp_all only [Sum.elim_inr, Function.comp_apply, Sum.map_inr]
    )

noncomputable def perm.instAddCommMonoid : AddCommMonoid (Quotient (@perm.setoid X)) where

  add_assoc := sorry

  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  add_comm := sorry
-- #check Sigma.curry_add
-- #check Function.uncurry
-- #check Sigma.map


instance perm.instMonoid [Monoid X] : Monoid (Quotient (@perm.setoid X)) where
  -- mul := Quotient.map₂ (fun a b ↦ ⟨a.1 × b.1, (Function.uncurry <| (a.2 · * b.2 ·))⟩) (by
  mul := Quotient.map₂ (fun a b ↦ ⟨a.1 × b.1, (fun m ↦ (a.2 m.1) * (b.2 m.2))⟩) (by

    simp only
    intro a1 a2 ⟨ae,ac⟩ b1 b2 ⟨be,bc⟩

    refine ⟨ae.prodCongr be,?_⟩
    simp_all only [Function.comp_apply, Equiv.prodCongr_apply]
    obtain ⟨fst, snd⟩ := a1
    obtain ⟨fst_1, snd_1⟩ := a2
    obtain ⟨fst_2, snd_2⟩ := b1
    obtain ⟨fst_3, snd_3⟩ := b2
    simp_all only
    rfl)
  mul_assoc := sorry
  one := ⟦⟨(1 : Cardinal).out,fun _ ↦ 1⟩⟧
  -- one := Quotient.map (fun i ↦ ⟨i, fun _ ↦ 1⟩) ( by exact fun a b ⟨(e : a ≃ b)⟩ ↦  ⟨e,by rfl⟩ ) (1 : Cardinal)
  one_mul := sorry
  mul_one := sorry


-- instance instCombined' [Group X] : Semiring (Quotient (@perm.setoid X)) where
--   add := Quotient.map₂ (fun a b ↦ ⟨a.1 ⊕ b.1, Sum.elim a.2 b.2⟩) (by
--     simp only
--     intro a1 a2 ⟨ae,ac⟩ b1 b2 ⟨be,bc⟩
--     change perm _ _
--     refine ⟨?_,?_⟩
--     simp only
--     exact ae.sumCongr be
--     simp only [id_eq]
--     simp_all only
--     obtain ⟨fst, snd⟩ := a1
--     obtain ⟨fst_1, snd_1⟩ := a2
--     obtain ⟨fst_2, snd_2⟩ := b1
--     obtain ⟨fst_3, snd_3⟩ := b2
--     simp_all only
--     ext x : 1
--     simp_all only [Function.comp_apply, Equiv.sumCongr_apply]
--     cases x with
--     | inl val => simp_all only [Sum.elim_inl, Function.comp_apply, Sum.map_inl]
--     | inr val_1 => simp_all only [Sum.elim_inr, Function.comp_apply, Sum.map_inr]
--     )
--   add_assoc := sorry
--   zero := ⟦⟨Empty, _⟩⟧
--   zero_add := sorry
--   add_zero := sorry
--   nsmul := sorry
--   add_comm := sorry
--   mul := Quotient.map₂ (fun a b ↦ ⟨a.1 × b.1, (fun m ↦ (a.2 m.1) * (b.2 m.2))⟩) (by
--     simp only
--     intro a1 a2 ⟨ae,ac⟩ b1 b2 ⟨be,bc⟩
--     refine ⟨ae.prodCongr be,?_⟩
--     simp_all only [Function.comp_apply, Equiv.prodCongr_apply]
--     obtain ⟨fst, snd⟩ := a1
--     obtain ⟨fst_1, snd_1⟩ := a2
--     obtain ⟨fst_2, snd_2⟩ := b1
--     obtain ⟨fst_3, snd_3⟩ := b2
--     simp_all only
--     rfl)
--   left_distrib := sorry
--   right_distrib := sorry
--   zero_mul := sorry
--   mul_zero := sorry
--   mul_assoc := sorry
--   one := sorry
--   one_mul := sorry
--   mul_one := sorry


theorem CoverDecomposes.sum_eq {al : ι → X → ℕ∞} {sl : ι → ι' → _}
  (lh : ∀i, CoverDecomposes (al i) F (sl i))
  : CoverDecomposes (func_sum al) F (fun w : ι × ι' ↦ sl w.1 w.2)
  := by sorry

theorem ComposeCover.sum_singletons {a : X → ℕ∞} {series : ι → Set X}
  : ComposeCover series = func_sum (series · |>.indicator 1)
  := by sorry


open scoped MeasureTheory
open MeasureTheory
-- instance [S : MeasurableSpace X] : Semiring <| MultiCover ℕ (MeasurableSet[S]) where

def CoverDecomposesIn.measurex [S : MeasurableSpace X] : Subsemiring (X → ℕ∞) where
  carrier := MultiCover ℕ (MeasurableSet[S])
  add_mem' {a b} ha hb := by
    apply by_equiv (?_) |>.mp
    apply add ha hb
    exact instEquivPairInfinite
  zero_mem' := zero MeasurableSet.empty
  mul_mem' {a b} ha hb := by

    sorry
  one_mem' := sorry




end addition
