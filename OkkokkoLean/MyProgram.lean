import Mathlib.Tactic


def main: IO Unit := IO.println "Hello, world!"

#eval main

section first_sec

variable {ι : Type} [Fintype ι] {X : Type} [LinearOrder ι] [LinearOrder X]

def swap {X Y : Type} [DecidableEq X] (x y : X) (a : X → Y)  : X → Y := (fun i ↦
        if i = x
          then a y
        else if i = y
          then a x
        else a i)

def swap_comp {X : Type} [DecidableEq X]  (x y : X) : X → X := fun i ↦
  if i = x
    then y
  else if i = y
    then x
  else i
theorem swap_comp_eq{X Y : Type} [DecidableEq X] (a : X → Y) (x y : X) : swap x y a = a ∘ (swap_comp x y) := by
  ext w
  unfold swap swap_comp
  simp only [Function.comp_apply]
  bound


def merged : List X × List X → List X
  | ⟨[], []⟩ => []
  | ⟨[], bs⟩ => bs
  | ⟨as, []⟩ => as
  | ⟨a::as, b::bs⟩ => if a ≤ b then a::(merged (as, (b::bs))) else b::(merged ((a::as), bs))

def sorted : List X → List X
  | [] => []
  | a::[] => a::[]
  -- | as => merged ((as.splitAt (as.length / 2)).map sorted sorted)
  | a::as => sorted (as)


-- def sorted (a : ℤ → X) : ℤ → ℕ → ℤ → X
--   | start, 0 => a
--   | start, 1 => a
--   | start, 2 =>
--     if (a start > a (start + 1)) then
--       (swap start (start + 1) a)
--     else a
--   | start, len => sorry --fun i ↦ if i < (start + len/2)


-- theorem sorted_spec (a : ℤ → X) (start : ℤ) (len : ℕ) : MonotoneOn (sorted a start len) (Set.Ico start (start+len)) := sorry
-- theorem sorting_spec (a : ι → X) : Monotone (sorted a) := sorry

example {X Y : Type} (f : X → Y) (B : Set X) (A : Set Y) : (f ⁻¹' A ∩ B).Nonempty ↔ (A ∩ f '' B).Nonempty := by
  reduce
  simp only [↓existsAndEq, and_true]

end first_sec

section product_cover_try

#check Set.prod_inter_prod

open Set Function


def UnionEq {X : Type} (a b : ℕ → Set X) : Prop :=
  (⋃ n, a n = ⋃ n, b n)

def UnionEquivalence {X : Type} : Equivalence (@UnionEq X) where
  refl := fun x ↦ rfl
  symm := fun {x y} a ↦ id (Eq.symm a)
  trans := by
    unfold UnionEq
    intro x y z a a_1
    simp_all only

-- #check MeasureTheory.Measure

#check Pairwise

#check disjointed




theorem disjointed_def {X : Type} (a : ℕ → Set X) : disjointed a = fun i ↦ a i \ (⋃ (j < i), a j) := by
  unfold disjointed
  simp only [Finset.sup_set_eq_biUnion, Finset.mem_Iio]

-- #check disjointed
-- #check partialSups_disjointed
-- #check partialSups

theorem disjointed_unionEq {X : Type} {a : ℕ → Set X} : UnionEq a (disjointed a) := by
  unfold UnionEq
  -- have := partialSups_disjointed a
  exact Eq.symm iUnion_disjointed

def pointwiseProd {N : Type} {Xa Xb : Type} (a : N → Set Xa) (b : N → Set Xb) := fun i ↦ a i ×ˢ b i

#check Fin.foldl

example (a b : ℝ) : (∀ε>0, a ≤ b + ε) → a ≤ b := by
  intro h
  exact le_of_forall_pos_le_add h

theorem product_disjointed {Xa Xb : Type} (a : ℕ → Set Xa) (b : ℕ → Set Xb)
  : ∃(a' : ℕ → Set Xa)(b' : ℕ → Set Xb), (Pairwise (Disjoint on (pointwiseProd a' b'))) ∧ UnionEq (pointwiseProd a b) (pointwiseProd a' b') := by

  sorry




end product_cover_try





section multi_cover


#check Membership

variable  {X : Type} {F : Type} [SetLike F X]

#check Subgroup


-- todo: other sets than N

structure MultiCover {X : Type} (F : Type) [SetLike F X] where
  func (x : X) : ℕ∞
  possible: ∃(series: ℕ → F), func = fun x ↦ ENat.card {n | x ∈ series n}


-- structure MultiCover {X : Type} (F : Type) (c : Cardinal) [SetLike F X] where
--   func (x : X) : ℕ∞
--   possible: ∃(ι : Type)(_ : Cardinal.mk ι ≤ c)(series: ι → F), func = fun x ↦ ENat.card {n | x ∈ series n}

example : ℕ ≃ ℕ ⊕ ℕ := by exact Equiv.natSumNatEquivNat.symm

-- instance : ℕ ≅ ℕ×ℕ := by

--   sorry

-- structure MultiCover2 {X : Type} (F : Type) [Membership X F] where
--   series: ℕ → F
--   -- func (x : X) : ℕ∞ := ENat.card {n | x ∈ series n}
-- def MultiCover2.func (f : MultiCover2 F) (x : X) : ℕ∞ := ENat.card {n | x ∈ f.series n}

instance : FunLike (MultiCover F) X ℕ∞ where
  coe := MultiCover.func
  coe_injective' := by
    intro a b fu
    change ⟨a.func,_⟩ = b
    simp only [fu]

-- instance : CoeFun (MultiCover F) (fun _ ↦ (X → ℕ∞)) := ⟨MultiCover.func⟩

instance : Membership X (MultiCover F) where
  mem f x := f x > 0

-- #check type_eq_of_heq


def possible_equiv' {ι₁ ι₂ : Type} (e : ι₁ ≃ ι₂) (f : ι₁ → F) (x : X)
  : {n | x ∈ f n} ≃ {n | x ∈ f (e.symm n)} := by
  rw [Equiv.setOf_apply_symm_eq_image_setOf e (x ∈ f ·)]
  exact e.image {n | x ∈ f n}

theorem possible_equiv {ι₁ ι₂ : Type} (e : ι₁ ≃ ι₂) (f : ι₁ → F) (x : X)
  : ENat.card ↑{n | x ∈ f n} = ENat.card ↑{n | x ∈ f (e.symm n)} := by
  apply ENat.card_congr
  exact possible_equiv' e f x


-- theorem MultiCover.equiv_ι {ι₁ ι₂ : Type} (e : ι₁ ≃ ι₂) : MultiCover F ι₁ = MultiCover F ι₂ := by

--   let w : MultiCover F ι₁ := sorry
--   have ⟨w_func,⟨w_series,w_poss⟩⟩ := w
--   let q : MultiCover F ι₂ := ⟨w_func,
--     by
--     use w_series ∘ e.symm
--     rw [w_poss]
--     funext x
--     exact possible_equiv e w_series x
--     ⟩
--   apply type_eq_of_heq (a := w) (b := q)
--   sorry


def alternating' {X : Type} (a b : ℕ → X) : ℕ → X
  | 0 => a 0
  | n + 1 => alternating' b (a <| · + 1) n

#eval Array.range 10 |>.map <| alternating' ((Array.range 5)[·]!) ((Array.range 5 |>.map (· + 10))[·]!)

-- def alternating {X : Type} (a b : ℕ → X) (n : ℕ) : X :=
--   match (Equiv.natSumNatEquivNat.symm n) with
--    | .inl i => a i
--    | .inr i => b i

def alternating {X : Type} (a b : ℕ → X) (n : ℕ) : X := (Equiv.natSumNatEquivNat.symm n).elim a b


-- make this for disjoint MultiCover
-- #check SetLike
#check ENat.card_congr
#check ENat.card


instance : Add (MultiCover F) where
  add a b := ⟨(a + b), by
    have ⟨as,as_spec⟩ := a.possible
    have ⟨bs,bs_spec⟩ := b.possible
    use fun n ↦ (Equiv.natSumNatEquivNat.symm n).elim as bs
    change a.func + b.func = _
    rw [as_spec,bs_spec]
    funext x
    simp only [Pi.add_apply]
    rw [←ENat.card_sum]
    apply ENat.card_congr
    symm
    trans
    apply (possible_equiv' Equiv.natSumNatEquivNat _ x).symm
    apply Equiv.subtypeSum
  ⟩

instance : AddCommSemigroup (MultiCover F)  where
  add_assoc a b c := by
    change a + b + c = ⟨a + (b + c), _⟩
    ring_nf
    rfl
  add_comm a b := by
    change ⟨a + b, _⟩ = b + a
    rw [show b + a = ⟨b + a, _⟩ by rfl]
    simp only [MultiCover.mk.injEq]
    exact AddCommMagma.add_comm ⇑a ⇑b

-- Surely this already exists.
class HasEmpty (A : Type*) {B : outParam Type*} [SetLike A B] extends EmptyCollection A where
  empty_is_empty : SetLike.coe (∅ : A) = ∅


instance [HasEmpty F] : Zero (MultiCover F) where
  zero := ⟨fun x ↦ 0, by
    use fun i ↦ ∅
    funext x
    symm
    rw [ENat.card_eq_zero_iff_empty]
    have : x ∉ (∅ : F) := by
      simp [←SetLike.mem_coe]
      rw [HasEmpty.empty_is_empty]
      exact fun a ↦ a
    exact Subtype.isEmpty_of_false fun a ↦ this
    ⟩

instance [HasEmpty F] : AddCommMonoid (MultiCover F) where
  zero_add a := by
    rw [show 0 + a = ⟨0 + a,_⟩ by rfl]
    simp only [zero_add]
    rfl
  add_zero a := by
    rw [show a + 0 = ⟨a + 0,_⟩ by rfl]
    simp only [add_zero]
    rfl
  nsmul := nsmulRec


theorem MultiCover.add_fun_coe {a b : MultiCover F} : ⇑(a + b) = ⇑a + ⇑b := by rfl
theorem MultiCover.zero_fun_coe [HasEmpty F] : ⇑(0 : MultiCover F) = 0 := by rfl



instance : LE (MultiCover F) where
  le a b := (a : X → ℕ∞) ≤ (b : X → ℕ∞)
  -- le a b := LE.le (a : X → ℕ∞) (b : X → ℕ∞)

instance : Preorder (MultiCover F) where
  le_refl a := by
    intro x
    exact Std.IsPreorder.le_refl _
  le_trans := by
    intro a b c ab bc x
    exact Std.IsPreorder.le_trans (a x) (b x) (c x) (ab x) (bc x)

instance : TopologicalSpace (MultiCover F) := Preorder.topology _
local instance : TopologicalSpace ℕ∞ := Preorder.topology _

example : ℕ ≃ ℕ × ℕ := by exact Nat.pairEquiv.symm


theorem MultiCover.hasSum [HasEmpty F]  (s : ℕ → MultiCover F) : HasSum s ⟨
  (∑' n, ⇑(s n)),
  by
  -- let series n : F := Nat.pairEquiv



  sorry
⟩ := by sorry

theorem MultiCover.summable [HasEmpty F]  (s : ℕ → MultiCover F) : Summable s := by sorry

theorem MultiCover.sum_coe [HasEmpty F]  (s : ℕ → MultiCover F) : (∑' n, ⇑(s n)) = ⇑(∑' n, (s n)) := by

  sorry

theorem MultiCover.sum [HasEmpty F]  (s : ℕ → MultiCover F) (x : X) : (∑' n, (s n)) x = (∑' n, (s n x)) := by
  -- rw [tsum]
  -- apply ENNReal.tsum_apply
  -- apply tsum_apply
  -- rw [tsum_apply]
  -- simp only [SummationFilter.support_eq_univ, Set.inter_univ, Set.indicator_univ]
  sorry

/-
section test_structure_parameters

-- is test X = test Y if they don't use the parameter anywhere?

structure test (X : Type) where
  foo : Prop

theorem test_heq {X Y : Type} : test X = test Y := sorry

def test_back {X : Type} (t : test X) : Type := X

-- if this is true, I'm wrong.
example {X Y : Type} (x : test X) (y : test Y) (h : test X = test Y) : X = Y := by
  change test_back x = test_back y
  rw [h] at x
  -- x is now a different variable.
  -- this is useless
  sorry
end test_structure_parameters
-/

end multi_cover
