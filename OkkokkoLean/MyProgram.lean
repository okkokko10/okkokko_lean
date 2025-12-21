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

variable  {X : Type} {F : Type} [SetLike F X] {c : Cardinal}

#check Subgroup



def possible_equiv' {ι₁ ι₂ : Type} (e : ι₁ ≃ ι₂) (f : ι₁ → F) (x : X)
  :  {n | x ∈ f (e.symm n)} ≃ {n | x ∈ f n} := by
  symm
  rw [Equiv.setOf_apply_symm_eq_image_setOf e (x ∈ f ·)]
  exact e.image {n | x ∈ f n}

@[simp]
theorem possible_equiv {ι₁ ι₂ : Type} (e : ι₁ ≃ ι₂) (f : ι₁ → F) (x : X)
  : ENat.card {n // x ∈ f (e.symm n)} = ENat.card {n // x ∈ f n}  := by
  apply ENat.card_congr
  exact possible_equiv' e f x

class HasEmpty (A : Type*) {B : outParam Type*} [SetLike A B] extends EmptyCollection A where
  empty_is_empty : SetLike.coe (∅ : A) = ∅




-- todo: other sets than N

section card_multi_cover
open scoped Cardinal

-- if c is finite, it's any finite combination
structure CardMultiCover {X : Type} (F : Type) (c : Cardinal) [SetLike F X] where
  func (x : X) : ℕ∞
  possible: ∃(ι : Type)(_ : ℵ₀ ≤ #ι → #ι ≤ c)(series: ι → F), func = fun x ↦ ENat.card {n | x ∈ series n}


example : ℕ ≃ ℕ ⊕ ℕ := by exact Equiv.natSumNatEquivNat.symm

-- instance : ℕ ≅ ℕ×ℕ := by

--   sorry

-- structure MultiCover2 {X : Type} (F : Type) [Membership X F] where
--   series: ℕ → F
--   -- func (x : X) : ℕ∞ := ENat.card {n | x ∈ series n}
-- def MultiCover2.func (f : MultiCover2 F) (x : X) : ℕ∞ := ENat.card {n | x ∈ f.series n}

instance : FunLike (CardMultiCover F c) X ℕ∞ where
  coe := CardMultiCover.func
  coe_injective' := by
    intro a b fu
    change ⟨a.func,_⟩ = b
    simp only [fu]

-- instance : CoeFun (MultiCover F) (fun _ ↦ (X → ℕ∞)) := ⟨MultiCover.func⟩

instance : Membership X (CardMultiCover F c) where
  mem f x := f x > 0

-- #check type_eq_of_heq



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


-- def alternating' {X : Type} (a b : ℕ → X) : ℕ → X
--   | 0 => a 0
--   | n + 1 => alternating' b (a <| · + 1) n

-- #eval Array.range 10 |>.map <| alternating' ((Array.range 5)[·]!) ((Array.range 5 |>.map (· + 10))[·]!)

-- def alternating {X : Type} (a b : ℕ → X) (n : ℕ) : X :=
--   match (Equiv.natSumNatEquivNat.symm n) with
--    | .inl i => a i
--    | .inr i => b i

def alternating {X : Type} (a b : ℕ → X) (n : ℕ) : X := (Equiv.natSumNatEquivNat.symm n).elim a b


-- make this for disjoint MultiCover
-- #check SetLike
#check ENat.card_congr
#check ENat.card


-- the name is just a placeholder
lemma cw_greater_cardinal {ai : Type} {c : Cardinal} (c_infty : ℵ₀ ≤ c) (ai_c : ℵ₀ ≤ #ai → #ai ≤ c) : #ai ≤ c := by
        by_cases! aw : #ai < ℵ₀
        exact le_trans aw.le c_infty
        exact ai_c aw

instance : Add (CardMultiCover F c) where
  add a b := ⟨(a + b), by
    have ⟨ai,ai_c,as,as_spec⟩ := a.possible
    have ⟨bi,bi_c,bs,bs_spec⟩ := b.possible

    use ai ⊕ bi
    refine ⟨?_,?_⟩
    ·
      simp only [Cardinal.mk_sum, Cardinal.lift_id]
      intro infi
      -- this might could be a lemma
      have : ℵ₀ ≤ #ai ∨ ℵ₀ ≤ #bi := by exact Cardinal.aleph0_le_add_iff.mp infi
      have af := fun w ↦ le_trans w (ai_c w)
      have bf := fun w ↦ le_trans w (bi_c w)
      have c_infty := this.elim af bf


      exact Cardinal.add_le_of_le c_infty (cw_greater_cardinal c_infty ai_c) (cw_greater_cardinal c_infty bi_c)



    use fun n ↦ n.elim as bs
    change a.func + b.func = _
    rw [as_spec,bs_spec]
    funext x
    simp only [Pi.add_apply]
    rw [←ENat.card_sum]
    apply ENat.card_congr
    symm
    trans
    · apply Equiv.subtypeSum
    rfl

  ⟩

instance : AddCommSemigroup (CardMultiCover F c)  where
  add_assoc a b c := by
    change a + b + c = ⟨a + (b + c), _⟩
    ring_nf
    rfl
  add_comm a b := by
    change ⟨a + b, _⟩ = b + a
    rw [show b + a = ⟨b + a, _⟩ by rfl]
    simp only [CardMultiCover.mk.injEq]
    exact AddCommMagma.add_comm ⇑a ⇑b

-- Surely this already exists.


theorem CardMultiCover.hasEmpty_strict_cardinal [HasEmpty F] (h : ℵ₀ ≤ c) (f : X → ℕ∞) :
  (∃(ι : Type)(_ : ℵ₀ ≤ #ι → #ι ≤ c)(series: ι → F), f = fun x ↦ ENat.card {n | x ∈ series n})
  ↔ (∃(series: c.out → F), f = fun x ↦ ENat.card {n | x ∈ series n}) := by
  constructor
  ·
    rw [←Cardinal.mk_out c] at *
    intro ⟨ι, i_c, ser, ser_spec⟩


    have ll : #ι ≤ #c.out := cw_greater_cardinal h i_c

    have emb := ((Cardinal.le_def _ _).mp ll).some

    sorry

  sorry

-- instance [HasEmpty F] : Zero (MultiCover F c) where
--   zero := ⟨fun x ↦ 0, by

--     use fun i ↦ ∅
--     funext x
--     symm
--     rw [ENat.card_eq_zero_iff_empty]
--     have : x ∉ (∅ : F) := by
--       simp [←SetLike.mem_coe]
--       rw [HasEmpty.empty_is_empty]
--       exact fun a ↦ a
--     exact Subtype.isEmpty_of_false fun a ↦ this
--     ⟩

-- could be changed to embedding for free
noncomputable def emptyFun (X : Type): Empty → X := by
  -- there has to be an easier way to access this
  have : # Empty ≤ # X := by
    simp only [Cardinal.mk_eq_zero, zero_le]
  have emb := ((Cardinal.le_def _ _).mp this).some
  apply emb.toFun


instance : Zero (CardMultiCover F c) where
  zero := ⟨fun x ↦ 0, by
    use Empty
    simp only [Set.coe_setOf, Cardinal.mk_eq_zero, nonpos_iff_eq_zero, zero_le, implies_true,
      exists_const]
    use emptyFun _
    funext x
    rw [Eq.comm, ENat.card_eq_zero_iff_empty]
    exact instIsEmptySubtype fun n ↦ x ∈ emptyFun F n
    ⟩

instance : AddCommMonoid (CardMultiCover F c) where
  zero_add a := by
    rw [show 0 + a = ⟨0 + a,_⟩ by rfl]
    simp only [zero_add]
    rfl
  add_zero a := by
    rw [show a + 0 = ⟨a + 0,_⟩ by rfl]
    simp only [add_zero]
    rfl
  nsmul := nsmulRec


theorem CardMultiCover.add_fun_coe {a b : CardMultiCover F c} : ⇑(a + b) = ⇑a + ⇑b := by rfl
theorem CardMultiCover.zero_fun_coe : ⇑(0 : CardMultiCover F c) = 0 := by rfl



instance : LE (CardMultiCover F c) where
  le a b := (a : X → ℕ∞) ≤ (b : X → ℕ∞)
  -- le a b := LE.le (a : X → ℕ∞) (b : X → ℕ∞)

instance : Preorder (CardMultiCover F c) where
  le_refl a := by
    intro x
    exact Std.IsPreorder.le_refl _
  le_trans := by
    intro a b c ab bc x
    exact Std.IsPreorder.le_trans (a x) (b x) (c x) (ab x) (bc x)

-- instance : TopologicalSpace (CardMultiCover F c) := Preorder.topology _
-- local instance : TopologicalSpace ℕ∞ := Preorder.topology _

example : ℕ ≃ ℕ × ℕ := by exact Nat.pairEquiv.symm


-- issue: the result of the sum has a different type...
-- I should just let the cardinality be a property.

-- theorem CardMultiCover.hasSum {ι : Type} (s : ι → CardMultiCover F c) : HasSum s ⟨
--   (∑' n, ⇑(s n)),
--   by
--   -- let series n : F := Nat.pairEquiv



--   sorry
-- ⟩ := by sorry

-- theorem CardMultiCover.summable {ι : Type}  (s : ι → CardMultiCover F c) : Summable s := by sorry

-- theorem CardMultiCover.sum_coe {ι : Type}  (s : ι → CardMultiCover F c) : (∑' n, ⇑(s n)) = ⇑(∑' n, (s n)) := by

--   sorry

-- theorem CardMultiCover.sum {ι : Type}  (s : ι → CardMultiCover F c) (x : X) : (∑' n, (s n)) x = (∑' n, (s n x)) := by
--   -- rw [tsum]
--   -- apply ENNReal.tsum_apply
--   -- apply tsum_apply
--   -- rw [tsum_apply]
--   -- simp only [SummationFilter.support_eq_univ, Set.inter_univ, Set.indicator_univ]
--   sorry
end card_multi_cover


section exact_multi_cover

structure MultiCover {X : Type} (F : Type) [SetLike F X] where
  func (x : X) : ℕ∞
  possible: ∃(series: ℕ → F), func = fun x ↦ ENat.card {n // x ∈ series n}


instance : FunLike (MultiCover F) X ℕ∞ where
  coe := MultiCover.func
  coe_injective' := by
    intro a b fu
    change ⟨a.func,_⟩ = b
    simp only [fu]


noncomputable def MultiCover.series (a : MultiCover F) : ℕ → F := a.possible.choose

theorem MultiCover.series_def (a : MultiCover F) (x : X) : a x = ENat.card {n // x ∈ a.series n} := by
  change a.func x = _
  rw [a.possible.choose_spec]
  rfl

theorem MultiCover.series_def' (a : MultiCover F) : ⇑a = fun x ↦ ENat.card {n // x ∈ a.series n} := by
  funext x
  exact series_def a x


def MultiCover.mem_series (a : MultiCover F) (x : X) (n : ℕ) := x ∈ a.series n

theorem MultiCover.mem_series_def (a : MultiCover F) : ⇑a = fun x ↦ ENat.card {n // a.mem_series x n} := series_def' a


noncomputable def MultiCover.series_func (s : ℕ → F) (x : X) := ENat.card {n // x ∈ s n}

theorem MultiCover.series_def'' (a : MultiCover F) : ⇑a = series_func a.series := series_def' a

def MultiCover.mk' (f : X → ℕ∞) (p : ∃(series: ℕ → F), f = series_func series) : MultiCover F where
  func := f
  possible := p


instance : Membership X (MultiCover F) where
  mem f x := f x > 0


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
    apply (possible_equiv' Equiv.natSumNatEquivNat _ x)
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


-- in the future, use .lift?
-- #check Preorder.lift
-- interesting: #check CircularOrder

-- instance : Preorder (MultiCover F) := Preorder.lift (⇑)
instance : PartialOrder (MultiCover F) := PartialOrder.lift (⇑) (DFunLike.coe_injective')


variable [HasEmpty F]

-- MultiCover does not have a LinearOrder

local instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞
instance : OrderTopology ℕ∞ := by exact { topology_eq_generate_intervals := rfl }

-- local instance ww: TopologicalSpace (ℕ → ℕ∞) := by exact Pi.topologicalSpace
-- local instance www: TopologicalSpace (ℕ → ℕ∞) := Preorder.topology _



-- instance : OrderTopology (ℕ → ℕ∞) := by exact { topology_eq_generate_intervals := rfl }



-- instance : TopologicalSpace (MultiCover F) := by

--   exact Preorder.topology (MultiCover F)



--nevermind, unused.
lemma enat_HasSum_IsLUB {X : Type} (f : X → ℕ∞) (i : ℕ∞) (hf : IsLUB (Set.range fun s ↦ ∑ i ∈ s, f i) i) : HasSum f i := hasSum_of_isLUB_of_nonneg (α := ℕ∞) (f := f) (h := by simp only [zero_le, implies_true]) i hf

-- why is this not in Mathlib?
-- nevermind
theorem IsLUB_top {X : Type} [LE X] [OrderTop X] {s : Set X} (h : ⊤ ∈ s) : IsLUB s ⊤ := by
  unfold IsLUB IsLeast upperBounds lowerBounds
  simp_all only [Set.mem_setOf_eq, le_top, implies_true, and_self]


-- based on:
-- #check ENNReal.hasSum
theorem ENat.hasSum  {α : Type} (f : α → ℕ∞) : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

@[simp]
theorem ENat.summable {α : Type} (f : α → ℕ∞) : Summable f :=
  ⟨_, ENat.hasSum _⟩

theorem ENat.sum_with_top {α : Type}  {f : α → ℕ∞} (h : ∃n, f n = ⊤) : HasSum f ⊤ := by
  convert ENat.hasSum f
  symm
  apply ciInf_eq_top_of_top_mem
  simp only [Set.mem_range]
  obtain ⟨n, ns⟩ := h
  use {n}
  simp only [Finset.sum_singleton]
  exact ns

theorem ENat.sum_infinite_support_top {α : Type} (f : α → ℕ∞) (h : (Function.support f).Infinite) : HasSum f ⊤ := by
  convert ENat.hasSum f
  have tw (n : ℕ) : ∃(s : Finset α), ↑n ≤ ∑ i ∈ s, f i := by
    have ⟨s, s_s, sc⟩ := h.exists_subset_card_eq n
    use s
    rw [←sc]
    trans ∑ i ∈ s, 1
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, le_refl]
    have qqq (i) (hh : i ∈ s) : 1 ≤ f i := ENat.one_le_iff_ne_zero.mpr (s_s hh)
    exact Finset.sum_le_sum qqq
  set sc := fun s ↦ ∑ i ∈ s, f i
  change ∀(n : ℕ), ∃ s, ↑n ≤ sc s at tw
  symm
  apply ENat.eq_top_iff_forall_ge.mpr
  intro m
  have ⟨s,sw⟩ := tw (m)
  exact le_iSup_of_le s sw


#check tsum_apply


theorem ENat.hasSum_apply  {α β  : Type} (f : α → β → ℕ∞) : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

theorem ENat.sum_finite_support {α : Type} (f : α → ℕ∞) (hf : (f.support).Finite)
  : HasSum f (∑ a ∈ hf.toFinset, f a) := by
  convert ENat.hasSum f
  change (Finset.sum · f) hf.toFinset = iSup (Finset.sum · f)
  apply le_antisymm
  exact le_iSup_iff.mpr fun b a ↦ a hf.toFinset
  simp only [iSup_le_iff]
  intro s
  refine Finset.sum_le_sum_of_ne_zero ?_
  simp only [ne_eq, Set.Finite.mem_toFinset, Function.mem_support, imp_self, implies_true]

-- instance : TopologicalSpace (MultiCover F) := by

--   exact Preorder.topology (MultiCover F)

-- -- instance : SupSet (MultiCover F) := by

-- --   sorry

-- theorem MultiCover.hasSum_apply  {α : Type} (f : α → (MultiCover F)) : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
--   tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

-- -- instance : T2Space (MultiCover F) := sorry

theorem encard_sigma {X Y : Type} (hit : X → Y → Prop) :
  ∑' (a), ENat.card { b // hit a b } = ENat.card { ab : X × Y // hit ab.1 ab.2 }  := by
  symm

  set σ := (fun (a : X) ↦ { b // hit a b })

  trans ENat.card (Sigma σ)
  apply ENat.card_congr
  exact Equiv.subtypeProdEquivSigmaSubtype hit

  by_cases! h : ∃ a, ENat.card (σ a) = ⊤
  {
  trans ⊤
  ·
    simp only [ENat.card_eq_top] at h ⊢
    obtain ⟨a, aw⟩ := h
    exact Infinite.sigma_of_right (a := a)
  refine HasSum.tsum_eq ?_ |>.symm
  exact ENat.sum_with_top h
  }

  have h' : ∀ (a : X), Finite (σ a) := by
    simpa only [ne_eq, ENat.card_eq_top, not_infinite_iff_finite] using h
  clear h
  change _ = ∑' a, ENat.card (σ a)
  simp only [(ENat.card_eq_coe_natCard <| σ ·)]
  have q: {a | Nonempty (σ a)} = Function.support fun a ↦ (Nat.card (σ a) : ℕ∞) := by
    ext a
    simp only [Set.mem_setOf_eq, Function.mem_support, ne_eq, Nat.cast_eq_zero]
    simp only [iff_not_comm, not_nonempty_iff]
    exact Finite.card_eq_zero_iff


  have s_equiv : Sigma σ ≃ (Σ x : {a // Nonempty (σ a)}, σ x) := by
    refine (Equiv.sigmaSubtypeEquivOfSubset σ (fun a ↦ Nonempty (σ a)) ?_).symm
    exact fun _ ↦ Nonempty.intro

  rw [ENat.card_congr s_equiv]


  by_cases! hf : (fun a ↦ (Nat.card (σ a) : ℕ∞)).support.Finite
  {
    have hf' : {a | Nonempty (σ a)}.Finite := by convert hf
    have hf'' : Finite {a // Nonempty (σ a)} := hf'
    have hf''' : Fintype {a // Nonempty (σ a)} := Fintype.ofFinite _

    have : Finite (Sigma σ) := by
      apply Equiv.finite_iff s_equiv |>.mpr
      apply Finite.instSigma

    simp only [ENat.card_eq_coe_natCard]
    rw [Nat.card_sigma]


    have hfa : hf.toFinset = { a | Nonempty (σ a) } := by
      rw [q]
      exact Set.Finite.coe_toFinset hf

    have hfa' : hf.toFinset = { a // Nonempty (σ a) } := by exact congrArg Subtype hfa



    have hfaq : hf.toFinset = @Set.toFinset _ { a | Nonempty (σ a) } hf''' := by
      simp_all [σ]
      ext a : 1
      simp_all only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Nat.cast_eq_zero, nonempty_subtype,
        Set.mem_toFinset]
    symm
    refine HasSum.tsum_eq ?_
    convert ENat.sum_finite_support _ hf
    norm_cast
    let ss x := Nat.card (σ x)
    change ∑ x : { a // Nonempty (σ a) }, (ss ↑x) = ∑ x ∈ hf.toFinset, ss x
    rw [hfaq]

    convert Finset.sum_finset_coe ss ?_
    simp only [Set.coe_toFinset]
    rfl
    simp only [Set.coe_toFinset, Set.mem_setOf_eq]
  }

  change Set.Infinite _ at hf

  symm
  trans ⊤
  ·
    refine HasSum.tsum_eq ?_
    exact ENat.sum_infinite_support_top _ hf
  refine Eq.symm ((fun {α} ↦ ENat.card_eq_top.mpr) ?_)

  refine @Infinite.instSigmaOfNonempty _ _ ?_ ?_
  rw [←q] at hf
  exact { not_finite := hf }
  intro a
  simp_all only [nonempty_subtype, σ]
  obtain ⟨val, property⟩ := a
  simp_all only
  simp_all only [nonempty_subtype, σ]


noncomputable def MultiCover.sum (s : ℕ → MultiCover F) : MultiCover F where
  func := ∑' n, (s n).func
  possible := by
    use fun n ↦ (fun ab ↦ s ab.1 |>.series ab.2) (Nat.pairEquiv.symm n)
    change ∑' n, ⇑(s n) = _
    funext x
    rw [possible_equiv]
    simp only [series_def']
    rw [tsum_apply ⟨_, ENat.hasSum_apply _ ⟩]
    exact encard_sigma _




-- open Filter in
-- theorem MultiCover.summable_coe (s : ℕ → MultiCover F) : Summable (fun n ↦ ⇑(s n)) := by

--   -- use fun x ↦ _
--   constructor
--   rotate_left
--   use fun x ↦ ∑' n, ⇑(s n) x
--   unfold HasSum
--   simp only [SummationFilter.unconditional_filter]

--   unfold Tendsto
--   unfold map
--   rw [le_def]
--   simp only [Filter.mem_mk, Set.mem_preimage, Filter.mem_sets, mem_atTop_sets, ge_iff_le,
--     Finset.le_eq_subset]
--   intro x x_nhds


--   sorry

open scoped ENNReal

#check ENat.toENNRealOrderEmbedding

-- lemma enat_as_ennreal_tsum (f : ℕ → ℕ∞) : (tsum f).toENNReal = tsum (f · |>.toENNReal) := by



--   sorry

-- theorem MultiCover.hasSum (s : ℕ → MultiCover F) : HasSum s ⟨
--   (∑' n, ⇑(s n)),
--   by

--   let ser n := Function.uncurry (s · |>.series) (Nat.pairEquiv.symm n)
--   use ser
--   funext x

--   -- rw [tsum_apply]
--   #check ENNReal.tsum_apply
--   #check tsum_apply



--   simp only [series_def']
--   -- simp_rw [ENNReal.tsum_apply]



--   sorry
-- ⟩ := by sorry

end exact_multi_cover



end multi_cover
