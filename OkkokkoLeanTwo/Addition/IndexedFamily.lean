import Mathlib

universe u v v' v''

variable {X : Type u}

section func_lift_eq
variable {X : Sort*}
variable (f : X → Cardinal.{v}) (g : X → Cardinal.{v'}) (h : X → Cardinal.{v''})


abbrev _root_.func_lift_eq : Prop := Cardinal.lift.{v'} ∘ f = Cardinal.lift.{v} ∘ g
-- same priority as Equiv
/-- same function to Cardinal in different universes.

Cardinal.lift.{v'} ∘ f = Cardinal.lift.{v} ∘ g -/
infixl:25 " =cl " => func_lift_eq

@[simp↓]
theorem _root_.func_lift_eq.same {f g : X → Cardinal.{v}} : f =cl g ↔ f = g := by
  unfold func_lift_eq
  refine ⟨?_,?_⟩
  simp_all only [funext_iff, Function.comp_apply, Cardinal.lift_id, implies_true]
  intro a
  subst a
  rfl
--@[simps]


variable {f g h}
@[refl]
theorem _root_.func_lift_eq.refl : f =cl f := by rfl

@[symm]
theorem _root_.func_lift_eq.symm  : f =cl g ↔ g =cl f :=
  { mp := fun a ↦ (Eq.symm a), mpr := fun a ↦ (Eq.symm a) }

@[trans]
theorem _root_.func_lift_eq.trans  : f =cl g → g =cl h → f =cl h := by
  unfold func_lift_eq
  intro a b
  simp_all only [funext_iff, Function.comp_apply]
  simp_all only [← Cardinal.lift_umax_eq.{_, _, max v v' v''}, implies_true]


theorem _root_.func_lift_eq.funext_iff  : f =cl g ↔ ∀x, Cardinal.lift.{v'} (f x) = Cardinal.lift.{v} (g x) := by
  unfold func_lift_eq
  simp only [_root_.funext_iff, Function.comp_apply]

theorem _root_.func_lift_eq.funext  : (∀x, Cardinal.lift.{v'} (f x) = Cardinal.lift.{v} (g x)) → f =cl g := funext_iff.mpr

end func_lift_eq


#check MulEquiv

-- a ↪ b -- should mean a is less than b
#check RelEmbedding
#check Setoid.ker
-- a = b ∘ toFun
-- ∀i, a i = b (toFun i)
-- #check a ↪r b


-- structure SubReordering (a : ι → X) (b : ι' → X) extends ι ↪ ι' where
--   uee : a = b ∘ (toFun)

-- infixr:25 " ↪f " => SubReordering

-- theorem SubReordering.ff (e : SubReordering a b) (i) :
--   a i = b (e i)
--   := sorry



-- structure Reordering (a : ι → X) (b : ι' → X) extends ι ≃ ι' where
--   uee : a = b ∘ (toFun)

-- -- todo: in Embedding.arrowCongrLeft the equals is flipped
-- def perm (a : ι → X) (b : ι' → X) : Prop
--   := ∃(e : _ ≃ _), a = b ∘ e

open scoped Function

@[pp_with_univ]
abbrev IndexedFamily (X : Type u) := (ι : Type v) × (ι → X)
namespace IndexedFamily

-- variable (f : IndexedFamily X)

def preimageCard (f : IndexedFamily.{u,v} X) (x : Set X) : Cardinal.{v}
  := Cardinal.mk (f.snd ⁻¹' x)


#check Setoid.ker

def elemCard (f : IndexedFamily X) (x : X) : Cardinal.{v} := preimageCard f {x}


irreducible_def equivalence (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X) : Prop
  := f.elemCard =cl g.elemCard

infixl:25 " ≃' " => equivalence
theorem equivalence.elemCard_iff {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  : f ≃' g ↔ f.elemCard =cl g.elemCard := by simp only [equivalence_def]

lemma elemCard_preimageCard_iff (f g : IndexedFamily X)
  : f.preimageCard =cl g.preimageCard ↔ f.elemCard =cl g.elemCard
  := by
    unfold elemCard preimageCard
    refine ⟨?_,?_⟩
    {
      rw [func_lift_eq.funext_iff]
      rw [func_lift_eq.funext_iff]
      intro w x
      exact (w {x})
    }
    rw [func_lift_eq.funext_iff]
    rw [func_lift_eq.funext_iff]
    intro w s
    simp_rw [Cardinal.lift_mk_eq'] at w ⊢
    refine ⟨?_⟩
    change {i // f.snd i ∈ s} ≃ {i // g.snd i ∈ s}

    have tf: { i // f.snd i ∈ s } ≃ Σ (x : s), { i // f.snd i = x } := by
      refine (Equiv.sigmaSubtypeFiberEquivSubtype f.snd ?_).symm
      simp only [implies_true]
    have tg: { i // g.snd i ∈ s } ≃ Σ (x : s), { i // g.snd i = x } := by
      refine (Equiv.sigmaSubtypeFiberEquivSubtype g.snd ?_).symm
      simp only [implies_true]
    apply Equiv.trans tf
    symm
    apply Equiv.trans tg
    symm
    refine Equiv.sigmaCongr ?_ fun a ↦ ?_
    exact Equiv.refl _
    simp only [Equiv.refl_apply]
    apply (w a).some


theorem equivalence.preimageCard_iff {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  : f ≃' g ↔ f.preimageCard =cl g.preimageCard := by rw [equivalence.elemCard_iff,elemCard_preimageCard_iff f g]


section restrict
-- noncomputable def IndexedFamily.preimage_card.restrict (p : Set X → Prop) (f : IndexedFamily X) : Set X → Cardinal.{v}
--   := Set.indicator p f.preimage_card
  -- := open scoped Classical in if p x then preimage_card f x else 0


def preimageCard_restrict (p : Set X) (f : IndexedFamily.{u,v} X) (x : Set X) : Cardinal.{v}
  := preimageCard f (p ∩ x)

-- theorem preimage_card.restrict.as

def elemCard_restrict (p : Set X) (f : IndexedFamily X) (x : X) : Cardinal.{v} := preimageCard_restrict p f {x}

theorem elemCard_preimageCard_iff_restrict (p : Set X) (f g : IndexedFamily X)
  : f.preimageCard_restrict p = g.preimageCard_restrict p ↔ f.elemCard_restrict p = g.elemCard_restrict p
  := by sorry

-- def restrict (p : Set X) (f : IndexedFamily X) : IndexedFamily X := ⟨_, restrict_range p f.snd⟩
end restrict
-- #check fun p ↦ (· = ·) on (preimage_card_restrict p)

-- todo: further quotients where IndexedFamilies are given equivalences, like disjoint union additivity
-- restriction could just be that f is equated with restrict p f.
-- for some things, equate countable and uncountable.


-- theorem setoid_equiv :

-- this file describes how to define homomorphisms:
-- #check DFunLike
-- also could this be used for quotient? quotient.out

-- #check Equiv

section equivalence_iffs


lemma equivalence.iff_elementwise_equiv_sets (f g : IndexedFamily X)
  : f ≃' g ↔ Nonempty (∀(x : Set X), ↑(f.snd ⁻¹' x) ≃ ↑(g.snd ⁻¹' x))
  := by
  rw [equivalence.preimageCard_iff]
  simp only [funext_iff]
  unfold preimageCard
  constructor
  {
    exact fun fg ↦ ⟨fun x ↦ (Cardinal.lift_mk_eq'.mp (fg x)).some⟩
  }
  intro ⟨ee⟩ x
  apply Cardinal.lift_mk_eq'.mpr ⟨ee x⟩

theorem equivalence.iff_elementwise_equiv (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X)
  : f ≃' g ↔ Nonempty (∀(x : X), ↑(f.snd ⁻¹' {x}) ≃ ↑(g.snd ⁻¹' {x}))
  := by
  rw [equivalence.elemCard_iff]
  simp only [funext_iff]
  unfold elemCard preimageCard
  simp only [Function.comp_apply]
  constructor
  {
    intro fg
    refine ⟨?_⟩
    intro x
    exact (Cardinal.lift_mk_eq'.mp (fg x)).some
  }
  intro ⟨ee⟩ x
  apply Cardinal.lift_mk_eq'.mpr ⟨ee x⟩


lemma equivalence.iff_elementwise_equiv_fiber (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X)
  :  f ≃' g ↔ Nonempty (∀(x : X), {i // f.snd i = x} ≃ {i // g.snd i = x})
  := by
    rw [equivalence.iff_elementwise_equiv]
    obtain ⟨fst, snd⟩ := f
    obtain ⟨fst_1, snd_1⟩ := g
    simp_all only
    rfl

open scoped Function

theorem equivalence.iff_equiv (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X)
  :  f ≃' g ↔ ∃e : _ ≃ _, g.snd ∘ e = f.snd
  := by
  rw [equivalence.iff_elementwise_equiv_fiber]
  constructor
  {
    intro ⟨ee⟩
    refine ⟨?_,?_⟩
    apply Equiv.ofFiberEquiv (γ := X) (g := g.snd) (f := f.snd) ee
    funext x
    simp only [Function.comp_apply]
    exact Equiv.ofFiberEquiv_map _ _
  }
  intro ⟨e,e_p⟩
  refine ⟨?_⟩
  intro x
  apply Equiv.subtypeEquiv e
  exact fun a ↦ Eq.congr (congrFun (id (Eq.symm e_p)) a) rfl

#check Equiv.ofFiberEquiv_apply

-- structure EquivF (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X) extends (f.fst ≃ g.fst) where
--   isComp' : g.snd ∘ toFun = f.snd
-- instance (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X) : EquivLike (EquivF f g) f.fst g.fst :=

def equivalence.asSubtype (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X)
  :=  {e : f.fst ≃ g.fst // g.snd ∘ e = f.snd}

-- infixl:25 " ≃ " => equivalence.asSubtype
-- theorem equivalence.subtype_iff {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
--   :  f ≃' g ↔ Nonempty (f ≃ g) := Trans.simple (iff_equiv f g) (Iff.symm nonempty_subtype)



noncomputable def equivalence.equiv {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  (e' : f ≃' g) : f.fst ≃ g.fst := Equiv.ofFiberEquiv (equivalence.iff_elementwise_equiv_fiber _ _ |>.mp e').some

theorem equivalence.equiv_map {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  (e' : f ≃' g) : g.snd ∘ e'.equiv = f.snd := by
  funext x
  simp only [Function.comp_apply]
  exact Equiv.ofFiberEquiv_map _ x

-- I wonder, is it possible to use coe to automatically convert propositions

theorem equivalence.ofEquiv {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  (e : f.fst ≃ g.fst) (h : g.snd ∘ e = f.snd) : f ≃' g := iff_equiv f g |>.mpr ⟨e,h⟩

variable {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X} {h : IndexedFamily.{u,v''} X}

@[refl]
theorem equivalence.refl (f : IndexedFamily.{u,v} X) : f ≃' f := by
  apply ofEquiv (Equiv.refl _) rfl

@[symm]
theorem equivalence.symm  : f ≃' g → g ≃' f := by
  intro w
  refine ofEquiv w.equiv.symm ?_
  have := equiv_map w
  exact (Equiv.comp_symm_eq w.equiv g.snd f.snd).mpr (id (Eq.symm this))

@[trans]
theorem equivalence.trans  : f ≃' g → g ≃' h → f ≃' h := by
  intro fg gh
  have := fg.equiv.trans gh.equiv
  refine ofEquiv (fg.equiv.trans gh.equiv) ?_
  rw [←fg.equiv_map, ← gh.equiv_map]
  rfl





end equivalence_iffs
section basic

def basic.zero : IndexedFamily.{u,v} X := ⟨ULift Empty,Empty.elim ∘ ULift.down⟩
def basic.add (f : IndexedFamily.{u,v} X) ( g : IndexedFamily.{u,v'} X) : IndexedFamily X := ⟨_,Sum.elim f.snd g.snd⟩
def basic.hAdd {Y : Type*} (f : IndexedFamily X) ( g : IndexedFamily Y) : IndexedFamily (X ⊕ Y) := ⟨_,Sum.map f.snd g.snd⟩


-- could be called "flatten"
-- (f : (ι' : Type v') × (ι' → (ι : Type v) × (ι → X)))
def basic.nestSum  (f : IndexedFamily.{_, v'} (IndexedFamily.{_, v} X)) : IndexedFamily.{_, _} X
  := ⟨Σi : f.fst, (f.snd i).fst, fun m ↦ (f.snd m.fst).snd m.snd⟩
  -- := ⟨Sigma fun i ↦ (f.snd i).fst, fun m ↦ (f.snd m.fst).snd m.snd⟩


-- todo: equivalence over two nested IF, with their nesting levels provided

def basic.mulCard (c : Cardinal.{v'})  (f : IndexedFamily.{u,v} X) : IndexedFamily X
  := ⟨c.out × f.fst, fun m ↦ f.snd m.2⟩
def basic.mulCard' (t : Type v')  (f : IndexedFamily.{u,v} X) : IndexedFamily X
  := ⟨f.fst × t, fun m ↦ f.snd m.1⟩

def basic.image {Y : Type*} (func : X → Y) (f : IndexedFamily.{u,v} X) : IndexedFamily.{_, v} Y :=
  ⟨f.fst, func ∘ f.snd⟩
def basic.multiImage.{u'} {Y : Type u'} (func : X → IndexedFamily.{u',v'} Y) (f : IndexedFamily.{u,v} X) : IndexedFamily.{u', max v v'} Y :=
  nestSum (image func f)

#check CanLift
-- #check Subgroup.transferFunction
#check Preorder.lift

-- todo: consider stricter IndexedFamily equivalences that preserve some additional property.

def basic.singleton' (x : X) : IndexedFamily.{u,v} X := ⟨ULift (Fin 1), fun _ ↦ x⟩
def basic.singleton (x : X) : IndexedFamily.{u,0} X := ⟨ULift (Fin 1), fun _ ↦ x⟩
def basic.univ: IndexedFamily X := ⟨X, id⟩
def basic.univ' (X : Type u) : IndexedFamily X := univ
def basic.ofSet (s : Set X) : IndexedFamily X := ⟨Subtype s, Subtype.val⟩
-- theorem basic.univ_ofSet : univ X ≈ ofSet (Set.univ) := by
--   sorry



-- ∑x ∈ univ, (ec x) • {x}
def basic.ofElemCard (ec : X → Cardinal.{v}) : IndexedFamily X := multiImage (fun x ↦ mulCard (ec x) (singleton x) ) univ

theorem basic.ofElemCard_elemCard (ec : X → Cardinal.{v}) : (ofElemCard ec).elemCard =cl ec
  := by
  funext x
  simp only [Function.comp_apply]
  unfold ofElemCard elemCard  preimageCard -- multiImage nestSum image

  -- simp only [Function.comp_apply]
  -- todo: mulCard's preimageCard is multiplied


  sorry

-- this is trivial from the earlier.
theorem basic.elemCard_ofElemCard (f : IndexedFamily.{u,v} X) : (ofElemCard f.elemCard).elemCard =cl f.elemCard := ofElemCard_elemCard f.elemCard


-- todo: [X * Y] : IndexedFamily X * IndexedFamily Y

instance basic.instZero : Zero (IndexedFamily X) where zero := basic.zero
instance basic.instAdd : Add (IndexedFamily X) where add := basic.add
instance basic.instAddZero : AddZero (IndexedFamily X) := {}
def basic.instAdd_univ : HAdd (IndexedFamily X) (IndexedFamily X) (IndexedFamily X) where hAdd := basic.add
def basic.instHAdd {Y : Type*}: HAdd (IndexedFamily X) (IndexedFamily Y) (IndexedFamily (X ⊕ Y)) where hAdd := basic.hAdd


def Sum_elim_preimage_equiv {α β : Type*} {X : Type u} (a : α → X) (b : β → X) (x : Set X) :
  ↑(a ⁻¹' x) ⊕ ↑(b ⁻¹' x) ≃ ↑(Sum.elim a b ⁻¹' x) where
  toFun := Sum.elim (fun w ↦ ⟨.inl w.val, w.property⟩) (fun w ↦ ⟨.inr w.val, w.property⟩)
  invFun := by
    intro ⟨ab,e⟩
    cases ab with
    | inl af => refine .inl ⟨af, e⟩
    | inr bf => refine .inr ⟨bf, e⟩
  left_inv := by
    unfold Function.LeftInverse
    simp only [Sum.forall, Sum.elim_inl, Subtype.coe_eta, implies_true, Sum.elim_inr, and_self]
  right_inv := by
    unfold Function.RightInverse Function.LeftInverse
    simp only [Subtype.forall, Set.mem_preimage, Sum.forall, Sum.elim_inl, implies_true,
      Sum.elim_inr, and_self]

-- #check Functor

@[simp]
theorem Sum_elim_preimage_equiv.vals {α β : Type*} {X : Type u} (a : α → X) (b : β → X) (x : Set X) :
  ∀q,  Subtype.val ((Sum_elim_preimage_equiv a b x) q) = (Sum.map (Subtype.val) (Subtype.val)) q
  := by
  intro q
  unfold Sum_elim_preimage_equiv
  simp only [Equiv.coe_fn_mk]
  cases q with
  | inl af => simp only [Sum.map_inl, Sum.elim_inl]
  | inr bf => simp only [Sum.map_inr, Sum.elim_inr]


def preimageCard.addHom : AddHom (IndexedFamily.{u,v} X) (Set X → Cardinal) where
  toFun := IndexedFamily.preimageCard
  map_add' a b := by
    unfold preimageCard
    funext x
    simp only [Pi.add_apply]
    rw [Cardinal.add_def]
    rw [Cardinal.eq]
    refine ⟨(Sum_elim_preimage_equiv a.snd b.snd x).symm⟩





def elemCard.addHom : AddHom (IndexedFamily.{u,v} X) (X → Cardinal) where
  toFun := IndexedFamily.elemCard
  map_add' a b := by
    unfold elemCard
    funext x
    convert_to (a + b).preimageCard {x} = (a.preimageCard + b.preimageCard) {x}
    apply congrFun
    apply preimageCard.addHom.map_add




def preimageCard.zeroHom : ZeroHom (IndexedFamily.{u,v} X) (Set X → Cardinal) where
  toFun := IndexedFamily.preimageCard
  map_zero' := by
    unfold preimageCard
    funext x
    simp only [Pi.zero_apply]
    refine Cardinal.mk_emptyCollection_iff.mpr ?_
    ext q
    apply q.down.elim


def elemCard.zeroHom : ZeroHom (IndexedFamily.{u,v} X) (X → Cardinal) where
  toFun := IndexedFamily.elemCard
  map_zero' := by
    unfold elemCard
    funext x
    simp only [Pi.zero_apply]
    refine Cardinal.mk_emptyCollection_iff.mpr ?_
    ext q
    apply q.down.elim

instance preimageCard.addMonoidHom : AddMonoidHom (IndexedFamily.{u,v} X) (Set X → Cardinal) where
  toFun := IndexedFamily.preimageCard
  map_zero' := zeroHom.map_zero
  map_add' := addHom.map_add


instance elemCard_addMonoidHom : AddMonoidHom (IndexedFamily.{u,v} X) (X → Cardinal) where
  toFun := IndexedFamily.elemCard
  map_zero' := elemCard.zeroHom.map_zero
  map_add' := elemCard.addHom.map_add

theorem equivalence.elemCard_addMonoid_iff {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  : f ≃' g ↔ elemCard_addMonoidHom f =cl elemCard_addMonoidHom g := by simp only [equivalence_def,
    elemCard_addMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]


end basic

section quotient

#check Equiv.symm

instance setoid {X : Type u} : Setoid (IndexedFamily X) where
  r := equivalence
  iseqv := {
    refl := equivalence.refl
    symm := equivalence.symm
    trans := equivalence.trans
  }

-- def setoid {X : Type u} : Setoid (IndexedFamily X) :=
--   Setoid.ker (preimageCard)

theorem setoid.equ {f g : IndexedFamily X} : setoid f g ↔ f ≃' g := by rfl

def quotient  := Quotient (setoid (X := X))

@[simp]
lemma quotient.equ {f g : IndexedFamily.{u,v} X} : (⟦f⟧ : quotient) = ⟦g⟧ ↔ f ≃' g := by
  simp only [Quotient.eq, ← setoid.equ]

@[simp]
lemma quotient.equ' {f g : IndexedFamily.{u,v} X} : f ≈ g ↔ f ≃' g := by
  simp only [← setoid.equ]
  simp only [HasEquiv.Equiv]

-- theorem basic.equivalence.add (f : IndexedFamily.{u,v} X) ( g : IndexedFamily.{u,v'} X) : basic.add f g


instance quotient.instAddZeroClass: AddZeroClass (@quotient.{u,v} X) where
  add := Quotient.lift₂ (fun a b ↦ ⟦a + b⟧) <| by
    simp only
    intro a1 b1 a2 b2 ae be
    apply equ.mpr
    simp only [equ'] at ae be
    simp only [equivalence.elemCard_addMonoid_iff, ↓func_lift_eq.same, map_add] at *
    simp_all only
  zero := ⟦0⟧
  zero_add := by
    apply Quotient.ind
    intro a
    change Quotient.lift₂ (fun a b ↦ ⟦a + b⟧) _ ⟦0⟧ ⟦a⟧ = ⟦a⟧
    simp only [Quotient.lift_mk, quotient.equ]
    simp only [equivalence.elemCard_addMonoid_iff, ↓func_lift_eq.same]
    simp only [map_add, map_zero, zero_add]
  add_zero := by
    apply Quotient.ind
    intro a
    change Quotient.lift₂ (fun a b ↦ ⟦a + b⟧) _ ⟦a⟧ ⟦0⟧ = ⟦a⟧
    simp only [Quotient.lift_mk, quotient.equ]
    simp only [equivalence.elemCard_addMonoid_iff, ↓func_lift_eq.same]
    simp only [map_add, map_zero, add_zero]
instance quotient.instAddCommMonoid: AddCommMonoid (@quotient.{u,v} X) where
  add_assoc := by
    intro a b c
    cases a using Quotient.ind
    cases b using Quotient.ind
    cases c using Quotient.ind
    rename_i a b c
    -- simp [· + ·,Add.add]
    apply equ.mpr
    simp only [equivalence.elemCard_addMonoid_iff, ↓func_lift_eq.same]
    simp only [map_add]
    group
  add_comm a b := by
    cases a using Quotient.ind
    cases b using Quotient.ind
    rename_i a b
    change ⟦a + b⟧ = ⟦b + a⟧
    simp only [quotient.equ]
    simp only [equivalence.elemCard_addMonoid_iff, ↓func_lift_eq.same]
    simp only [map_add]
    group
  nsmul := nsmulRec

instance basic.smul : SMul Cardinal (IndexedFamily X) where
  smul := basic.mulCard
-- lemma basic.smul.def (c : Cardinal.{v}) (f : IndexedFamily.{u,v} X)
--   : c • f = ⟨f.fst × c.out, fun m ↦ f.snd m.1⟩ := by rfl

/-- it's weird that this didn't exist -/
noncomputable instance _root_.Cardinal.one_unique : Unique (Quotient.out (1 : Cardinal.{v})) := by
    have : (1 : Cardinal.{v}).out ≃ PUnit.{v+1} := by
      change (1 : Cardinal.{v}).out ≃ PUnit.{v + 1}
      refine Cardinal.eq.mp ?_ |>.some
      simp only [Cardinal.mk_out, Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one]
    apply Equiv.unique this

open Cardinal in
instance quotient.instModule : Module Cardinal.{v} (@quotient.{u,v} X) where
  smul c := Quotient.map (basic.mulCard c) <| by
    intro a b ab
    simp only [quotient.equ'] at *
    -- change basic.mulCard c a ≃' basic.mulCard c b
    unfold basic.mulCard
    refine equivalence.ofEquiv ?_ ?_
    simp only
    exact Equiv.prodCongr (Equiv.refl _) ab.equiv
    simp only [id_eq]
    have := ab.equiv_map
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl]
    funext x
    simp only [Function.comp_apply, Prod.map_snd]
    simp [funext_iff] at this
    simp_all only

  one_smul := by
    apply Quotient.ind
    intro a
    simp only [HSMul.hSMul, Quotient.map_mk]
    apply equ.mpr
    unfold basic.mulCard
    refine equivalence.ofEquiv ?_ ?_
    simp only
    exact Equiv.uniqueProd a.fst _
    funext x
    simp only [id_eq, Equiv.coe_uniqueProd, Function.comp_apply]
  mul_smul x y := by
    apply Quotient.ind
    intro a
    cases x using Quotient.ind
    cases y using Quotient.ind
    rename_i x y
    simp only [HSMul.hSMul, Quotient.map_mk]
    apply equ.mpr
    unfold basic.mulCard
    simp only
    refine equivalence.ofEquiv ?_ ?_
    simp only
    simp [· * ·,Mul.mul,Cardinal.map₂]
    have txy: (⟦x × y⟧ : Cardinal).out ≃ x × y := by
      apply Cardinal.outMkEquiv
    have tx: x ≃ (⟦x⟧ : Cardinal).out := by
      apply Cardinal.outMkEquiv.symm
    have ty: y ≃ (⟦y⟧ : Cardinal).out := by
      apply Cardinal.outMkEquiv.symm
    have t1: (⟦x × y⟧ : Cardinal).out × a.fst ≃ x × y × a.fst  := by
      trans
      exact Equiv.prodCongrLeft fun a ↦ txy
      exact Equiv.prodAssoc x y a.fst
    trans
    exact t1
    have t2 : y × a.fst ≃ (⟦y⟧ : Cardinal).out × a.fst := Equiv.prodCongrLeft fun a ↦ ty
    exact Equiv.prodCongr tx t2
    simp only [id_eq, Equiv.coe_trans, Equiv.prodCongr_apply]
    ext x
    simp only [Function.comp_apply, Equiv.prodAssoc_apply, Prod.map_apply,
      Equiv.prodCongrLeft_apply]
    congr
  smul_zero := by
    -- apply Quotient.ind
    intro c
    simp only [HSMul.hSMul]
    apply equ.mpr
    unfold basic.mulCard
    symm
    refine equivalence.ofEquiv ?_ ?_
    -- todo: an element is in 0 iff its domain is 0
    simp only
    symm
    refine (fun w ↦ @Equiv.equivOfIsEmpty _ _ (by simp only [isEmpty_prod, w, or_true]) w) ?_
    reduce
    simp only [isEmpty_ulift]
    exact Empty.instIsEmpty
    funext x
    reduce at x
    simp_all only [id_eq, Function.comp_apply]
    have fwd : Empty := x.down
    have fwd_1 : False := Aesop.BuiltinRules.empty_false fwd
    simp_all only
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry



-- X * Y = ∑x : X, x * Y = ∑x : X, (x * ·) '' Y
def basic.mul {Y Z : Type*} (m : X → Y → Z) (f : IndexedFamily X) (g : IndexedFamily Y) : IndexedFamily Z
  := multiImage (fun x ↦ image (m x) g) f

-- todo: mul where x * x = x, x * y = 0


#check LinearMap
-- theorem basic.mul_linear

end quotient

end IndexedFamily
