import OkkokkoLeanTwo.Addition.PermSetoid


universe u v v' v''

variable {X : Type u}



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

-- noncomputable def IndexedFamily.preimage_card.restrict (p : Set X → Prop) (f : IndexedFamily X) : Set X → Cardinal.{v}
--   := Set.indicator p f.preimage_card
  -- := open scoped Classical in if p x then preimage_card f x else 0


def preimageCard_restrict (p : Set X) (f : IndexedFamily.{u,v} X) (x : Set X) : Cardinal.{v}
  := preimageCard f (p ∩ x)

-- theorem preimage_card.restrict.as


#check Setoid.ker

def elemCard (f : IndexedFamily X) (x : X) : Cardinal.{v} := preimageCard f {x}
def elemCard_restrict (p : Set X) (f : IndexedFamily X) (x : X) : Cardinal.{v} := preimageCard_restrict p f {x}

theorem elemCard_preimageCard_iff (f g : IndexedFamily X)
  : f.preimageCard = g.preimageCard ↔ f.elemCard = g.elemCard
  := by sorry

theorem elemCard_preimageCard_iff_restrict (p : Set X) (f g : IndexedFamily X)
  : f.preimageCard_restrict p = g.preimageCard_restrict p ↔ f.elemCard_restrict p = g.elemCard_restrict p
  := by sorry

def restrict (p : Set X) (f : IndexedFamily X) : IndexedFamily X := ⟨_, restrict_range p f.snd⟩

-- #check fun p ↦ (· = ·) on (preimage_card_restrict p)

def setoid {X : Type u} : Setoid (IndexedFamily X) :=
  Setoid.ker (preimageCard)


def quotient  := Quotient (setoid (X := X))

-- todo: further quotients where IndexedFamilies are given equivalences, like disjoint union additivity
-- restriction could just be that f is equated with restrict p f.
-- for some things, equate countable and uncountable.


-- theorem setoid_equiv :

-- this file describes how to define homomorphisms:
#check DFunLike
-- also could this be used for quotient? quotient.out

#check Equiv

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

def basic.mulCard (f : IndexedFamily.{u,v} X) (c : Cardinal.{v'}) : IndexedFamily X
  := ⟨f.fst × c.out, fun m ↦ f.snd m.1⟩
def basic.mulCard' (f : IndexedFamily.{u,v} X) (t : Type v') : IndexedFamily X
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

def basic.ofElemCard (ec : X → Cardinal.{v}) : IndexedFamily X := multiImage (fun x ↦ mulCard (singleton x) (ec x)) univ

theorem basic.ofElemCard_elemCard (ec : X → Cardinal.{v}) : (ofElemCard ec).elemCard = Cardinal.lift ∘ ec
  := by
  funext x
  simp only [Function.comp_apply]
  unfold ofElemCard elemCard
  sorry

-- X * Y = ∑x : X, x * Y = ∑x : X, (x * ·) '' Y
def basic.mul {Y Z : Type*} (m : X → Y → Z) (f : IndexedFamily X) (g : IndexedFamily Y) : IndexedFamily Z
  := multiImage (fun x ↦ image (m x) g) f


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


instance elemCard.addMonoidHom : AddMonoidHom (IndexedFamily.{u,v} X) (X→ Cardinal) where
  toFun := IndexedFamily.elemCard
  map_zero' := zeroHom.map_zero
  map_add' := addHom.map_add





end basic

end IndexedFamily
