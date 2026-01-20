import OkkokkoLeanTwo.IndexedFamily.Basic
namespace IndexedFamily

universe u v v' v''

variable {X : Type u}

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

end IndexedFamily
