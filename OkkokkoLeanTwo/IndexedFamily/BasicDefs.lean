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


end basic

end IndexedFamily
