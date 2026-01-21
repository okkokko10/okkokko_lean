import OkkokkoLeanTwo.IndexedFamily.BasicDefs

namespace IndexedFamily

universe v v' v'' u

variable {X : Type u}

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


def preimageCard.addHom : AddHom (IndexedFamily.{v} X) (Set X → Cardinal) where
  toFun := IndexedFamily.preimageCard
  map_add' a b := by
    unfold preimageCard
    funext x
    simp only [Pi.add_apply]
    rw [Cardinal.add_def]
    rw [Cardinal.eq]
    refine ⟨(Sum_elim_preimage_equiv a.snd b.snd x).symm⟩





def elemCard.addHom : AddHom (IndexedFamily.{v} X) (X → Cardinal) where
  toFun := IndexedFamily.elemCard
  map_add' a b := by
    unfold elemCard
    funext x
    convert_to (a + b).preimageCard {x} = (a.preimageCard + b.preimageCard) {x}
    apply congrFun
    apply preimageCard.addHom.map_add




def preimageCard.zeroHom : ZeroHom (IndexedFamily.{v} X) (Set X → Cardinal) where
  toFun := IndexedFamily.preimageCard
  map_zero' := by
    unfold preimageCard
    funext x
    simp only [Pi.zero_apply]
    refine Cardinal.mk_emptyCollection_iff.mpr ?_
    ext q
    apply q.down.elim


def elemCard.zeroHom : ZeroHom (IndexedFamily.{v} X) (X → Cardinal) where
  toFun := IndexedFamily.elemCard
  map_zero' := by
    unfold elemCard
    funext x
    simp only [Pi.zero_apply]
    refine Cardinal.mk_emptyCollection_iff.mpr ?_
    ext q
    apply q.down.elim

instance preimageCard.addMonoidHom : AddMonoidHom (IndexedFamily.{v} X) (Set X → Cardinal) where
  toFun := IndexedFamily.preimageCard
  map_zero' := zeroHom.map_zero
  map_add' := addHom.map_add


instance elemCard_addMonoidHom : AddMonoidHom (IndexedFamily.{v} X) (X → Cardinal) where
  toFun := IndexedFamily.elemCard
  map_zero' := elemCard.zeroHom.map_zero
  map_add' := elemCard.addHom.map_add

theorem equivalence.elemCard_addMonoid_iff {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
  : f ≃' g ↔ elemCard_addMonoidHom f =cl elemCard_addMonoidHom g := by simp only [equivalence_def,
    elemCard_addMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
