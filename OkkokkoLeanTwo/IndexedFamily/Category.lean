import OkkokkoLeanTwo.IndexedFamily.Basic
import OkkokkoLeanTwo.IndexedFamily.BasicDefs
import OkkokkoLeanTwo.IndexedFamily.Hom
import OkkokkoLeanTwo.IndexedFamily.Equivalence
namespace IndexedFamily

universe v v' v'' u

variable {α : Type u}


namespace category
open CategoryTheory
#check Category

-- #check Grp

#check equivalence.equiv_map

instance instCategory : Category (IndexedFamily.{v} α) where
  Hom A B := {e : A.fst → B.fst // A.snd = B.snd ∘ e}
  id A := ⟨id,rfl⟩
  comp ab bc := ⟨bc.val ∘ ab.val, by
    have t1:= ab.property
    have t2:= bc.property
    simp only [t1, t2]
    rfl
    ⟩
  id_comp := fun {X_2 Y} f ↦ rfl
  comp_id := fun {X_2 Y} f ↦ rfl
  assoc {A B C D} ab bc cd := rfl
-- #check equivalence.asSubtype

noncomputable example (A B : IndexedFamily α) (h : A ≃' B) : (A ≅ B) where
  hom := ⟨h.equiv,h.equiv_map.symm⟩
  inv := ⟨h.equiv.symm,(Equiv.eq_comp_symm h.equiv B.snd A.snd).mpr (equivalence.equiv_map h)⟩
  hom_inv_id := by
    simp only [CategoryStruct.comp, Equiv.symm_comp_self]
    rfl
  inv_hom_id := by
    simp only [CategoryStruct.comp, Equiv.self_comp_symm]
    rfl
-- #check SemiRingCat
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (IndexedFamily.{v} α) where
  tensorObj A B := sorry
  whiskerLeft := sorry
  whiskerRight := sorry
  tensorUnit := sorry
  associator := sorry
  leftUnitor := sorry
  rightUnitor := sorry
-- instance instMonoidalCategory : MonoidalCategory (IndexedFamily.{v} X) where




end category
