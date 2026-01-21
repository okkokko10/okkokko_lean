import Mathlib
import OkkokkoLeanTwo.IndexedFamily.CardinalLiftFunEq

universe v v' v'' u

variable {X : Type u}

open scoped CardinalLiftFunEq



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

def preimageCard (f : IndexedFamily.{v} X) (x : Set X) : Cardinal.{v}
  := Cardinal.mk (f.snd ⁻¹' x)


#check Setoid.ker

def elemCard (f : IndexedFamily X) (x : X) : Cardinal.{v} := preimageCard f {x}


irreducible_def equivalence (f : IndexedFamily.{v} X) (g : IndexedFamily.{v'} X) : Prop
  := f.elemCard =cl g.elemCard

infixl:25 " ≃' " => equivalence
theorem equivalence.elemCard_iff {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
  : f ≃' g ↔ f.elemCard =cl g.elemCard := by simp only [equivalence_def]


end IndexedFamily
