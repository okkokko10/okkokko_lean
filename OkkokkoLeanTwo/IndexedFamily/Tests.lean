import OkkokkoLeanTwo.IndexedFamily.Basic
import OkkokkoLeanTwo.IndexedFamily.BasicDefs
import OkkokkoLeanTwo.IndexedFamily.Equivalence
import OkkokkoLeanTwo.IndexedFamily.CardQuotient

namespace IndexedFamily

universe v v' v'' u

variable {X : Type u}

#check equivalence.preimageCard_iff


-- this could be expanded upon. instead of Cardinal, it uses the quotient of some other equivalence.
example {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
  : f ≃' g ↔ Nonempty (∀s : Set X, (f.snd ⁻¹' s) ≃ (g.snd ⁻¹' s)) := equivalence.iff_elementwise_equiv_sets f g
