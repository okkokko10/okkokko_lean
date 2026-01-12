import OkkokkoLeanTwo.Addition.PermSetoid


universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}


variable {a : ι → X} {b : ι' → X}

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

abbrev IndexedFamily (X : Type u) := (ι : Type v) × (ι → X)
namespace IndexedFamily

variable (f : IndexedFamily X)

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

def setoid (X : Type u) : Setoid (IndexedFamily X) :=
  Setoid.ker (preimageCard)


def quotient  := Quotient (setoid X)

-- todo: further quotients where IndexedFamilies are given equivalences, like disjoint union additivity
-- restriction could just be that f is equated with restrict p f.



-- theorem setoid_equiv

end IndexedFamily
