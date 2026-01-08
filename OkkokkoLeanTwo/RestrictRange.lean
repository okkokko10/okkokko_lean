
import OkkokkoLeanTwo.Basic

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}

section restrict_range

def restrict_range (p : X → Prop) (a : ι → X) := Subtype.restrict (p ∘ a) a

#check Subtype.restrict_apply

@[simp]
theorem restrict_range.apply (p : X → Prop) (a : ι → X) (i : _)
  : restrict_range p a i = a ↑i
  := rfl
theorem restrict_range.comp (p : X → Prop) (a : ι → X) (e : ι' → { x // p (a x) }) (i : { x // p (a ↑(e x)) })
  : (restrict_range p a) (e i) = restrict_range p (a <| e ·) i
  := rfl
theorem restrict_range.comp' (p : X → Prop) (a : ι → X) (e : ι' → { x // (p ∘ a) x })
  : ((restrict_range p a) ∘ e) = fun i : ι' ↦ restrict_range p (a <| e ·) ⟨i,by
    simp only [Function.comp_apply]
    exact e i |>.prop
    ⟩
  := rfl

#check Subtype.coind


theorem restrict_range.comp_subtype (p p' : X → Prop) (a : ι → X)
  : Subtype (p ∘ restrict_range p' a) = @Subtype (Subtype (p' ∘ a)) (p ∘ a ∘ Subtype.val)
  := rfl
@[simp]
theorem restrict_range.comp_subtype' (p p' : X → Prop) (a : ι → X)
  : (p ∘ restrict_range p' a) = (p ∘ a ∘ Subtype.val)
  := rfl

theorem restrict_range.and (p p' : X → Prop) (a : ι → X) i
  : restrict_range p (restrict_range p' a) i = restrict_range (fun x ↦ p x ∧ p' x) a ⟨i.val, ⟨i.2, i.1.2⟩⟩
  := rfl

@[simp]
theorem restrict_range.idempotent (p : X → Prop) (a : ι → X)
  : restrict_range p (restrict_range p a) = fun i ↦ restrict_range p a i.val
  := rfl

end restrict_range


def removed_empties' [EmptyCollection X] (a : ι → X)
  : {i : ι // ¬ a i = ∅} → X
  := restrict_range (¬ · = ∅) a
def removed_empties  (a : ι → Set X)
  -- : {i : ι // Set.Nonempty (a i)} → X
  := restrict_range (Set.Nonempty) a

theorem removed_empties.def {a : ι → Set X}
  : removed_empties a = restrict_range (Set.Nonempty) a
  := by rfl
