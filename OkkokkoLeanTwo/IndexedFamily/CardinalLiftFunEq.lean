import Mathlib

universe u v v' v''

variable {X : Type u}

variable (f : X → Cardinal.{v}) (g : X → Cardinal.{v'}) (h : X → Cardinal.{v''})

abbrev CardinalLiftFunEq : Prop := Cardinal.lift.{v'} ∘ f = Cardinal.lift.{v} ∘ g
-- same priority as Equiv

namespace CardinalLiftFunEq
/-- same function to Cardinal in different universes.

Cardinal.lift.{v'} ∘ f = Cardinal.lift.{v} ∘ g -/
infixl:25 " =cl " => CardinalLiftFunEq

@[simp↓]
theorem same {f g : X → Cardinal.{v}} : f =cl g ↔ f = g := by
  unfold CardinalLiftFunEq
  refine ⟨?_,?_⟩
  simp_all only [funext_iff, Function.comp_apply, Cardinal.lift_id, implies_true]
  intro a
  subst a
  rfl
--@[simps]


variable {f g h}
@[refl]
theorem refl : f =cl f := by rfl

@[symm]
theorem symm  : f =cl g ↔ g =cl f :=
  { mp := fun a ↦ (Eq.symm a), mpr := fun a ↦ (Eq.symm a) }

@[trans]
theorem trans  : f =cl g → g =cl h → f =cl h := by
  unfold CardinalLiftFunEq
  intro a b
  simp_all only [funext_iff, Function.comp_apply]
  simp_all only [← Cardinal.lift_umax_eq.{_, _, max v v' v''}, implies_true]


theorem funext_iff  : f =cl g ↔ ∀x, Cardinal.lift.{v'} (f x) = Cardinal.lift.{v} (g x) := by
  unfold CardinalLiftFunEq
  simp only [_root_.funext_iff, Function.comp_apply]

theorem funext  : (∀x, Cardinal.lift.{v'} (f x) = Cardinal.lift.{v} (g x)) → f =cl g := funext_iff.mpr

end CardinalLiftFunEq
