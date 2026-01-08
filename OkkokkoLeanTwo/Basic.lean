import Mathlib.Tactic

namespace Basic_variables
universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}


@[simp]
theorem _root_.ENat.card_false : ENat.card { _i : ι // False} = 0 := by
  rw [ENat.card_eq_zero_iff_empty]
  exact Subtype.isEmpty_false

end Basic_variables
