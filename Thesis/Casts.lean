import Mathlib

namespace Casts

abbrev IntSubgroup := AddSubgroup.zmultiples (1 : ℝ)
abbrev IntSubmodule := IntSubgroup.toIntSubmodule

abbrev Zn (ι : Type*) := (AddSubgroup.toIntSubmodule (((Int.castAddHom ℝ).compLeft ι).range ))

abbrev Zn_to_Zqn {ι : Type*} {q : ℕ} : (ι → ℤ) →ₗ[ℤ] (ι → ZMod q)  := by
  exact (Algebra.linearMap ℤ (ZMod q)).compLeft ι

abbrev Zn_to_Rn {ι : Type*} : (ι → ℤ) →ₗ[ℤ] (ι → ℝ)  := by
  exact (Algebra.linearMap ℤ ℝ).compLeft ι
