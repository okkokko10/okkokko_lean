import Mathlib

namespace Casts

abbrev IntSubgroup := AddSubgroup.zmultiples (1 : ℝ)
abbrev IntSubmodule := IntSubgroup.toIntSubmodule

abbrev Zn (ι : Type*) := (AddSubgroup.toIntSubmodule (((Int.castAddHom ℝ).compLeft ι).range ))

abbrev Zn_to_Zqn {ι : Type*} {q : ℕ} : (ι → ℤ) →ₗ[ℤ] (ι → ZMod q)  := by
  exact (Algebra.linearMap ℤ (ZMod q)).compLeft ι

abbrev Zn_to_Rn {ι : Type*} : (ι → ℤ) →ₗ[ℤ] (ι → ℝ)  := by
  exact (Algebra.linearMap ℤ ℝ).compLeft ι

theorem IntSubmodule.exist (x) : x ∈ IntSubmodule ↔ ∃i : ℤ, i = x := by
  change x ∈ (Set.range fun x ↦ x • 1) ↔ ∃ i : ℤ, ↑i = x
  simp only [zsmul_eq_mul, mul_one, Set.mem_range]

theorem Zn_pi {ι : Type*} : Zn ι = Submodule.pi Set.univ (fun _ => Casts.IntSubmodule) := by
  unfold Zn IntSubmodule IntSubgroup
  ext w
  simp only [Submodule.mem_pi, Set.mem_univ, forall_const]
  change
    w ∈ ((Int.castAddHom ℝ).compLeft ι).range ↔
      ∀ (i : ι), w i ∈ (AddSubgroup.zmultiples 1)
  simp only [AddMonoidHom.mem_range]
  constructor
  intro ⟨x,xw⟩ i
  sorry


  sorry
