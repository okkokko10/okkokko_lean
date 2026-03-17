import Mathlib

abbrev Zqn (n q : ℕ) := (Fin n → ZMod q)
namespace Casts

abbrev IntSubgroup := AddSubgroup.zmultiples (1 : ℝ)
abbrev IntSubmodule := IntSubgroup.toIntSubmodule

abbrev Zn (ι : Type*) := (AddSubgroup.toIntSubmodule (((Int.castAddHom ℝ).compLeft ι).range ))

abbrev Intn_to_Zqn {ι : Type*} {q : ℕ} : (ι → ℤ) →ₗ[ℤ] (ι → ZMod q)  := by
  exact (Algebra.linearMap ℤ (ZMod q)).compLeft ι

abbrev Intn_to_Rn {ι : Type*} : (ι → ℤ) →ₗ[ℤ] (ι → ℝ)  := by
  exact (Algebra.linearMap ℤ ℝ).compLeft ι

theorem IntSubmodule.exist (x) : x ∈ IntSubmodule ↔ ∃i : ℤ, i = x := by
  change x ∈ (Set.range fun x ↦ x • 1) ↔ ∃ i : ℤ, ↑i = x
  simp only [zsmul_eq_mul, mul_one, Set.mem_range]


theorem Zn.eq_compLeftRange {ι : Type*} : Zn ι = (AddSubgroup.toIntSubmodule (((Int.castAddHom ℝ).compLeft ι).range )) := by rfl

theorem Zn.eq_pi {ι : Type*} : Zn ι = Submodule.pi Set.univ (fun _ => Casts.IntSubmodule) := by
  unfold Zn IntSubmodule IntSubgroup
  ext w
  simp only [Submodule.mem_pi, Set.mem_univ, forall_const]
  change
    w ∈ ((Int.castAddHom ℝ).compLeft ι).range ↔
      ∀ (i : ι), w i ∈ (AddSubgroup.zmultiples 1)
  simp only [AddMonoidHom.mem_range]
  constructor
  · intro ⟨x,xw⟩ i
    rw [←funext_iff.mp xw i]
    simp only [AddMonoidHom.compLeft_apply, Int.coe_castAddHom, Function.comp_apply,
      AddSubgroup.intCast_mem_zmultiples_one]
  intro aw
  use fun i ↦ (aw i).choose
  funext i
  rw [←(aw i).choose_spec]
  simp only [zsmul_eq_mul, mul_one, AddMonoidHom.compLeft_apply, Int.coe_castAddHom,
    Function.comp_apply]

theorem Zn.exist {ι : Type*} (x) : x ∈ Zn ι ↔ ∀i, ∃z : ℤ, z = x i := by
  rw [Zn.eq_pi]
  simp only [Submodule.mem_pi, Set.mem_univ, forall_const]
  simp_rw [IntSubmodule.exist]

theorem Zn.pi_single_mem {ι : Type*} [DecidableEq ι] (i i' : ι) : ((Pi.single (M := fun _ => ℝ) i (1 : ℝ) i') : ℝ) ∈ Casts.IntSubmodule := by
  rw [Pi.single_apply]
  change _ ∈ IntSubgroup
  split
  exact AddSubgroup.mem_zmultiples 1
  exact AddSubgroup.zero_mem IntSubgroup


theorem Zn.eq_Intn_to_Rn_range  {ι : Type*} : Zn ι = LinearMap.range Intn_to_Rn := by
  rw [Zn.eq_compLeftRange]
  rfl



noncomputable def IntnToZn {ι : Type*} : (ι → ℤ) ≃ₗ[ℤ] Zn (ι) := by
  rw [Zn.eq_Intn_to_Rn_range]
  #check LinearEquiv.range
  apply LinearEquiv.ofInjective (f := Intn_to_Rn)
  unfold Intn_to_Rn
  intro a b ab
  rw [funext_iff] at ab ⊢
  intro i
  specialize ab i
  simpa only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply,
    algebraMap_int_eq, eq_intCast, Int.cast_inj] using ab



theorem IntnToZn_apply  {ι : Type*} (x : ι → ℤ) : (IntnToZn x).val = (↑) ∘ x := rfl


noncomputable abbrev ZnToZqn {ι : Type*} {q : ℕ} : (Zn ι) →ₗ[ℤ] (ι → ZMod q)  := by
  -- refine LinearMap.comp ?_ ?_
  refine Casts.Intn_to_Zqn ∘ₗ  IntnToZn.symm.toLinearMap
