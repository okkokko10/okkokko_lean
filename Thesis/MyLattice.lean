import Mathlib
import Thesis.Casts

noncomputable section


open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] --(B : Basis ι)


abbrev 𝓛 ι := Submodule ℤ (ι → ℝ)



variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section lattices



def dualLattice_basic : AddSubgroup (ι → ℝ) where
  carrier := { x : ι → ℝ | ∀ v ∈ Λ, x ⬝ᵥ v ∈ Casts.IntSubmodule}
  add_mem' := by
    intro a b ha hb v hL
    specialize ha v hL
    specialize hb v hL
    rw [add_dotProduct]
    exact AddMemClass.add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq, zero_dotProduct, zero_mem, implies_true]
  neg_mem' := by
    simp only [Set.mem_setOf_eq, neg_dotProduct, neg_mem_iff, imp_self, implies_true]

def 𝓛.dualLattice : 𝓛 ι := (dualLattice_basic Λ).toIntSubmodule


lemma 𝓛.dualLattice.mem_def' (x : ι → ℝ) :
  x ∈ (dualLattice Λ) ↔
  ∀ v ∈ Λ,  x ∈ Casts.IntSubmodule.comap (dotProductBilin ℤ ℤ v) := by
    unfold dualLattice dualLattice_basic
    simp only [Submodule.mem_comap, dotProductBilin_apply_apply, dotProduct_comm]
    rfl

lemma 𝓛.dualLattice.mem_def''.step1 (v : ι → ℝ) :
  Submodule.comap (dotProductBilin ℤ ℤ v) Casts.IntSubmodule
  = ZLattice.comap ℝ Casts.IntSubmodule (dotProductBilin ℝ ℝ v)
  := by
    apply SetLike.coe_set_eq.mp
    ext y
    simp only [Submodule.comap_coe, AddSubgroup.coe_toIntSubmodule, Set.mem_preimage,
      dotProductBilin_apply_apply, SetLike.mem_coe, ZLattice.coe_comap]

#check instIsZLatticeComap




theorem 𝓛.dualLattice.involution : Function.Involutive (𝓛.dualLattice (ι := ι)) := sorry

-- #check ZSpan

def 𝓛.minimum_distance [NormedAddCommGroup (ι → ℝ)] : ℝ≥0 := ⨅ (x ∈ Λ) (_ : x ≠ 0), ‖x‖₊

/-
paper:
The minimum distance λ1(Λ) of a lattice Λ is the length (in the Euclidean `2 norm, unless otherwise
indicated) of its shortest nonzero vector: λ1(Λ) = min06=x∈Λkxk. More generally, the ith successive
minimum λi(Λ) is the smallest radius r such that Λ contains i linearly independent vectors of norm at
most r. We write λ∞
1
to denote the minimum distance measured in the ∞ norm (which is defined as ‖x‖∞ = max |xᵢ|).
-/
-- i or more
def successive_minimum_distance [Norm (ι → ℝ)] (i : ℕ)
  := ⨅ (r : ℝ≥0) (_ : ∃s ⊆ (Λ.carrier), LinearIndependent ℝ (Subtype.val : s → _) ∧ s.encard ≤ i ∧ ∀x ∈ s, ‖x‖ ≤ r), r
-- note: for i := 0 this is ⊥ and i := 1 this is 0
def successive_minimum_distance' [Norm (ι → ℝ)] (i : ℕ)
  := ⨅ (s ⊆ (Λ.carrier)) (_ : LinearIndependent ℝ (Subtype.val : s → _)) (_ : s.encard ≤ i), ⨆x ∈ s, ‖x‖

-- def dualLattice

def infinity_norm : NormedAddCommGroup (ι → ℝ) := Pi.normedAddCommGroup

/-- λ₁∞ -/
def 𝓛.minimum_distance_sup := @𝓛.minimum_distance ι _ Λ (infinity_norm)

theorem 𝓛.minimum_distance.positive
  -- (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology ↥Λ]
  (h : Λ ≠ ⊥) : NeZero (𝓛.minimum_distance Λ) := by
  -- relies on the fact that Λ has elements other than 0, and nnnorm_eq_zero, and that Λ is discrete
  constructor
  unfold 𝓛.minimum_distance
  have tw (x : ι → ℝ) : ‖x‖₊ = 0 → x = 0 := nnnorm_eq_zero.mp
  #check IsZLattice

  simp only [ne_eq]
  #check NNReal.instConditionallyCompleteLinearOrderBot
  #check ConditionallyCompleteLinearOrderBot
  #check ConditionallyCompleteLattice
  change ¬(⨅x, ⨅ (_ : x ∈ Λ), ⨅ (_ : ¬x = 0), ‖x‖₊) = 0

  intro asm
  #check InfSet




  sorry



end lattices
