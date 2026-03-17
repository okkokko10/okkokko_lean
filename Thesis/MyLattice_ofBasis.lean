import Mathlib
import Thesis.Casts

noncomputable section


open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] --(B : Basis ι)


-- abbrev 𝓛 ι := Submodule ℤ (ι → ℝ)



variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section lattices




open Module

-- shows that for a Λ, there exists a ℝⁿ basis B that generates Λ.
example :
  let B : Module.Basis ι ℝ (ι → ℝ) := (IsZLattice.basis Λ).ofZLatticeBasis ℝ Λ;
  Submodule.span ℤ (Set.range B) = Λ
  := (IsZLattice.basis Λ).ofZLatticeBasis_span ℝ

section ofBasis

abbrev 𝓛.ofBasis (B : Basis ι ℝ (ι → ℝ)) : 𝓛 ι := Submodule.span ℤ (Set.range B)

/--arbitrary basis -/
noncomputable def 𝓛.toBasis : Basis ι ℝ (ι → ℝ) := (IsZLattice.basis Λ).ofZLatticeBasis ℝ
@[simp]
theorem 𝓛.ofBasis_of_toBasis : ofBasis Λ.toBasis = Λ := Basis.ofZLatticeBasis_span ℝ Λ (IsZLattice.basis Λ)

theorem Casts.Zn_ofBasis : Casts.Zn ι = 𝓛.ofBasis (Pi.basisFun ℝ ι) := by
  unfold 𝓛.ofBasis
  ext x
  rw [Casts.Zn.exist]
  rw [Module.Basis.mem_span_iff_repr_mem]
  simp only [algebraMap_int_eq, Int.coe_castRingHom, Pi.basisFun_repr, Set.mem_range]


instance (ι : Type*) [Fintype ι] [DecidableEq ι] :  DiscreteTopology (Casts.Zn ι) := by
  rw [Casts.Zn_ofBasis]
  exact ZSpan.discreteTopology_pi_basisFun
instance (ι : Type*) [Fintype ι] [DecidableEq ι] :  IsZLattice ℝ (Casts.Zn ι) := by
  convert instIsZLatticeRealSpan (Pi.basisFun ℝ ι) -- convert is unreasonably effective
  exact Casts.Zn_ofBasis


#check Quotient.ind
theorem 𝓛.basis_ind
  {motive : (𝓛 ι) → Prop}
  (prf : (B : Basis ι ℝ (ι → ℝ)) → motive (𝓛.ofBasis B))
  : motive Λ := Λ.ofBasis_of_toBasis ▸ prf (Λ.toBasis)

theorem 𝓛.basis_ind'
  {motive : (Λ : 𝓛 ι) → (_ : DiscreteTopology ↥Λ) → (IsZLattice ℝ Λ) → Prop}
  : ((a : Basis ι ℝ (ι → ℝ)) → motive (𝓛.ofBasis a) (
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite a) (instIsZLatticeRealSpan a)
    )
  → (Λ : 𝓛 ι) → (dt : DiscreteTopology ↥Λ) → (zl: IsZLattice ℝ Λ) → motive Λ dt zl :=
  sorry

end ofBasis
