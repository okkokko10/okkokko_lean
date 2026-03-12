import Thesis.MyLattice
import Thesis.SmoothingParameter
import Thesis.Statistic
import Thesis.Gaussians


open scoped NNReal ENNReal
open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
variable (Λ' : 𝓛 ι) [DiscreteTopology Λ'] [IsZLattice ℝ Λ']


-- it doesn't seem like Λ' as a submodule of Λ is considered a lattice: the superspace is not ℝⁿ, but Λ

def 𝓛.quot (Λ' : 𝓛 ι)
  := Λ ⧸ (Λ'.submoduleOf Λ)

-- note this:
#check Submodule.submoduleOfEquivOfLe
#check IsZLattice
instance  : MeasurableSpace (Λ.quot Λ') := ⊤


instance [sub : Fact (Λ' ≤ Λ)] : Finite (Λ.quot Λ') := by
  unfold 𝓛.quot
  -- #check Submodule.quotientEquivPiZMod
  have same_finrank : Module.finrank ℤ ↥(Submodule.submoduleOf Λ' Λ) = Module.finrank ℤ ↥Λ := (by
    rw [ZLattice.rank ℝ Λ, ←ZLattice.rank ℝ Λ']
    apply LinearEquiv.finrank_eq
    exact Submodule.submoduleOfEquivOfLe sub.elim
    )
  have decomp := Submodule.quotientEquivPiZMod (Λ'.submoduleOf Λ) (ι := ι) (IsZLattice.basis Λ) same_finrank

  refine Finite.of_equiv (h := ?_) _ decomp.symm.toEquiv

  refine @Pi.finite _ _ inferInstance ?_
  intro i
  apply @ZMod.fintype _ ?_ |>.finite
  constructor
  rw [Int.natAbs_ne_zero]

  exact Submodule.smithNormalFormCoeffs_ne_zero
    (IsZLattice.basis Λ) same_finrank i






instance : Nonempty (Λ.quot Λ') := Nonempty.intro (Submodule.Quotient.mk 0)


noncomputable def 𝓛.quot_uniform (sub : (Λ' ≤ Λ)) : ProbabilityMeasure (Λ.quot Λ') :=
  have := Fact.mk sub
  ⟨ProbabilityTheory.uniformOn Set.univ,
  ProbabilityTheory.uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty⟩


abbrev 𝓛.mod (Λ' : 𝓛 ι) {S : 𝓛 ι} : S → S.quot Λ' := Submodule.Quotient.mk

-- set_option trace.Meta.synthInstance true in
variable {Λ} in
noncomputable def 𝓛.mod_distribution (e : ProbabilityMeasure Λ) : ProbabilityMeasure (Λ.quot Λ')
  := e.map (f := 𝓛.mod Λ') (AEMeasurable.of_discrete)


#check 𝓛.gaussianDistribution Λ

#check HasQuotient


theorem corollary_2_8 (Λ' : 𝓛 ι) [DiscreteTopology Λ'] [IsZLattice ℝ Λ']
  (sub : Λ' ≤ Λ)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0)
  (s_prop :  Λ'.smoothing_parameter ε ≤ s)
  (c : ι → ℝ) :
  have : NeZero s := sorry; -- by s_prop which states s is ≥ a positive value
  statistical_distance ( 𝓛.mod_distribution Λ' (𝓛.discreteGaussianProbability Λ s c)) (𝓛.quot_uniform _ _ sub) ≤ 2 * ε
  := sorry
