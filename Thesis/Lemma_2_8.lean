import Thesis.MyLattice
import Thesis.SmoothingParameter
import Thesis.Statistic
import Thesis.Gaussians
import Thesis.StatisticalDistance
import Thesis.LatticeQuot


open scoped NNReal ENNReal
open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
variable (Λ' : 𝓛 ι) [DiscreteTopology Λ'] [IsZLattice ℝ Λ']


#check 𝓛.gaussianDistribution Λ

#check HasQuotient


theorem corollary_2_8 (Λ' : 𝓛 ι) [DiscreteTopology Λ'] [IsZLattice ℝ Λ']
  (sub : Λ' ≤ Λ)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0)
  (s_prop :  Λ'.smoothing_parameter ε ≤ s)
  (c : ι → ℝ) :
  have : NeZero s := sorry; -- by s_prop which states s is ≥ a positive value
  statisticalDistance ( 𝓛.mod_distribution Λ' (𝓛.discreteGaussianProbability Λ s c)) (𝓛.quot_uniform _ _ sub) ≤ 2 * ε
  := sorry
