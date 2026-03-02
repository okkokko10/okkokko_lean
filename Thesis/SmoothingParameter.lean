import Thesis.Gaussians

open scoped NNReal ENNReal
noncomputable section

variable {ι : Type*} [Fintype ι] --(B : Basis ι)

variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

local instance (s : ℝ≥0) [NeZero s] : NeZero s⁻¹ := .mk fun cont ↦ NeZero.out (inv_eq_zero.mp cont) in

/--
η
-/
def 𝓛.smoothing_parameter (ε : ℝ≥0) [NeZero ε]
  := ⨅ (s : ℝ≥0) (_ : NeZero s)
  (_ : 𝓛.gaussianMeasure' (𝓛.dualLattice Λ) s⁻¹ 0 (Set.compl {0}) ≤ ε), s
