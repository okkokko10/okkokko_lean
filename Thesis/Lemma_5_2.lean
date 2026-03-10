import Thesis.A_Matrix
import Thesis.Lemma_5_1
import Thesis.SmoothingParameter
import Thesis.A_Matrix_Lattice
import Thesis.Statistic
import Thesis.Zqn


noncomputable section
open scoped NNReal ENNReal


theorem lemma_5_2 {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) (ass : lemma_5_1_statement A)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0)
  (s_prop :  𝓛.smoothing_parameter (A.Λ_ortho') ε ≤ s) :
  have : NeZero s := sorry; -- by s_prop which states s is ≥ a positive value
  statistical_distance (A.syndrome_distributed (int_gaussian m s)) (uniform_over_Zqn _ _) ≤ 2 * ε
  := sorry

theorem lemma_5_2_furthermore {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) (ass : lemma_5_1_statement A)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0)
  (s_prop : 𝓛.smoothing_parameter (A.Λ_ortho') ε ≤ s) (u : Fin n → ZMod q) (t : Fin m → ℤ) (ht : A.syndrome_map t = u)
  :
  have : NeZero s := sorry;
  -- ProbabilityTheory.cond (int_gaussian m hs) (A.syndrome_map ⁻¹' {u}) = t +ᵥ (int_gaussian_sublattice m hs A.Λ_ortho (-t))
  ProbabilityTheory.cond (int_gaussian m s) (A.syndrome_map ⁻¹' {u}) = (int_gaussian_sublattice m s A.Λ_ortho (-t)).map (f := (· + t)) (AEMeasurable.of_discrete)
  := sorry
