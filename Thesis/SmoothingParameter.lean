import Thesis.Gaussians

open scoped NNReal ENNReal
noncomputable section
-- let's add Nonempty ι as well. it's possible some statements don't account for 0D lattices.
variable {ι : Type*} [Fintype ι] [Nonempty ι] --(B : Basis ι)

variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

local instance (s : ℝ≥0) [NeZero s] : NeZero s⁻¹ := .mk fun cont ↦ NeZero.out (inv_eq_zero.mp cont)

/--
η
-/
def 𝓛.smoothing_parameter (ε : ℝ≥0) [NeZero ε] : ℝ≥0
  := sInf ({s | ∃(_ : NeZero s), 𝓛.latticeGaussianMeasure (𝓛.dualLattice Λ) s⁻¹ 0 {0}ᶜ ≤ ε})

theorem 𝓛.smoothing_parameter.positive (ε : ℝ≥0) [NeZero ε] : NeZero (Λ.smoothing_parameter ε) := by
  -- definition 2.5 asserts this.
  sorry


-- simple: as ε grows, the set under infimum grows
theorem 𝓛.smoothing_parameter.antitone (ε : ℝ≥0) (ε' : ℝ≥0) [NeZero ε] [NeZero ε']
  (le : ε ≤ ε'):
  Λ.smoothing_parameter ε' ≤ Λ.smoothing_parameter ε
  := by
    -- have : Antitone (fun (e : (Set.Ioi 0 : Set ℝ≥0)) ↦
    --   let : NeZero (e : ℝ≥0) := ⟨by aesop⟩
    --   Λ.smoothing_parameter e) := sorry
    unfold smoothing_parameter
    refine csInf_le_csInf' ?_ ?_

    sorry
    simp only [Set.setOf_subset_setOf, forall_exists_index]
    intro s ns p
    use ns
    set w := (Λ.dualLattice.latticeGaussianMeasure s⁻¹ 0) {0}ᶜ
    have : (ε : ℝ≥0∞ ) ≤ ε' := by exact ENNReal.coe_le_coe.mpr le
    exact Std.IsPreorder.le_trans w (↑ε) (↑ε') p this
