import Mathlib

#check Asymptotics.IsLittleO
open Asymptotics MeasureTheory
open ProbabilityTheory
open scoped NNReal ENNReal
#check ℙ

noncomputable section statistic

-- f(x) = ω(g(x))
notation:100 f " =ω[" l "] " g:100 => g =o[l] f
notation:100 f " =ω " g:100 => g =o[Filter.atTop] f

def negligible {R : Type*} [Norm R] (f : ℕ → R) := ∀(c : ℕ), c > 0 → f =o[Filter.atTop] (fun (n : ℕ) ↦ (n : ℝ) ^ (-(c : ℝ)))

-- #check ProbabilityTheory.HasPDF
#check MeasureTheory.pdf

--- [https://www.cs.bu.edu/~reyzin/teaching/s11cs937/notes-leo-1.pdf]


#check PMF


#check MeasureTheory.SignedMeasure.totalVariation -- Gemini found this.


-- I need to explain this
def statistical_distance' {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D) := (2⁻¹) * (SignedMeasure.totalVariation (X.toMeasure.toSignedMeasure - Y.toMeasure.toSignedMeasure)) Set.univ
lemma statistical_distance_finite_1 {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D)
  : IsFiniteMeasure ((X.toMeasure.toSignedMeasure - Y.toMeasure.toSignedMeasure).totalVariation) := isFiniteMeasureAdd
lemma statistical_distance_finite_2 {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D)
  : statistical_distance' X Y < ∞ := by
    unfold statistical_distance'
    refine ENNReal.mul_lt_top ?_ ?_
    simp only [ENNReal.inv_lt_top, Nat.ofNat_pos]
    exact @measure_lt_top _ _ _ (statistical_distance_finite_1 X Y) Set.univ

def statistical_distance {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D) : ℝ≥0 := statistical_distance' X Y |>.toNNReal

instance : Norm ℝ≥0 := ⟨(↑)⟩
#check EMetricSpace
example {D : Type*} [MeasurableSpace D] : PseudoMetricSpace (ProbabilityMeasure D) where
  dist := (statistical_distance' · · |>.toReal)
  dist_self x := by
    rw [statistical_distance', sub_self, SignedMeasure.totalVariation_zero]
    bound
  dist_comm x y := by
    unfold statistical_distance'
    rw [← SignedMeasure.totalVariation_neg _, neg_sub]
  dist_triangle x y z := by

    have f a b := ne_top_of_lt  <| @measure_lt_top D _ _ (statistical_distance_finite_1 a b) Set.univ
    have fxy := f x y
    have fxz := f x z
    have fyz := f y z
    -- simp only [statistical_distance_finite_1, measure_lt_top]
    unfold statistical_distance' at *

    set x' := x.toMeasure.toSignedMeasure
    set y' := y.toMeasure.toSignedMeasure
    set z' := z.toMeasure.toSignedMeasure

    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at *

    field_simp
    rw [←ENNReal.toReal_add fxy fyz]
    -- unfold SignedMeasure.totalVariation
    -- simp only [Measure.coe_add, Pi.add_apply, ne_eq, ENNReal.add_eq_top, measure_ne_top, or_self,
    --   not_false_eq_true, ENNReal.toReal_le_toReal]


    suffices
      ((x' - z').totalVariation Set.univ) ≤
      ((x' - y').totalVariation Set.univ) + ((y' - z').totalVariation Set.univ) by
      simp_all only [ne_eq, not_false_eq_true, ENNReal.add_eq_top, or_self, ENNReal.toReal_le_toReal, x', y', z']
    clear f
    set U := Set.univ
    revert U
    suffices
      ∀U, MeasurableSet U →
      (x' - y').totalVariation U ≠ ⊤ →
        (x' - z').totalVariation U ≠ ⊤ →
          (y' - z').totalVariation U ≠ ⊤ →
            (x' - z').totalVariation U ≤ (x' - y').totalVariation U + (y' - z').totalVariation U by
      exact this Set.univ (MeasurableSet.univ)

    intro U mU fxy fxz fyz
    clear fxy fxz fyz


    unfold SignedMeasure.totalVariation
    simp only [Measure.coe_add, Pi.add_apply]

    -- #check JordanDecomposition.mutuallySingular (x' - z').toJordanDecomposition
    have ⟨sxz, m_sxz, l_sxz, r_sxz, pos0_xz, neg0_xz⟩:= JordanDecomposition.exists_compl_positive_negative (x' - z').toJordanDecomposition
    have ⟨sxy, m_sxy, l_sxy, r_sxy, pos0_xy, neg0_xy⟩:= JordanDecomposition.exists_compl_positive_negative (x' - y').toJordanDecomposition
    have ⟨syz, m_syz, l_syz, r_syz, pos0_yz, neg0_yz⟩:= JordanDecomposition.exists_compl_positive_negative (y' - z').toJordanDecomposition

    -- simp_all only [ne_eq, SignedMeasure.toSignedMeasure_toJordanDecomposition,
    --   VectorMeasure.restrict_sub, VectorMeasure.restrict_zero, tsub_le_iff_right, zero_add,
    --   sub_nonneg, ge_iff_le]

    set xz := (x' - z').toJordanDecomposition
    set xy := (x' - y').toJordanDecomposition
    set yz := (y' - z').toJordanDecomposition


    #check MeasurableSet

    simp only [ge_iff_le]
    #check measure_inter_add_diff
    simp_rw [← measure_inter_add_diff U m_syz]

    -- simp [pos0_yz]






    -- [x - z] + [z - x] ≤ [x - y] + [y - x] + [y - z] + [z - y]
    -- [x - z]


    sorry
  edist_dist := sorry
  uniformity_dist := sorry
  cobounded_sets := sorry


-- #exit

def statistically_close {D : (n : ℕ) →  Type*} [∀n, MeasurableSpace (D n)] (X Y : (n : ℕ) → ProbabilityMeasure (D n)) :=
  negligible (fun n ↦ statistical_distance (X n) (Y n))


-- theorem lemma_5_1 {m : ℝ≥0} {_ : 2 * n }

-- #check Mathlib.Testing.SlimCheck


def sqrt_log : ℕ → ℝ≥0 := (Real.toNNReal ∘ Real.sqrt ∘  Real.log ∘ (↑))
def ω_sqrt_log (ω : ℕ → ℝ≥0) : Prop := ω =ω sqrt_log

abbrev goes_to_infinity (f : ℕ → ℕ) : Prop := Filter.Tendsto f Filter.atTop Filter.atTop

end statistic
