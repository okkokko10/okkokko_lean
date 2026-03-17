import Mathlib
import Thesis.MyLattice
import Thesis.Casts



noncomputable section
open scoped NNReal ENNReal
variable {ι : Type*} [Fintype ι]


variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section gaussians

open ProbabilityTheory
open MeasureTheory

#check EuclideanSpace

-- NOTE:
def gaussianFunction (s : ℝ≥0) [NeZero s] (c : ι → ℝ) : (ι → ℝ) → ℝ≥0∞
  := gaussianPDF 0 (s ^ 2 / (2 * NNReal.pi)) ∘ (fun x ↦ ‖(WithLp.toLp 2 (x - c) : EuclideanSpace ℝ ι)‖)

#check MeasureTheory.Measure.count
-- #check Measure.comap

#check gaussianReal
/--
2.4 Gaussians on Lattices
ρ_{s,c}
-/
def gaussianMeasure (s : ℝ≥0) [NeZero s] (c : ι → ℝ) := Measure.count.withDensity (gaussianFunction s c)

#check ProbabilityMeasure


def 𝓛.gaussianMeasure' (s : ℝ≥0) [NeZero s] (c : ι → ℝ)  := (gaussianMeasure s c).restrict Λ
#check Measure.measure_subtype_coe_le_comap
def 𝓛.latticeGaussianMeasure (s : ℝ≥0) [NeZero s] (c : ι → ℝ) : Measure Λ :=
  (_root_.gaussianMeasure s c).comap Subtype.val


-- omit [DiscreteTopology ↥Λ] [IsZLattice ℝ Λ] in
theorem 𝓛.latticeGaussianMeasure_apply (v : ℝ≥0) [NeZero v] (c : ι → ℝ) (p : Set Λ)
  : 𝓛.latticeGaussianMeasure Λ v c p = (_root_.gaussianMeasure v c) ((↑) '' p) := by
    unfold 𝓛.latticeGaussianMeasure
    have mea_val: Measurable (Subtype.val : Λ → _) := measurable_subtype_coe
    refine MeasurableEmbedding.comap_apply ?_ (gaussianMeasure v c) p
    refine Measurable.measurableEmbedding mea_val ?_
    exact Subtype.val_injective


-- maybe too difficult. ρ_{s,c} Λ is finite
-- ASSUMPTION
theorem Assumptions.gaussian_finite_on_lattice (s : ℝ≥0) [NeZero s] (c : ι → ℝ) : (gaussianMeasure s c) Λ < ∞ := sorry



lemma 𝓛.gaussianMeasure'_finite (s : ℝ≥0) [NeZero s]  (c : ι → ℝ) : IsFiniteMeasure (𝓛.gaussianMeasure' Λ s c) := sorry
-- def gaussianMeasure'_total [Norm (ι → ℝ)] (c : ι → ℝ) {s : ℝ≥0} (hs : s ≠ 0) := (gaussianMeasure' Λ c hs) Set.univ


theorem 𝓛.latticeGaussianMeasure_finite (v : ℝ≥0) [NeZero v] (c : ι → ℝ)
  : IsFiniteMeasure (𝓛.latticeGaussianMeasure Λ v c) := by
    sorry

-- def gaussianDistribution [Norm (ι → ℝ)] {s : ℝ≥0} (hs : s ≠ 0)  (c : ι → ℝ) := ((gaussianMeasure' Λ hs c) Set.univ)⁻¹ • gaussianMeasure' Λ hs c
def 𝓛.gaussianDistribution (s : ℝ≥0) [NeZero s]  (c : ι → ℝ) := (𝓛.gaussianMeasure' Λ s c)[|Set.univ]
def 𝓛.latticeGaussianDistribution (s : ℝ≥0) [NeZero s]  (c : ι → ℝ) := (𝓛.latticeGaussianMeasure Λ s c)[|Set.univ]

lemma 𝓛.latticeGaussianDistribution_prob (s : ℝ≥0) [NeZero s] (c : ι → ℝ)
  : IsProbabilityMeasure (𝓛.latticeGaussianDistribution Λ s c) := by
  unfold 𝓛.latticeGaussianDistribution
  -- unfold 𝓛.latticeGaussianMeasure

  refine cond_isProbabilityMeasure_of_finite ?_ ?_
  ·
    rw [𝓛.latticeGaussianMeasure_apply]
    apply pos_iff_ne_zero.mp
    rw [Set.image_univ, Subtype.range_coe_subtype, SetLike.setOf_mem_eq]
    unfold gaussianMeasure
    have : {(0 : ι → ℝ)} ⊆ (Λ : Set _) := by
      simp only [Set.singleton_subset_iff, SetLike.mem_coe, zero_mem]
    refine lt_of_lt_of_le ?_
      (OuterMeasureClass.measure_mono (Measure.count.withDensity (gaussianFunction s c)) this)


    simp only [MeasurableSet.singleton, withDensity_apply, Measure.restrict_singleton,
      Measure.count_singleton', one_smul, lintegral_dirac]
    unfold gaussianFunction gaussianPDF
    simp
    apply gaussianPDFReal_pos _ _ _ ?_

    simp only [ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      mul_eq_zero, false_or, not_or]
    constructor
    exact NeZero.ne s
    exact NNReal.pi_ne_zero


  rw [𝓛.latticeGaussianMeasure_apply]
  rw [Set.image_univ, Subtype.range_coe_subtype, SetLike.setOf_mem_eq]
  rw [←lt_top_iff_ne_top]
  exact Assumptions.gaussian_finite_on_lattice Λ s c

-- same as above
lemma 𝓛.gaussianDistribution_prob (s : ℝ≥0) [NeZero s] (c : ι → ℝ) : IsProbabilityMeasure (𝓛.gaussianDistribution Λ s c) := by
  unfold 𝓛.gaussianDistribution
  -- refine cond_isProbabilityMeasure ?_
  refine isProbabilityMeasure_iff.mpr ?_
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply, smul_eq_mul]
  refine ENNReal.inv_mul_cancel ?_ ?_
  -- todo: make its own theorem
  simp only [ne_eq, Measure.measure_univ_eq_zero]
  intro gm
  rw [Measure.ext_iff] at gm
  specialize gm {0}
  simp only [MeasurableSet.singleton, Measure.coe_zero, Pi.ofNat_apply, forall_const] at gm
  unfold 𝓛.gaussianMeasure' gaussianMeasure at gm
  have : {0} ∩ (Λ : Set (ι → ℝ)) = {0} := by
    rw [Set.inter_eq_left, Set.singleton_subset_iff, SetLike.mem_coe]
    exact zero_mem Λ

  simp only [MeasurableSet.singleton, Measure.restrict_apply, this, withDensity_apply,
    Measure.restrict_singleton, Measure.count_singleton', one_smul, lintegral_dirac] at gm
  unfold gaussianFunction gaussianPDF at gm
  simp at gm
  revert gm
  simp only [imp_false, not_le]
  exact gaussianPDFReal_pos _ _ _ sorry

  have := 𝓛.gaussianMeasure'_finite Λ s c
  exact this.1.ne

omit [DiscreteTopology ↥Λ] [IsZLattice ℝ Λ] in
lemma 𝓛.gaussianDistribution.eq (s : ℝ≥0) [NeZero s] (c : ι → ℝ)
  : 𝓛.gaussianDistribution Λ s c = (gaussianMeasure s c)[|Λ] := by
    unfold 𝓛.gaussianDistribution 𝓛.gaussianMeasure'
    simp only [ProbabilityTheory.cond, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
      Measure.restrict_univ]


def int_gaussian_real_measure (m) (s : ℝ≥0) [NeZero s] : Measure (Fin m → ℝ)
  :=
  𝓛.gaussianDistribution (Casts.Zn (Fin m)) s 0



-- def int_gaussian_int_measure (m) [Norm (Fin m → ℝ)] {s : ℝ≥0} (hs : s ≠ 0)  : Measure (Fin m → ℤ)
--   :=  (gaussianMeasure hs 0)[| (s2.Zn (Fin m))].comap ((↑) ∘ ·)
def int_gaussian_int_measure (m) (s : ℝ≥0) [NeZero s] (c : Fin m → ℝ)  : Measure (Fin m → ℤ)
  :=  ((gaussianMeasure s c).comap Casts.Intn_to_Rn)[|Set.univ]

/-- D_{Zᵐ,s} -/
def int_gaussian (m) (s : ℝ≥0) [NeZero s]  : ProbabilityMeasure (Fin m → ℤ) :=
  ⟨
    int_gaussian_int_measure m s 0
    , sorry
  ⟩

def int_gaussian_sublattice (m) (s : ℝ≥0) [NeZero s] (Λ : AddSubgroup (Fin m → ℤ)) (c : Fin m → ℤ) : ProbabilityMeasure (Fin m → ℤ) :=
  ⟨
    (int_gaussian_int_measure m s (Casts.Intn_to_Rn c))[|Λ]
    , sorry
  ⟩


noncomputable def 𝓛.gaussianProbability_supertype (s : ℝ≥0) [NeZero s] (c : ι → ℝ)
  : ProbabilityMeasure (ι → ℝ)
  := .mk (𝓛.gaussianDistribution Λ s c) (gaussianDistribution_prob Λ s c)

noncomputable def 𝓛.discreteGaussianProbability (s : ℝ≥0) [NeZero s] (c : ι → ℝ)
  : ProbabilityMeasure (Λ)
  := .mk (𝓛.latticeGaussianDistribution Λ s c) (latticeGaussianDistribution_prob Λ s c)


-- todo: change int_gaussian to be the lattice Casts.Zn's discreteGaussianProbability

end gaussians
