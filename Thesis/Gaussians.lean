import Mathlib
import Thesis.MyLattice



noncomputable section
open scoped NNReal ENNReal
variable {ι : Type*} [Fintype ι]


variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section gaussians

open ProbabilityTheory
open MeasureTheory


def gaussianFunction [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s] (c : ι → ℝ)  := gaussianPDF 0 s ∘ (‖· - c‖)

#check MeasureTheory.Measure.count
-- #check Measure.comap

#check gaussianReal
/-
2.4 Gaussians on Lattices
ρ s c
-/
def gaussianMeasure [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s] (c : ι → ℝ) := Measure.count.withDensity (gaussianFunction s c)

#check ProbabilityMeasure


def 𝓛.gaussianMeasure' [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s] (c : ι → ℝ)  := (gaussianMeasure s c).restrict Λ


lemma 𝓛.gaussianMeasure'_finite [Norm (ι → ℝ)]  (s : ℝ≥0) [NeZero s]  (c : ι → ℝ) : IsFiniteMeasure (𝓛.gaussianMeasure' Λ s c) := sorry
-- def gaussianMeasure'_total [Norm (ι → ℝ)] (c : ι → ℝ) {s : ℝ≥0} (hs : s ≠ 0) := (gaussianMeasure' Λ c hs) Set.univ

-- def gaussianDistribution [Norm (ι → ℝ)] {s : ℝ≥0} (hs : s ≠ 0)  (c : ι → ℝ) := ((gaussianMeasure' Λ hs c) Set.univ)⁻¹ • gaussianMeasure' Λ hs c
def 𝓛.gaussianDistribution [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s]  (c : ι → ℝ) := (𝓛.gaussianMeasure' Λ s c)[|Set.univ]

lemma 𝓛.gaussianDistribution_prob [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s] (c : ι → ℝ) : IsProbabilityMeasure (𝓛.gaussianDistribution Λ s c) := by
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
  exact gaussianPDFReal_pos _ _ _ NeZero.out

  have := 𝓛.gaussianMeasure'_finite Λ s c
  exact this.1.ne


lemma 𝓛.gaussianDistribution.eq [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s] (c : ι → ℝ)
  : 𝓛.gaussianDistribution Λ s c = (gaussianMeasure s c)[|Λ] := by
    unfold 𝓛.gaussianDistribution 𝓛.gaussianMeasure'
    simp only [ProbabilityTheory.cond, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
      Measure.restrict_univ]


def int_gaussian_real_measure (m) [Norm (Fin m → ℝ)] (s : ℝ≥0) [NeZero s] : Measure (Fin m → ℝ)
  :=
  𝓛.gaussianDistribution (AddSubgroup.toIntSubmodule (((Int.castAddHom ℝ).compLeft (Fin m)).range )) s 0



-- def int_gaussian_int_measure (m) [Norm (Fin m → ℝ)] {s : ℝ≥0} (hs : s ≠ 0)  : Measure (Fin m → ℤ)
--   :=  (gaussianMeasure hs 0)[| (s2.Zn (Fin m))].comap ((↑) ∘ ·)
def int_gaussian_int_measure (m) [Norm (Fin m → ℝ)] (s : ℝ≥0) [NeZero s] (c : Fin m → ℝ)  : Measure (Fin m → ℤ)
  :=  ((gaussianMeasure s c).comap ((Int.cast : ℤ → ℝ) ∘ ·))[|Set.univ]

/-- D_{Zᵐ,s} -/
def int_gaussian (m) [Norm (Fin m → ℝ)] (s : ℝ≥0) [NeZero s]  : ProbabilityMeasure (Fin m → ℤ) :=
  ⟨
    int_gaussian_int_measure m s 0
    , sorry
  ⟩

def int_gaussian_sublattice (m) [Norm (Fin m → ℝ)] (s : ℝ≥0) [NeZero s] (Λ : AddSubgroup (Fin m → ℤ)) (c : Fin m → ℤ) : ProbabilityMeasure (Fin m → ℤ) :=
  ⟨
    (int_gaussian_int_measure m s ((↑) ∘ c))[|Λ]
    , sorry
  ⟩


end gaussians
