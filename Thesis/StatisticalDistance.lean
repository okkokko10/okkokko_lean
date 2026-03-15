import Mathlib
import Thesis.Statistic -- currently only uses negligible


open MeasureTheory
open ProbabilityTheory
open scoped NNReal ENNReal


noncomputable section



def statisticalDistance {D : Type*} [MeasurableSpace D]  (X Y : ProbabilityMeasure D) : ℝ≥0 :=
  ∑' (x : D), Real.nnabs ((X {x}).toReal - (Y {x}).toReal)



theorem statisticalDistance_def  {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D)
  : (statisticalDistance X Y) = ∑' (x : D), Real.nnabs ((X {x}).toReal - (Y {x}).toReal) := by
    rfl





theorem statisticalDistance_conserve_equiv {D G : Type*} [MeasurableSpace D] [MeasurableSpace G] [DiscreteMeasurableSpace G]
  (X Y : ProbabilityMeasure D) (e : D ≃ᵐ G)
  : statisticalDistance X Y = statisticalDistance (X.map (f := e) e.measurable.aemeasurable) (Y.map (f := e) e.measurable.aemeasurable) := by
    have eme {μ} := e.measurable.aemeasurable (μ := μ)
    unfold statisticalDistance

    have aq (X : ProbabilityMeasure D) x : X.map eme {e x} = X {x} := by
      rw [ProbabilityMeasure.map_apply]
      congr
      rw [←Set.image_singleton]
      exact MeasurableEquiv.preimage_image e {x}
      exact measurableSet_singleton (e x)
    let f x := Real.nnabs (↑((X.map eme) {x}) - ↑((Y.map eme) {x}))
    simp_rw [←aq]
    change ∑' (x : D), f (e x) = ∑' (x : G), f x

    exact Equiv.tsum_eq e.toEquiv f

theorem statisticalDistance_conserve_injective {D G : Type*} [MeasurableSpace D] [MeasurableSpace G] [DiscreteMeasurableSpace G]
  (X Y : ProbabilityMeasure D) (e : D → G) (me : Measurable e) (e_inj : Function.Injective e)
  : statisticalDistance X Y = statisticalDistance (X.map (f := e) me.aemeasurable) (Y.map (f := e) me.aemeasurable) := by
    have eme {μ} := me.aemeasurable (μ := μ)
    unfold statisticalDistance

    have aq (X : ProbabilityMeasure D) x : X.map eme {e x} = X {x} := by
      rw [ProbabilityMeasure.map_apply]
      congr
      rw [←Set.image_singleton]
      exact Function.Injective.preimage_image e_inj {x}
      exact measurableSet_singleton (e x)
    let f x := Real.nnabs (↑((X.map eme) {x}) - ↑((Y.map eme) {x}))
    simp_rw [←aq]
    change ∑' (x : D), f (e x) = ∑' (x : G), f x
    apply e_inj.tsum_eq
    -- rw [←Set.compl_subset_compl]
    simp only [Function.support_subset_iff, ne_eq]

    intro y fy
    contrapose! fy
    have : e ⁻¹' {y} = ∅ := by exact Set.preimage_singleton_eq_empty.mpr fy
    subst f
    simp_rw [ProbabilityMeasure.map_apply _ eme (measurableSet_singleton _)]
    rw [this]
    simp only [ProbabilityMeasure.coeFn_empty, NNReal.coe_zero, sub_self, le_refl,
      Real.nnabs_of_nonneg, Real.toNNReal_zero]



def statisticallyClose {D : (n : ℕ) →  Type*} [∀n, MeasurableSpace (D n)] [∀n, DiscreteMeasurableSpace (D n)] (X Y : (n : ℕ) → ProbabilityMeasure (D n)) :=
  negligible (fun n ↦ statisticalDistance (X n) (Y n))
