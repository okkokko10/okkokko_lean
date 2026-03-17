import Mathlib
import Thesis.Statistic -- currently only uses negligible


open MeasureTheory
open ProbabilityTheory
open scoped NNReal ENNReal


noncomputable section

variable  {D G : Type*} [MeasurableSpace D] [MeasurableSpace G]


def statisticalDistance (X Y : ProbabilityMeasure D) : ℝ≥0 :=
  (2⁻¹) * ∑' (x : D), Real.nnabs ((X {x}).toReal - (Y {x}).toReal)



theorem statisticalDistance_def (X Y : ProbabilityMeasure D)
  : (statisticalDistance X Y) = (2⁻¹) * ∑' (x : D), Real.nnabs ((X {x}).toReal - (Y {x}).toReal) := by
    rfl




theorem statisticalDistance_conserve_equiv [DiscreteMeasurableSpace G]
  (X Y : ProbabilityMeasure D) (e : D ≃ᵐ G)
  : statisticalDistance X Y = statisticalDistance (X.map (f := e) e.measurable.aemeasurable) (Y.map (f := e) e.measurable.aemeasurable) := by
    have eme {μ} := e.measurable.aemeasurable (μ := μ)
    simp_rw [statisticalDistance_def]
    congr 1 -- get rid of (2⁻¹) * ·
    have aq (X : ProbabilityMeasure D) x : X.map eme {e x} = X {x} := by
      rw [ProbabilityMeasure.map_apply]
      congr
      rw [←Set.image_singleton]
      exact MeasurableEquiv.preimage_image e {x}
      exact measurableSet_singleton (e x)
    simp_rw [←aq]
    let f x := Real.nnabs (↑((X.map eme) {x}) - ↑((Y.map eme) {x}))
    change ∑' (x : D), f (e x) = ∑' (x : G), f x
    exact Equiv.tsum_eq e.toEquiv f

theorem statisticalDistance_conserve_injective [DiscreteMeasurableSpace G]
  (X Y : ProbabilityMeasure D) (e : D → G) (me : Measurable e) (e_inj : Function.Injective e)
  : statisticalDistance X Y = statisticalDistance (X.map (f := e) me.aemeasurable) (Y.map (f := e) me.aemeasurable) := by
    have eme {μ} := me.aemeasurable (μ := μ)
    simp_rw [statisticalDistance_def]
    congr 1 -- get rid of (2⁻¹) * ·

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



theorem statisticalDistance_conserve_injective'  [DiscreteMeasurableSpace D] [DiscreteMeasurableSpace G]
  (X Y : ProbabilityMeasure D) (e : D → G) (e_inj : Function.Injective e)
  : statisticalDistance X Y = statisticalDistance (X.map (f := e) AEMeasurable.of_discrete) (Y.map (f := e) AEMeasurable.of_discrete) := by
  refine statisticalDistance_conserve_injective X Y e ?_ e_inj
  exact Measurable.of_discrete

-- without need for it to be a measurable equiv
theorem statisticalDistance_conserve_equiv' [DiscreteMeasurableSpace D] [DiscreteMeasurableSpace G]
  (X Y : ProbabilityMeasure D) (e : D ≃ G)
  : statisticalDistance X Y = statisticalDistance (X.map (f := e) AEMeasurable.of_discrete) (Y.map (f := e) AEMeasurable.of_discrete) := by
    have := statisticalDistance_conserve_injective' X Y e (Equiv.injective e)
    exact this


def statisticallyClose {D : (n : ℕ) →  Type*} [∀n, MeasurableSpace (D n)] (X Y : (n : ℕ) → ProbabilityMeasure (D n)) :=
  negligible (fun n ↦ statisticalDistance (X n) (Y n))

section properties

-- todo: this isn't a PDF
def toPMF [DiscreteMeasurableSpace D] (X : ProbabilityMeasure D) : D →₁[Measure.count] ℝ := by

  refine MemLp.toLp (fun x ↦ (X {x}).toReal) ?_
  refine mem_L1_toReal_of_lintegral_ne_top AEMeasurable.of_discrete ?_
  rw [lintegral_count]
  apply lt_top_iff_ne_top.mp
  apply lt_of_le_of_lt ?_ (ENNReal.one_lt_top)
  apply tsum_le_of_sum_le' (zero_le_one)
  intro s
  rw [sum_measure_singleton]
  exact prob_le_one


theorem toPMF_injective [DiscreteMeasurableSpace D] [Countable D] : Function.Injective (toPMF (D := D)) := by
  intro X Y
  unfold toPMF
  simp only [MemLp.toLp_eq_toLp_iff]
  rw [Filter.EventuallyEq]
  rw [Measure.ae_count_iff]
  simp only [NNReal.coe_inj]
  intro w
  apply ProbabilityMeasure.toMeasure_injective
  let s (i : D) := ({i} : Set D)
  refine Measure.ext_of_iUnion_eq_univ (s := s) ?_ ?_
  unfold s
  exact Set.iUnion_of_singleton D
  intro i
  unfold s
  simp only [Measure.restrict_singleton]
  congr 1
  specialize w i
  have : (X {i}) = ((Y {i}) : ℝ≥0∞) := by exact congrArg ENNReal.ofNNReal w
  convert this
  exact Eq.symm (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure X {i})
  exact Eq.symm (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure Y {i})


  -- refine ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq X Y ?_
  -- intro s ms
  -- #check Measure.ext_of_iUnion_eq_univ
  -- have s_made : s = Set.iUnion (fun (x : s) ↦ {Subtype.val x}) := by
  --   simp only [Set.iUnion_singleton_eq_range, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  -- rw [s_made]



lemma toPMF_apply [DiscreteMeasurableSpace D] (X : ProbabilityMeasure D) x :
  toPMF X x = (X {x}).toReal := by
    unfold toPMF
    let p x :=(X {x}).toReal
    change (MemLp.toLp p _) x = p x
    revert x
    rw [← Measure.ae_count_iff] -- under the counting measure, ae is everywhere
    rw [← Filter.EventuallyEq]
    exact MemLp.coeFn_toLp (toPMF._proof_1 X)




instance statisticalDistancePseudoMetric {D : Type*} [MeasurableSpace D] [DiscreteMeasurableSpace D] : PseudoMetricSpace (ProbabilityMeasure D) := by
  let met : MetricSpace (D →₁[Measure.count] ℝ) := inferInstance
  exact PseudoMetricSpace.induced toPMF met.toPseudoMetricSpace


/-- metric space where dist is equal to statistical distance times 2 -/
instance statisticalDistanceMetric {D : Type*} [MeasurableSpace D] [DiscreteMeasurableSpace D] [Countable D] : MetricSpace (ProbabilityMeasure D) := by
  let met : MetricSpace (D →₁[Measure.count] ℝ) := inferInstance
  exact (MetricSpace.induced toPMF toPMF_injective met)

instance statisticalDistancePseudoEMetric {D : Type*} [MeasurableSpace D] [DiscreteMeasurableSpace D] : PseudoEMetricSpace (ProbabilityMeasure D) :=
  statisticalDistancePseudoMetric.toPseudoEMetricSpace


example {D : Type*} [MeasurableSpace D] [DiscreteMeasurableSpace D] [Countable D] :
  statisticalDistancePseudoMetric (D := D) = statisticalDistanceMetric.toPseudoMetricSpace := by rfl



theorem statisticalDistancePseudoMetric_eq {D : Type*} [MeasurableSpace D] [DiscreteMeasurableSpace D]
  (X Y : ProbabilityMeasure D)
  : dist X Y = 2 * statisticalDistance X Y := by
    change dist (toPMF X) (toPMF Y) = 2 * ↑(statisticalDistance X Y)
    unfold statisticalDistance
    simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_ofNat, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_inv_cancel_left₀]
    -- #check MemLp.toLp_sub

    rw [Lp.dist_def]
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp only [Pi.sub_apply]
    simp_rw [toPMF_apply]


    rw [lintegral_count]
    let pp x := Real.nnabs (↑(X {x}) - ↑(Y {x}))
    have ww x : ‖(X {x}).toReal - (Y {x}).toReal‖ₑ = pp x := by
      rfl
    simp_rw [ww]
    change (∑' (a : D), ((pp a) : ℝ≥0∞)).toReal = (∑' (x : D), pp x)
    suffices (∑' (a : D), ((pp a) : ℝ≥0∞)).toNNReal = (∑' (x : D), pp x) by
      rw [←this]
      rfl
    exact Eq.symm NNReal.tsum_eq_toNNReal_tsum

#check IsometryEquiv

-- probably not used, but I wanted to try making this
theorem statisticalDistance_isometry [DiscreteMeasurableSpace D] [DiscreteMeasurableSpace G]
  (e : D → G) (e_inj : Function.Injective e)
  : Isometry (fun ν ↦ ProbabilityMeasure.map ν (f := e) (f_aemble := AEMeasurable.of_discrete)) := by
    apply isometry_iff_dist_eq.mpr
    intro X Y
    simp_rw [statisticalDistancePseudoMetric_eq]
    simp only [mul_eq_mul_left_iff, NNReal.coe_inj, OfNat.ofNat_ne_zero, or_false]
    exact Eq.symm (statisticalDistance_conserve_injective' X Y e e_inj)

def statisticalDistance_IsometryEquiv [DiscreteMeasurableSpace D] [DiscreteMeasurableSpace G]
  (e : D ≃ G)
  : (ProbabilityMeasure D) ≃ᵢ (ProbabilityMeasure G) := by
    have := fun ν ↦ ProbabilityMeasure.map ν (f := e) (f_aemble := AEMeasurable.of_discrete)

    refine ⟨?_,?_⟩
    sorry
    sorry
