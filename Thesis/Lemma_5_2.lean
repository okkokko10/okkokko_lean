import Thesis.A_Matrix
import Thesis.Lemma_5_1
import Thesis.SmoothingParameter
import Thesis.A_Matrix_Lattice
import Thesis.Statistic
import Thesis.Zqn
import Thesis.Lemma_2_8


noncomputable section
open scoped NNReal ENNReal
open MeasureTheory


-- move to other file
instance (ι : Type*) [Fintype ι] [DecidableEq ι] :  DiscreteTopology (Casts.Zn ι) := by
  rw [Casts.Zn_ofBasis]
  exact ZSpan.discreteTopology_pi_basisFun
instance (ι : Type*) [Fintype ι] [DecidableEq ι] :  IsZLattice ℝ (Casts.Zn ι) := by
  convert instIsZLatticeRealSpan (Pi.basisFun ℝ ι) -- convert is unreasonably effective
  exact Casts.Zn_ofBasis

theorem statistical_distance_conserve {D G : Type*} [MeasurableSpace D] [MeasurableSpace G] (X Y : ProbabilityMeasure D)
  (e : D ≃ᵐ G)
  : statistical_distance X Y = statistical_distance (X.map (f := e) e.measurable.aemeasurable) (Y.map (f := e) e.measurable.aemeasurable) := by
    have eme {μ} := e.measurable.aemeasurable (μ := μ)
    unfold statistical_distance
    congr 1

    unfold statistical_distance'
    congr 1
    -- simp only [ProbabilityMeasure.toMeasure_map]
    have uni : @Set.univ G = e '' (@Set.univ D) := by simp only [Set.image_univ, EquivLike.range_eq_univ]
    -- rw [this]
    have tt (X : ProbabilityMeasure D) : (X.map eme).toMeasure.toSignedMeasure = (VectorMeasure.map (X.toMeasure).toSignedMeasure ⇑e) := by
      refine VectorMeasure.ext_iff _ _ |>.mpr ?_
      intro s ms
      rw [VectorMeasure.map_apply _ e.measurable ms]
      rw [Measure.toSignedMeasure_apply_measurable ms]

      rw [Measure.toSignedMeasure_apply_measurable (e.measurableSet_preimage.mpr ms)]
      simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn]
      simp only [NNReal.coe_inj]
      exact
        ProbabilityMeasure.map_apply_of_aemeasurable X
          (Measurable.aemeasurable (MeasurableEquiv.measurable e)) ms
    simp_rw [tt]
    have  tr (X Y : SignedMeasure D) :
      (VectorMeasure.map X ⇑e -
              VectorMeasure.map Y ⇑e)
              = (VectorMeasure.map (X - Y) ⇑e) := by
      abel_nf
      rw [←VectorMeasure.map_smul]
      exact (VectorMeasure.map_add X _ ⇑e).symm
    simp_rw [tr]
    set p := (X.toMeasure).toSignedMeasure - (Y.toMeasure).toSignedMeasure

    #check VectorMeasure.mapGm
    change
      p.totalVariation Set.univ = (SignedMeasure.totalVariation (VectorMeasure.mapGm e p)) Set.univ

    set q :=((VectorMeasure.mapGm ⇑e) p)


    -- rw [uni]

    -- have :
    --   (VectorMeasure.map p.totalVariation.toSignedMeasure ⇑e)) Set.univ =
    --     (SignedMeasure.totalVariation (VectorMeasure.map p ⇑e)) (⇑e '' Set.univ)
    unfold SignedMeasure.totalVariation
    simp only [Measure.coe_add, Pi.add_apply]
    obtain ⟨s,ms, pos, neg, pos_eq, neg_eq⟩:= SignedMeasure.toJordanDecomposition_spec p
    rw [pos_eq, neg_eq]
    obtain ⟨s',ms', pos', neg', pos_eq', neg_eq'⟩:= SignedMeasure.toJordanDecomposition_spec q
    rw [pos_eq', neg_eq']







    have tt (X : SignedMeasure D) :
      (SignedMeasure.toJordanDecomposition (VectorMeasure.map X e)).posPart =
      (Measure.map e (SignedMeasure.toJordanDecomposition X).posPart) := by

      sorry


    sorry

#check MeasurableEquiv

theorem lemma_5_2 {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) (ass : lemma_5_1_statement A)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0)
  (s_prop :  𝓛.smoothing_parameter (A.Λ_ortho') ε ≤ s) :
  have : NeZero s := sorry; -- by s_prop which states s is ≥ a positive value
  statistical_distance (A.syndrome_distributed (int_gaussian m s)) (uniform_over_Zqn _ _) ≤ 2 * ε
  := by
    simp only
    have : LinearMap.range A.syndrome_map = ⊤ := sorry -- from [ass]
    #check corollary_2_8

    have s_pos : NeZero s := sorry
    -- statistical_distance (A.syndrome_distributed (int_gaussian m s)) (uniform_over_Zqn _ _) ≤ 2 * ε
    -- statistical_distance ( 𝓛.mod_distribution Λ' (𝓛.discreteGaussianProbability Λ s c)) (𝓛.quot_uniform _ _ sub) ≤ 2 * ε
    let Λt := A.Λ_ortho'
    let e_distribution : ProbabilityMeasure (Casts.Zn (Fin m)) := 𝓛.discreteGaussianProbability ((Casts.Zn (Fin m)) : 𝓛 _) s 0

    let e_modΛt_distribution := 𝓛.mod_distribution Λt e_distribution

    -- todo: show A.Λ_ortho' ≤ Casts.Zn _

    have sub : A.Λ_ortho' ≤ Casts.Zn _ := sorry

    have isomorphic_ver : statistical_distance ( e_modΛt_distribution ) (𝓛.quot_uniform (Casts.Zn _) Λt sub) ≤ 2 * ε := sorry

    -- todo: statistical distance is conserved by maps?
    have : ∃equi : (𝓛.quot (Casts.Zn (Fin m)) Λt) ≃ᵐ (Fin n → ZMod q),
      (𝓛.quot_uniform (Casts.Zn (Fin m)) Λt sub).map (f := equi) (AEMeasurable.of_discrete) = (uniform_over_Zqn n q) := by

        sorry


    -- plan: implement Zqn as a quotient of Zn

    -- convert corollary_2_8

    sorry

theorem lemma_5_2_furthermore {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) (ass : lemma_5_1_statement A)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0)
  (s_prop : 𝓛.smoothing_parameter (A.Λ_ortho') ε ≤ s) (u : Fin n → ZMod q) (t : Fin m → ℤ) (ht : A.syndrome_map t = u)
  :
  have : NeZero s := sorry;
  -- ProbabilityTheory.cond (int_gaussian m hs) (A.syndrome_map ⁻¹' {u}) = t +ᵥ (int_gaussian_sublattice m hs A.Λ_ortho (-t))
  ProbabilityTheory.cond (int_gaussian m s) (A.syndrome_map ⁻¹' {u}) = (int_gaussian_sublattice m s A.Λ_ortho (-t)).map (f := (· + t)) (AEMeasurable.of_discrete)
  := sorry
