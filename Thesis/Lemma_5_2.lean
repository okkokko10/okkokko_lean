import Thesis.A_Matrix
import Thesis.Lemma_5_1
import Thesis.SmoothingParameter
import Thesis.A_Matrix_Lattice
import Thesis.Statistic
import Thesis.Zqn
import Thesis.Lemma_2_8
import Thesis.StatisticalDistance
import Thesis.Casts
import Thesis.A_Matrix_LatticeQuot


noncomputable section
open scoped NNReal ENNReal
open MeasureTheory





#check MeasurableEquiv






theorem lemma_5_2 {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) (ass : lemma_5_1_statement A)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0)
  (s_prop :  𝓛.smoothing_parameter (A.Λ_ortho') ε ≤ s) :
  have : NeZero s := sorry; -- by s_prop which states s is ≥ a positive value
  statisticalDistance (A.syndrome_distributed (int_gaussian m s)) (uniform_over_Zqn _ _) ≤ 2 * ε
  := by
    simp only
    have syndromes_top: A.syndromes = ⊤ := sorry -- from [ass]

    have s_pos : NeZero s := sorry
    -- statisticalDistance (A.syndrome_distributed (int_gaussian m s)) (uniform_over_Zqn _ _) ≤ 2 * ε
    -- statisticalDistance ( 𝓛.mod_distribution Λ' (𝓛.discreteGaussianProbability Λ s c)) (𝓛.quot_uniform _ _ sub) ≤ 2 * ε
    let Λt := A.Λ_ortho'
    let e_distribution : ProbabilityMeasure (Casts.Zn (Fin m)) := 𝓛.discreteGaussianProbability ((Casts.Zn (Fin m)) : 𝓛 _) s 0

    let e_modΛt_distribution := 𝓛.mod_distribution Λt e_distribution

    -- todo: show A.Λ_ortho' ≤ Casts.Zn _

    have sub : A.Λ_ortho' ≤ Casts.Zn _ := sorry

    have isomorphic_ver : statisticalDistance ( e_modΛt_distribution ) (𝓛.quot_uniform (Casts.Zn _) Λt sub) ≤ 2 * ε := by
      apply corollary_2_8
      exact ε_bound
      exact s_prop

    convert isomorphic_ver using 1
    #check statisticalDistance_conserve_injective'




    -- todo: statistical distance is conserved by maps?
    have : ∃equi : (𝓛.quot (Casts.Zn (Fin m)) Λt) ≃ (Zqn n q),
      (𝓛.quot_uniform (Casts.Zn (Fin m)) Λt sub).map (f := equi) (AEMeasurable.of_discrete) = (uniform_over_Zqn n q)
      ∧
      (e_modΛt_distribution).map (f := equi) (AEMeasurable.of_discrete) = (A.syndrome_distributed (int_gaussian m s))

      := by
        refine ⟨?_,?_,?_⟩
        ·
          apply (A_bijection_equiv A).toEquiv |>.trans
          apply Equiv.subtypeUnivEquiv
          rw [syndromes_top]
          simp only [Submodule.mem_top, implies_true]

         --using syndromes_top

        -- have := Submodule.Quotient.induction_on
        -- todo: a finite equivalence maps an uniform distribution to another uniform distribution
        sorry
        subst e_modΛt_distribution e_distribution
        unfold 𝓛.mod_distribution

        simp only [Equiv.coe_trans]




        sorry

    -- rw [statisticalDistance_conserve_injective' (A.syndrome_distributed (int_gaussian m s)) (uniform_over_Zqn n q) ?_ ?_]



    -- plan: implement Zqn as a quotient of Zn

    -- convert corollary_2_8

    sorry

-- seems to not be used by 5_4
theorem lemma_5_2_furthermore {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) (ass : lemma_5_1_statement A)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0)
  (s_prop : 𝓛.smoothing_parameter (A.Λ_ortho') ε ≤ s) (u : Zqn n q) (t : Fin m → ℤ) (ht : A.syndrome_map t = u)
  :
  have : NeZero s := sorry;
  -- ProbabilityTheory.cond (int_gaussian m hs) (A.syndrome_map ⁻¹' {u}) = t +ᵥ (int_gaussian_sublattice m hs A.Λ_ortho (-t))
  ProbabilityTheory.cond (int_gaussian m s) (A.syndrome_map ⁻¹' {u})
  = (int_gaussian_sublattice m s sorry (-t)).map (f := (· + t)) (AEMeasurable.of_discrete) -- sorry = A.Λ_ortho
  := sorry
