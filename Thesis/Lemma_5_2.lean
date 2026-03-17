import Thesis.A_Matrix
import Thesis.Lemma_5_1
import Thesis.SmoothingParameter
import Thesis.A_Matrix_Lattice
import Thesis.Statistic
import Thesis.Zqn
import Thesis.Lemma_2_8
import Thesis.StatisticalDistance
import Thesis.Casts


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




#check MeasurableEquiv

def Casts.Zn_int {ι : Type*} [Fintype ι] : Casts.Zn (ι) ≃ₗ[ℤ] (ι → ℤ) := by
  sorry


-- temp
def A_Matrix.syndrome_map_Zn {n m q : ℕ} (A : A_Matrix n m q) : (Casts.Zn (Fin m)) →ₗ[ℤ] (Zqn n q) := by sorry


def A_Matrix.syndromes {n m q : ℕ} (A : A_Matrix n m q) : Submodule ℤ (Zqn n q) := LinearMap.range A.syndrome_map_Zn

-- temp
def A_Matrix.Λ_ortho_Zn {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : Submodule ℤ ↥(Casts.Zn (Fin m)) := (LinearMap.ker A.syndrome_map_Zn)



theorem A_Matrix.Λ_ortho_Zn_eq {n m q : ℕ} [NeZero q] (A : A_Matrix n m q)
  :
  A.Λ_ortho' = A.Λ_ortho_Zn.map (Submodule.subtype (Casts.Zn (Fin m))) -- AI suggestion, coerce submodule of submodule
  := sorry

theorem A_Matrix.Λ_ortho'_submoduleOf {n m q : ℕ} [NeZero q] (A : A_Matrix n m q)
  : A.Λ_ortho'.submoduleOf (Casts.Zn (Fin m)) = A.Λ_ortho_Zn := by
    rw [Λ_ortho_Zn_eq]

    ext x
    constructor
    intro xS
    sorry
    intro xA


    #check Submodule.submoduleOfEquivOfLe
    sorry

#check Submodule.Quotient.addCommGroup

-- temp
def A_bijection {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  (𝓛.quot (Casts.Zn (Fin m)) A.Λ_ortho') ≃ A.syndromes := by

  have ww (a b) : (A.Λ_ortho'.submoduleOf (Casts.Zn (Fin m))).quotientRel a b
    ↔ A.syndrome_map_Zn a = A.syndrome_map_Zn b := by
    simp_rw [ Submodule.quotientRel_def]
    rw [A_Matrix.Λ_ortho'_submoduleOf]

    unfold A_Matrix.Λ_ortho_Zn
    simp only [LinearMap.mem_ker, map_sub]
    exact sub_eq_zero

  let F : 𝓛.quot (Casts.Zn (Fin m)) A.Λ_ortho' → ↥A.syndromes := by
    unfold 𝓛.quot
    refine Quotient.lift ?_ ?_
    ·
      intro e
      refine ⟨A.syndrome_map_Zn e,?_⟩
      unfold A_Matrix.syndromes
      exact LinearMap.mem_range_self A.syndrome_map_Zn e
    -- simp only [Subtype.mk.injEq, Subtype.forall]
    intro a b ab
    simp only [Subtype.mk.injEq]
    simp_rw [HasEquiv.Equiv] at ab
    exact (ww a b).mp ab
  have : Function.Bijective F := by
    constructor
    ·
      intro a b FaFb
      induction a, b using Quotient.ind₂ with | _ a b =>
      subst F
      simp only [id_eq, Quotient.lift_mk, Subtype.mk.injEq] at FaFb
      have := (ww a b).mpr FaFb
      apply Quotient.eq.mpr this
    ·
      apply Quotient.lift_surjective
      intro ⟨s,sw⟩
      unfold A_Matrix.syndromes at sw
      simpa only [Subtype.mk.injEq, Subtype.exists, LinearMap.mem_range] using sw
  exact Equiv.ofBijective F this



def A_bijection_equiv {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :

  let : AddCommGroup (𝓛.quot (Casts.Zn (Fin m)) A.Λ_ortho') :=  Submodule.Quotient.addCommGroup ((A.Λ_ortho'.submoduleOf (Casts.Zn (Fin m))))

  (𝓛.quot (Casts.Zn (Fin m)) A.Λ_ortho') ≃ₗ[ℤ] A.syndromes := by

  let : AddCommGroup (𝓛.quot (Casts.Zn (Fin m)) A.Λ_ortho') :=  Submodule.Quotient.addCommGroup ((A.Λ_ortho'.submoduleOf (Casts.Zn (Fin m))))

  have ww (a b) : (A.Λ_ortho'.submoduleOf (Casts.Zn (Fin m))).quotientRel a b
    ↔ A.syndrome_map_Zn a = A.syndrome_map_Zn b := by
    simp_rw [ Submodule.quotientRel_def]
    rw [A_Matrix.Λ_ortho'_submoduleOf]

    unfold A_Matrix.Λ_ortho_Zn
    simp only [LinearMap.mem_ker, map_sub]
    exact sub_eq_zero
  let F : 𝓛.quot (Casts.Zn (Fin m)) A.Λ_ortho' → ↥A.syndromes := by
    unfold 𝓛.quot
    refine Quotient.lift ?_ ?_
    ·
      intro e
      refine ⟨A.syndrome_map_Zn e,?_⟩
      unfold A_Matrix.syndromes
      exact LinearMap.mem_range_self A.syndrome_map_Zn e
    -- simp only [Subtype.mk.injEq, Subtype.forall]
    intro a b ab
    simp only [Subtype.mk.injEq]
    simp_rw [HasEquiv.Equiv] at ab
    exact (ww a b).mp ab
  have F_bij: Function.Bijective F := by
    constructor
    ·
      intro a b FaFb
      induction a, b using Quotient.ind₂ with | _ a b =>
      subst F
      simp only [id_eq, Quotient.lift_mk, Subtype.mk.injEq] at FaFb
      have := (ww a b).mpr FaFb
      apply Quotient.eq.mpr this
    ·
      apply Quotient.lift_surjective
      intro ⟨s,sw⟩
      unfold A_Matrix.syndromes at sw
      simpa only [Subtype.mk.injEq, Subtype.exists, LinearMap.mem_range] using sw
  let F' : 𝓛.quot (Casts.Zn (Fin m)) A.Λ_ortho' →ₗ[ℤ] ↥A.syndromes := by
    refine AddMonoidHom.toIntLinearMap ?_
    apply AddMonoidHom.mk' F
    intro a b
    induction a, b using Quotient.ind₂' with | _ a b =>
    simp_rw [Submodule.Quotient.mk''_eq_mk]
    rw [←Submodule.Quotient.mk_add]
    simp_rw [←Submodule.Quotient.mk''_eq_mk]
    subst F
    simp only [id_eq, Quotient.lift_mk, map_add, AddMemClass.mk_add_mk]
  refine LinearEquiv.ofBijective F' F_bij



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
          apply A_bijection A |>.trans
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
  ProbabilityTheory.cond (int_gaussian m s) (A.syndrome_map ⁻¹' {u}) = (int_gaussian_sublattice m s A.Λ_ortho (-t)).map (f := (· + t)) (AEMeasurable.of_discrete)
  := sorry
