import Thesis.A_Matrix_Lattice
import Thesis.LatticeQuot

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
variable (Λ' : 𝓛 ι) [DiscreteTopology Λ'] [IsZLattice ℝ Λ']




theorem A_Matrix.Λ_ortho'_submoduleOf {n m q : ℕ} [NeZero q] (A : A_Matrix n m q)
  : A.Λ_ortho'.submoduleOf (Casts.Zn (Fin m)) = (LinearMap.ker A.syndromeMap) := by

    sorry


def A_bijection_equiv {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  (𝓛.quot (Casts.Zn (Fin m)) A.Λ_ortho') ≃ₗ[ℤ] A.syndromes := by
  have ww (a b) : (A.Λ_ortho'.submoduleOf (Casts.Zn (Fin m))).quotientRel a b
    ↔ A.syndromeMap a = A.syndromeMap b := by
    simp_rw [ Submodule.quotientRel_def]

    rw [A_Matrix.Λ_ortho'_submoduleOf]

    -- unfold A_Matrix.Λ_ortho_Zn
    simp only [LinearMap.mem_ker, map_sub]
    exact sub_eq_zero
  let F : 𝓛.quot (Casts.Zn (Fin m)) A.Λ_ortho' → ↥A.syndromes := by
    unfold 𝓛.quot
    refine Quotient.lift ?_ ?_
    ·
      intro e
      refine ⟨A.syndromeMap e,?_⟩
      unfold A_Matrix.syndromes
      exact LinearMap.mem_range_self A.syndromeMap e
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
