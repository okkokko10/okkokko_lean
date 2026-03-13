import Mathlib
import Thesis.Casts

noncomputable section


open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] --(B : Basis ι)


abbrev 𝓛 ι := Submodule ℤ (ι → ℝ)



variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section lattices



def dualLattice_basic (Λ : 𝓛 ι) : AddSubgroup (ι → ℝ) where
  carrier := { x : ι → ℝ | ∀ v ∈ Λ, x ⬝ᵥ v ∈ Casts.IntSubmodule}
  add_mem' := by
    intro a b ha hb v hL
    specialize ha v hL
    specialize hb v hL
    rw [add_dotProduct]
    exact AddMemClass.add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq, zero_dotProduct, zero_mem, implies_true]
  neg_mem' := by
    simp only [Set.mem_setOf_eq, neg_dotProduct, neg_mem_iff, imp_self, implies_true]

def 𝓛.dualLattice : 𝓛 ι := (dualLattice_basic Λ).toIntSubmodule


lemma 𝓛.dualLattice.mem_def' (Λ : 𝓛 ι) (x : ι → ℝ) :
  x ∈ (dualLattice Λ) ↔
  ∀ v ∈ Λ,  x ∈ Casts.IntSubmodule.comap (dotProductBilin ℤ ℤ v) := by
    unfold dualLattice dualLattice_basic
    simp only [Submodule.mem_comap, dotProductBilin_apply_apply, dotProduct_comm]
    rfl

lemma 𝓛.dualLattice.mem_def''.step1 (v : ι → ℝ) :
  Submodule.comap (dotProductBilin ℤ ℤ v) Casts.IntSubmodule
  = ZLattice.comap ℝ Casts.IntSubmodule (dotProductBilin ℝ ℝ v)
  := by
    apply SetLike.coe_set_eq.mp
    ext y
    simp only [Submodule.comap_coe, AddSubgroup.coe_toIntSubmodule, Set.mem_preimage,
      dotProductBilin_apply_apply, SetLike.mem_coe, ZLattice.coe_comap]

#check instIsZLatticeComap




lemma Continuous_dotProduct (v : ι → ℝ) : Continuous (dotProductBilin ℝ ℝ v)
  := LinearMap.continuous_on_pi (dotProductBilin ℝ ℝ v)

-- I'm an idiot, this obviously isn't discrete
-- #check ZLattice.comap_discreteTopology
-- instance (v : ι → ℝ) : DiscreteTopology (ZLattice.comap ℝ Casts.IntSubmodule (dotProductBilin ℝ ℝ v)) := by
--   have : DiscreteTopology ↥Casts.IntSubmodule := by
--     sorry
--   apply ZLattice.comap_discreteTopology
--   exact Continuous_dotProduct v


--   sorry

-- example (v : ι → ℝ)  : IsZLattice ℝ (ZLattice.comap ℝ Casts.IntSubmodule (dotProductBilin ℝ ℝ v)) := by

--   sorry

-- #check ZSpan

def 𝓛.minimum_distance [NormedAddCommGroup (ι → ℝ)] : ℝ≥0 := sInf  { ‖x‖₊ | (x ∈ Λ) (_ : x ≠ 0) }

/-
paper:
The minimum distance λ1(Λ) of a lattice Λ is the length (in the Euclidean `2 norm, unless otherwise
indicated) of its shortest nonzero vector: λ1(Λ) = min06=x∈Λkxk. More generally, the ith successive
minimum λi(Λ) is the smallest radius r such that Λ contains i linearly independent vectors of norm at
most r. We write λ∞
1
to denote the minimum distance measured in the ∞ norm (which is defined as ‖x‖∞ = max |xᵢ|).
-/
-- i or more
def successive_minimum_distance [Norm (ι → ℝ)] (i : ℕ)
  := ⨅ (r : ℝ≥0) (_ : ∃s ⊆ (Λ.carrier), LinearIndependent ℝ (Subtype.val : s → _) ∧ s.encard ≤ i ∧ ∀x ∈ s, ‖x‖ ≤ r), r
-- note: for i := 0 this is ⊥ and i := 1 this is 0
def successive_minimum_distance' [Norm (ι → ℝ)] (i : ℕ)
  := ⨅ (s ⊆ (Λ.carrier)) (_ : LinearIndependent ℝ (Subtype.val : s → _)) (_ : s.encard ≤ i), ⨆x ∈ s, ‖x‖

-- def dualLattice

def infinity_norm : NormedAddCommGroup (ι → ℝ) := Pi.normedAddCommGroup

/-- λ₁∞ -/
def 𝓛.minimum_distance_sup := @𝓛.minimum_distance ι _ Λ (infinity_norm)

-- issue: the norm is already implied
-- IsZLattice alongside Nonempty ι should imply Λ ≠ ⊥
theorem 𝓛.minimum_distance.positive
  -- (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology ↥Λ]
  (h : Λ ≠ ⊥) : NeZero (𝓛.minimum_distance Λ) := by
  -- relies on the fact that Λ has elements other than 0, and nnnorm_eq_zero, and that Λ is discrete
  constructor
  unfold 𝓛.minimum_distance
  have tw (x : ι → ℝ) : ‖x‖₊ = 0 → x = 0 := nnnorm_eq_zero.mp
  #check IsZLattice

  simp only [ne_eq]
  #check NNReal.instConditionallyCompleteLinearOrderBot
  #check ConditionallyCompleteLinearOrderBot
  #check ConditionallyCompleteLattice
  -- change ¬(⨅x, ⨅ (_ : x ∈ Λ), ⨅ (_ : ¬x = 0), ‖x‖₊) = 0

  intro asm
  #check InfSet




  sorry


open Module

-- shows that for a Λ, there exists a ℝⁿ basis B that generates Λ.
example :
  let B : Module.Basis ι ℝ (ι → ℝ) := (IsZLattice.basis Λ).ofZLatticeBasis ℝ Λ;
  Submodule.span ℤ (Set.range B) = Λ
  := (IsZLattice.basis Λ).ofZLatticeBasis_span ℝ

section basis_matrix

abbrev basis_matrix (B : Module.Basis ι ℝ (ι → ℝ)) : Matrix ι ι ℝ := (Pi.basisFun ℝ ι).toMatrix B

instance basis_matrix.Invertible (B : Module.Basis ι ℝ (ι → ℝ)) : Invertible (basis_matrix B) :=
  (Pi.basisFun ℝ ι).invertibleToMatrix B

-- temp name
def matrix_basis (B' : Matrix ι ι ℝ) [inv : Invertible B'] : Module.Basis ι ℝ (ι → ℝ) :=
  Basis.map (Pi.basisFun ℝ ι) (Matrix.toLinearEquiv' B' inv)

@[simp]
theorem matrix_basis_inverse (B' : Matrix ι ι ℝ) [inv : Invertible B']
  : basis_matrix (matrix_basis B') = B' := by
    unfold matrix_basis
    unfold basis_matrix Module.Basis.toMatrix
    ext i j
    simp only [Basis.map_apply, Pi.basisFun_apply, Pi.basisFun_repr]
    change (B'.toLinearEquiv' inferInstance : Module.End ℝ (ι → ℝ)) (Pi.single j 1) i = B' i j
    rw [Matrix.toLinearEquiv'_apply B' inferInstance]
    simp only [Matrix.toLin'_apply, Matrix.mulVec_single, MulOpposite.op_one, Pi.smul_apply,
      Matrix.col_apply, one_smul]

-- shows that the basis is the columns
theorem matrix_basis_list
  (B' : Matrix ι ι ℝ) [Invertible B'] (i) : matrix_basis B' i = B'.col i := by
    unfold matrix_basis
    simp only [Basis.map_apply, Pi.basisFun_apply]
    ext j
    change (B'.toLinearEquiv' inferInstance : Module.End ℝ (ι → ℝ)) (Pi.single i 1) j = B' j i
    simp only [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply, Matrix.mulVec_single,
      MulOpposite.op_one, Pi.smul_apply, Matrix.col_apply, one_smul]


@[simp]
theorem basis_matrix_inverse (B : Module.Basis ι ℝ (ι → ℝ))
  : matrix_basis (basis_matrix B ) = B := by
    ext i j
    simp only [matrix_basis_list, Matrix.col_apply]
    unfold basis_matrix  Module.Basis.toMatrix
    simp only [Pi.basisFun_repr]

theorem basis_matrix_list (B : Module.Basis ι ℝ (ι → ℝ)) (i)
  : B i = (basis_matrix B ).col i  := by
    rw [←basis_matrix_inverse B]
    rw [matrix_basis_list]
    congr
    exact Eq.symm (basis_matrix_inverse B)

theorem matrix_basis_refl (A : Matrix ι ι ℝ) (B : Matrix ι ι ℝ) (h : A = B)
  [invA : Invertible A] [inv : Invertible B]
  : matrix_basis A = matrix_basis B := by
    subst h
    ext i x : 2
    rfl

theorem basis_matrix_injective : Function.Injective (basis_matrix (ι := ι) )  := by
  intro b b' bb'
  rw [←basis_matrix_inverse b]
  rw [←basis_matrix_inverse b']
  exact matrix_basis_refl _ _ bb'

end basis_matrix

abbrev 𝓛.ofBasis (B : Basis ι ℝ (ι → ℝ)) : 𝓛 ι := Submodule.span ℤ (Set.range B)

/--arbitrary basis -/
noncomputable def 𝓛.toBasis : Basis ι ℝ (ι → ℝ) := (IsZLattice.basis Λ).ofZLatticeBasis ℝ
@[simp]
theorem 𝓛.ofBasis_of_toBasis : ofBasis Λ.toBasis = Λ := Basis.ofZLatticeBasis_span ℝ Λ (IsZLattice.basis Λ)




-- temp name
theorem 𝓛.dualLattice.limit_basis (B : Basis ι ℝ (ι → ℝ)) (x : ι → ℝ) :
  x ∈ (dualLattice (𝓛.ofBasis B)) ↔
  ∀ i, x ⬝ᵥ (B i) ∈ Casts.IntSubmodule
  := by
    change (∀ v ∈ (𝓛.ofBasis B), x ⬝ᵥ v ∈ Casts.IntSubmodule) ↔ ∀ (i : ι), x ⬝ᵥ B i ∈ Casts.IntSubmodule
    refine ⟨?_,?_⟩
    intro aa i
    apply aa (B i) ?_
    exact Submodule.mem_span_of_mem (Set.mem_range_self i)

    intro q
    apply Submodule.span_induction
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact q
    simp only [dotProduct_zero, zero_mem]
    intro x_1 y hx hy a a_1
    simp_all only [dotProduct_add]
    apply AddMemClass.add_mem
    · simp_all only
    · simp_all only
    intro z a aB pa
    simp only [dotProduct_smul _ _]
    rw [Casts.IntSubmodule.exist _] at pa ⊢
    obtain ⟨i, pa'⟩ := pa
    refine ⟨z * i, ?_⟩
    simp_all only [Int.cast_mul, zsmul_eq_mul]


lemma 𝓛.dualLattice.limit_basis' (B : Basis ι ℝ (ι → ℝ)) (x : ι → ℝ) :
  x ∈ (dualLattice (𝓛.ofBasis B)) ↔
  (basis_matrix B).transpose.mulVec x ∈ Casts.Zn ι
  := by
    rw [Casts.Zn.eq_pi]
    set wp: Submodule ℤ (ι → ℝ) := Submodule.pi Set.univ (fun _ => Casts.IntSubmodule)
    rw [limit_basis]
    simp_rw [basis_matrix_list B]
    set B' := basis_matrix B
    simp_rw [dotProduct_comm x _]

    change (∀ (i : ι), B'.transpose.mulVec x i ∈ Casts.IntSubmodule) ↔ _

    constructor
    intro ww
    simp_all only [Submodule.mem_pi, Set.mem_univ, imp_self, implies_true, B', wp]
    intro a i
    simp_all only [Submodule.mem_pi, Set.mem_univ, forall_const, wp, B']

lemma 𝓛.dualLattice.limit_basis'' (B : Basis ι ℝ (ι → ℝ)) :
  (dualLattice (𝓛.ofBasis B)) =
  ZLattice.comap ℝ (Casts.Zn ι) ((basis_matrix B).transpose.toLinearEquiv' inferInstance)
  := by
    ext x
    exact limit_basis' B x



lemma 𝓛.dualLattice.limit_basis''' (B : Basis ι ℝ (ι → ℝ)) :
  (dualLattice (𝓛.ofBasis B)) =
  (Casts.Zn ι).comap ((basis_matrix B).transpose.toLinearEquiv' inferInstance).toIntLinearEquiv
  := by
    #check Submodule.map
    ext x
    exact limit_basis' B x


theorem Casts.Zn_ofBasis : Casts.Zn ι = 𝓛.ofBasis (Pi.basisFun ℝ ι) := by
  unfold 𝓛.ofBasis
  ext x
  rw [Casts.Zn.exist]
  rw [Module.Basis.mem_span_iff_repr_mem]
  simp only [algebraMap_int_eq, Int.coe_castRingHom, Pi.basisFun_repr, Set.mem_range]


theorem 𝓛.basis_matrix_repr_leftInverse (B : Basis ι ℝ (ι → ℝ)) : Function.LeftInverse (basis_matrix B).mulVec (B.repr ·) := by
  refine Function.leftInverse_iff_comp.mpr ?_
  funext x i
  simp only [Function.comp_apply, Basis.toMatrix_mulVec_repr, Pi.basisFun_repr, id_eq]

theorem 𝓛.basis_matrix_repr_rightInverse (B : Basis ι ℝ (ι → ℝ)) : Function.RightInverse (basis_matrix B).mulVec (B.repr · ) := by
  refine Function.rightInverse_of_injective_of_leftInverse ?_ ?_
  exact Matrix.mulVec_injective_of_invertible (basis_matrix B)
  exact basis_matrix_repr_leftInverse B

lemma 𝓛.basis_matrix_map (B : Basis ι ℝ (ι → ℝ)) :
  𝓛.ofBasis B = (Casts.Zn ι).map ((basis_matrix B).toLinearEquiv' inferInstance).toIntLinearEquiv
  := by
    ext x
    rw [Casts.Zn_ofBasis]
    simp only [Submodule.mem_map, AddEquiv.coe_toIntLinearEquiv, AddEquiv.coe_mk,
      Matrix.toLinearEquiv'_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk, Matrix.toLin'_apply]
    have tt y : (basis_matrix B).mulVec y = x ↔ (B).repr x = y := by
      constructor
      intro rfl
      apply 𝓛.basis_matrix_repr_rightInverse B
      intro rfl
      apply 𝓛.basis_matrix_repr_leftInverse B
    simp_rw [tt]
    simp_rw [Basis.mem_span_iff_repr_mem]
    simp only [algebraMap_int_eq, Int.coe_castRingHom, Set.mem_range, ↓existsAndEq,
      Pi.basisFun_repr, and_true]


lemma 𝓛.dualLattice.limit_basis'''' (B : Basis ι ℝ (ι → ℝ)) :
  (dualLattice (𝓛.ofBasis B)) =
  (Casts.Zn ι).map ((⅟(basis_matrix B)).transpose.toLinearEquiv' inferInstance).toIntLinearEquiv
  := by
    convert_to
      dualLattice (ofBasis B) =
        Submodule.map
          (((basis_matrix B).transpose).toLinearEquiv' inferInstance).toAddEquiv.toIntLinearEquiv.symm
          (Casts.Zn ι)

    rw [limit_basis''' B]
    set pp := ((basis_matrix B).transpose.toLinearEquiv' inferInstance).toAddEquiv.toIntLinearEquiv
    apply SetLike.ext'_iff.mpr

    rw [Submodule.comap_coe]
    rw [Submodule.map_coe]
    exact Eq.symm (LinearEquiv.image_symm_eq_preimage pp ↑(Casts.Zn ι))

def 𝓛.dualBasis (B : Basis ι ℝ (ι → ℝ)) := (matrix_basis (⅟(basis_matrix B)).transpose)

theorem 𝓛.dualBasis_spec (B : Basis ι ℝ (ι → ℝ)) :
  (dualLattice (𝓛.ofBasis B)) =
  𝓛.ofBasis (𝓛.dualBasis B) := by
    unfold dualBasis

    rw [𝓛.dualLattice.limit_basis'''', basis_matrix_map]
    ext x : 1
    simp_all only [Submodule.mem_map, AddEquiv.coe_toIntLinearEquiv, AddEquiv.coe_mk, Matrix.toLinearEquiv'_apply,
      Matrix.invOf_eq_nonsing_inv, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.invFun_eq_symm,
      Equiv.coe_fn_mk, Matrix.toLin'_apply, matrix_basis_inverse]


theorem 𝓛.dualLattice_by_basis :
  Λ.dualLattice =
  𝓛.ofBasis (𝓛.dualBasis Λ.toBasis) := by
  rw [←𝓛.dualBasis_spec, ofBasis_of_toBasis]



theorem 𝓛.dualBasis_involutive : Function.Involutive (𝓛.dualBasis (ι := ι)) := by
  intro B
  unfold dualBasis

  set Y := (⅟(basis_matrix B)).transpose
  change matrix_basis (⅟(basis_matrix (matrix_basis Y))).transpose = B
  let B' := basis_matrix B
  apply basis_matrix_injective
  simp only [matrix_basis_inverse, Matrix.invOf_eq_nonsing_inv]
  subst Y

  rw [Matrix.transpose_invOf (basis_matrix B)]
  simp only [Matrix.invOf_eq_nonsing_inv, Matrix.inv_inv_of_invertible, Matrix.transpose_transpose]


instance : DiscreteTopology (Λ.dualLattice) := by
  rw [𝓛.dualLattice_by_basis Λ]
  exact ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite
      (𝓛.dualBasis Λ.toBasis)


instance [DiscreteTopology Λ] [IsZLattice ℝ Λ] : IsZLattice ℝ (Λ.dualLattice) := by
  convert instIsZLatticeRealSpan (𝓛.dualBasis Λ.toBasis)
  exact 𝓛.dualLattice_by_basis Λ


theorem 𝓛.dualLattice_involutive : Λ.dualLattice.dualLattice = Λ := by
  nth_rw 2 [dualLattice_by_basis]
  rw [dualBasis_spec, dualBasis_involutive]
  exact ofBasis_of_toBasis Λ

theorem 𝓛.dualLattice_involutive' (L : 𝓛 ι) [DiscreteTopology ↥L]
  [IsZLattice ℝ L] : Λ.dualLattice = L ↔ L.dualLattice = Λ := by
  constructor <;>
  · intro rfl
    exact dualLattice_involutive _



example [DecidableEq ι] (B : Module.Basis ι ℝ (ι → ℝ)) : False := by

  let iden : Module.Basis ι ℝ (ι → ℝ) := Pi.basisFun ℝ ι
  let B' := iden.toMatrix B
  -- example: B as a function goes through the columns of B' (columns are of the same shape as Bx)
  have examp t : B'.col t = B t := by
    ext w
    unfold B' iden
    unfold Module.Basis.toMatrix
    simp only [Pi.basisFun_repr, Matrix.col_apply]


  have : Invertible (B') := Module.Basis.invertibleToMatrix iden B
  let B'_dual := this.invOf.transpose

  have B'_dual_invertible : Invertible (B'_dual) := (⅟B').invertibleTranspose
  have B'_tr_invertible : Invertible (B'.transpose) := by exact B'.invertibleTranspose


  let tt := Matrix.toLinearEquiv' B'_dual B'_dual_invertible

  let B_dual : Module.Basis ι ℝ (ι → ℝ) := matrix_basis B'_dual

  have B_dual_spec : iden.toMatrix B_dual = B'_dual := by
    exact matrix_basis_inverse B'_dual



  #check Finsupp.linearCombination

  #check Module.Basis.map


  let Λ := Submodule.span ℤ (Set.range B)
  let Λ_dual := Submodule.span ℤ (Set.range B_dual)
  have key : 𝓛.dualLattice Λ = Λ_dual := by



    sorry




  sorry

-- this actually is related
#check Module.Dual


theorem 𝓛.basis_ind'
  {motive : (Λ : 𝓛 ι) → (_ : DiscreteTopology ↥Λ) → (IsZLattice ℝ Λ) → Prop}
  : ((a : Basis ι ℝ (ι → ℝ)) → motive (𝓛.ofBasis a) (
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite a) (instIsZLatticeRealSpan a)
    )
  → (Λ : 𝓛 ι) → (dt : DiscreteTopology ↥Λ) → (zl: IsZLattice ℝ Λ) → motive Λ dt zl :=
  sorry

#check Quotient.ind
theorem 𝓛.basis_ind
  {motive : (Λ : 𝓛 ι) → Prop}
  (Λ : 𝓛 ι) [dt : DiscreteTopology ↥Λ] [zl: IsZLattice ℝ Λ]
  (prf : (B : Basis ι ℝ (ι → ℝ)) → motive (𝓛.ofBasis B))
  : motive Λ := Λ.ofBasis_of_toBasis ▸ prf (Λ.toBasis)


theorem 𝓛.minimum_distance_sup.positive [Nonempty ι] : NeZero (𝓛.minimum_distance_sup Λ) := by
  constructor
  apply pos_iff_ne_zero.mp
  apply basis_ind Λ
  -- apply basis_ind (motive := fun Λ ↦ 0 < Λ.minimum_distance_sup)
  intro B
  unfold minimum_distance_sup minimum_distance
  have := 𝓛.ofBasis_of_toBasis Λ
  let e : ℝ≥0 := sorry -- shortest basis vector length
  have e_pos : 0 < e := sorry
  apply lt_of_lt_of_le e_pos

  set p := {y | ∃ x ∈ ofBasis B, ∃ (_ : x ≠ 0), ‖x‖₊ = y}

  have e_bound : ∀y ∈ p, e ≤ y := sorry
  have p_nonempty : p.Nonempty := sorry
  exact ConditionallyCompleteLattice.le_csInf p e p_nonempty e_bound





end lattices
