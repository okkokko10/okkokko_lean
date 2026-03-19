import Thesis.A_Matrix
import Thesis.MyLattice

noncomputable section

section A_Matrix

-- {e | Ae mod q = 0 }
-- def A_Matrix.Λ_ortho {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : AddSubgroup (Fin m → ℤ) := A.syndrome_map.toAddMonoidHom.ker

-- helper. todo: make global
def coeSubmodule {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {A : Submodule R M} (B : Submodule R A)
  : Submodule R M
  := B.map (Submodule.subtype _) -- AI suggestion, coerce submodule of submodule


def A_Matrix.Λ_ortho' {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : 𝓛 (Fin m) :=
  coeSubmodule <| LinearMap.ker A.syndromeMap

-- does it matter that this is ZMod q?
-- I wonder, a philosophical idea about a sense in which ℕ is equivalent to {0 mod 2, 1 mod 2}
-- def A_Matrix.Λ_main_base {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : AddSubgroup (Fin m → ZMod q) := (A_Matrix.syndrome_map (A.transpose : A_Matrix m n q)).toAddMonoidHom.range
-- def A_Matrix.Λ_main {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : AddSubgroup (Fin m → ℤ)
--   := (A_Matrix.syndrome_map A.transpose).toAddMonoidHom.range.comap
--   ((Int.castAddHom (ZMod q)).compLeft (Fin m))


def A_Matrix.syndromes {n m q : ℕ} (A : A_Matrix n m q) : Submodule ℤ (Zqn n q) := LinearMap.range A.syndromeMap

def A_Matrix.Λ_main'' {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : Submodule ℤ (Fin m → ZMod q)
  := syndromes A.transpose

def A_Matrix.Λ_main' {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : 𝓛 (Fin m)
  := coeSubmodule <| A.Λ_main''.comap Casts.ZnToZqn


-- def to_R {m} (L : AddSubgroup (Fin m → ℤ) ) : 𝓛 (Fin m) := (L.map ((Int.castAddHom ℝ).compLeft (Fin m))).toIntSubmodule



-- def A_Matrix.Λ_ortho' {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : 𝓛 (Fin m) := to_R A.Λ_ortho
-- def A_Matrix.Λ_main' {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : 𝓛 (Fin m) := to_R A.Λ_main
open scoped Pointwise in
theorem A_Matrix.Λ_dual {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  -- (to_R A.Λ_ortho) = (q : ℤ) • (dualLattice <| to_R A.Λ_main)
  (A.Λ_ortho') = (q : ℝ) • (𝓛.dualLattice <| A.Λ_main')
  := by sorry
open scoped Pointwise in
theorem A_Matrix.Λ_dual' {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  (A.Λ_main') = (q : ℝ) • (𝓛.dualLattice <| A.Λ_ortho')
  := by sorry

lemma A_Matrix.Λ_ortho'.has_qZn {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  ∀i, Pi.single i q ∈ (A.Λ_ortho') := by
    sorry
    -- intro i
    -- refine (Submodule.mem_toAddSubgroup A.Λ_ortho').mp ?_
    -- unfold Λ_ortho' to_R
    -- simp only [AddSubgroup.toIntSubmodule_toAddSubgroup, AddSubgroup.mem_map]
    -- unfold Λ_ortho
    -- simp only [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe]
    -- use Pi.single i q
    -- constructor
    -- {
    --   ext jacobiSum
    --   simp only [syndrome_map_linearCombination, Fintype.linearCombination_apply_single,
    --     Pi.smul_apply, zsmul_eq_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul, Pi.zero_apply]
    -- }
    -- ext j
    -- simp only [AddMonoidHom.compLeft_apply, Int.coe_castAddHom, Function.comp_apply]
    -- by_cases h : i = j
    -- subst h
    -- simp only [Pi.single_eq_same, Int.cast_natCast]
    -- simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne', Int.cast_zero]





#check instIsZLatticeComap
#check Submodule.IsLattice

instance A_Matrix.Λ_ortho'.instDiscreteTopology {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  DiscreteTopology ↥(A.Λ_ortho') := sorry
instance A_Matrix.Λ_ortho'.instIsZLattice {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  IsZLattice ℝ (A.Λ_ortho') := sorry
instance A_Matrix.Λ_main'.instDiscreteTopology {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  DiscreteTopology ↥(A.Λ_main') := sorry
instance A_Matrix.Λ_main'.instIsZLattice {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  IsZLattice ℝ (A.Λ_main') := sorry


end A_Matrix
