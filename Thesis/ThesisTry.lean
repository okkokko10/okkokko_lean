import Mathlib


noncomputable section


open scoped NNReal ENNReal


#check IsZLattice
#check Submodule.IsLattice

abbrev Basis (ι : Type*) [Fintype ι] := Module.Basis ι ℝ (ι → ℝ)

variable {ι : Type*} [Fintype ι] (B : Basis ι)
variable (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section lattices

abbrev 𝓛 := Submodule.span ℤ (Set.range B)

-- example :=

example : DiscreteTopology (𝓛 B) := ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite B
example : IsZLattice ℝ (𝓛 B) := by infer_instance
example : Basis ι := (IsZLattice.basis Λ).ofZLatticeBasis ℝ

def dualLattice_basic : AddSubgroup (ι → ℝ) where
  carrier := { x : ι → ℝ | ∀ v ∈ Λ, x ⬝ᵥ v ∈ (Int.castAddHom ℝ |>.range)}
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

def dualLattice : Submodule ℤ (ι → ℝ) := (dualLattice_basic Λ).toIntSubmodule

theorem dualLattice.involution : Function.Involutive (dualLattice (ι := ι)) := sorry

-- #check ZSpan

def minimum_distance [NormedAddCommGroup (ι → ℝ)] : ℝ≥0 := ⨅ (x ∈ Λ) (_ : x ≠ 0), ‖x‖₊

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
def minimum_distance_sup := @minimum_distance ι _ Λ (infinity_norm)

theorem minimum_distance.positive
  -- (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology ↥Λ]
  (h : Λ ≠ ⊥) : NeZero (minimum_distance Λ) := by
  -- relies on the fact that Λ has elements other than 0, and nnnorm_eq_zero, and that Λ is discrete
  constructor
  unfold minimum_distance
  have tw (x : ι → ℝ) : ‖x‖₊ = 0 → x = 0 := nnnorm_eq_zero.mp
  #check IsZLattice

  simp only [ne_eq]
  #check NNReal.instConditionallyCompleteLinearOrderBot
  #check ConditionallyCompleteLinearOrderBot
  #check ConditionallyCompleteLattice
  change ¬(⨅x, ⨅ (_ : x ∈ Λ), ⨅ (_ : ¬x = 0), ‖x‖₊) = 0

  intro asm
  #check InfSet




  sorry



end lattices

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


def gaussianMeasure' [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s] (c : ι → ℝ)  := (gaussianMeasure s c).restrict Λ


lemma gaussianMeasure'_finite [Norm (ι → ℝ)]  (s : ℝ≥0) [NeZero s]  (c : ι → ℝ) : IsFiniteMeasure (gaussianMeasure' Λ s c) := sorry
-- def gaussianMeasure'_total [Norm (ι → ℝ)] (c : ι → ℝ) {s : ℝ≥0} (hs : s ≠ 0) := (gaussianMeasure' Λ c hs) Set.univ

-- def gaussianDistribution [Norm (ι → ℝ)] {s : ℝ≥0} (hs : s ≠ 0)  (c : ι → ℝ) := ((gaussianMeasure' Λ hs c) Set.univ)⁻¹ • gaussianMeasure' Λ hs c
def gaussianDistribution [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s]  (c : ι → ℝ) := (gaussianMeasure' Λ s c)[|Set.univ]

lemma gaussianDistribution_prob [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s] (c : ι → ℝ) : IsProbabilityMeasure (gaussianDistribution Λ s c) := by
  unfold gaussianDistribution
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
  unfold gaussianMeasure' gaussianMeasure at gm
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

  have := gaussianMeasure'_finite Λ s c
  exact this.1.ne


lemma gaussianDistribution.eq [Norm (ι → ℝ)] (s : ℝ≥0) [NeZero s] (c : ι → ℝ)
  : gaussianDistribution Λ s c = (gaussianMeasure s c)[|Λ] := by
    unfold gaussianDistribution gaussianMeasure'
    simp only [ProbabilityTheory.cond, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
      Measure.restrict_univ]


def int_gaussian_real_measure (m) [Norm (Fin m → ℝ)] (s : ℝ≥0) [NeZero s] : Measure (Fin m → ℝ)
  :=
  gaussianDistribution (AddSubgroup.toIntSubmodule (((Int.castAddHom ℝ).compLeft (Fin m)).range )) s 0



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

-- section quantities

local instance (s : ℝ≥0) [NeZero s] : NeZero s⁻¹ := .mk fun cont ↦ NeZero.out (inv_eq_zero.mp cont) in

/--
η
-/
def smoothing_parameter (ε : ℝ≥0) [NeZero ε]
  := ⨅ (s : ℝ≥0) (_ : NeZero s)
  (_ : gaussianMeasure' (dualLattice Λ) s⁻¹ 0 (Set.compl {0}) ≤ ε), s


#check EuclideanSpace
-- todo: Norm is just a notation class. theorems about defs using it need [NormedAddCommGroup]
#check NormedAddCommGroup
#check ForIn
#check Monad
def SampleD {n : ℕ} {m : ℕ} (hn : 0 < n) (gs_b : Basis (Fin n)) (s : ℝ≥0) (hs : s ≠ 0) (center : (Fin n) → ℝ) (DZ : {s' : ℝ // s' > 0} → ℝ → PMF (ℤ)) : PMF ( Fin n → ℝ)  := do {
  let mut v : ((Fin n) → ℝ)  := 0;
  let mut c : ((Fin n) → ℝ) := center;

  for hi : i in (Vector.range n).reverse do
    let fi : Fin n := ⟨i,(Vector.mem_range.mp (Vector.mem_reverse.mp hi))⟩
    let bi := gs_b fi
    let c'i : ℝ := (c ⬝ᵥ bi) / (bi ⬝ᵥ bi);
    let s'i : ℝ := s / ‖bi‖;
    have : s'i > 0 := by sorry;
    -- step (b)
    let zi ← (DZ ⟨s'i,this⟩ c'i);
    -- step (c)
    c := (c - zi • bi)
    v := (v + zi • bi)

  return v
}

#check Asymptotics.IsLittleO
open Asymptotics MeasureTheory
open ProbabilityTheory
#check ℙ

section statistic

-- f(x) = ω(g(x))
notation:100 f " =ω[" l "] " g:100 => g =o[l] f
notation:100 f " =ω " g:100 => g =o[Filter.atTop] f

def negligible {R : Type*} [Norm R] (f : ℕ → R) := ∀(c : ℕ), c > 0 → f =o[Filter.atTop] (fun (n : ℕ) ↦ (n : ℝ) ^ (-(c : ℝ)))

-- #check ProbabilityTheory.HasPDF
#check MeasureTheory.pdf

--- [https://www.cs.bu.edu/~reyzin/teaching/s11cs937/notes-leo-1.pdf]


#check PMF


#check MeasureTheory.SignedMeasure.totalVariation -- Gemini found this.


-- I need to explain this
def statistical_distance' {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D) := (2⁻¹) * (SignedMeasure.totalVariation (X.toMeasure.toSignedMeasure - Y.toMeasure.toSignedMeasure)) Set.univ
lemma statistical_distance_finite_1 {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D)
  : IsFiniteMeasure ((X.toMeasure.toSignedMeasure - Y.toMeasure.toSignedMeasure).totalVariation) := isFiniteMeasureAdd
lemma statistical_distance_finite_2 {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D)
  : statistical_distance' X Y < ∞ := by
    unfold statistical_distance'
    refine ENNReal.mul_lt_top ?_ ?_
    simp only [ENNReal.inv_lt_top, Nat.ofNat_pos]
    simp only [statistical_distance_finite_1, measure_lt_top]
def statistical_distance {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D) : ℝ≥0 := statistical_distance' X Y |>.toNNReal

instance : Norm ℝ≥0 := ⟨(↑)⟩


def statistically_close {D : (n : ℕ) →  Type*} [∀n, MeasurableSpace (D n)] (X Y : (n : ℕ) → ProbabilityMeasure (D n)) :=
  negligible (fun n ↦ statistical_distance (X n) (Y n))


-- theorem lemma_5_1 {m : ℝ≥0} {_ : 2 * n }

-- #check Mathlib.Testing.SlimCheck


def sqrt_log : ℕ → ℝ≥0 := (Real.toNNReal ∘ Real.sqrt ∘  Real.log ∘ (↑))
def ω_sqrt_log (ω : ℕ → ℝ≥0) : Prop := ω =ω sqrt_log

abbrev goes_to_infinity (f : ℕ → ℕ) : Prop := Filter.Tendsto f Filter.atTop Filter.atTop

end statistic

section hypotheses

def mHyp (m n q : ℕ) : Prop := (2 * n * Real.log q) ≤ m

end hypotheses

section Lemma_2_6

-- what log base?
theorem Lemma_2_6 (ε : ℝ≥0) [NeZero ε] [DiscreteTopology ↥Λ] [IsZLattice ℝ Λ]
  [Nonempty ι] --
  : smoothing_parameter Λ ε ≤
  (√ (Real.log (2 * Fintype.card ι / (1 + ε⁻¹)) / Real.pi)).toNNReal -- conversion to ℝ≥0 for convenience
  / minimum_distance_sup (dualLattice Λ) := by
    unfold smoothing_parameter

    sorry


/--
stronger than what the paper literally says, I think, since the dimension is not n, but instead just goes to infinity alongside n
-/
theorem Lemma_2_6_then'
  {ι : (n : ℕ) → Type*} [∀n, Fintype (ι n)] (ι_top : goes_to_infinity (Fintype.card <| ι ·)) (Λ : (n : ℕ) → Submodule ℤ ((ι n) → ℝ)) [∀n, DiscreteTopology ↥(Λ n)] [∀n, IsZLattice ℝ (Λ n)]
  (s : (n : ℕ) → ℝ≥0) (hs : ω_sqrt_log s)
  : ∃(ε : (n : ℕ) → ℝ≥0) (negl_ε : negligible ε) (ε_pos : ∀n, NeZero (ε n)), ∀n,
  smoothing_parameter (Λ n) (ε n) ≤ s n / minimum_distance_sup (dualLattice (Λ n))
  := by
    #check Lemma_2_6
    -- have ttt n ε (ε_pos : ε ≠ 0) := Lemma_2_6 (Λ n) ε_pos
    change
      ∃ ε,
        ∃ (_ : negligible ε) (ε_pos : ∀ (n : ℕ), NeZero (ε n)),
          ∀ (n : ℕ),
            smoothing_parameter (Λ n) (ε n) ≤ s n / minimum_distance_sup (dualLattice (Λ n))

    sorry

-- note: NeZero allows this to be inferred, while h : q > 0 doesn't
example  {q : ℕ} [NeZero q] : Finite (ZMod q) := inferInstance
-- instance {q : ℕ} : Zero (ZMod q) where zero := 0
end Lemma_2_6

section A_Matrix

def A_Matrix (n m q : ℕ) : Type := Matrix (Fin n) (Fin m) (ZMod q)

instance A_Matrix.instFinite {n m q : ℕ} [NeZero q] : Finite (A_Matrix n m q) := Matrix.instFinite (ZMod q)
instance {n m q : ℕ} [NeZero q] : Nonempty (A_Matrix n m q) := Equiv.nonempty Matrix.of.symm

-- set_option trace.Meta.synthInstance true in
example (q)  [NeZero q] : Algebra ℤ (ZMod q) := inferInstance

#eval (List.range 10).map ((↑) : _ → ℤ) |>.map (Algebra.linearMap ℤ (ZMod 3))


def A_Matrix.syndrome_map {n m q : ℕ} (A : A_Matrix n m q) : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ZMod q) := by
  -- have := Matrix.toLin (m := Fin n) (n := Fin m) (R := ZMod q) sorry sorry
  let vl:= Matrix.mulVecLin A

  let toZModLin (q) : ℤ →ₗ[ℤ] (ZMod q) := Algebra.linearMap ℤ (ZMod q)
  -- have this be →ₗ[ℤ] as well
  -- is converting to ZMod q the same before or after "this"?
  let : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ZMod q) := by
    exact (toZModLin q).compLeft (Fin m)
  exact Fintype.linearCombination ℤ fun a a_1 ↦ A a_1 a

  -- refine ((LinearMap.comp this vl) )


-- this shows that modulo can be done before or after
example (q : ℕ) (a b : ℤ) : ((a : ZMod q) * (b : ZMod q)) = ↑(a * b) := by
  simp only [Int.cast_mul]

def A_Matrix.syndrome_map' {n m q : ℕ} (A : A_Matrix n m q) : (Fin m → ℤ) → (Fin n → ZMod q) := by
  intro x
  apply A.mulVec <| Int.cast ∘ x

section testing
open Plausible



instance {q} : Arbitrary (ZMod q) :=
  match q with
    | 0 => Int.Arbitrary
    | _ + 1 => Fin.Arbitrary
instance {q} : Shrinkable (ZMod q) :=
  match q with
    | 0 => Int.shrinkable
    | _ + 1 => Fin.shrinkable
#test ∀i : (ZMod 5), i + 0 = i
#test ∀i : (Fin 2 → Fin 2), i + 0 = i

-- experimentally checks that syndrome_map is correct
#eval Testable.check
    (∀ ee : _ → _ → (ZMod _),
    let A : A_Matrix 3 4 5 := Matrix.of ee;
    ∀xx, A.syndrome_map xx = A.syndrome_map' xx)
  {traceSuccesses := true}



end testing

#check DiscreteMeasurableSpace
-- #check OpensMeasurableSpace

instance A_Matrix.instMeasurableSpace (n m q : ℕ) [NeZero q] : MeasurableSpace (A_Matrix n m q) := ⊤
example (n m q : ℕ) [NeZero q] : DiscreteMeasurableSpace (A_Matrix n m q) := inferInstance

def A_Matrix.uniform {n m q : ℕ} [NeZero q] : ProbabilityMeasure (A_Matrix n m q) :=
  ⟨ProbabilityTheory.uniformOn Set.univ,
  ProbabilityTheory.uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty⟩

instance {n m q : ℕ} [NeZero q] : MeasureSpace (A_Matrix n m q) where
  volume := @A_Matrix.uniform n m q _

end A_Matrix

def uniform_over_Zqn (n q : ℕ) [NeZero q] : ProbabilityMeasure (Fin n → ZMod q) :=
  ⟨ProbabilityTheory.uniformOn Set.univ,
  ProbabilityTheory.uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty⟩

#check ProbabilityTheory.uniformOn_univ


#check int_gaussian


-- "the subset-sums of the columns of A generate Zqn"
def lemma_5_1_statement {n m q : ℕ} (A : A_Matrix n m q) : Prop :=
  A.syndrome_map '' {e | ∀i, e i = 0 ∨ e i = 1} = Set.univ

-- the form seems complete
-- wait, is q_prime
theorem lemma_5_1 {n m q : ℕ} [NeZero q]  (q_prime : Nat.Prime q) (m_hyp : mHyp m n q) : ℙ (lemma_5_1_statementᶜ : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ)) := sorry

section A_Matrix

-- {e | Ae mod q = 0 }
def A_Matrix.Λ_ortho {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : AddSubgroup (Fin m → ℤ) := A.syndrome_map.toAddMonoidHom.ker

-- does it matter that this is ZMod q?
-- I wonder, a philosophical idea about a sense in which ℕ is equivalent to {0 mod 2, 1 mod 2}
def A_Matrix.Λ_main_base {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : AddSubgroup (Fin m → ZMod q) := (A_Matrix.syndrome_map (A.transpose : A_Matrix m n q)).toAddMonoidHom.range
def A_Matrix.Λ_main {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : AddSubgroup (Fin m → ℤ)
  := (A_Matrix.syndrome_map A.transpose).toAddMonoidHom.range.comap
  ((Int.castAddHom (ZMod q)).compLeft (Fin m))

-- todo: once Lattice is a definition, change this
def to_R {m} (L : AddSubgroup (Fin m → ℤ) ) : Submodule ℤ (Fin m → ℝ) := (AddSubgroup.map ((Int.castAddHom ℝ).compLeft (Fin m)) L).toIntSubmodule

def A_Matrix.Λ_ortho' {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : Submodule ℤ (Fin m → ℝ) := to_R A.Λ_ortho
def A_Matrix.Λ_main' {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : Submodule ℤ (Fin m → ℝ) := to_R A.Λ_main

theorem A_Matrix.Λ_dual {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  -- (to_R A.Λ_ortho) = (q : ℤ) • (dualLattice <| to_R A.Λ_main)
  (A.Λ_ortho') = (dualLattice <| A.Λ_main').map (LinearMap.lsmul ℤ _ q)
  := by sorry
theorem A_Matrix.Λ_dual' {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  (A.Λ_main') = (dualLattice <| A.Λ_ortho').map (LinearMap.lsmul ℤ _ q)
  := by sorry

lemma A_Matrix.Λ_ortho'.has_qZn {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) :
  ∀i, Pi.single i q ∈ (A.Λ_ortho') := by
    intro i
    refine (Submodule.mem_toAddSubgroup A.Λ_ortho').mp ?_
    unfold Λ_ortho' to_R
    simp only [AddSubgroup.toIntSubmodule_toAddSubgroup, AddSubgroup.mem_map]
    unfold Λ_ortho
    simp only [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe]
    use Pi.single i q
    constructor
    {
      ext j
      unfold syndrome_map
      simp only [Fintype.linearCombination_apply_single, Pi.smul_apply, zsmul_eq_mul,
        Int.cast_natCast, CharP.cast_eq_zero, zero_mul, Pi.zero_apply]
    }
    ext j
    simp only [AddMonoidHom.compLeft_apply, Int.coe_castAddHom, Function.comp_apply]
    by_cases h : i = j
    subst h
    simp only [Pi.single_eq_same, Int.cast_natCast]
    simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne', Int.cast_zero]





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

def A_Matrix.syndrome_distributed {n m q : ℕ} [NeZero q] (A : A_Matrix n m q)
  (e : ProbabilityMeasure (Fin m → ℤ))
  := e.map (f := A.syndrome_map) (AEMeasurable.of_discrete)

end A_Matrix

theorem lemma_5_2 {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) (ass : lemma_5_1_statement A)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0) [Fintype (Fin m)]
  (s_prop : s ≥ smoothing_parameter (A.Λ_ortho') ε) :
  let hs : NeZero s := sorry;
  statistical_distance (A.syndrome_distributed (int_gaussian m s)) (uniform_over_Zqn _ _) ≤ 2 * ε
  := sorry

theorem lemma_5_2_furthermore {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) (ass : lemma_5_1_statement A)
  (ε : ℝ≥0) [NeZero ε] (ε_bound : ε < 2⁻¹) (s : ℝ≥0) [Fintype (Fin m)]
  (s_prop : s ≥ smoothing_parameter (A.Λ_ortho') ε) (u : Fin n → ZMod q) (t : Fin m → ℤ) (ht : A.syndrome_map t = u)
  :
  let hs : NeZero s := sorry;
  -- ProbabilityTheory.cond (int_gaussian m hs) (A.syndrome_map ⁻¹' {u}) = t +ᵥ (int_gaussian_sublattice m hs A.Λ_ortho (-t))
  ProbabilityTheory.cond (int_gaussian m s) (A.syndrome_map ⁻¹' {u}) = (int_gaussian_sublattice m s A.Λ_ortho (-t)).map (f := (· + t)) (AEMeasurable.of_discrete)
  := sorry


def lemma_5_3_statement {n m q : ℕ} [NeZero q] (A : A_Matrix n m q) : Prop :=
  minimum_distance_sup (A.Λ_main') ≥ q/4

abbrev N := ℕ
abbrev M := ℕ
abbrev Q := ℕ

section hypotheses

def mHyp' (m : N → M) (q : N → Q) : Prop := ∀n, (2 * n * Real.log (q n)) ≤ m n


lemma mHyp'_ge_id (m : N → M) (q : N → Q) (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q) : id ≤ m :=
  by
  unfold mHyp' at m_hyp
  intro n
  dsimp only [id_eq]
  specialize m_hyp n
  rify
  apply le_trans ?_ m_hyp
  trans  ↑n * 2 * Real.log 2
  · clear * -
    suffices 1 ≤ 2 * Real.log 2 by
      convert_to ↑n * 1 ≤ ↑n * (2 * Real.log 2)
      · group
      · group
      refine mul_le_mul (le_refl _) this (zero_le_one' ℝ) (Nat.cast_nonneg' n)
    linarith only [Real.log_two_gt_d9]
  have tt : Real.log (2) ≤ Real.log ↑(q n) := by
    apply Real.log_le_log zero_lt_two
    simp only [Nat.ofNat_le_cast]
    apply Nat.Prime.two_le (q_prime n)
  ring_nf
  refine mul_le_mul ?_ (by rfl) zero_le_two (by positivity)
  refine mul_le_mul (by rfl) tt (by positivity) (Nat.cast_nonneg' n)

lemma mHyp'_tendsTo (m : N → M) (q : N → Q) (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  : Filter.Tendsto m Filter.atTop Filter.atTop := sorry -- use [mHyp'_ge_id]

end hypotheses

theorem lemma_5_3       {n m q : ℕ} [NeZero q] (q_prime : Nat.Prime q) (m_hyp : mHyp m n q)
  : ℙ (lemma_5_3_statementᶜ : Set <| A_Matrix n m q) ≤ (q ^ (- n : ℝ)) := sorry


theorem lemma_5_3_also (q : N → Q) [∀n, NeZero (q n)]  (m : N → M) (q_prime : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  (A : (n : N) → (A_Matrix n (m n) (q n)))(hA : ∀n, lemma_5_3_statement (A n))
  (s : (n : N) → ℝ≥0) (hs : s =ω (sqrt_log ∘ m))
  : ∃ (ε : (n : N) → ℝ≥0) (negl_ε : negligible ε) (ε_pos : ∀n, NeZero (ε n)), -- change
  ∀n : N, smoothing_parameter ((A n).Λ_ortho') (ε n) ≤ s n := by

  #check Lemma_2_6_then'
  #check A_Matrix.Λ_dual'
  let ⟨ε, negl_ε, ε_pos, so⟩ := Lemma_2_6_then' (ι := (Fin <| m ·)) ?_ (fun n ↦ (A n).Λ_ortho') (s) ?_
  use ε, negl_ε, ε_pos
  intro n
  specialize so n
  -- simp only [Function.comp_apply] at so
  specialize hA n
  set ww := smoothing_parameter (A n).Λ_ortho' (ε n)
  -- change ww ≤ _ at so
  apply le_trans so


  unfold lemma_5_3_statement at hA
  -- nth_rw 2 [A_Matrix.Λ_dual] at so





  sorry
  sorry
  have m_top := mHyp'_tendsTo _ _ q_prime m_hyp
  #check IsLittleO.comp_tendsto
  unfold ω_sqrt_log at *
  #check IsBigO.trans_isLittleO
  have : s =O[Filter.atTop] (s ∘ m) := by sorry
  -- refine IsBigO.trans_isLittleO ?_ ?_

  sorry


-- hmm, in Corollary 5.4, "statistically close" describes what happens as n varies, but A is conditioned on n. this means statistically_close does not fit
-- what does it mean?

-- the distribution of the syndrome is statistically close to uniform
-- statistically close = statistical distance is negligible in n
-- blackboard: (A, Ax mod q) ≈ (A, y)     f m ≥ ...
-- is it expressed that the distribution sampled from (A : Uniform,e : Gaussian) to (A, Ae mod q), is compared to the distribution (A : Uniform, y: Uniform),
--  and these distributions have type [ProbabilityMeasure ()]
#check let n :=5; let m := 7; let q := 10;
  ProbabilityMeasure ((A_Matrix n m q) × (Fin n → ZMod q))




-- example (q : ℕ → ℕ) (m : ℕ → ℕ)

-- this collection of subsets have all but 2q^-n values
def corollary_5_4_condition {q : N → Q} [∀n, NeZero (q n)] {m : N → M} (subsets : (n : N) → Set (A_Matrix n (m n) (q n)))
  := (∀n, ℙ (subsets n) ≤ 2 * ((q n) ^ (- n : ℝ)))


def corollary_5_4_statement (q : N → Q) [∀n, NeZero (q n)]  (m : N → M)
  (A : (n : N) → A_Matrix n (m n) (q n)) (s : N → ℝ≥0) (s_pos : ∀n, NeZero (s n)) :=
    statistically_close
      (fun n ↦ (A n).syndrome_distributed (int_gaussian (m n) (s n)))
      (fun n ↦ uniform_over_Zqn n (q n))


theorem corollary_5_4 (q : N → Q) [∀n, NeZero (q n)]  (m : N → M) (q_hyp : ∀n, Nat.Prime (q n)) (m_hyp : mHyp' m q)
  : ∃(subsets : (n : N) → Set (A_Matrix n (m n) (q n)))(_ : corollary_5_4_condition subsets),
  ∀(A : (n : N) → (A_Matrix n (m n) (q n)))(_ : ∀n, A n ∈ subsets n),
  ∀(s : N → ℝ≥0)(_ : s =ω (sqrt_log ∘ m)) (s_pos : ∀n, NeZero (s n)) , -- ≥ω is the same as =ω, right?
  corollary_5_4_statement q m A s s_pos
  := by


  sorry

-- should s be a function of m?

-- idea: have m be N → M, to not confuse variables

-- unrelated idea: Module with polynomials as the scalars.
