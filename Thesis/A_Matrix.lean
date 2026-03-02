import Mathlib

section A_Matrix

def A_Matrix (n m q : ℕ) : Type := Matrix (Fin n) (Fin m) (ZMod q)

instance A_Matrix.instFinite {n m q : ℕ} [NeZero q] : Finite (A_Matrix n m q) := Matrix.instFinite (ZMod q)
instance {n m q : ℕ} [NeZero q] : Nonempty (A_Matrix n m q) := Equiv.nonempty Matrix.of.symm

-- set_option trace.Meta.synthInstance true in
example (q)  [NeZero q] : Algebra ℤ (ZMod q) := inferInstance

#eval (List.range 10).map ((↑) : _ → ℤ) |>.map (Algebra.linearMap ℤ (ZMod 3))


def A_Matrix.syndrome_map {n m q : ℕ} (A : A_Matrix n m q) : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ZMod q) := by
  -- have := Matrix.toLin (m := Fin n) (n := Fin m) (R := ZMod q) sorry sorry
  let vl:= (Matrix.mulVecLin A).toAddMonoidHom.toIntLinearMap

  let toZModLin (q) : ℤ →ₗ[ℤ] (ZMod q) := Algebra.linearMap ℤ (ZMod q)
  -- have this be →ₗ[ℤ] as well
  -- is converting to ZMod q the same before or after "this"?
  let : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ZMod q) := by
    exact (toZModLin q).compLeft (Fin m)


  refine vl.comp this


-- this shows that modulo can be done before or after
example (q : ℕ) (a b : ℤ) : ((a : ZMod q) * (b : ZMod q)) = ↑(a * b) := by
  simp only [Int.cast_mul]

def A_Matrix.syndrome_map' {n m q : ℕ} (A : A_Matrix n m q) : (Fin m → ℤ) → (Fin n → ZMod q) := by
  intro x
  apply A.mulVec <| Int.cast ∘ x


theorem A_Matrix.syndrome_map_linearCombination {n m q : ℕ} (A : A_Matrix n m q) (x) :
  A.syndrome_map x = (Fintype.linearCombination ℤ fun a a_1 ↦ A a_1 a) x := by
  unfold syndrome_map

  simp only [LinearMap.coe_comp, AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe,
    Function.comp_apply, Matrix.mulVecBilin_apply]
  ext i
  simp [Fintype.linearCombination_apply ]
  simp [Matrix.mulVec, dotProduct]
  congr 1
  ext j
  exact Eq.symm (Int.cast_comm (x j) (A i j))


section testing
-- open Plausible



-- instance {q} : Arbitrary (ZMod q) :=
--   match q with
--     | 0 => Int.Arbitrary
--     | _ + 1 => Fin.Arbitrary
-- instance {q} : Shrinkable (ZMod q) :=
--   match q with
--     | 0 => Int.shrinkable
--     | _ + 1 => Fin.shrinkable
-- #test ∀i : (ZMod 5), i + 0 = i
-- #test ∀i : (Fin 2 → Fin 2), i + 0 = i

-- -- experimentally checks that syndrome_map is correct
-- #eval Testable.check
--     (∀ ee : _ → _ → (ZMod _),
--     let A : A_Matrix 3 4 5 := Matrix.of ee;
--     ∀xx, A.syndrome_map xx = A.syndrome_map' xx)
--   {traceSuccesses := true}



end testing

#check DiscreteMeasurableSpace
-- #check OpensMeasurableSpace

instance A_Matrix.instMeasurableSpace (n m q : ℕ) [NeZero q] : MeasurableSpace (A_Matrix n m q) := ⊤
example (n m q : ℕ) [NeZero q] : DiscreteMeasurableSpace (A_Matrix n m q) := inferInstance

open MeasureTheory

noncomputable def A_Matrix.uniform {n m q : ℕ} [NeZero q] : ProbabilityMeasure (A_Matrix n m q) :=
  ⟨ProbabilityTheory.uniformOn Set.univ,
  ProbabilityTheory.uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty⟩

noncomputable instance {n m q : ℕ} [NeZero q] : MeasureSpace (A_Matrix n m q) where
  volume := @A_Matrix.uniform n m q _



open MeasureTheory
noncomputable def A_Matrix.syndrome_distributed {n m q : ℕ} [NeZero q] (A : A_Matrix n m q)
  (e : ProbabilityMeasure (Fin m → ℤ))
  := e.map (f := A.syndrome_map) (AEMeasurable.of_discrete)

end A_Matrix
