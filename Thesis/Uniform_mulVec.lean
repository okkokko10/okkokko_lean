-- import Thesis.A_Matrix
import Mathlib

-- lemma 5.3 seems like it uses a claim that with Prime q, for nonzero s, the distribution A ↦ As is uniform
variable {n m q : ℕ} [NeZero n] [NeZero m] [NeZero q]
universe u
example (q : ℕ) (q_prime : Fact <| Nat.Prime q) : Field (ZMod q) := by infer_instance

abbrev A_Matrix (n m q : ℕ) := Matrix (Fin n) (Fin m) (ZMod q)

-- wait, equivalences preserve uniform distribution

-- theorem A_Matrix.uniform_of_uniform_vecMul_const
--     (s : Fin n → ZMod q)
--     : (@A_Matrix.uniform n m q _ |>.map ( f:= fun A : A_Matrix n m q ↦ A.transpose.mulVec s) sorry).toMeasure
--       = ProbabilityTheory.uniformOn (@Set.univ _) := sorry

-- theorem ZMod_uniform_of_const_mul_uniform {q : ℕ} [NeZero q]
-- #check ZMod.AddAutEquivUnits
-- #check ZMod.ringEquivOfPrime -- that's cool. maybe irrelevant


-- #check ProbabilityTheory.uniformOn
#check PMF.uniformOfFinset
#check Set.BijOn
#check PMF.seq

-- open PMF
set_option trace.aesop true

section PMF'


section uniform_preserving

variable {G : Type*} [Group G] [Fintype G] [Nonempty G] (a : G)



-- idea: UniformPreserving can be extended as mapping the counting measure to a scalar multiple of the counting measure
-- this is because the finite uniform probability is the only probability measure that is a scalar multiple of the counting measure
-- wait, what if the domain has greater cardinality?

-- I wish you could use do? to desugar a do expression

-- the idea is that if `∀x, UniformPreserving (f x)`, then f X U for any distribution X
-- @[to_additive, simp, local aesop safe apply]
-- theorem upre.bi.Group.mul'
--   (P : PMF G)
--   :
--     do {
--       let x ← P
--       let y ← PMF.uniformOfFintype G
--       return x * y
--     } = PMF.uniformOfFintype _ := by
--   -- change (P >>= fun x ↦ (PMF.uniformOfFintype G >>= fun y ↦ pure (x * y))) = PMF.uniformOfFintype G
--   -- change (PMF.bind P fun x ↦ ((PMF.uniformOfFintype G).bind fun y ↦ pure (x * y))) = PMF.uniformOfFintype G
--   -- dsimp [PMF.monad_map_eq_map]
--   simp only [bind_pure_comp]
--   simp [PMF.monad_map_eq_map,Group.const_mulLeft]
--   simp [bind]

open scoped BigOperators


/-
I want to express that a function preserves uniform distribution
maybe without bringing in Fintype and Nonempty
```class UniformPreserving {α β : Type*} (f : α → β) where prf := ∀b₁ b₂, f ⁻¹' {b₁} ≃ f ⁻¹' {b₂}```
-/
#check Equiv.ofFiberEquiv -- this is similar
#check Equiv.sigmaFiberEquiv
#check Function.Fiber -- this ignores values outside the range

#check MeasureTheory.pdf.IsUniform

section UniformPreserving

variable {α β γ : Type*} (f : α → β)


#check ZeroHom -- name inspired

class UHom (f : α → β) where
  prf b₁ b₂ : {x₁ // f x₁ = b₁} ≃ {x₂ // f x₂ = b₂}
-- [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
variable [f_upr : UHom f]

instance (e : α ≃ β) : UHom e where
  prf b₁ b₂ := by
    simp_rw [Eq.comm,←Equiv.symm_apply_eq e]
    exact Equiv.ofUnique { x₁ // e.symm b₁ = x₁ } { x₂ // e.symm b₂ = x₂ }

#check TensorProduct --unrelated

noncomputable instance (e : α → β) (bij : Function.Bijective e) : UHom e := inferInstanceAs (UHom (Equiv.ofBijective e bij))

variable (F : α → β → γ)



-- UniformLeftAbsorbing
-- UniformRightAbsorbing
-- UniformAbsorbing
-- shorten Uniform to U?

-- what's the name for an element where x*x=x? idempotent?

-- then for n-ary operations

/--f U U = U-/
abbrev UIdempotent (f : α → β → γ) := UHom (f.uncurry)
variable {α β γ : Type u} in
noncomputable example (F : α → β → γ) (A : PMF α) (B : PMF β) : False := by
  let u := do {
    let a ← A
    let b ← B
    return F a b
  }
  revert u
  change
    let u := do
      A >>= fun a ↦ B >>= fun b ↦ pure (F a b);
    False
  sorry

#check Equiv.curry
example  (f : α → β → γ)  : Function.uncurry f = fun (x,y) ↦ f x y := rfl
abbrev ULeftAbsorbing (f : α → β → γ) := ∀b, UHom (f · b)
abbrev URightAbsorbing (f : α → β → γ) := ∀a, UHom (f a)
abbrev UAbsorbing (f : α → β → γ) := ULeftAbsorbing f × URightAbsorbing f

-- if the other distribution is in s, U is preserved
abbrev ULeftAbsorbingOn (f : α → β → γ) (s : Set β) := ∀b ∈ s, UHom (f · b)
abbrev URightAbsorbingOn (f : α → β → γ) (s : Set α) := ∀a ∈ s, UHom (f a)
abbrev UAbsorbingOn (f : α → α → γ) (s : Set α) := ULeftAbsorbingOn f s × URightAbsorbingOn f s


-- abbrev PiUAbsorbing (f : (α → β) → γ)

-- theorem UAbsorbing.by_foldl
--   [UAbsorbing F]
--   :




#check MonoidWithZero





-- great note: As is a linear combination of A (Pi.single i 1)


-- I wonder, could it be true that this is equivalent to UniformPreserving F

@[simp]
theorem UHom.main
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  : PMF.map f (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := sorry

@[simp]
theorem UHom.main' {α β : Type u}
  (f : α → β) [UHom f]
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  : f <$> (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := sorry


-- [mul_boole]
example {α : Type*} [MulZeroOneClass α] (P : Prop) [Decidable P] (x : α)
  : (if P then x else 0) = x * if P then 1 else 0
  := by
    exact Eq.symm (mul_boole P x)

section mul

@[to_additive]
def UAbsorbing.mul {G : Type*} [Group G] : UAbsorbing (@Mul.mul G _) := by
  change ((b : G) → UHom (Equiv.mulRight b)) × ((a : G) → UHom (Equiv.mulLeft a))
  constructor <;> infer_instance
#check MulActionWithZero

@[to_additive]
def UAbsorbing.mulAction {G X : Type*} [Group G] [MulAction G X] : URightAbsorbing (@SMul.smul G X _) := by
  change  ((a : G) → UHom (MulAction.toPerm a))
  infer_instance

noncomputable def UAbsorbing.mulOnUnits {M : Type*} [Monoid M] : UAbsorbingOn (@Mul.mul M _) (IsUnit) := by

  change ((a : M) → (bu : IsUnit a) → UHom (Units.mulRight bu.unit))
        × ((b : M) → (bu : IsUnit b) → UHom (Units.mulLeft bu.unit))
  constructor <;> infer_instance

-- def UAbsorbing.mul₀ {G₀ : Type*} [GroupWithZero G₀] : UAbsorbingOn (@Mul.mul G₀ _) (· ≠ 0) := by

--   change ((b : G₀) → (bn0 : _) → UHom (Equiv.mulRight₀ b bn0))
--     × _
--   constructor <;> infer_instance


end mul

end UniformPreserving
