-- import Thesis.A_Matrix
import Mathlib

-- lemma 5.3 seems like it uses a claim that with Prime q, for nonzero s, the distribution A ↦ As is uniform
variable {n m q : ℕ} [NeZero n] [NeZero m] [NeZero q]
universe u
example (q : ℕ) (q_prime : Fact <| Nat.Prime q) : Field (ZMod q) := by infer_instance



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

#check AddHom

-- UniformLeftAbsorbing
-- UniformRightAbsorbing
-- UniformAbsorbing
-- shorten Uniform to U?

-- what's the name for an element where x*x=x? idempotent?

-- then for n-ary operations

/--f U U = U-/
abbrev UIdempotent (f : α → β → γ) := UHom (f.uncurry)
-- variable {α β γ : Type u} in
-- noncomputable example (F : α → β → γ) (A : PMF α) (B : PMF β) : False := by
--   let u := do {
--     let a ← A
--     let b ← B
--     return F a b
--   }
--   revert u
--   change
--     let u := do
--       A >>= fun a ↦ B >>= fun b ↦ pure (F a b);
--     False
--   sorry

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
  : PMF.map f (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
    ext x
    open scoped Classical in

    simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
    -- simp_rw [←Set.indicator_apply]
    set b := (↑(Fintype.card β) : ENNReal)
    set a := (↑(Fintype.card α) : ENNReal)
    have a_pos : a ≠ 0 := by simp [a]
    have b_pos : b ≠ 0 := by simp [b]
    have a_fin : a ≠ ⊤ := by simp [a]
    have b_fin : b ≠ ⊤ := by simp [b]
    rw [←ENNReal.mul_left_inj a_pos a_fin]
    rw [←ENNReal.mul_left_inj b_pos b_fin]
    simp only [← ENNReal.tsum_mul_right, ite_mul, zero_mul]
    ring_nf
    rw [ENNReal.inv_mul_cancel (by assumption) (by assumption)]
    rw [ENNReal.mul_inv_cancel_right (by assumption) (by assumption)]
    simp only [one_mul]
    rw [tsum_eq_sum' (s := Finset.univ) (by norm_num)]
    suffices (∑ i, if x = f i then (Fintype.card β) else 0) = (Fintype.card α) by
      unfold a b
      rw [←this]
      simp only [Nat.cast_sum, Nat.cast_ite, CharP.cast_eq_zero]
    -- change (∑ i ∈ Finset.univ, if i ∈ {i | f i = x} then Fintype.card β else 0) = Fintype.card α
    have := Finset.sum_ite_mem Finset.univ {i | x = f i} (fun _ ↦ Fintype.card β)
    convert this
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.univ_inter, Finset.sum_const, smul_eq_mul]
    simp_rw [Eq.comm (a := x)]
    rw [←Fintype.card_subtype]
    rw [←Fintype.card_prod]
    apply Fintype.card_congr
    calc
      _ ≃ (y : β) × { i // f i = y } := by
        exact (Equiv.sigmaFiberEquiv f).symm
      _ ≃ (y : β) × { i // f i = x } := by
        refine Equiv.sigmaCongr (Equiv.refl _) ?_
        intro b
        exact (UHom.prf b x)
      _ ≃ (β) × { i // f i = x } := by
        exact Equiv.sigmaEquivProd β { i // f i = x }
      _ ≃ { i // f i = x } × β := by exact Equiv.prodComm β { i // f i = x }


@[simp]
theorem UHom.main' {α β : Type u}
  (f : α → β) [UHom f]
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  : f <$> (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := UHom.main _


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

@[to_additive]
noncomputable def UAbsorbing.mulOnUnits {M : Type*} [Monoid M] : UAbsorbingOn (@Mul.mul M _) (IsUnit) := by

  change ((a : M) → (bu : IsUnit a) → UHom (Units.mulRight bu.unit))
       × ((b : M) → (bu : IsUnit b) → UHom (Units.mulLeft bu.unit))
  constructor <;> infer_instance

def UAbsorbing.mul₀ {G₀ : Type*} [GroupWithZero G₀] : UAbsorbingOn (@Mul.mul G₀ _) (· ≠ 0) := by
  change ((b : G₀) → (bn0 : _) → UHom (Equiv.mulRight₀ b bn0))
       × ((b : G₀) → (bn0 : _) → UHom (Equiv.mulLeft₀ b bn0))
  constructor <;> infer_instance

-- given f : G →* H, f(G) ≃* G ⧸ (ker f) [first isomorphism theorem].
-- I think the coset isomorphic to h : f(G) is the fiber of h

#check Submodule.Quotient.addCommGroup

#check Subgroup.quotientEquivOfEq

#check MonoidHom.ker

-- found by Gemini:
#check QuotientGroup.quotientKerEquivRange

#check QuotientGroup.quotientKerEquivOfSurjective
#check QuotientGroup.quotientKerEquivOfRightInverse



@[to_additive]
def UHom.mulHomOfRightInverse {G H: Type*} [Group G] [Group H]
  (φ : G →* H)
  (ψ : H → G) (hφ : Function.RightInverse ψ ⇑φ)
  : UHom φ := by
  constructor
  intro h₁ h₂
  let ww := MonoidHom.fiberEquiv φ (ψ h₁) (ψ h₂)
  rw [hφ h₁, hφ h₂] at ww
  exact ww

@[to_additive]
noncomputable def UHom.mulHomOfSurjective {G H: Type*} [Group G] [Group H]
  (φ : G →* H) (hφ : Function.Surjective ⇑φ)
  : UHom φ := { prf := MonoidHom.fiberEquivOfSurjective hφ }



#check Finset.sum_fiberwise




end mul

end UniformPreserving

theorem A_Matrix.mulVec_const_neZero_surjective
  {n m α : Type*} [Fintype n] [DecidableEq n]
  [Field α]
  (s : n → α) (hs : s ≠ 0)
  : Function.Surjective (fun (A : Matrix n m α) ↦ A.transpose.mulVec s) := by
    intro x
    simp only
    obtain ⟨i, si_nz⟩ : ∃i, s i ≠ 0 := by
      by_contra! w
      apply hs
      funext i
      exact w i
    -- #check Matrix.of_col -- this means what we want is:
    -- use Matrix.of (Pi.single i ((s i)⁻¹ • x))
    use Matrix.of (fun a ↦ if a = i then ((s i)⁻¹ • x) else 0)
    funext j
    change ∑ i', (Matrix.of fun a ↦ if a = i then (s i)⁻¹ • x else 0).transpose j i' * s i' = x j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    change ∑ i', (if i' = i then (s i)⁻¹ • x else 0) j * s i' = x j
    simp_rw [ite_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    field

theorem A_Matrix.mulVec_const_neZero_rightInverse
  {n m α : Type*} [Fintype n] [DecidableEq n]
  [Field α]
  (s : n → α) (i : n) (hsi : s i ≠ 0)
  : Function.RightInverse
      (fun x ↦ Matrix.of (fun a ↦ if a = i then ((s i)⁻¹ • x) else 0))
      (fun (A : Matrix n m α) ↦ A.transpose.mulVec s) := by
    intro x
    funext j
    change ∑ i', (Matrix.of _).transpose j i' * s i' = x j
    change ∑ i', (if i' = i then (s i)⁻¹ • x else 0) j * s i' = x j
    simp_rw [ite_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    field


def A_Matrix.instUHom
  {n m α : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [Field α]
  (s : n → α) (i : n) (hsi : s i ≠ 0)
  : UHom (fun (A : Matrix n m α) ↦ A.transpose.mulVec s) := by
    let := (Matrix.mulVec.addMonoidHomLeft (m := m) s).comp (Matrix.transposeAddEquiv n m α |>.toAddMonoidHom)
    change UHom (this)
    exact UHom.addHomOfRightInverse this _ (mulVec_const_neZero_rightInverse s i hsi)


def A_Matrix.instUHom''
  {n m α : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [Field α]
  (s : n → α) (i : n) (hsi : s i ≠ 0)
  : UHom ((Matrix.vecMulBilin ℤ ℤ s |>.toAddMonoidHom) : Matrix n m α →+ m → α ) := by
    -- exact UHom.addHomOfRightInverse _ _ (mulVec_const_neZero_rightInverse s i hsi)
  sorry


open scoped Classical

open scoped NNReal ENNReal

#check Pi.monoidHom

#check AddHom.instAdd
-- example : AddGroup (α →+ β) := by
--   infer_instance

#check MonoidHom.instCommMonoid



lemma PMF'.subadditivity {α ι : Type*} (p : PMF α) (s : ι → (α → Prop)) :
  (p.map (fun a ↦ ∃i, s i a)) True ≤ ∑' (i : ι), (p.map (s i)) True := by
  simp only [PMF.map_apply, eq_iff_iff, true_iff]
  open scoped Classical in
  rw [ENNReal.tsum_comm]
  gcongr 1 with r
  by_cases h : ∃i, s i r
  ·
    simp only [h, ↓reduceIte]
    obtain ⟨i,v_s⟩ := h
    apply le_trans ?_ (ENNReal.le_tsum i)
    simp only [v_s, ↓reduceIte, le_refl]
  simp only [h, ↓reduceIte, zero_le]



lemma PMF'.mem_uniform_card
  {α : Type*} [Fintype α] [Nonempty α]
  (Z : Finset α)
  : (PMF.map (fun x ↦ x ∈ Z) (PMF.uniformOfFintype α)) True = Z.card / (Fintype.card (α)) := by
    simp only [PMF.map_apply, eq_iff_iff, true_iff, PMF.uniformOfFintype_apply]
    rw [←Finset.toFinset_coe Z]
    simp_rw [Set.mem_toFinset]
    simp_rw [←Set.indicator_apply (↑Z : Set α) (fun _ ↦ (↑(Fintype.card α) : ENNReal)⁻¹)]
    rw [←tsum_subtype]
    simp only [SetLike.coe_sort_coe, ENNReal.tsum_const, ENat.card_eq_coe_fintype_card,
      Fintype.card_coe, ENat.toENNReal_coe, Finset.toFinset_coe]
    rfl


variable {M α β : Type*}
  [AddGroup M]
  [AddGroup α]
  [AddCommGroup β] -- Gemini: this must be commutative, otherwise α →+ β won't necessarily form a monoid
  [Fintype M] [Nonempty M]
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]


#check AddMonoidHom.toHomAddUnits -- random
#check NonUnitalNonAssocSemiring
#check LieAlgebra
#check MonoidHom.flipHom

example (φ : M →+ α →+ β) : ∃ψ : α →+ M →+ β, ∀x y, φ x y = ψ y x  := by
  refine ⟨?_,?_⟩
  exact φ.flipHom
  exact fun _ _ ↦ rfl


variable (φ : M → α →+ β) (ψ : α → M →+ β)

-- set_option linter.unusedTactic false
omit [Nonempty α] in
theorem lemma_5_3_key
  (hφ : ∀x y, φ x y = ψ y x )
  (ψ_surj : ∀s ≠ 0, Function.Surjective (ψ s))
  (Z : Finset β)
  (hZ : 0 ∉ Z)
  : (PMF.uniformOfFintype M).map (fun A ↦ ∃v, v ∈ (φ A).range ∧ v ∈ Z) (True)
    ≤ Fintype.card α * Z.card / Fintype.card β
  := by
  conv_lhs => {
    simp only [AddMonoidHom.mem_range, exists_exists_eq_and]
    simp only [bind_pure_comp]
    change (PMF.uniformOfFintype M |>.map (fun m ↦ ∃ a, (φ m) a ∈ Z)) True
  }
  conv_rhs => {
      change (Fintype.card α : ENat) * Z.card / (Fintype.card β : ENNReal)
      rw [mul_div_assoc,
        ←ENat.card_eq_coe_fintype_card,
        ←ENNReal.tsum_one,
        ←ENNReal.tsum_mul_right,
        one_mul]
    }

  refine le_trans (PMF'.subadditivity (PMF.uniformOfFintype M) _) ?_
  suffices ∀a, (PMF.map (fun m ↦ (φ m) a ∈ Z) (PMF.uniformOfFintype M)) True ≤ (Z.card) / (Fintype.card (β)) by
    -- this "suffices" only provides structure.
    gcongr 1 with a
    exact this a
  intro a
  by_cases! ha : a = 0
  ·
    rw [ha]
    simp_rw [map_zero, hZ]

    simp only [PMF.map_apply, eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, tsum_zero,
      zero_le]


  simp_rw [hφ]
  specialize ψ_surj a ha
  set ρ := ψ a
  change (PMF.map ((· ∈ Z) ∘ ρ) (PMF.uniformOfFintype M)) True ≤ _
  simp_rw [←PMF.map_comp]
  rw [@UHom.main _ _ ρ ?_]
  rw [PMF'.mem_uniform_card]
  exact UHom.addHomOfSurjective ρ ψ_surj

example
  {M α β : Type}
  [AddGroup M]
  [AddGroup α]
  [AddCommGroup β] -- Gemini: this must be commutative, otherwise α →+ β won't necessarily form a monoid
  [Fintype M] [Nonempty M]
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  (φ : M → α →+ β) (ψ : α → M →+ β)
  (hφ : ∀x y, φ x y = ψ y x )
  (ψ_surj : ∀s ≠ 0, Function.Surjective (ψ s))
  (Z : Finset β)
  (hZ : 0 ∉ Z)
  :
  (do {
    let A ← PMF.uniformOfFintype M
    return ∃v, v ∈ (φ A).range ∧ v ∈ Z
  } : PMF Prop) (True) ≤ Fintype.card α * Z.card / Fintype.card β
  := lemma_5_3_key _ ψ hφ ψ_surj Z hZ
