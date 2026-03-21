import Thesis.A_Matrix

-- lemma 5.3 seems like it uses a claim that with Prime q, for nonzero s, the distribution A ↦ As is uniform
variable {n m q : ℕ} [NeZero n] [NeZero m] [NeZero q]

example (q : ℕ) (q_prime : Fact <| Nat.Prime q) : Field (ZMod q) := by infer_instance


-- wait, equivalences preserve uniform distribution

theorem A_Matrix.uniform_of_uniform_vecMul_const
    (s : Fin n → ZMod q)
    : (@A_Matrix.uniform n m q _ |>.map ( f:= fun A : A_Matrix n m q ↦ A.transpose.mulVec s) sorry).toMeasure
      = ProbabilityTheory.uniformOn (@Set.univ _) := sorry

-- theorem ZMod_uniform_of_const_mul_uniform {q : ℕ} [NeZero q]
-- #check ZMod.AddAutEquivUnits
-- #check ZMod.ringEquivOfPrime -- that's cool. maybe irrelevant


-- #check ProbabilityTheory.uniformOn
#check PMF.uniformOfFinset
#check Set.BijOn
#check PMF.seq

-- open PMF

-- maybe also for multisets?
lemma bijection_preserves_uniformOfFinset.{u} {α β : Type u}
  [DecidableEq α]
  [DecidableEq β]
  (s : Finset α) (hs : s.Nonempty) (t : Finset β) (ht : t.Nonempty) -- only one nonempty is needed, the other is implied by hf
  (f : α → β) (hf : Set.BijOn f s t)
  : PMF.map f (PMF.uniformOfFinset s hs) = (PMF.uniformOfFinset t ht) := by
    ext y
    -- change (PMF.map f (PMF.uniformOfFinset s hs)) x = (PMF.uniformOfFinset t ht) x


    rw [PMF.map_apply f (PMF.uniformOfFinset s hs) y]
    -- #check PMF.uniformOfFinset_apply_of_mem
    -- by_cases h : x ∈ t
    -- ·
    --   simp [h]
    --   sorry
    have : Nonempty α := ⟨hs.choose⟩


    by_cases h : y ∈ t
    ·
      have := hf.image_eq
      #check Set.MapsTo
      simp only [PMF.uniformOfFinset_apply]
      simp only [h, ↓reduceIte]



      #check Set.LeftInvOn
      obtain ⟨x,xw⟩ : ∃x, ∀x', y = f x' ↔ x' = x := by sorry
      simp only [xw, tsum_ite_eq]
      have : x ∈ s := by
        have := xw x
        simp only [iff_true] at this
        have := (hf.injOn)
        sorry
      simp only [this, ↓reduceIte, inv_inj, Nat.cast_inj]
      exact Set.BijOn.finsetCard_eq f hf

    rw [PMF.uniformOfFinset_apply_of_notMem _ h]
    simp only [PMF.uniformOfFinset_apply, ENNReal.tsum_eq_zero, ite_eq_right_iff, ENNReal.inv_eq_zero,
      ENNReal.natCast_ne_top, imp_false]
    intro x yfx
    contrapose! h
    rw [yfx]
    exact hf.mapsTo h


-- #exit
open scoped Classical in
@[simp, local aesop safe apply]
theorem bijection_preserves_uniformOfFintype {α β : Type*}
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β] -- only one nonempty is needed, the other is implied by hf
  -- [DecidableEq α] [DecidableEq β]
  {f : α → β} (hf : f.Bijective)
  : (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  ext y
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  let f' := Equiv.ofBijective f hf
  have qq a : a = f'.symm y ↔ y = f a := by
    rw [Eq.comm]
    exact Equiv.symm_apply_eq (Equiv.ofBijective f hf) (x := y) (y := a)
  simp_rw [←qq _]
  simp only [tsum_ite_eq, inv_inj, Nat.cast_inj]
  exact Fintype.card_congr f'


theorem bijection_preserves_uniformOfFintype' {α β : Type _}
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β] -- only one nonempty is needed, the other is implied by hf
  -- [DecidableEq α] [DecidableEq β]
  {f : α → β} (hf : f.Bijective)
  : f <$> (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
    exact bijection_preserves_uniformOfFintype hf

@[simp, local aesop safe apply]
theorem equiv_preserves_uniformOfFintype {α β : Type*}
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  (e : α ≃ β)
  : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
    exact bijection_preserves_uniformOfFintype (by exact Equiv.bijective e)


@[simp, local aesop safe apply]
theorem equiv_preserves_uniformOfFintype' {α β : Type _}
  [Fintype α] [Nonempty α]
  (e : α ≃ β)
  (inst_f : (Fintype β) := Fintype.ofEquiv α e) (inst_n : (Nonempty β) := Nonempty.map e inferInstance) -- todo: same for others
  : e <$> (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
    exact bijection_preserves_uniformOfFintype (by exact Equiv.bijective e)

@[simp, local aesop safe apply]
theorem equiv_preserves_uniformOfFintype'' {α β : Type _}
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  (e : α ≃ β)
  : do {
      let x ← (PMF.uniformOfFintype α)
      return e x
    }
    = PMF.uniformOfFintype β := by
    exact bijection_preserves_uniformOfFintype (by exact Equiv.bijective e)



theorem PMF'.remove_equiv {α β γ: Type _}
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  (e : α ≃ β) {f : β → PMF γ}
  : do {
      let x ← (PMF.uniformOfFintype α)
      f (e x)
    }
    =
    do {
      let y ← (PMF.uniformOfFintype β)
      f y
    } := by
    simp only [← bind_map_left, equiv_preserves_uniformOfFintype']

example {α β γ: Type _}
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  (e : α ≃ β) {f : β → PMF γ}
  : do {
      let x ← (PMF.uniformOfFintype α)
      f (e x)
    }
    =
    do {
      let y ← (e <$> PMF.uniformOfFintype α)
      f y
    } := by
    simp only [bind_map_left]

set_option trace.aesop true

section PMF'


open scoped Classical in
@[simp]
lemma PMF'.map_ofMultiset {α β : Type*}
  (s : Multiset α) (hs : s ≠ 0)
  (f : α → β)
  : PMF.map f (PMF.ofMultiset s hs) = (PMF.ofMultiset (Multiset.map f s) (hs ∘ Multiset.map_eq_zero.mp)) := by
    ext x
    simp only [PMF.map_apply, PMF.ofMultiset_apply, Multiset.card_map]
    suffices
      (∑' (i : α), if x = f i then (Multiset.count i s : ENNReal) else 0) =
        (Multiset.count x (Multiset.map f s) : ENNReal) by
      have := congrArg (· * (s.card : ENNReal)⁻¹) this
      simp only at this
      rw [←ENNReal.tsum_mul_right] at this
      simp only [ite_mul, zero_mul] at this
      simp_all only [ne_eq]
      exact this
    rw [tsum_eq_sum (s := s.toFinset)]
    rotate_left
    · intro b a
      simp_all only [ne_eq, Multiset.mem_toFinset, not_false_eq_true, Multiset.count_eq_zero_of_notMem,
        CharP.cast_eq_zero, ite_self]
    suffices
      (∑ b ∈ s.toFinset, if x = f b then (Multiset.count b s) else 0) =
        (Multiset.count x (Multiset.map f s)) by
        rw [←this]
        simp only [Nat.cast_sum, Nat.cast_ite, CharP.cast_eq_zero]
    simp only [Multiset.count_map]
    simp_rw [← Multiset.count_filter (p := (x = f ·))]
    set w :=  (Multiset.filter (x = f ·) s)
    rw [Multiset.sum_count_eq_card]
    subst w
    simp only [Multiset.mem_filter, Multiset.mem_toFinset, and_imp]
    tauto

set_option trace.aesop true
open scoped Classical in
-- @[simp]
theorem PMF'.uniformOfFintype_eq_ofMultiset_univ {α : Type*}
  [Fintype α] [ne : Nonempty α]
  : PMF.uniformOfFintype α = PMF.ofMultiset (Finset.univ.val) (fun uni ↦
    Finset.ne_empty_of_mem (Finset.mem_univ ne.some) (Finset.val_eq_zero.mp uni)) := by
    ext x : 1
    simp_all only [PMF.uniformOfFintype_apply, PMF.ofMultiset_apply, Multiset.count_univ, Nat.cast_one, Finset.card_val,
      Finset.card_univ, one_div]


theorem PMF'.ofMultiset_eq_smul {α : Type*}
  (s : Multiset α) {hs : s ≠ 0} (n : ℕ) (hn : n ≠ 0)
  : PMF.ofMultiset (n • s) (by simp [hn, hs]) = PMF.ofMultiset s hs := by
  ext x
  simp only [PMF.ofMultiset_apply, Multiset.count_nsmul, Nat.cast_mul, Multiset.card_nsmul]
  apply ENNReal.mul_div_mul_left
  · simp [hn]
  · simp


theorem PMF'.ofMultiset_multiples {α : Type*}
  {s₁ : Multiset α} {hs₁ : s₁ ≠ 0} {s₂ : Multiset α} {hs₂ : s₂ ≠ 0}
  (n₁ n₂ : ℕ) (n₁_pos : n₁ ≠ 0)
  (h : n₁ • s₁ = n₂ • s₂)
  : PMF.ofMultiset s₁ hs₁ = PMF.ofMultiset s₂ hs₂ := by
    rw [←PMF'.ofMultiset_eq_smul s₁ n₁ n₁_pos]
    simp_rw [h]
    apply PMF'.ofMultiset_eq_smul
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [zero_nsmul, IsAddTorsionFree.nsmul_eq_zero_iff, or_self]

/-- shortcut in case `s₂.card ∣ s₁.card`. only works if that is true.

s₁ must be an integer multiple of s₂
-/
theorem PMF'.ofMultiset_eq_smul_ratio {α : Type*}
  {s₁ : Multiset α} {s₂ : Multiset α}
  {hs₁ : s₁ ≠ 0} {hs₂ : s₂ ≠ 0}
  (h :  s₁ = (s₁.card / s₂.card) • s₂)
  : PMF.ofMultiset s₁ hs₁ = PMF.ofMultiset s₂ hs₂ := by
  apply PMF'.ofMultiset_multiples 1 (s₁.card / s₂.card)
  · norm_num
  · simp only [one_smul]
    exact h


end PMF'

section uniform_preserving

variable {G : Type*} [Group G] [Fintype G] [Nonempty G] (a : G)



@[to_additive, simp, local aesop safe apply]
theorem upre.Group.const_mulLeft : PMF.map (a * ·) (PMF.uniformOfFintype _) = PMF.uniformOfFintype _ := by
  exact equiv_preserves_uniformOfFintype (Equiv.mulLeft a)

-- @[simp, local aesop safe apply]
-- theorem upre.GroupWithZero.mulLeft : PMF.map (a * ·) (PMF.uniformOfFintype _) = PMF.uniformOfFintype _ := by
--   have := (Group.mulLeft_bijective a)
--   -- simp_all only [Multiset.bijective_iff_map_univ_eq_univ, bijection_preserves_uniformOfFintype]
--   exact bijection_preserves_uniformOfFintype this

example [q_prime : Fact <| Nat.Prime q] : GroupWithZero (ZMod q) := by infer_instance

-- attribute [simp] PMF.monad_map_eq_map

@[to_additive, simp, local aesop safe apply]
theorem upre.bi.Group.mul :
    do {
      let x ← PMF.uniformOfFintype G
      let y ← PMF.uniformOfFintype G
      return x * y
    } = PMF.uniformOfFintype _ := by
  simp only [bind_pure_comp, PMF.monad_map_eq_map, Group.const_mulLeft]
  simp only [bind, PMF.bind_const]

open scoped BigOperators

-- not upre
open scoped Classical in
theorem upre.multiset_bind.{u} {α β : Type u}
  (s : Multiset α)
  (hs : s ≠ 0)
  (f : α → Multiset β)
  (n : ℕ := (f ((Multiset.exists_mem_of_ne_zero hs).choose)).card) (n_pos : n ≠ 0)
  (hf : ∀a, (f a).card = n) -- #check PMF.bindOnSupport -- for an added (a ∈ s)
  :
    do {
      let x ← PMF.ofMultiset s hs
      PMF.ofMultiset (f x) (by simp only [ne_eq, ← Multiset.card_eq_zero, hf, n_pos, not_false_eq_true])
    } =
    PMF.ofMultiset (Multiset.bind s f) (by
      rw [Multiset.bind,ne_eq,Multiset.join,Multiset.sum_eq_zero_iff]
      simp [← Multiset.card_eq_zero,hf, n_pos,Multiset.exists_mem_of_ne_zero hs])
     := by
  #check Multiset.product
  #check Multiset.pi
  ext y
  simp only [bind, PMF.bind_apply, PMF.ofMultiset_apply, Multiset.card_bind, Function.comp_apply,
    Nat.cast_multiset_sum, Multiset.map_map]
  simp only [hf, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]

  suffices
    ∑a ∈ s.toFinset, (Multiset.count a s) * ((Multiset.count y (f a))) = (Multiset.count y (s.bind f)) by
      simp only [ENNReal.div_eq_inv_mul]
      rw [←this]
      simp only [Nat.cast_sum, Nat.cast_mul]
      rw [Finset.mul_sum]
      -- simp [ENNReal.tsum_mul_left]
      rw [tsum_eq_sum (s:= s.toFinset)]
      · congr 1
        ext i
        rw [ENNReal.mul_inv]
        ac_rfl
        right
        exact ENNReal.natCast_ne_top n
        right
        exact Nat.cast_ne_zero.mpr n_pos
      simp only [Multiset.mem_toFinset, mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top,
        Nat.cast_eq_zero, Multiset.count_eq_zero, false_or]
      exact fun b a ↦ Decidable.not_or_of_imp fun a_1 a_2 ↦ a a_1

  simp [Multiset.count_bind]
  exact Eq.symm (Finset.sum_multiset_map_count s fun b ↦ Multiset.count y (f b))
-- ‹_›



theorem upre.multiset_bind'.{u} {α β : Type u}
  (s : Multiset α)
  (hs : s ≠ 0)
  (f : α → Multiset β)
  (n : ℕ := (f ((Multiset.exists_mem_of_ne_zero hs).choose)).card) (n_pos : n ≠ 0)
  (hf : ∀a, (f a).card = n) -- #check PMF.bindOnSupport -- for an added (a ∈ s)
  :
    (PMF.ofMultiset s hs) >>= (fun x ↦ PMF.ofMultiset (f x) (by simp only [ne_eq, ← Multiset.card_eq_zero, hf, n_pos, not_false_eq_true]))
    =
    PMF.ofMultiset (do {
      let x ← s
      f x
    }) (by
      simp only [Multiset.bind_def]
      rw [Multiset.bind,ne_eq,Multiset.join,Multiset.sum_eq_zero_iff]
      simp [← Multiset.card_eq_zero,hf, n_pos,Multiset.exists_mem_of_ne_zero hs])
     := upre.multiset_bind (n := n) (n_pos := n_pos) (hf := hf)


#check Multiset.product

theorem upre.bi.Prod.{u} {α β : Type u}
  (s : Multiset α)(hs : s ≠ 0)
  (t : Multiset β)(ht : t ≠ 0)
  :
    do {
      let x ← PMF.ofMultiset s hs;
      let y ← PMF.ofMultiset t ht;
      return (x,y)
    } = PMF.ofMultiset (s ×ˢ t) (by simp_all [←Multiset.card_eq_zero] ) := by

    simp only [bind_pure_comp]
    simp_rw [PMF.monad_map_eq_map]
    simp only [PMF'.map_ofMultiset]
    apply upre.multiset_bind ( n := t.card) (n_pos := by simp [ht])
    simp only [Multiset.card_map, implies_true]

theorem upre.bi.Prod_uniform.{u} {α β : Type u}
  [Fintype α] [Nonempty α]
  [Fintype β] [Nonempty β]
  :
    do {
      let x ← PMF.uniformOfFintype (α)
      let y ← PMF.uniformOfFintype (β)
      return (x,y)
    } = PMF.uniformOfFintype _ := by
    simp_rw [PMF'.uniformOfFintype_eq_ofMultiset_univ]
    apply upre.bi.Prod






-- theorem upre.bi.General.{u} {α β γ : Type u}
--   [Fintype α] [Nonempty α]
--   [Fintype β] [Nonempty β]
--   (s : Multiset α)
--   (hs : s ≠ 0)
--   (t : Multiset β)
--   (ht : t ≠ 0)
--   (f : α → β → Multiset γ)
--   (hf : ∀a b, f a b ≠ 0)
--   :
--     do {
--       let x ← PMF.ofMultiset s hs;
--       let y ← PMF.ofMultiset t ht;
--       PMF.ofMultiset (f x y) (hf x y)
--     } = PMF.ofMultiset (

--     ) (sorry) := by
--   sorry


open scoped Classical in
@[to_additive, simp, local aesop safe apply]
theorem upre.prod [CommMonoid G] {n : ℕ} :
    do {
      let x ← PMF.uniformOfFintype (Fin n → G)
      return (Finset.prod (M:= G) Finset.univ x)
    } = PMF.uniformOfFintype _ := by

  -- have ind n : PMF.uniformOfFintype (Fin n → G)

  sorry




end uniform_preserving


@[simp]
lemma A_Matrix.uniform_of_transpose_uniform (n m q : ℕ) [NeZero m] [NeZero q] :
      PMF.map Matrix.transpose (PMF.uniformOfFintype (A_Matrix n m q)) = PMF.uniformOfFintype (A_Matrix m n q):= by
      change PMF.map (Matrix.transposeAddEquiv _ _ _ ·) _ = _
      apply bijection_preserves_uniformOfFintype
      exact AddEquiv.bijective (Matrix.transposeAddEquiv (Fin n) (Fin m) (ZMod q))

@[simp]
lemma A_Matrix.uniform_of_transpose_uniform' (n m q : ℕ) [NeZero m] [NeZero q] :
      Matrix.transpose <$> (PMF.uniformOfFintype (A_Matrix n m q)) = PMF.uniformOfFintype (A_Matrix m n q):= by
      simp only [PMF.monad_map_eq_map, uniform_of_transpose_uniform]

@[simp]
theorem A_Matrix.card {n m q : ℕ} [NeZero q] :
  (Fintype.card (A_Matrix m n q)) = (q ^ (m * n)) := by
    rw [Fintype.card_congr (Matrix.ofAddEquiv.toEquiv.symm)]
    simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring

example {α β γ : Type _} (A : PMF α) (f : α → β) (g : β → PMF γ) :
    do {
      let x ← A;
      have y := f x;
      g y
    } = do {
      let y ← do {
        let x ← A;
        pure (f x)
      }
      g y
    } := by
    simp only [pure_bind]


example {α β γ : Type _} (A : PMF α) (f : α → β) (g : β → PMF γ) :
    do {
      let x ← A;
      have y := f x;
      g y
    } = do {
      let x ← A;
      let y ← pure <| f x;
      g y
    } := by
    simp only [pure_bind]


example {α β γ : Type _} (A : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    do {
      let x ← A;
      let y ← f x;
      g y
    } = do {
      let y ← (do {
        let x ← A;
        f x
      })
      g y
    } := by
    simp only [bind_assoc]

open scoped Classical in
example {n m q : ℕ} [NeZero n][NeZero m] [q_prime : Fact <| Nat.Prime q]
    (s : Fin n → ZMod q)
    : do {
      let A ← PMF.uniformOfFintype (A_Matrix n m q)
      return A.transpose.mulVec s
    } = (PMF.uniformOfFintype (Fin m → ZMod q))
      := by
        have n_pos : 0 < n := NeZero.pos _
        have m_pos : 0 < m := NeZero.pos _
        have q_pos : 0 < q := NeZero.pos _


        -- rw []

        change
          (do
              let A ← PMF.uniformOfFintype (A_Matrix n m q)
              (fun B ↦ pure (Matrix.mulVec B s)) (Matrix.transpose A)) = _
        simp_rw [←bind_map_left (f := Matrix.transpose) (g := (fun B ↦ pure (Matrix.mulVec B s)))]
        simp only [A_Matrix.uniform_of_transpose_uniform']
        #check Matrix.toLin'_apply
        let toLin' := (Matrix.toLin' : (A_Matrix m n q ≃ₗ[_] _)).toEquiv

        change (do
              let b ← PMF.uniformOfFintype (A_Matrix m n q)
              (fun B ↦ pure <| (B : _ → _) s) (toLin' b))
              = _
        simp_rw [←bind_map_left (f := toLin') (g:= (pure <| · s))]
        simp_rw [equiv_preserves_uniformOfFintype' (toLin')]
        simp only [bind_pure_comp]



        -- convert_to
        --   (do
        --     let B ← (do
        --       let A ← PMF.uniformOfFintype (A_Matrix n m q)
        --       return (Matrix.transposeAddEquiv _ _ _).toEquiv A
        --       )
        --     return (B.mulVec s)) = _
        -- · simp only [bind_pure_comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
        --   Matrix.transposeAddEquiv_apply, Functor.map_map]



        sorry

open scoped Classical in
example {n m q : ℕ} [NeZero n][NeZero m] [q_prime : Fact <| Nat.Prime q]
    (s : Fin n → ZMod q)
    : do {
      let A ← PMF.uniformOfFintype (A_Matrix n m q)
      return A.transpose.mulVec s
    } = (PMF.uniformOfFintype (Fin m → ZMod q))
      := by
        have n_pos : 0 < n := NeZero.pos _
        have m_pos : 0 < m := NeZero.pos _
        have q_pos : 0 < q := NeZero.pos _


        -- rw []

        change
          (do
              let A ← PMF.uniformOfFintype (A_Matrix n m q)
              (fun B ↦ pure (Matrix.mulVec B s)) (Matrix.transpose A)) = _
        simp_rw [←bind_map_left (f := Matrix.transpose) (g := (fun B ↦ pure (Matrix.mulVec B s)))]
        simp only [A_Matrix.uniform_of_transpose_uniform']
        #check Matrix.toLin'_apply
        let toLin' := (Matrix.toLin' : (A_Matrix m n q ≃ₗ[_] _)).toEquiv

        change (do
              let b ← PMF.uniformOfFintype (A_Matrix m n q)
              (fun B ↦ pure <| (B : _ → _) s) (toLin' b))
              = _
        simp_rw [←bind_map_left (f := toLin') (g:= (pure <| · s))]
        simp_rw [equiv_preserves_uniformOfFintype' (toLin')]
        simp only [bind_pure_comp]



        -- convert_to
        --   (do
        --     let B ← (do
        --       let A ← PMF.uniformOfFintype (A_Matrix n m q)
        --       return (Matrix.transposeAddEquiv _ _ _).toEquiv A
        --       )
        --     return (B.mulVec s)) = _
        -- · simp only [bind_pure_comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
        --   Matrix.transposeAddEquiv_apply, Functor.map_map]



        sorry
-- #exit

theorem A_Matrix.uniform_of_uniform_vecMul_const' {n m q : ℕ} [NeZero n][NeZero m] [q_prime : Fact <| Nat.Prime q]
    (s : Fin n → ZMod q)
    : do {
      let A ← PMF.uniformOfFintype (A_Matrix n m q)
      return A.transpose.mulVec s
    } = (PMF.uniformOfFintype (Fin m → ZMod q))
      := by
        have n_pos : 0 < n := NeZero.pos _
        have m_pos : 0 < m := NeZero.pos _
        have q_pos : 0 < q := NeZero.pos _

        -- convert_to
        --   (do
        --     let B ← (do
        --       let A ← PMF.uniformOfFintype (A_Matrix n m q)
        --       return (Matrix.transposeAddEquiv _ _ _).toEquiv A
        --       )
        --     return (B.mulVec s)) = _
        -- · simp only [bind_pure_comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
        --   Matrix.transposeAddEquiv_apply, Functor.map_map]
        -- simp_rw [equiv_preserves_uniformOfFintype'']


        change
          (do
              let A ← PMF.uniformOfFintype (A_Matrix n m q)
              let B := (Matrix.transpose A)
              pure (B.mulVec s)) = _
        convert_to
          (do
              let A ← PMF.uniformOfFintype (A_Matrix n m q)
              let B ← pure (Matrix.transpose A)
              pure (B.mulVec s)) = _
        · simp only [pure_bind]
        change
          (do
              let A ← PMF.uniformOfFintype (A_Matrix n m q);
              let B ← pure (Matrix.transpose A);
              pure (B.mulVec s)) =
            PMF.uniformOfFintype (Fin m → ZMod q)
        simp [bind_pure_comp]



        change
          (do
              let A ← PMF.uniformOfFintype (A_Matrix n m q)
              -- let B := (Matrix.transpose A)
              pure (((fun B ↦ B.mulVec s) ∘ Matrix.transpose) A)) =
            PMF.uniformOfFintype (Fin m → ZMod q)



        simp only [bind_pure_comp]
        rw [PMF.monad_map_eq_map]
        change PMF.map ((Matrix.mulVec · s) ∘ Matrix.transpose) _ = _
        rw [←PMF.map_comp]
        simp only [uniform_of_transpose_uniform]
        simp only [PMF'.uniformOfFintype_eq_ofMultiset_univ, PMF'.map_ofMultiset]

        apply PMF'.ofMultiset_eq_smul_ratio
        simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, card, Fintype.card_pi,
          ZMod.card, Finset.prod_const, Fintype.card_fin]
        rw [Nat.pow_div]
        rotate_left
        · nlinarith [NeZero.pos n]
        · exact NeZero.pos q

        -- started work at 17-19

        have : Finset.univ (α := A_Matrix m n q).val = Multiset.map (Matrix.ofAddEquiv.toEmbedding) Finset.univ.val := by
          simp only [AddEquiv.toEquiv_eq_coe, Equiv.coe_toEmbedding, EquivLike.coe_coe,
            Matrix.coe_ofAddEquiv, Multiset.map_univ_val_equiv]
        rw [this]
        simp only [AddEquiv.toEquiv_eq_coe, Equiv.coe_toEmbedding, EquivLike.coe_coe,
          Matrix.coe_ofAddEquiv, Multiset.map_map, Function.comp_apply] -- simp? [-Multiset.map_univ_val_equiv]
        -- simp [Matrix.]




        -- apply PMF'.ofMultiset_multiples



          -- _ = (do
          --     let A ← PMF.uniformOfFintype (A_Matrix m n q)
          --     have B := Matrix.of.symm A
          --     pure (A.mulVec s)
          -- )
          --     := by
          --       #check Matrix.ofAddEquiv
          --       #check Matrix.mulVec_eq_sum
          --       sorry
        -- simp only [bind_pure_comp]
        -- simp_rw [Matrix.mulVec_eq_sum]
        -- simp only [op_smul_eq_smul]
        -- change
        --   (fun a ↦ ∑ x, s x • (fun y ↦ Matrix.transpose a x y)) <$> _ = _
        -- simp_rw [Matrix.transpose_apply]
        -- conv => {
        --   left; left; intro A; right; intro x; right; intro y

        --   rw [←Matrix.of_symm_apply A]
        -- }



          -- _ = PMF.uniformOfFintype (Fin m → ZMod q) := by sorry
        -- simp only [bind_pure_comp, map_pure]
        -- rw [bind_pure_comp]

        -- change
        --   (PMF.map (fun A ↦ (Matrix.transpose A).mulVec s)
        --         (PMF.uniformOfFintype (A_Matrix n m q))).toMeasure =
        --     (PMF.uniformOfFintype (Fin m → ZMod q)).toMeasure
        -- rw [←PMF.toMeasure_map]


        sorry
