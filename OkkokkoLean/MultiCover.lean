import Mathlib.Tactic

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}

-- #check Set.range (_ : SetLike F X).coe

-- def MultiCoverFree.coverSubtype (F : Set (Set X)) := Subtype (cover · F)

-- todo: also as SetLike, maybe?

noncomputable def ComposeCover (series: ι → Set X)
  (x : X) : ℕ∞ := ENat.card {i // x ∈ series i}
theorem ComposeCover.def
  : (ComposeCover) = fun (series: ι → Set X) x ↦ ENat.card {i // x ∈ series i}
  := by rfl
theorem ComposeCover.def' {series: ι → Set X}
  : (ComposeCover series) = fun x ↦ ENat.card {i // x ∈ series i}
  := by rfl
theorem ComposeCover_def_comp (x : X)
  : (ComposeCover · x) = (ENat.card ∘ Subtype ∘ (fun (series : ι → Set X) i ↦ x ∈ series i))
  := by rfl
def CoverDecomposes (func : X → ℕ∞) (F : Set (Set X)) (series: ι → Set X) : Prop
  := (∀i, series i ∈ F) ∧ func = ComposeCover series

theorem CoverDecomposes.def' (func : X → ℕ∞) (F : Set (Set X)) (series: ι → Set X)
  : CoverDecomposes func F series ↔ (Set.range series ⊆ F) ∧ func = ComposeCover series
  := by
  unfold CoverDecomposes
  congr! 1
  exact Iff.symm Set.range_subset_iff

def CoverDecomposesIn (func : X → ℕ∞) (ι : Type v) (F : Set (Set X)) : Prop
  := ∃ series: ι → Set X, CoverDecomposes func F series
theorem CoverDecomposesIn.def (func : X → ℕ∞) (ι : Type v) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, (∀i, series i ∈ F) ∧ func = ComposeCover series
  := by rfl
theorem CoverDecomposesIn.def' (func : X → ℕ∞) (ι : Type v) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, (∀i, series i ∈ F) ∧ ∀x, func x = ENat.card {n // x ∈ series n}
  := by simp_rw [←funext_iff]; rfl
theorem CoverDecomposesIn.def'' (func : X → ℕ∞) (ι : Type v) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, (Set.range series ⊆ F) ∧ func = ComposeCover series
  := by
  convert CoverDecomposesIn.def func ι F
  exact Set.range_subset_iff
theorem CoverDecomposesIn.def_CoverDecomposes (func : X → ℕ∞) (ι : Type v) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, CoverDecomposes func F series
  := by rfl

theorem CoverDecomposesIn.def_image (func : X → ℕ∞) (ι : Type v) (F : Set (Set X))
  : CoverDecomposesIn func ι F = (func ∈ ComposeCover '' { series : ι → Set X | Set.range series ⊆ F})
  := by
  simp_rw [CoverDecomposesIn.def'' _ ι F]
  rw [Set.image]
  simp only [Set.mem_setOf_eq]
  congr! 3
  exact eq_comm

section setlike
variable {F' : Type*} [SetLike F' X]
noncomputable def ComposeCover' (series: ι → F') (x : X)
  := ENat.card {i // x ∈ series i}
theorem ComposeCover'_def_comp (x : X)
  : (ComposeCover' · x) = (ENat.card ∘ Subtype ∘ (fun (series: ι → F') i ↦ x ∈ series i))
  := by rfl
def CoverDecomposes' (func : X → ℕ∞) (series: ι → F') : Prop
  := func = ComposeCover' series
def CoverDecomposesIn' (func : X → ℕ∞) (ι : Type*) (F' : Type*) [SetLike F' X] : Prop
  := ∃ series: ι → F', CoverDecomposes' func series

theorem CoverDecomposesIn'_def (func : X → ℕ∞) (ι : Type*) (F' : Type*) [SetLike F' X]
  : CoverDecomposesIn' func ι F' ↔
  ∃ series: ι → F', func = ComposeCover' series
  := by rfl

theorem CoverDecomposesIn'_def' (func : X → ℕ∞) (ι : Type*) (F' : Type*) [SetLike F' X]
  : CoverDecomposesIn' func ι F' ↔
  ∃ series: ι → F', ∀x, func x = ENat.card {n // x ∈ series n}
  := by simp_rw [←funext_iff]; rfl

def SetLike_to_Collection (F' : Type*) [inst : SetLike F' X] : Set (Set X)
  := Set.range inst.coe

def SetLike_Collection_isom (F' : Type*) [inst : SetLike F' X] (F : Set (Set X)) : Prop
  := SetLike_to_Collection F' = F

def SetLike_Collection_isom_def (F' : Type*) [inst : SetLike F' X] (F : Set (Set X))
  : SetLike_Collection_isom F' F ↔ Set.range inst.coe = F := Iff.rfl

theorem CoverDecomposesIn'_isom {F' : Type*} [SetLike F' X] {F : Set (Set X)}
  (h : SetLike_Collection_isom F' F) {func : X → ℕ∞} {ι : Type*}
  : CoverDecomposesIn func ι F ↔ CoverDecomposesIn' func ι (F')
  := by
    rw [CoverDecomposesIn'_def]
    rw [CoverDecomposesIn.def]
    sorry

end setlike

@[simp]
theorem ComposeCover_equiv_comp {ι₂ : Type v'} (e : ι₂ ≃ ι)
  : ComposeCover (series ∘ e) = ComposeCover series := by
  unfold ComposeCover
  funext x
  apply ENat.card_congr
  change { i // (x ∈ series ·) (e i) } ≃ { i // (x ∈ series ·) i }
  change Subtype ((x ∈ series ·) ∘ e) ≃ Subtype (x ∈ series ·)
  refine Equiv.subtypeEquiv e ?_
  simp only [Function.comp_apply, implies_true]


-- theorem ComposeCover_comp_embedding {ι₂ : Type*} {series₂ : ι₂ → Set X} (e : ι₂ ↪ ι)
--   (h : series₂ = series ∘ e)
--   : ComposeCover (series ∘ e) = ComposeCover series := by
--   unfold ComposeCover
--   funext x
--   apply ENat.card_congr

--   change Subtype ((x ∈ series ·) ∘ e) ≃ Subtype (x ∈ series ·)

section restrict_range

def restrict_range (p : X → Prop) (a : ι → X) := Subtype.restrict (p ∘ a) a

#check Subtype.restrict_apply

@[simp]
theorem restrict_range.apply (p : X → Prop) (a : ι → X) (i : _)
  : restrict_range p a i = a ↑i
  := rfl
theorem restrict_range.comp (p : X → Prop) (a : ι → X) (e : ι' → { x // p (a x) }) (i : { x // p (a ↑(e x)) })
  : (restrict_range p a) (e i) = restrict_range p (a <| e ·) i
  := rfl
theorem restrict_range.comp' (p : X → Prop) (a : ι → X) (e : ι' → { x // (p ∘ a) x })
  : ((restrict_range p a) ∘ e) = fun i : ι' ↦ restrict_range p (a <| e ·) ⟨i,by
    simp only [Function.comp_apply]
    exact e i |>.prop
    ⟩
  := rfl

#check Subtype.coind


theorem restrict_range.comp_subtype (p p' : X → Prop) (a : ι → X)
  : Subtype (p ∘ restrict_range p' a) = @Subtype (Subtype (p' ∘ a)) (p ∘ a ∘ Subtype.val)
  := rfl
@[simp]
theorem restrict_range.comp_subtype' (p p' : X → Prop) (a : ι → X)
  : (p ∘ restrict_range p' a) = (p ∘ a ∘ Subtype.val)
  := rfl

theorem restrict_range.and (p p' : X → Prop) (a : ι → X) i
  : restrict_range p (restrict_range p' a) i = restrict_range (fun x ↦ p x ∧ p' x) a ⟨i.val, ⟨i.2, i.1.2⟩⟩
  := rfl

@[simp]
theorem restrict_range.idempotent (p : X → Prop) (a : ι → X)
  : restrict_range p (restrict_range p a) = fun i ↦ restrict_range p a i.val
  := rfl

end restrict_range


def removed_empties' [EmptyCollection X] (a : ι → X)
  : {i : ι // ¬ a i = ∅} → X
  := restrict_range (¬ · = ∅) a
def removed_empties  (a : ι → Set X)
  -- : {i : ι // Set.Nonempty (a i)} → X
  := restrict_range (Set.Nonempty) a

theorem removed_empties.def {a : ι → Set X}
  : removed_empties a = restrict_range (Set.Nonempty) a
  := by rfl

#check Equiv.subtypeEquivOfSubtype

theorem ComposeCover.with_removed_empties
  : ComposeCover series = ComposeCover (removed_empties series)
  := by
  unfold ComposeCover
  funext x
  apply ENat.card_congr
  unfold removed_empties
  let P i := x ∈ series i
  let Q i := (series i ).Nonempty
  change { i // P i } ≃ { i : { i // Q i } // P ↑i }
  refine (Equiv.subtypeSubtypeEquivSubtype ?_).symm
  subst P Q
  intro i pi
  exact Set.nonempty_of_mem pi

-- is there a standard for this?

section perm

variable {a : ι → X} {b : ι' → X}

-- todo: in Embedding.arrowCongrLeft the equals is flipped
def perm (a : ι → X) (b : ι' → X) : Prop
  := ∃(e : _ ≃ _), a = b ∘ e

@[refl]
theorem perm.refl (a : ι → X)
  : perm a a := ⟨Equiv.refl _, by rfl⟩
@[symm]
theorem perm.symm (h : perm a b)
  : perm b a := by
    obtain ⟨e, s⟩ := h
    refine ⟨e.symm,?_⟩
    simp_all only
    ext x : 1
    simp_all only [Function.comp_apply, Equiv.apply_symm_apply]
@[trans]
theorem perm.trans {ι'' : Type v''} {c : ι'' → X}
  (ab : perm a b) (bc : perm b c)
  : perm a c := by
    obtain ⟨e_ab, s_ab⟩ := ab
    obtain ⟨e_bc, s_bc⟩ := bc
    refine ⟨Equiv.trans e_ab e_bc, ?_⟩
    simp_all only [Equiv.coe_trans]
    rfl

theorem perm.range_iff: perm a b ↔ ∀x, Nonempty <| {i // a i = x} ≃ {i // b i = x}
  := by
  constructor
  {
    intro ⟨e,w⟩ x
    refine ⟨?_⟩
    rw [w]
    simp only [Function.comp_apply]
    let P i := b i = x
    change { i // P (e i) } ≃ { i // P i }
    exact e.subtypeEquivOfSubtype
  }
  intro w
  have e : (c : X) → { i // a i = c } ≃ { i // b i = c } := fun c ↦ (w c).some
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  symm
  apply Equiv.ofFiberEquiv_map


set_option pp.proofs true in
noncomputable def perm.range (h : perm a b)
  : ∀x, {i // a i = x} ≃ {i // b i = x}
  := fun x ↦ (perm.range_iff.mp h x).some
  -- #help attr
theorem perm.from_range
  (h' : ∀x, {i // a i = x} ≃ {i // b i = x})
  : perm a b
  := perm.range_iff.mpr fun x ↦ Nonempty.intro (h' x)



theorem perm.inEquiv (a : ι → X) (e : ι ≃ ι') : ∃(b : ι' → X), perm a b := by
  unfold perm
  refine ⟨a ∘ e.symm, e,?_⟩
  exact (Equiv.comp_symm_eq e (a ∘ ⇑e.symm) a).mp rfl

noncomputable def perm.inEquiv_choose (a : ι → X) (e : ι ≃ ι') := (perm.inEquiv a e).choose
-- todo: add Equiv.perm

@[simp]
theorem perm.inEquiv_choose_spec (a : ι → X) (e : ι ≃ ι') :  perm a (perm.inEquiv_choose a e) := (perm.inEquiv a e).choose_spec


section perm.restrict

#check Subtype.restrict

def perm.restrict (p : X → Prop) (a : ι → X) (b : ι' → X) : Prop
  := perm (restrict_range p a) (restrict_range p b)

-- todo: do lemmas about perm get inherited by perm.restrict?
--  if not automatically, can something resembling @[to_additive] be done?
-- @[simps]
-- #check tsum



noncomputable def perm.extracted1  {p : X → Prop} (x : X)
  (px : p x)
  : { i // a i = x } ≃ { i : Subtype (p ∘ a) // a ↑i = x }
  := by
  apply Equiv.ofBijective ?_ ?_
  intro ⟨i, w⟩
  exact ⟨⟨i,(w ▸ px : p _)⟩,w⟩
  refine Function.bijective_iff_has_inverse.mpr ?_
  refine ⟨fun ⟨h,e⟩ ↦ ⟨h.val,e⟩, by tauto⟩


def perm.restrict.ofPerm.extracted2
  (p : X → Prop) (x : X) (px : ¬p x)
  : { i : Subtype (p ∘ a) // a ↑i = x } ≃ { i : Subtype (p ∘ b) // b ↑i = x } := by

  refine @Equiv.equivOfIsEmpty _ _ ?_ ?_
  <;> {
    convert Subtype.isEmpty_false
    rename_i i
    simp only [iff_false]
    intro d
    apply px
    rw [←d]
    apply i.2
  }
noncomputable def perm.restrict.ofPerm.extracted
  (p : X → Prop) (x : X) (h : { i // a i = x } ≃ { i // b i = x }) :
  { i : Subtype (p ∘ a) // a ↑i = x } ≃ { i : Subtype (p ∘ b) // b ↑i = x } := by
    by_cases px : p x
    refine Equiv.trans (Equiv.symm ?_) (Equiv.trans h ?_)
    <;> exact extracted1 x px
    exact extracted2 p x px

-- if the functions are permutations, then their subcollections are too.
@[simp]
theorem perm.restrict.ofPerm (p : X → Prop) (h : perm a b)
  : perm.restrict p a b
  := by
    -- replace with anti_imp
    unfold restrict
    rw [perm.range_iff] at h ⊢
    simp only [restrict_range.apply]
    intro x
    obtain ⟨h⟩ := h x
    refine ⟨?_⟩
    exact ofPerm.extracted p x h


abbrev perm.r (h : perm a b) (p : X → Prop) : perm.restrict p a b := restrict.ofPerm p h

#check Equiv.asEmbedding


theorem perm.restrict.inEquiv (p : X → Prop) (a : ι → X) (e : ι ≃ ι') : ∃(b : ι' → X), perm.restrict p a b :=
  ⟨perm.inEquiv_choose a e,by simp only [inEquiv_choose_spec, ofPerm]⟩


noncomputable def perm.restrict.inEquiv_choose (p : X → Prop)  (a : ι → X) (e : ι ≃ ι') := (perm.restrict.inEquiv p a e).choose

@[simp]
theorem perm.restrict.inEquiv_choose_spec (p : X → Prop)  (a : ι → X) (e : ι ≃ ι') :  perm.restrict p a (perm.restrict.inEquiv_choose p a e) := (perm.restrict.inEquiv p a e).choose_spec

open Function

theorem perm.restrict.anti_imp {p p' : X → Prop} (pp : ∀x, p x → p' x) (h : perm.restrict p' a b)
  : perm.restrict p a b
  := by
    unfold restrict at h ⊢
    rw [perm.range_iff] at h ⊢
    simp only [restrict_range.apply]
    intro x
    obtain ⟨h⟩ := h x
    refine ⟨?_⟩
    by_cases q : p x
    · refine Equiv.trans ?_ (Equiv.trans h ?_)
      symm
      repeat
      {
        -- todo: extract this too
      simp_all
      apply Equiv.ofBijective ?_ ?_
      intro ⟨i, w⟩
      exact ⟨⟨i,(w ▸ q : p _)⟩,w⟩
      refine Function.bijective_iff_has_inverse.mpr ?_
      refine ⟨fun ⟨⟨h,hh⟩,e⟩ ↦ ⟨⟨h,pp _ hh⟩,e⟩, by tauto⟩
      }
    refine @Equiv.equivOfIsEmpty _ _ ?_ ?_
    <;> {
      convert Subtype.isEmpty_false
      rename_i i
      simp only [iff_false]
      intro d
      apply q
      rw [←d]
      apply i.2
    }



@[refl]
theorem perm.restrict.refl (p : X → Prop) (a : ι → X)
  : perm.restrict p a a := ⟨Equiv.refl _, by rfl⟩
@[symm]
theorem perm.restrict.symm {p : X → Prop} (h : perm.restrict p a b)
  : perm.restrict p b a := by
    obtain ⟨e, s⟩ := h
    refine ⟨e.symm,?_⟩
    simp_all only
    ext x : 1
    simp_all only [Function.comp_apply, Equiv.apply_symm_apply]
@[trans]
theorem perm.restrict.trans {p : X → Prop} {ι'' : Type v''} {c : ι'' → X}
  (ab : perm.restrict p a b) (bc : perm.restrict p b c)
  : perm.restrict p a c := by
    obtain ⟨e_ab, s_ab⟩ := ab
    obtain ⟨e_bc, s_bc⟩ := bc
    refine ⟨Equiv.trans e_ab e_bc, ?_⟩
    simp_all only [Equiv.coe_trans]
    rfl

theorem perm.restrict.with_restrict_range {p : X → Prop}
  : perm.restrict p a (restrict_range p a)
  := by
    unfold restrict
    simp only [restrict_range.comp_subtype', restrict_range.idempotent]
    refine ⟨?_,?_⟩
    exact (Equiv.subtypeSubtypeEquivSubtype (by exact fun {x} a ↦ a)).symm
    rfl


theorem perm.restrict.range_iff {p : X → Prop}: perm.restrict p a b ↔ ∀x, p x → Nonempty ({i // a i = x} ≃ {i // b i = x})
  := by
  unfold restrict
  rw [perm.range_iff]
  simp only [restrict_range.apply]
  constructor
  {
    intro w x px
    refine ⟨?_⟩
    obtain h := (w x).some
    refine Equiv.trans (?_) (Equiv.trans h (Equiv.symm  ?_))
    <;>
    exact perm.extracted1 x px

  }
  intro w x
  refine ⟨?_⟩
  by_cases px : p x
  obtain h := (w x px).some
  exact ofPerm.extracted p x h
  exact ofPerm.extracted2 p x px

-- set_option pp.proofs true in
noncomputable def perm.restrict.range {p : X → Prop} (h : perm.restrict p a b)
  : ∀x, p x → {i // a i = x} ≃ {i // b i = x}
  := fun x px ↦ (perm.restrict.range_iff.mp h x px).some
  -- #help attr
theorem perm.restrict.from_range {p : X → Prop}
  (h' : ∀x, p x → {i // a i = x} ≃ {i // b i = x})
  : perm.restrict p a b
  := perm.restrict.range_iff.mpr fun x a_1 ↦ Nonempty.intro (h' x a_1)


-- todo: the above rhs with (p := Set.Nonempty) → ComposeCover =

-- weaker. todo: rename range_iff
theorem perm.restrict.range_eq {p : X → Prop}
  (h : perm.restrict p a b)
  : ∀x, (p x) → (x ∈ Set.range a ↔ x ∈ Set.range b)
  := by
  intro x px
  simp only [Set.mem_range]
  unfold restrict perm at h
  obtain ⟨e,h⟩ := h
  constructor
  rotate_left
  symm at h
  rw [←Equiv.eq_comp_symm] at h
  repeat' {
  intro ⟨y,ayx⟩
  simp only [funext_iff, restrict_range.apply, Function.comp_apply, Subtype.forall] at h
  have := h y (ayx ▸ px)
  rw [←ayx,this]
  simp only [exists_apply_eq_apply]
  }



-- #check Function.Embedding
#check Embedding.arrowCongrLeft
#check Embedding.arrowCongrLeft_apply
#check extend -- interesting


-- set_option pp.proofs true in
theorem perm.restrict.with_extend {p : X → Prop} {b : ι' → X} (e : ι ↪ ι') (a : ι → X) (h : ∀ i, ¬ p (b i))
  : perm.restrict p a (extend e a b)
  := by
  unfold restrict
  -- this could be its own lemma
  apply from_range
  intro x px
  have dd i : ¬ b i = x := fun w ↦ h i (w ▸ px)
  open Classical in
  have bb i:= extend_def e a b i
  simp_rw [bb]
  simp_rw [apply_dite (· = x)]
  set s := (a · = x)
  simp_rw [dd]
  simp only [dite_else_false]
  change { i // a i = x } ≃ { i' // ∃ (h : ∃ i, e i = i'), a (choose h) = x }
  convert_to { i // a i = x } ≃ { i' // ∃i, (e i = i') ∧  a i = x }
  {
    congr! with i'
    apply Iff.intro
    · intro a_1
      obtain ⟨w, h_1⟩ := a_1
      obtain ⟨w, h_1⟩ := w
      subst h_1 h_1
      simp_all only [EmbeddingLike.apply_eq_iff_eq, choose_eq, exists_eq_left]
    · intro a_1
      obtain ⟨w, h_1⟩ := a_1
      obtain ⟨left, right⟩ := h_1
      subst left right
      simp_all only [EmbeddingLike.apply_eq_iff_eq, choose_eq, exists_eq, exists_const]
  }
  have : { i' | ∃ i, e i = i' ∧ a i = x } = e '' {i | a i = x} := by
    ext i' : 1
    simp_all only [Set.mem_setOf_eq, Set.mem_image]
    tauto
  convert_to { i // a i = x } ≃ (⇑e '' {i | a i = x})
  · exact congrArg Subtype this
  change { i | a i = x } ≃ (⇑e '' {i | a i = x})
  set S := { i | a i = x }
  refine Equiv.Set.imageOfInjOn (⇑e) S ?_
  simp only [EmbeddingLike.apply_eq_iff_eq, implies_true, Set.injOn_of_eq_iff_eq]




-- theorem perm.restrict.extend {p : X → Prop} {a : ι → X} (e' : ι ↪ ι') {x : X} (h : ¬ p x)
--   : perm.restrict p a (extend e' a (const _ x))
--   := sorry


noncomputable def perm.restrict.embedding (a : ι → X) (e : ι ↪ ι') (default : X)
  : ι' → X
  := (extend (⇑e) a (const _ default))

#check CanLift

theorem perm.restrict.embedding_spec (a : ι → X) (e : ι ↪ ι') (x) (p : X → Prop) (h : ¬ p x)
  : perm.restrict p a (embedding a e x)
  := with_extend e a fun _ ↦ h

theorem extend_range (f : ι → ι') (g : ι → X) (j : ι' → X) : Set.range (extend f g j) ⊆ Set.range g ∪ Set.range j
    := by
    intro x
    unfold extend
    simp
    intro x_2 h_1
    subst h_1
    split
    next h_1 => simp_all only [exists_apply_eq_apply, true_or]
    next h_1 => simp_all only [not_exists, exists_apply_eq_apply, or_true]


theorem perm.restrict.embedding_range_higher (a : ι → X) (e : ι ↪ ι') (default : X)
  : Set.range (embedding a e default) ⊆ insert default (Set.range a)
  := by
  unfold embedding
  by_cases! hq : IsEmpty ι'
  · rw [Set.range_eq_empty_iff.mpr hq]
    exact Set.empty_subset _

  -- #check Set.restrict_extend_range
  have : insert default (Set.range a) = Set.range a ∪ {default} := by exact Eq.symm Set.union_singleton
  have qq : {default} = Set.range (const ι' default) := by
    ext x'
    simp only [Set.mem_singleton_iff, Set.mem_range, const_apply, exists_const]
    tauto
  rw [this, qq]
  exact extend_range (⇑e) a (const ι' default)
theorem perm.restrict.embedding_range_lower (a : ι → X) (e : ι ↪ ι') (default : X)
  : Set.range a ⊆ Set.range (embedding a e default)
  := by
  intro y
  simp only [Set.mem_range, forall_exists_index]
  intro i aiy
  unfold embedding
  use (⇑e i)
  rw [←aiy]
  exact e.injective.extend_apply a (const ι' default) i

-- todo: if it's left, e is a bijection.
theorem perm.restrict.embedding_range_either (a : ι → X) (e : ι ↪ ι') (default : X)
  : Set.range (embedding a e default) = Set.range a ∨ Set.range (embedding a e default) = insert default (Set.range a)
  := by
  have lo := embedding_range_lower a e default
  have hi := embedding_range_higher a e default
  set s := Set.range a
  set q := Set.range (embedding a e default)
  by_cases h : default ∈ q
  right
  apply hi.antisymm
  exact Set.insert_subset h lo
  left
  apply lo.antisymm'
  exact (Set.subset_insert_iff_of_notMem h).mp hi


end perm.restrict
end perm

section perm_nonempty


-- #check Function

-- variable [EmptyCollection X]

abbrev perm_nonempty (a : ι → Set X) (b : ι' → Set X) : Prop
  := perm.restrict (Set.Nonempty) a b

theorem perm_nonempty.of_removed_empties (a : ι → Set X)
  : perm_nonempty a (removed_empties a)
  := perm.restrict.with_restrict_range


abbrev perm_nonempty.embedding (a : ι → Set X) (e : ι ↪ ι')
  := perm.restrict.embedding a e ∅
@[simp]
theorem perm_nonempty.embedding_spec (a : ι → Set X) (e : ι ↪ ι')
  : perm_nonempty a (perm_nonempty.embedding a e)
  := perm.restrict.embedding_spec a e ∅ _ (Set.not_nonempty_empty)


theorem perm.composeCover_eq (p : perm series series')
  : ComposeCover series = ComposeCover series'
  := by
    obtain ⟨e,w⟩ := p
    simp only [ComposeCover.def]
    funext x
    apply ENat.card_congr
    refine Equiv.subtypeEquiv e ?_
    intro a
    subst w
    simp_all only [Function.comp_apply]


theorem perm_nonempty.composeCover_eq (p : perm_nonempty series series')
  : ComposeCover series = ComposeCover series'
  := by
    calc  ComposeCover series
        = ComposeCover (removed_empties series) := ComposeCover.with_removed_empties
      _ = ComposeCover (removed_empties series') := perm.composeCover_eq p
      _ = ComposeCover series' := ComposeCover.with_removed_empties.symm


end perm_nonempty



theorem CoverDecomposes.from_perm (n : ∅ ∈ F) (p : perm_nonempty series series') :
  CoverDecomposes func F series ↔ CoverDecomposes func F series'
  := by
  constructor
  repeat
  {
    unfold CoverDecomposes
    intro ⟨cf, wf⟩
    subst wf
    constructor
    -- convert_to Set.range series' ⊆ F
    rw [←Set.range_subset_iff] at cf ⊢

    unfold perm_nonempty at p
    have := p.range_eq
    intro r rs
    by_cases re : r = ∅
    · exact Set.mem_of_eq_of_mem re n
    have ttt:= this r (Set.nonempty_iff_ne_empty.mpr re)
    apply cf

    try apply ttt.mp rs
    try apply ttt.mpr rs

    try exact perm_nonempty.composeCover_eq p
    try exact (perm_nonempty.composeCover_eq p).symm

  }




theorem CoverDecomposes.with_removed_empties (n : ∅ ∈ F) :
  CoverDecomposes func F series ↔ CoverDecomposes func F (removed_empties series)
  := by
  apply CoverDecomposes.from_perm n
  exact perm_nonempty.of_removed_empties series


theorem CoverDecomposes.no_empty (n : ∅ ∉ F) :
  CoverDecomposes func F series → _root_.perm series (removed_empties series)
  := by
  sorry

-- open perm.restrict in perm_nonempty


theorem CoverDecomposesIn.by_embedding (n : ∅ ∈ F) (e : ι ↪ ι')
  : CoverDecomposesIn func ι F → CoverDecomposesIn func ι' F
  := by
  simp_rw [def_CoverDecomposes]
  intro ⟨series, cd⟩
  let em := perm_nonempty.embedding series e
  use em
  rw [CoverDecomposes.def'] at cd ⊢
  refine ⟨?_,?_⟩
  have wq : Set.range em = _ ∨ Set.range em = _ := perm.restrict.embedding_range_either series e ∅
  cases wq with
  | inl h =>
    rw [h]
    exact cd.left
  | inr h =>
    rw [h]
    have : F = insert ∅ F := by exact Eq.symm (Set.insert_eq_of_mem n)
    -- rw [this]
    refine Set.insert_subset n cd.left
  have qe := perm_nonempty.embedding_spec series e
  rw [cd.right]
  exact perm_nonempty.composeCover_eq qe


theorem CoverDecomposesIn.by_equiv (e : ι ≃ ι')
  : CoverDecomposesIn func ι F ↔ CoverDecomposesIn func ι' F
  := by
  symm
  symm at e
  simp_rw [CoverDecomposesIn.def]
  have t (series : ι → Set X)
    : (∀ (i : ι), series i ∈ F) ↔ (∀ (i : ι'), (series ∘ e) i ∈ F)
    := Equiv.forall_congr_right (q :=(series · ∈ F) ) e |>.symm
  simp_rw [t]
  simp_rw [←ComposeCover_equiv_comp e]
  refine Function.Surjective.exists ?_
  refine Function.Injective.surjective_comp_right ?_
  exact Equiv.injective e

def MultiCover (ι : Type v) (F : Set (Set X))
  := { f | CoverDecomposesIn f ι F}
theorem MultiCover.def' (ι : Type v) (F : Set (Set X))
  : MultiCover ι F = ComposeCover '' { series : ι → Set X | Set.range series ⊆ F}
  := by
  unfold MultiCover
  ext f
  simp only [Set.mem_setOf_eq]
  rw [CoverDecomposesIn.def_image]
theorem MultiCover.def'' (ι : Type v) (F : Set (Set X))
  : MultiCover ι F = ComposeCover '' ((fun a i ↦ a i) '' @Set.univ (ι → F))
  := by sorry


theorem MultiCover.ι_equiv (e : ι ≃ ι')
  : MultiCover ι F = MultiCover ι' F
  := by simp_rw [MultiCover, CoverDecomposesIn.by_equiv e]

open scoped Cardinal
-- #check embeddingToCardinal
#check Cardinal.le_def
-- ↪ is ≤

theorem MultiCover.ι_less (n : ∅ ∈ F) (e : ι ↪ ι')
  : MultiCover ι F ⊆ MultiCover ι' F := fun _ a_1 ↦ CoverDecomposesIn.by_embedding n e a_1


instance type_size : Preorder (Type v) := Preorder.lift (#·)


theorem CoverDecomposesIn.ι_monotone (n : ∅ ∈ F)
  : Monotone (CoverDecomposesIn func · F)
  := fun ⦃_ι _ι'⦄ em ↦ Nonempty.casesOn em (by_embedding n)

theorem MultiCover.ι_monotone (n : ∅ ∈ F) : Monotone (MultiCover · F)
  := fun ⦃_ι _ι'⦄ em ⦃_a⦄ ↦ CoverDecomposesIn.ι_monotone n em


theorem CoverDecomposesIn.F_monotone
  : Monotone (CoverDecomposesIn func ι)
  := by
  change Monotone (CoverDecomposesIn func ι ·)
  simp_rw [CoverDecomposesIn.def_image]
  change Monotone fun x ↦ (func ∈ ·) <| Set.image ComposeCover (Set.range · ⊆ x)
  change Monotone fun x ↦ ((func ∈ ·) ∘ Set.image ComposeCover) ((fun x a ↦ Set.range a ⊆ x) x)
  change Monotone ((func ∈ ·) ∘ Set.image ComposeCover ∘ fun x a ↦ Set.range a ⊆ x)
  apply Monotone.comp
  tauto
  apply Monotone.comp
  exact Set.monotone_image
  tauto

theorem MultiCover.F_monotone : Monotone (MultiCover (X := X) ι)
  := fun ⦃_ι _ι'⦄ em ⦃_a⦄ ↦ CoverDecomposesIn.F_monotone em

instance [Infinite ι] : AddCommSemigroup <| MultiCover ι F where
  add a b := sorry
  add_assoc := sorry
  add_comm := sorry

open scoped MeasureTheory

-- instance [S : MeasurableSpace X] : Semiring <| MultiCover ℕ (MeasurableSet[S]) where
