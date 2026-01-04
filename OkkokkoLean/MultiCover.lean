import Mathlib.Tactic

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}

-- #check Set.range (_ : SetLike F X).coe

-- def MultiCoverFree.coverSubtype (F : Set (Set X)) := Subtype (cover · F)

-- todo: also as SetLike, maybe?

noncomputable def ComposeCover (series: ι → Set X)
  (x : X) : ℕ∞ := ENat.card {i // x ∈ series i}
theorem ComposeCover_def {series: ι → Set X} {x : X}
  : (ComposeCover series x) = ENat.card {i // x ∈ series i}
  := by rfl
theorem ComposeCover_def_comp (x : X)
  : (ComposeCover · x) = (ENat.card ∘ Subtype ∘ (fun (series : ι → Set X) i ↦ x ∈ series i))
  := by rfl
def CoverDecomposes (func : X → ℕ∞) (F : Set (Set X)) (series: ι → Set X) : Prop
  := (∀i, series i ∈ F) ∧ func = ComposeCover series
def CoverDecomposesIn (func : X → ℕ∞) (ι : Type v) (F : Set (Set X)) : Prop
  := ∃ series: ι → Set X, CoverDecomposes func F series
theorem CoverDecomposesIn_def (func : X → ℕ∞) (ι : Type v) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, (∀i, series i ∈ F) ∧ func = ComposeCover series
  := by rfl
theorem CoverDecomposesIn_def' (func : X → ℕ∞) (ι : Type v) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, (∀i, series i ∈ F) ∧ ∀x, func x = ENat.card {n // x ∈ series n}
  := by simp_rw [←funext_iff]; rfl
theorem CoverDecomposesIn_def'' (func : X → ℕ∞) (ι : Type v) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, (Set.range series ⊆ F) ∧ func = ComposeCover series
  := by
  convert CoverDecomposesIn_def func ι F
  exact Set.range_subset_iff
theorem CoverDecomposesIn_def''' (func : X → ℕ∞) (ι : Type v) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, CoverDecomposes func F series
  := by rfl

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
    rw [CoverDecomposesIn_def]
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

def removed_empties [EmptyCollection X] (series : ι → X)
  : {i : ι // ¬ series i = ∅} → X
  := Subtype.restrict (¬ series · = ∅) series

theorem removed_empties.restriction [EmptyCollection X]
  : removed_empties series = (setOf (¬ series · = ∅) ).restrict series
  := by rfl

#check Equiv.subtypeEquivOfSubtype

theorem ComposeCover_nonempty
  : ComposeCover series = ComposeCover (removed_empties series)
  := by
  unfold ComposeCover
  funext x
  apply ENat.card_congr
  unfold removed_empties
  let P i := x ∈ series i
  let Q i := ¬series i = ∅
  change { i // P i } ≃ { i : { i // Q i } // P ↑i }
  refine (Equiv.subtypeSubtypeEquivSubtype ?_).symm
  unfold P Q
  intro i pi w
  apply w ▸ pi

section perm_nonempty

variable {X : Type u} [EmptyCollection X] {ι : Type v} {ι' : Type v'} {a : ι → X} {b : ι' → X}


def perm_nonempty (a : ι → X) (b : ι' → X) : Prop
  := ∃(e : _ ≃ _), removed_empties a = (removed_empties b) ∘ e

section same_universe

variable {ι' : Type v}  {b : ι' → X}
private
def perm_nonempty' (a' b' : Σ (ι : Type v), (ι → X)) : Prop
  := ∃(e : _ ≃ _), removed_empties a'.snd = (removed_empties b'.snd) ∘ e


theorem perm_nonempty'.coe (p : perm_nonempty a b)
  : perm_nonempty' ⟨_, a⟩ ⟨_, b⟩
  := p

theorem perm_nonempty'.coe_iff
  : perm_nonempty a b ↔ perm_nonempty' ⟨_, a⟩ ⟨_, b⟩
  := Iff.rfl


instance inst_perm_nonempty' : Equivalence (perm_nonempty' (X := X)) where
  refl a := ⟨Equiv.refl _,by rfl⟩
  symm := by
    intro ⟨ai, a⟩ ⟨bi, b⟩ ⟨e, s⟩
    refine ⟨e.symm,?_⟩
    simp_all only
    ext x : 1
    simp_all only [Function.comp_apply, Equiv.apply_symm_apply]
  trans := by
    intro ⟨ai, a⟩ ⟨bi, b⟩ ⟨ci, c⟩ ⟨e_ab, s_ab⟩ ⟨e_bc, s_bc⟩
    refine ⟨Equiv.trans e_ab e_bc, ?_⟩
    simp_all only [Equiv.coe_trans]
    rfl


end same_universe


theorem perm_nonempty.simple (p : perm_nonempty a b)
  : ∃(e : _ ≃ _), removed_empties a = (removed_empties b) ∘ e
  := p

theorem perm_nonempty.simple_iff
  : perm_nonempty a b ↔ ∃(e : _ ≃ _), removed_empties a = (removed_empties b) ∘ e := by rfl

#check Eq.symm

@[refl]
theorem perm_nonempty.refl (a : ι → X)
  : perm_nonempty a a := inst_perm_nonempty'.refl ⟨_, a⟩
@[symm]
theorem perm_nonempty.symm (h : perm_nonempty a b)
  : perm_nonempty b a := by
    obtain ⟨e, s⟩ := h
    refine ⟨e.symm,?_⟩
    simp_all only
    ext x : 1
    simp_all only [Function.comp_apply, Equiv.apply_symm_apply]
@[trans]
theorem perm_nonempty.trans {ι'' : Type v''} {c : ι'' → X}
  (ab : perm_nonempty a b) (bc : perm_nonempty b c)
  : perm_nonempty a c := by
    obtain ⟨e_ab, s_ab⟩ := ab
    obtain ⟨e_bc, s_bc⟩ := bc
    refine ⟨Equiv.trans e_ab e_bc, ?_⟩
    simp_all only [Equiv.coe_trans]
    rfl




end perm_nonempty


theorem CoverDecomposes.perm (p : perm_nonempty series series') :
  CoverDecomposes func F series ↔ CoverDecomposes func F series'
  := by
  sorry



theorem CoverDecomposes_removed_empties :
  CoverDecomposes func F series ↔ CoverDecomposes func F (removed_empties series)
  := by

  sorry

-- todo: use ComposeCover_nonempty
theorem CoverDecomposesIn_embedding {ι₂ : Type v'} (n : ∅ ∈ F) (e : ι ↪ ι₂)
  : CoverDecomposesIn func ι F → CoverDecomposesIn func ι₂ F
  := by
  classical
  simp_rw [CoverDecomposesIn_def'']
  intro ⟨series, rang, feq⟩
  rw [feq]
  have e':= Equiv.ofInjective e e.injective

  let s2 : ι₂ → Set X := fun i ↦ if h : (i ∈ Set.range e) then series (e'.symm ⟨i,h⟩) else ∅
  have requirement : Set.range s2 ⊆ (Set.range series ∪ {∅}) := by
    unfold s2
    simp only [Set.mem_range, Set.union_singleton]
    intro q ⟨i,w⟩
    simp only at w
    split at w <;> rw [←w]
    · simp only [Set.mem_insert_iff, Set.mem_range, exists_apply_eq_apply, or_true]
    · simp only [Set.mem_insert_iff, Set.mem_range, true_or]



  refine ⟨s2,?_,?_⟩
  refine trans requirement ?_
  have : {∅} ⊆ F := Set.singleton_subset_iff.mpr n
  exact Set.union_subset rang this

  unfold ComposeCover
  funext x
  unfold s2
  simp only [Set.mem_range]
  apply ENat.card_congr
  simp_rw [apply_dite (x ∈ ·)]
  simp only [Set.mem_empty_iff_false, dite_else_false]

  suffices { i // x ∈ series i } ≃ { i : ι // ∃ (h : ∃ y, e y = e' i), x ∈ series (e'.symm ⟨e' i, h⟩) } by
    apply this.trans
    change
      { i // (fun i' ↦ ∃ (h : ∃ y, e y = i'), x ∈ series (e'.symm ⟨i', h⟩)) (e' i) } ≃
        { i // ∃ (h : ∃ y, e y = i), x ∈ series (e'.symm ⟨i, h⟩) }

    sorry
  simp

  -- refine ComposeCover_equiv_comp ?_ ?_



  sorry

theorem CoverDecomposesIn_equiv (e : ι ≃ ι')
  : CoverDecomposesIn func ι F ↔ CoverDecomposesIn func ι' F
  := by
  symm
  symm at e
  simp_rw [CoverDecomposesIn_def]
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

theorem MultiCover.ι_equiv (e : ι ≃ ι')
  : MultiCover ι F = MultiCover ι' F
  := by simp_rw [MultiCover, CoverDecomposesIn_equiv e]

open scoped Cardinal
-- #check embeddingToCardinal
#check Cardinal.le_def
-- ↪ is ≤

theorem MultiCover.ι_less (n : ∅ ∈ F) (e : ι ↪ ι')
  : MultiCover ι F ⊆ MultiCover ι' F := by
  unfold MultiCover
  simp only [Set.setOf_subset_setOf]
  intro s

  sorry

instance [Infinite ι] : AddCommSemigroup <| MultiCover ι F where
  add a b := sorry
  add_assoc := sorry
  add_comm := sorry

open scoped MeasureTheory

-- instance [S : MeasurableSpace X] : Semiring <| MultiCover ℕ (MeasurableSet[S]) where
