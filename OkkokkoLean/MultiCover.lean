import Mathlib.Tactic

variable {X : Type*} {ι : Type*} {func : X → ℕ∞} {series: ι → Set X} {F : Set (Set X)}

-- #check Set.range (_ : SetLike F X).coe

-- def MultiCoverFree.coverSubtype (F : Set (Set X)) := Subtype (cover · F)

-- todo: also as SetLike, maybe?

noncomputable def ComposeCover (series: ι → Set X)
  (x : X) : ℕ∞ := ENat.card {i // x ∈ series i}
theorem ComposeCover_def_comp (x : X)
  : (ComposeCover · x) = (ENat.card ∘ Subtype ∘ (fun (series : ι → Set X) i ↦ x ∈ series i))
  := by rfl
def CoverDecomposes (func : X → ℕ∞) (series: ι → Set X) : Prop
  := func = ComposeCover series
def CoverDecomposesIn (func : X → ℕ∞) (ι : Type*) (F : Set (Set X)) : Prop
  := ∃ series: ι → Set X, (∀i, series i ∈ F) ∧ CoverDecomposes func series
theorem CoverDecomposesIn_def (func : X → ℕ∞) (ι : Type*) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, (∀i, series i ∈ F) ∧ func = ComposeCover series
  := by rfl
theorem CoverDecomposesIn_def' (func : X → ℕ∞) (ι : Type*) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, (∀i, series i ∈ F) ∧ ∀x, func x = ENat.card {n // x ∈ series n}
  := by simp_rw [←funext_iff]; rfl
theorem CoverDecomposesIn_def'' (func : X → ℕ∞) (ι : Type*) (F : Set (Set X))
  : CoverDecomposesIn func ι F ↔
  ∃ series: ι → Set X, (Set.range series ⊆ F) ∧ func = ComposeCover series
  := by
  convert CoverDecomposesIn_def func ι F
  exact Set.range_subset_iff


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
theorem ComposeCover_equiv_comp {ι₂ : Type*} (e : ι₂ ≃ ι)
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

def removed_empties (series : ι → Set X)
  : {i : ι // series i ≠ ∅} → Set X
  := (series ·)


#check Equiv.subtypeEquivOfSubtype

theorem ComposeCover_nonempty
  : ComposeCover series = ComposeCover (removed_empties series)
  := by
  simp only [ne_eq]
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
  have := w ▸ pi
  exact this


-- todo: use ComposeCover_nonempty
theorem CoverDecomposesIn_embedding {ι₂ : Type*} (n : ∅ ∈ F) (e : ι ↪ ι₂)
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

theorem CoverDecomposesIn_equiv {ι₁ ι₂ : Type*} (e : ι₂ ≃ ι₁)
  : CoverDecomposesIn func ι₁ F ↔ CoverDecomposesIn func ι₂ F
  := by
  simp_rw [CoverDecomposesIn_def]
  have t (series : ι₁ → Set X)
    : (∀ (i : ι₁), series i ∈ F) ↔ (∀ (i : ι₂), (series ∘ e) i ∈ F)
    := Equiv.forall_congr_right (q :=(series · ∈ F) ) e |>.symm
  simp_rw [t]
  simp_rw [←ComposeCover_equiv_comp e]
  refine Iff.symm (Function.Surjective.exists ?_)
  refine Function.Injective.surjective_comp_right ?_
  exact Equiv.injective e

def MultiCover (ι : Type*) (F : Set (Set X))
  := { f | CoverDecomposesIn f ι F}

theorem MultiCover.ι_equiv {ι₂ : Type*} (e : ι₂ ≃ ι)
  : MultiCover ι F = MultiCover ι₂ F
  := by simp_rw [MultiCover, CoverDecomposesIn_equiv e]

open scoped Cardinal
-- #check embeddingToCardinal


theorem MultiCover.ι_less (n : ∅ ∈ F) {ι₂ : Type*} (e : ι ↪ ι₂)
  : MultiCover ι F ⊆ MultiCover ι₂ F := by
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
