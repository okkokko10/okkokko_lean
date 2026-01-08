import OkkokkoLeanTwo.CoverDecomposes.MultiCover

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}

open scoped Cardinal

section monotone

theorem MultiCover.ι_less (n : ∅ ∈ F) (e : ι ↪ ι')
  : MultiCover ι F ⊆ MultiCover ι' F := fun _ a_1 ↦ CoverDecomposesIn.by_embedding n e a_1


instance type_size : Preorder (Type v) := Preorder.lift (#·)

-- todo: this requires ι ι' are in the same universe. nevermind, by_embedding already handles that
theorem CoverDecomposesIn.ι_monotone (n : ∅ ∈ F)
  : Monotone (CoverDecomposesIn func · F)
  := fun ⦃_ι _ι'⦄ em ↦ Nonempty.casesOn em (by_embedding n)

theorem MultiCover.ι_monotone (n : ∅ ∈ F) : Monotone (MultiCover · F)
  := fun ⦃_ι _ι'⦄ em ⦃_a⦄ ↦ CoverDecomposesIn.ι_monotone n em


theorem CoverDecomposesIn.F_monotone {F' : Set (Set X)} (l : F ⊆ F')
  : (CoverDecomposesIn func ι F) → (CoverDecomposesIn func ι F')
  := by
  revert l F F'
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
theorem CoverDecomposesIn.F_monotone'
  : Monotone (CoverDecomposesIn func ι)
  := fun _ _ ↦ F_monotone

theorem MultiCover.F_monotone : Monotone (MultiCover (X := X) ι)
  := fun ⦃_ι _ι'⦄ em ⦃_a⦄ ↦ CoverDecomposesIn.F_monotone em

theorem CoverDecomposes.F_monotone {F' : Set (Set X)} (l : F ⊆ F')
  : (CoverDecomposes func F series) → (CoverDecomposes func F' series)
  := by
  simp_rw [CoverDecomposes.def']
  tauto
theorem CoverDecomposes.F_monotone_union_left {F' : Set (Set X)}
  : (CoverDecomposes func F series) → (CoverDecomposes func (F ∪ F') series)
  := F_monotone Set.subset_union_left
theorem CoverDecomposes.F_monotone_union_right {F' : Set (Set X)}
  : (CoverDecomposes func F series) → (CoverDecomposes func (F' ∪ F) series)
  := F_monotone Set.subset_union_right


end monotone
