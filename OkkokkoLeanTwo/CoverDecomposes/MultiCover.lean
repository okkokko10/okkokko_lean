import OkkokkoLeanTwo.CoverDecomposes.Extra

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}


def MultiCover (ι : Type v) (F : Set (Set X))
  := { f | CoverDecomposesIn f ι F}
theorem MultiCover.def' (ι : Type v) (F : Set (Set X))
  : MultiCover ι F = ComposeCover '' { series : ι → Set X | Set.range series ⊆ F}
  := by
  unfold MultiCover
  congr
  ext f
  simp only [CoverDecomposesIn.def_image, Set.mem_image, Set.mem_setOf_eq]

theorem MultiCover.def'' (ι : Type v) (F : Set (Set X))
  : MultiCover ι F = ComposeCover '' ((fun a i ↦ a i) '' @Set.univ (ι → F))
  := by sorry

theorem MultiCover.mem (ι : Type v) (F : Set (Set X)) f :
  f ∈ MultiCover ι F ↔ CoverDecomposesIn f ι F := by rfl

theorem MultiCover.ι_equiv (e : ι ≃ ι')
  : MultiCover ι F = MultiCover ι' F
  := by simp_rw [MultiCover, CoverDecomposesIn.by_equiv e]
