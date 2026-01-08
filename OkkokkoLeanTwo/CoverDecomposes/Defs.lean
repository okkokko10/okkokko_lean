import Mathlib.Tactic
import OkkokkoLeanTwo.Basic

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}

section ComposeCover

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

end ComposeCover

section CoverDecomposes

def CoverDecomposes (func : X → ℕ∞) (F : Set (Set X)) (series: ι → Set X) : Prop
  := (∀i, series i ∈ F) ∧ func = ComposeCover series

theorem CoverDecomposes.def' (func : X → ℕ∞) (F : Set (Set X)) (series: ι → Set X)
  : CoverDecomposes func F series ↔ (Set.range series ⊆ F) ∧ func = ComposeCover series
  := by
  unfold CoverDecomposes
  congr! 1
  exact Iff.symm Set.range_subset_iff
@[inline]
abbrev CoverDecomposes.f {func : X → ℕ∞} {F : Set (Set X)} {series: ι → Set X}
  (_cd : CoverDecomposes func F series) := func
@[inline]
noncomputable abbrev CoverDecomposes.cover {func : X → ℕ∞} {F : Set (Set X)} {series: ι → Set X}
  (_cd : CoverDecomposes func F series) := ComposeCover series
theorem CoverDecomposes.eq (cd : CoverDecomposes func F series ) : func = ComposeCover series := cd.right
@[inline]
abbrev CoverDecomposes.range {func : X → ℕ∞} {F : Set (Set X)} {series: ι → Set X}
  (_cd : CoverDecomposes func F series) := Set.range series
theorem CoverDecomposes.range_subset {func : X → ℕ∞} {F : Set (Set X)} {series: ι → Set X}
  (cd : CoverDecomposes func F series) : Set.range series ⊆ F
  := ((def' func F series).mp cd).left

end CoverDecomposes

section CoverDecomposesIn

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

end CoverDecomposesIn
