import OkkokkoLeanTwo.Basic
import OkkokkoLeanTwo.RestrictRange
import OkkokkoLeanTwo.Perm
import OkkokkoLeanTwo.CoverDecomposes.Basic

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}


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
