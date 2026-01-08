import OkkokkoLeanTwo.PermNonempty

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}

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

theorem CoverDecomposes.by_embedding (n : ∅ ∈ F) (e : ι ↪ ι')
  : CoverDecomposes func F series → CoverDecomposes func F (perm_nonempty.embedding series e)
  := by
  intro cd
  set em := perm_nonempty.embedding series e
  -- use em
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



theorem CoverDecomposesIn.by_embedding (n : ∅ ∈ F) (e : ι ↪ ι')
  : CoverDecomposesIn func ι F → CoverDecomposesIn func ι' F
  := by
  simp_rw [def_CoverDecomposes]
  intro ⟨series, cd⟩
  refine ⟨_, CoverDecomposes.by_embedding n e cd⟩


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
  simp_rw [←ComposeCover.equiv_comp e]
  refine Function.Surjective.exists ?_
  refine Function.Injective.surjective_comp_right ?_
  exact Equiv.injective e
