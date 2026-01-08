import OkkokkoLeanTwo.Basic
import OkkokkoLeanTwo.Perm

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}



-- ∑ and ∏ are very simple for ℕ∞
noncomputable def func_sum (al : ι → X → ℕ∞) : X → ℕ∞ :=
  open scoped Classical in
  fun x ↦ if h : (Function.support (al · x)).Finite then  ∑ i ∈ h.toFinset, (al i x) else ⊤
noncomputable def func_prod (al : ι → X → ℕ∞) : X → ℕ∞ :=
  open scoped Classical in
  fun x ↦ if ∃i, al i x = 0 then 0 else if h : (Function.mulSupport (al · x)).Finite then ∏ i ∈ h.toFinset, (al i x) else ⊤

theorem func_sum.perm_eq  (al : ι → X → ℕ∞) (bl : ι' → X → ℕ∞)
  (h : perm.restrict (· ≠ 0) al bl)
  : func_sum al = func_sum bl
  := by sorry


theorem func_sum.add  (al : ι → X → ℕ∞) (bl : ι' → X → ℕ∞)
  : func_sum al + func_sum bl = func_sum (Sum.elim al bl)
  := by
  sorry

-- instance : LinearMap func_sum

theorem func_sum.add_comm  (al : ι → X → ℕ∞) (bl : ι' → X → ℕ∞)
  :  func_sum (Sum.elim al bl) = func_sum (Sum.elim bl al)
  := by sorry -- by perm_eq

theorem func_sum.monotone : Monotone (@func_sum X ι) := by
  sorry

theorem func_sum.support_card_lb (al : ι → X → ℕ∞) x :
  ENat.card (Function.support (al · x)) ≤ func_sum al x
  := by
  sorry
theorem func_sum.support_card_le_ub (al : ι → X → ℕ∞) x (t) (h : ∀i, al i x ≤ t) :
  func_sum al x ≤ ENat.card (Function.support (al · x)) * t
  := by
  sorry


theorem func_sum.sum_sum (all : ι → ι' → X → ℕ∞)
  : func_sum (fun i ↦ func_sum (all i)) = func_sum (fun m : ι × ι' ↦ all m.1 m.2)
  := by
  funext x
  apply le_antisymm

  sorry



  -- funext x



  -- by_cases! oo : (∀i, (Function.support (all i · x)).Finite) ∧ ∀i', (Function.support (all · i' x)).Finite
  -- {
  --   -- no, that's wrong. a diagonal won't be detected.
  --   obtain ⟨l,r⟩ := oo
  --   unfold func_sum
  --   simp [l]

  --   sorry
  -- }

  -- unfold func_sum
  -- simp only
  -- split
  -- split
  -- have h_prod i : (Function.support fun i' ↦ all i i' x).Finite := by

  --   sorry
  -- refine Finset.sum_equiv ?_ (fun i ↦ ?_) ?_

  sorry



#check tsum
