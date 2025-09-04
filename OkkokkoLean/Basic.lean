import Mathlib

theorem nat_le_ext {a b : ℕ} : (∀i : ℕ, a ≤ i ↔ b ≤ i) → a = b := by
  intro h
  have t1:= h a
  have t2:= h b
  simp only [le_refl, iff_true, true_iff] at t2 t1
  exact Nat.le_antisymm t2 t1


-- move to misc
@[simp]
theorem exists_ge (p : ℕ → Prop) (m : ℕ) : (∃n ≥ m, p n) ↔ ∃n, p (n + m) := by

  constructor
  · intro ⟨n,g,pn⟩
    use n - m
    simp_all only [ge_iff_le, Nat.sub_add_cancel]
  intro a
  simp_all only [ge_iff_le]
  obtain ⟨w, h⟩ := a
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {exact h
    }
    · simp_all only [le_add_iff_nonneg_left, zero_le]

@[simp]
theorem eventually_ge (p : ℕ → Prop) : (∃m, ∀n ≥ m, p n) ↔ ∃m, ∀n, p (n + m) := by
  rw [← @not_iff_not]
  simp only [ge_iff_le, not_exists, not_forall, Classical.not_imp]
  simp only [exists_prop, exists_ge]


@[simp]
theorem forall_add (p : ℕ → Prop) : (∀n m, p (n + m)) ↔ ∀n, p (n) := by
  constructor
  exact (· · 0)
  exact (· <| · + ·)

@[simp]
theorem exists_add (p : ℕ → Prop) : (∃n m, p (n + m)) ↔ ∃n, p (n) := by
  constructor
  intro ⟨n, m, w⟩
  exact ⟨n + m, w⟩
  intro ⟨n, w⟩
  exact ⟨n, 0, w⟩
