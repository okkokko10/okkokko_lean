import Mathlib

theorem nat_le_ext {a b : ℕ} : (∀i : ℕ, a ≤ i ↔ b ≤ i) → a = b := by
  intro h
  have t1:= h a
  have t2:= h b
  simp only [le_refl, iff_true, true_iff] at t2 t1
  exact Nat.le_antisymm t2 t1
