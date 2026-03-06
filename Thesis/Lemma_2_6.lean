import Mathlib
import Thesis.SmoothingParameter
import Thesis.Statistic

noncomputable section
open scoped NNReal ENNReal
variable {ι : Type*} [Fintype ι] [Nonempty ι]

section Lemma_2_6

-- this doesn't seem correct. if ε is low enough it's going to have a square root of a negative
def lemma_2_6_upper (ε : ℝ≥0) [NeZero ε]  (n : ℕ) : ℝ≥0 :=
  (√ (Real.log (2 * n / (1 + ε⁻¹)) / Real.pi)).toNNReal -- conversion to ℝ≥0 for convenience

theorem lemma_2_6_upper.mono (ε : ℝ≥0) (ε' : ℝ≥0) [NeZero ε] [NeZero ε']
  (le : ε ≤ ε') (n : ℕ) : lemma_2_6_upper ε n ≤ lemma_2_6_upper ε' n := by
    -- it's clear from the definition
    sorry


variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
-- what log base?
theorem Lemma_2_6 (ε : ℝ≥0) [NeZero ε]
  : 𝓛.smoothing_parameter Λ ε ≤
  lemma_2_6_upper ε (Fintype.card ι)
  / 𝓛.minimum_distance_sup (𝓛.dualLattice Λ) := by
    sorry


/--
stronger than what the paper literally says, I think, since the dimension is not n, but instead just goes to infinity alongside n
-/
theorem Lemma_2_6_then'
  {ι : (n : ℕ) → Type*} [∀n, Fintype (ι n)] (ι_top : goes_to_infinity (Fintype.card <| ι ·)) (Λ : (n : ℕ) → 𝓛 (ι n)) [∀n, DiscreteTopology ↥(Λ n)] [∀n, IsZLattice ℝ (Λ n)]
  (s : (n : ℕ) → ℝ≥0) (hs : ω_sqrt_log s)
  : ∃(ε : (n : ℕ) → ℝ≥0) (negl_ε : negligible ε) (ε_pos : ∀n, NeZero (ε n)), ∀n,
  𝓛.smoothing_parameter (Λ n) (ε n) ≤ s n / 𝓛.minimum_distance_sup (𝓛.dualLattice (Λ n))
  := by
    #check Lemma_2_6
    -- have ttt n ε (ε_pos : ε ≠ 0) := Lemma_2_6 (Λ n) ε_pos
    change
      ∃ ε,
        ∃ (_ : negligible ε) (ε_pos : ∀ (n : ℕ), NeZero (ε n)),
          ∀ (n : ℕ),
            𝓛.smoothing_parameter (Λ n) (ε n) ≤ s n / 𝓛.minimum_distance_sup (𝓛.dualLattice (Λ n))

    sorry




/--
for any s, there is a ε such that η_ε * λ ≤ s

if there is a function ε, there is a negligible such function?

-/

theorem Lemma_2_6_then''
  {m : (n : ℕ) → ℕ} (m_top : id ≤ m) (m_pos : ∀n, NeZero (m n)) (Λ : (n : ℕ) → 𝓛 (Fin (m n))) [∀n, DiscreteTopology ↥(Λ n)] [∀n, IsZLattice ℝ (Λ n)]
  (s : (n : ℕ) → ℝ≥0) (hs : ω_sqrt_log s)
  : ∃(ε : (n : ℕ) → ℝ≥0) (negl_ε : negligible ε) (ε_pos : ∀n, NeZero (ε n)), ∀n,
  𝓛.smoothing_parameter (Λ n) (ε n) ≤ s n / 𝓛.minimum_distance_sup (𝓛.dualLattice (Λ n))
  := by
    #check Lemma_2_6
    -- have ttt n ε (ε_pos : ε ≠ 0) := Lemma_2_6 (Λ n) ε_pos

    suffices
        ∃(ε : (n : ℕ) → ℝ≥0) (negl_ε : negligible ε) (ε_pos : ∀n, NeZero (ε n)),
        ∀n, lemma_2_6_upper (ε n) (m n) ≤ s n by
      obtain ⟨ε, negl_ε,ε_pos,w⟩ := this
      refine ⟨ε, negl_ε,ε_pos,?_⟩
      intro n
      specialize w n
      trans
      apply Lemma_2_6 (Λ n)
      simp only [Fintype.card_fin]
      refine (div_le_div_iff_of_pos_right ?_).mpr w

      have := 𝓛.minimum_distance_sup.positive ((Λ n).dualLattice)
      exact NeZero.pos (Λ n).dualLattice.minimum_distance_sup

    -- lemma_2_6_upper is monotone on ε

    suffices
      ∃ ε : ℕ → ℝ≥0,
        ∃ (ε_pos : ∀ (n : ℕ), NeZero (ε n)),
          ∀ (n : ℕ), lemma_2_6_upper (ε n) (m n) ≤ s n by
      obtain ⟨ε,ε_pos,w⟩ := this
      let sma := negligible.smaller ε
      refine ⟨sma, ?_,?_,?_⟩
      exact negligible.smaller_negligible ε
      exact negligible.smaller_pos ε_pos
      intro n
      specialize w n
      apply le_trans _ w
      have := negligible.smaller_pos ε_pos
      apply lemma_2_6_upper.mono _ _ ?_ (m n)
      apply negligible.smaller_le ε




    sorry


-- note: NeZero allows this to be inferred, while h : q > 0 doesn't
example  {q : ℕ} [NeZero q] : Finite (ZMod q) := inferInstance
-- instance {q : ℕ} : Zero (ZMod q) where zero := 0
end Lemma_2_6
