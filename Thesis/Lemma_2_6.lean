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

    suffices ∀n, ∃ ε : ℝ≥0, ∃ (ε_pos :  NeZero (ε)), lemma_2_6_upper (ε) (m n) ≤ s n by

      refine ⟨fun n ↦ (this n).choose, ?_, ?_⟩
      exact fun n ↦ (this n).choose_spec.choose
      exact fun n ↦ (this n).choose_spec.choose_spec
    intro n

    -- the rest is clear

    let m' := m n


    have : (fun ε : ℝ≥0 ↦ ((1 + ε⁻¹)⁻¹).toReal) = fun ε ↦ ((1 + (ε.toReal)⁻¹)⁻¹) := by rfl

    set d : ℝ≥0 → _ :=
      (Real.toNNReal) ∘ (√·) ∘ (· / Real.pi) ∘
      (Real.log) ∘ ((2 * m') * ·) ∘
      (·⁻¹) ∘ (1 + ·) ∘ (·⁻¹)  ∘ NNReal.toReal

    change ∃ε, ∃ε_pos, d ε ≤ s n

    let w := (√(Real.log (2 * m') / Real.pi)).toNNReal / 2


    set s' := s n ⊓ w
    suffices (s') ∈ d '' (Set.Ioi 0) by
      simp only [Set.mem_image, Set.mem_Ioi] at this
      obtain ⟨x, pos_x, dxs⟩ := this
      refine ⟨x,NeZero.of_pos pos_x,?_⟩
      rw [dxs]
      subst s'
      exact min_le_left (s n) w
    subst d
    convert_to
      s' ∈
        Real.toNNReal '' (
        (√·) ''
        ((· / Real.pi) ''
        (Real.log ''
        (((2 * ↑m') * ·) ''
        ((·⁻¹) ''
        ((1 + ·) ''
        ((·⁻¹) ''
        (NNReal.toReal '' Set.Ioi 0))))))))
    · simp only [Set.image_comp]

    set uu := 2 * (m' : ℝ)
    have uu_pos : 0 < uu := by
      subst uu
      simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
      exact Nat.pos_of_neZero m'

    have : (NNReal.toReal '' Set.Ioi 0) = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_image, Set.mem_Ioi]
      refine ⟨fun ⟨y,y_pos, yx⟩ ↦ ?_,fun x_pos ↦ ⟨⟨x,x_pos.le⟩,x_pos,rfl⟩⟩
      exact lt_of_lt_of_eq y_pos yx
    rw [this]

    have : (fun ε : ℝ ↦ (ε⁻¹)) '' Set.Ioi 0 = Set.Ioi 0 := by
      ext x
      simp only [Set.image_inv_eq_inv, Set.mem_inv, Set.mem_Ioi, inv_pos]
    rw [this]
    have : (fun ε : ℝ ↦ 1 + ε) '' Set.Ioi 0 = Set.Ioi 1 := by
      ext x
      simp only [Set.image_add_left, Set.preimage_const_add_Ioi, sub_neg_eq_add, zero_add,
        Set.mem_Ioi]

    rw [this]
    have : (fun ε : ℝ ↦ (ε⁻¹)) '' Set.Ioi 1 = Set.Ioo 0 1 := by
      ext x
      simp only [Set.image_inv_eq_inv, Set.mem_inv, Set.mem_Ioi, Set.mem_Ioo]
      apply one_lt_inv_iff₀
    rw [this]
    have : ((fun x : ℝ ↦ uu * x) '' Set.Ioo 0 1) = Set.Ioo 0 (uu) := by
      ext y
      simp only [Set.mem_image, Set.mem_Ioo]

      refine ⟨fun ⟨x,⟨x0,x1⟩,xy⟩ ↦ ?_,?_⟩
      rw [←xy]
      constructor
      apply mul_pos uu_pos x0
      exact mul_lt_of_lt_one_right uu_pos x1
      intro ⟨y_pos,y_uu⟩
      use y * uu⁻¹
      refine ⟨⟨?_,?_⟩,?_⟩
      field_simp
      ring_nf
      exact y_pos
      field_simp
      exact y_uu
      field_simp

    rw [this]
    have : (Real.log '' Set.Ioo 0 (uu)) = Set.Iio (Real.log (uu)) := by
      ext x
      simp


      sorry
    rw [this]
    have : ((fun x ↦ x / Real.pi) '' Set.Iio (Real.log (2 * ↑m'))) =  Set.Iio (Real.log (2 * ↑m') / Real.pi) := by sorry
    rw [this]
    have : ((fun x ↦ √x) '' Set.Iio (Real.log (2 * ↑m') / Real.pi)) = Set.Ico 0 (√(Real.log (2 * ↑m') / Real.pi)) := by
      sorry
    rw [this]
    have : (Real.toNNReal '' Set.Ico 0 (√(Real.log (2 * ↑m') / Real.pi))) = Set.Ico 0 (Real.toNNReal √(Real.log (2 * ↑m') / Real.pi))  := by sorry
    rw [this]
    simp only [Set.mem_Ico, zero_le, true_and, gt_iff_lt]
    subst s'
    simp
    right
    subst w
    simp only [half_lt_self_iff, Real.toNNReal_pos, Real.sqrt_pos]



    sorry


-- note: NeZero allows this to be inferred, while h : q > 0 doesn't
example  {q : ℕ} [NeZero q] : Finite (ZMod q) := inferInstance
-- instance {q : ℕ} : Zero (ZMod q) where zero := 0
end Lemma_2_6
