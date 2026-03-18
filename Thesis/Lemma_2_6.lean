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

    set m' := m n
    set w := (√(Real.log (2 * m') / Real.pi)).toNNReal / 2
    have w_pos : 0 < w := sorry -- known
    set s' := s n ⊓ w
    let eps n y := Real.toNNReal (2 * n * Real.exp (-Real.pi * (y^2)) - 1)⁻¹
    use (eps (↑m') (↑s')), sorry
    unfold lemma_2_6_upper eps

    have m'_pos : 0 < (m' : ℝ) := Nat.cast_pos'.mpr (m_pos n |>.pos)
    simp only [neg_mul, NNReal.coe_inv, Real.coe_toNNReal']
    have condition : 0 < (2 * (m' : ℝ) * Real.exp (-(Real.pi * s' ^ 2)) - (1 : ℝ))⁻¹ := by
      simp only [inv_pos, sub_pos]

      have : ↑s' < √ (Real.log (2 * ↑m') / Real.pi) := by
        simp_all only [Nat.ofNat_pos, div_pos_iff_of_pos_right, Real.toNNReal_pos, Real.sqrt_pos, Nat.cast_pos,
          NNReal.coe_min, NNReal.coe_div, Real.coe_toNNReal', Real.sqrt_nonneg, sup_of_le_left, NNReal.coe_ofNat,
          inf_lt_iff, half_lt_self_iff, or_true, w, m', s'] -- aesop
      simp only [gt_iff_lt]

      convert_to 1 < Real.exp (Real.log (2 * ↑m')) * Real.exp (-(Real.pi * ↑s' ^ 2)) using 2
      ·
        apply Real.exp_log ?_ |>.symm
        linarith only [m'_pos]
      rw [←Real.exp_add]
      simp only [Real.one_lt_exp_iff, lt_add_neg_iff_add_lt, zero_add]

      -- clear

      sorry
    simp only [condition.le, sup_of_le_left, inv_inv, add_sub_cancel, ge_iff_le]
    ring_nf
    simp only [mul_inv_cancel_of_invertible, one_mul, Real.log_inv, Real.log_exp, neg_neg]
    ac_nf
    simp only [isUnit_iff_ne_zero, ne_eq, Real.pi_ne_zero, not_false_eq_true,
      IsUnit.mul_inv_cancel_left, NNReal.zero_le_coe, Real.sqrt_sq, Real.toNNReal_coe]
    exact min_le_left (s n) w


-- note: NeZero allows this to be inferred, while h : q > 0 doesn't
-- example  {q : ℕ} [NeZero q] : Finite (ZMod q) := inferInstance
-- instance {q : ℕ} : Zero (ZMod q) where zero := 0
end Lemma_2_6

-- this had a typo in the paper
def lemma_2_6_upper' (ε : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  (√ (Real.log (2 * n * (1 + ε⁻¹)) / Real.pi)).toNNReal -- conversion to ℝ≥0 for convenience

variable (Λ : 𝓛 ι) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem Lemma_2_6' (ε : ℝ≥0) [NeZero ε]
  : 𝓛.smoothing_parameter Λ ε ≤
  lemma_2_6_upper' ε (Fintype.card ι)
  / 𝓛.minimum_distance_sup (𝓛.dualLattice Λ) := by
    sorry


def negligible_over {R : Type*} [Norm R] (f : ℕ → R) (m : ℕ → ℕ) := ∀(c : ℕ), c > 0 → f =o[Filter.atTop] ((fun (n : ℕ) ↦ (n : ℝ) ^ (-(c : ℝ))) ∘ m)


theorem Lemma_2_6_then'''
  {m : ℕ → ℕ} (m_top : id ≤ m) (m_pos : ∀n, NeZero (m n)) (Λ : (n : ℕ) → 𝓛 (Fin (m n))) [∀n, DiscreteTopology ↥(Λ n)] [∀n, IsZLattice ℝ (Λ n)]
  (s : ℕ → ℝ≥0) (hs : s =ω (sqrt_log ∘ m))
  : ∃(ε : ℕ → ℝ≥0) (negl_ε : negligible_over ε m) (ε_pos : ∀n, NeZero (ε n)), -- maybe doesn't need to be positive always, but 𝓛.smoothing_parameter depends on it so the
  (fun n ↦ 𝓛.smoothing_parameter (Λ n) (ε n)) ≤ᶠ[Filter.atTop] (fun n ↦ s n / 𝓛.minimum_distance_sup (𝓛.dualLattice (Λ n)))
  := by

    let inv (n : ℕ) (s : ℝ≥0) := ((Real.exp ((s ^ 2 * Real.pi))) / (2 * n) - 1)⁻¹.toNNReal

    let cond (n : ℕ) (s : ℝ≥0) := 2 * ↑n < Real.exp (↑s ^ 2 * Real.pi)


    have inv_pos' (n) [NeZero n] s (co : cond n s) : 0 < inv n s := by
      unfold inv
      rw [Real.toNNReal_pos, inv_pos, sub_pos]
      bound [co, NeZero.pos n]
    have inv_pos (n) [NeZero n] s (co : cond n s) : NeZero <| inv n s := NeZero.of_pos (inv_pos' n s co)

    have inv_spec (n) [NeZero n] s (co : cond n s) : lemma_2_6_upper' (inv n s) n = s := by
      have n_pos : 0 < n := NeZero.pos _

      unfold lemma_2_6_upper' inv
      simp_all only [NNReal.coe_inv, Real.coe_toNNReal']
      have : 0 < (Real.exp (↑s ^ 2 * Real.pi ) / (2 * ↑n) - 1)⁻¹ := Real.toNNReal_pos.mp (inv_pos' n s co)
      simp_rw [max_eq_left_of_lt this]
      simp only [inv_inv, add_sub_cancel]
      simp_rw [mul_div_cancel₀ (b := 2 * (n : ℝ)) _ (by
        norm_num
        exact Nat.ne_zero_of_lt n_pos
        )]
      simp only [Real.log_exp, isUnit_iff_ne_zero, ne_eq, Real.pi_ne_zero, not_false_eq_true,
        IsUnit.mul_div_cancel_right, NNReal.zero_le_coe, Real.sqrt_sq, Real.toNNReal_coe]

    let default_const := (1 : ℝ≥0) -- to make 0 < ε true everywhere, not just eventually.
    let default_pos : NeZero (default_const) := inferInstance  -- [NeZero 1] is used by one_pos, so might as well get it directly
    -- I'll make it so $$\varepsilon=1$$ for the indices the condition doesn't hold,
    -- so I can still define the smoothing parameter $$\eta_\varepsilon$$ (requires positive $$\varepsilon$$) for all indices.

    let ε n := if cond (m n) (s n) then (inv (m n) (s n)) else default_const
    -- let ε n := (ε' (m n) (s n))
    have ε_pos: ∀n, NeZero (ε n) := by
      intro n
      unfold ε
      split
      ·
        rename_i co
        exact inv_pos (m n) (s n) co
      · exact default_pos

    have cond_eventually : ∀ᶠ n in Filter.atTop, cond (m n) (s n) := sorry

    refine ⟨ε,?_,?_,?_⟩
    ·
      -- negligible_over ε m
      sorry
    · exact ε_pos
    apply Filter.Eventually.mp cond_eventually
    apply Filter.Eventually.of_forall
    intro n co
    have tw : ε n = inv (m n) (s n) := ite_cond_eq_true _ _ (eq_true co)
    simp only [ge_iff_le]
    simp only [tw]
    trans
    · have := inv_pos (m n) (s n) co
      exact Lemma_2_6' (Λ n) (inv (m n) (s n))

    simp only [Fintype.card_fin]
    have := (inv_spec (m n) (s n) co).le
    gcongr
