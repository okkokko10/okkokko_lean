import Mathlib

#check Asymptotics.IsLittleO
open Asymptotics MeasureTheory
open ProbabilityTheory
open scoped NNReal ENNReal
#check ℙ

noncomputable section statistic

-- f(x) = ω(g(x))
notation:100 f " =ω[" l "] " g:100 => g =o[l] f
notation:100 f " =ω " g:100 => g =o[Filter.atTop] f

section negligible

def negligible {R : Type*} [Norm R] (f : ℕ → R) := ∀(c : ℕ), c > 0 → f =o[Filter.atTop] (fun (n : ℕ) ↦ (n : ℝ) ^ (-(c : ℝ)))



-- issue in Mathlib: Asymptotics.IsBigO.trans_isLittleO requires [SeminormedAddCommGroup F']
--  (through Asymptotics.IsBigOWith.weaken),
-- even though it actually only needs [Norm F'] such that ∀x : F', 0 ≤ ‖x‖
section IsBigO_fix

variable {α E F G : Type*} [Norm E]
  [Norm F] [Norm G] {l : Filter α} {f : α → E} {g' : α → F} {k : α → G}
  {c c' : ℝ}

open Asymptotics Filter


lemma fix.weaken (hF : ∀x : F, 0 ≤ ‖x‖) (h : IsBigOWith c l f g') (hc : c ≤ c') : IsBigOWith c' l f g' :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ ≤ c * ‖g' x‖ := hx
        _ ≤ _ := by
          gcongr
          exact hF (g' x)


lemma fix.exists_pos (hF : ∀x : F, 0 ≤ ‖x‖) (h : IsBigOWith c l f g') :
    ∃ c' > 0, IsBigOWith c' l f g' :=
  ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), weaken hF h <| le_max_left c 1⟩


lemma fix.exists_pos' (hF : ∀x : F, 0 ≤ ‖x‖) (h : f =O[l] g') : ∃ c > 0, IsBigOWith c l f g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  fix.exists_pos hF hc


@[trans]
theorem _root_.Asymptotics.IsBigO.trans_isLittleO' (hF : ∀x : F, 0 ≤ ‖x‖) {f : α → E} {g : α → F} {k : α → G} (hfg : f =O[l] g)
    (hgk : g =o[l] k) : f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := fix.exists_pos' hF hfg
  hc.trans_isLittleO hgk cpos


end IsBigO_fix

theorem negligible.bigO {R R' : Type*} [Norm R] [Norm R'] (hR' : ∀x : R', 0 ≤ ‖x‖)
    {f : ℕ → R} {g : ℕ → R'} (le : f =O[Filter.atTop] g) (g_negl : negligible g) : negligible f := by
  unfold negligible at *
  intro c c_pos
  apply le.trans_isLittleO' hR' (g_negl c c_pos)


instance : Norm ℝ≥0 := ⟨(↑)⟩

theorem negligible.bigO_nnreal {R : Type*} [Norm R]
    {f : ℕ → R} {g : ℕ → ℝ≥0} (le : f =O[Filter.atTop] g) (g_negl : negligible g) : negligible f := by
  refine negligible.bigO ?_ le g_negl
  intro x
  exact zero_le x

theorem negligible.of_le {a b : ℕ → ℝ≥0} (le : a ≤ b) (b_negl : negligible b) : negligible a := by
  unfold negligible at *
  intro c c_pos
  specialize b_negl c c_pos
  set w := fun (n : ℕ) ↦ (n : ℝ) ^ (-(c : ℝ))
  have : IsBigOWith 1 Filter.atTop a b := isBigOWith_of_le Filter.atTop le
  -- have : a =O[Filter.atTop] b := by exact Asymptotics.isBigO_of_le Filter.atTop le
  -- have := IsLittleO.trans_le
  exact this.trans_isLittleO b_negl (g := b) (Real.zero_lt_one)



-- todo: find an example
def negligible.examp : ℕ → ℝ≥0 := sorry
theorem negligible.example_spec : negligible examp := sorry
theorem negligible.example_pos : ∀n, NeZero (examp n) := sorry

#check NeZero.of_pos
#check NeZero.pos

-- theorem negligible.exists_smaller (f : ℕ → ℝ≥0) (f_pos : ∀ (n : ℕ), NeZero (f n)) :
--   ∃(ε : ℕ → ℝ≥0) (negl_ε : negligible ε) (ε_pos : ∀ (n : ℕ), NeZero (ε n)), ε ≤ f := by

--   refine ⟨fun n ↦ f n ⊓ examp n,?_,?_,?_⟩
--   · exact of_le (b := examp) inf_le_right example_spec
--   · intro n
--     apply NeZero.of_pos
--     refine lt_min (a := 0) ?_ ?_
--     exact NeZero.pos (f n)
--     exact negligible.example_pos n |>.pos
--   intro n
--   simp only [inf_le_left]


def negligible.smaller (f : ℕ → ℝ≥0) := fun n ↦ f n ⊓ examp n

theorem negligible.smaller_pos {f : ℕ → ℝ≥0}
  (f_pos : ∀ (n : ℕ), NeZero (f n)) (n) : NeZero (smaller f n)
  := by
  apply NeZero.of_pos
  refine lt_min ?_ ?_
  exact NeZero.pos (f n)
  exact negligible.example_pos n |>.pos

theorem negligible.smaller_le (f : ℕ → ℝ≥0) :
  smaller f ≤ f
  := by
  intro n
  exact min_le_left (f n) (examp n)




end negligible


-- #check ProbabilityTheory.HasPDF
#check MeasureTheory.pdf

--- [https://www.cs.bu.edu/~reyzin/teaching/s11cs937/notes-leo-1.pdf]


#check PMF


#check MeasureTheory.SignedMeasure.totalVariation -- Gemini found this.


-- I need to explain this
def statistical_distance' {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D) := (2⁻¹) * (SignedMeasure.totalVariation (X.toMeasure.toSignedMeasure - Y.toMeasure.toSignedMeasure)) Set.univ
lemma statistical_distance_finite_1 {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D)
  : IsFiniteMeasure ((X.toMeasure.toSignedMeasure - Y.toMeasure.toSignedMeasure).totalVariation) := isFiniteMeasureAdd
lemma statistical_distance_finite_2 {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D)
  : statistical_distance' X Y < ∞ := by
    unfold statistical_distance'
    refine ENNReal.mul_lt_top ?_ ?_
    simp only [ENNReal.inv_lt_top, Nat.ofNat_pos]
    exact @measure_lt_top _ _ _ (statistical_distance_finite_1 X Y) Set.univ

def statistical_distance {D : Type*} [MeasurableSpace D] (X Y : ProbabilityMeasure D) : ℝ≥0 := statistical_distance' X Y |>.toNNReal

#check EMetricSpace
example {D : Type*} [MeasurableSpace D] : PseudoMetricSpace (ProbabilityMeasure D) where
  dist := (statistical_distance' · · |>.toReal)
  dist_self x := by
    rw [statistical_distance', sub_self, SignedMeasure.totalVariation_zero]
    bound
  dist_comm x y := by
    unfold statistical_distance'
    rw [← SignedMeasure.totalVariation_neg _, neg_sub]
  dist_triangle x y z := by

    have f a b := ne_top_of_lt  <| @measure_lt_top D _ _ (statistical_distance_finite_1 a b) Set.univ
    have fxy := f x y
    have fxz := f x z
    have fyz := f y z
    -- simp only [statistical_distance_finite_1, measure_lt_top]
    unfold statistical_distance' at *

    set x' := x.toMeasure.toSignedMeasure
    set y' := y.toMeasure.toSignedMeasure
    set z' := z.toMeasure.toSignedMeasure

    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at *

    field_simp
    rw [←ENNReal.toReal_add fxy fyz]
    -- unfold SignedMeasure.totalVariation
    -- simp only [Measure.coe_add, Pi.add_apply, ne_eq, ENNReal.add_eq_top, measure_ne_top, or_self,
    --   not_false_eq_true, ENNReal.toReal_le_toReal]


    suffices
      ((x' - z').totalVariation Set.univ) ≤
      ((x' - y').totalVariation Set.univ) + ((y' - z').totalVariation Set.univ) by
      simp_all only [ne_eq, not_false_eq_true, ENNReal.add_eq_top, or_self, ENNReal.toReal_le_toReal, x', y', z']
    clear f
    set U := Set.univ
    revert U
    suffices
      ∀U, MeasurableSet U →
      (x' - y').totalVariation U ≠ ⊤ →
        (x' - z').totalVariation U ≠ ⊤ →
          (y' - z').totalVariation U ≠ ⊤ →
            (x' - z').totalVariation U ≤ (x' - y').totalVariation U + (y' - z').totalVariation U by
      exact this Set.univ (MeasurableSet.univ)

    intro U mU fxy fxz fyz
    clear fxy fxz fyz


    unfold SignedMeasure.totalVariation
    simp only [Measure.coe_add, Pi.add_apply]

    -- #check JordanDecomposition.mutuallySingular (x' - z').toJordanDecomposition
    have ⟨sxz, m_sxz, l_sxz, r_sxz, pos0_xz, neg0_xz⟩:= JordanDecomposition.exists_compl_positive_negative (x' - z').toJordanDecomposition
    have ⟨sxy, m_sxy, l_sxy, r_sxy, pos0_xy, neg0_xy⟩:= JordanDecomposition.exists_compl_positive_negative (x' - y').toJordanDecomposition
    have ⟨syz, m_syz, l_syz, r_syz, pos0_yz, neg0_yz⟩:= JordanDecomposition.exists_compl_positive_negative (y' - z').toJordanDecomposition

    -- simp_all only [ne_eq, SignedMeasure.toSignedMeasure_toJordanDecomposition,
    --   VectorMeasure.restrict_sub, VectorMeasure.restrict_zero, tsub_le_iff_right, zero_add,
    --   sub_nonneg, ge_iff_le]

    set xz := (x' - z').toJordanDecomposition
    set xy := (x' - y').toJordanDecomposition
    set yz := (y' - z').toJordanDecomposition


    #check MeasurableSet

    simp only [ge_iff_le]
    #check measure_inter_add_diff
    simp_rw [← measure_inter_add_diff U m_syz]

    -- simp [pos0_yz]






    -- [x - z] + [z - x] ≤ [x - y] + [y - x] + [y - z] + [z - y]
    -- [x - z]


    sorry
  edist_dist := sorry
  uniformity_dist := sorry
  cobounded_sets := sorry


-- #exit

def statistically_close {D : (n : ℕ) →  Type*} [∀n, MeasurableSpace (D n)] (X Y : (n : ℕ) → ProbabilityMeasure (D n)) :=
  negligible (fun n ↦ statistical_distance (X n) (Y n))


-- theorem lemma_5_1 {m : ℝ≥0} {_ : 2 * n }

-- #check Mathlib.Testing.SlimCheck


def sqrt_log : ℕ → ℝ≥0 := (Real.toNNReal ∘ Real.sqrt ∘  Real.log ∘ (↑))
def ω_sqrt_log (ω : ℕ → ℝ≥0) : Prop := ω =ω sqrt_log

abbrev goes_to_infinity (f : ℕ → ℕ) : Prop := Filter.Tendsto f Filter.atTop Filter.atTop

end statistic
