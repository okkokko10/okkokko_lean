import Mathlib.tactic

-- #check MeasureTheory.measurableSet_of_null


open Set Function MeasurableSpace Topology Filter ENNReal NNReal

variable {X : Type} (F : Set <| Set X) (A : Set X)

#check sInf_eq_iInf

@[inline]
def Covering : Set (ℕ → F) := {f : ℕ → F | A ⊆ ⋃ i, f i}
-- def Covering (f : ℕ → F) : Prop := A ⊆ ⋃ i, f i

theorem Covering.antitone : Antitone ( Covering F ) := by
  -- reduce
  -- exact fun ⦃a b⦄ a_3 ⦃a_4⦄ a_5 ⦃a_6⦄ a ↦ a_5 (a_3 a)
  intro A B alb
  -- simp only [le_eq_subset]
  intro x xb
  intro a aA
  exact xb (alb aA)
theorem Covering.bot_any : Covering F ∅ = univ := by
  simp only [Covering, empty_subset, setOf_true]

-- @[simp]
@[refl]
theorem Covering.mem (f) : f ∈ Covering F A ↔ A ⊆ ⋃ i, f i  := by rfl
theorem Covering.nonempty_antitone_univ (h : Nonempty (Covering F univ)) : Nonempty (Covering F A) := by
  -- simp [Covering.antitone]

  have qq : Covering F univ ⊆ Covering F A := by
    apply Covering.antitone
    simp only [le_eq_subset, subset_univ]
  simp_all only [nonempty_subtype]
  obtain ⟨w, h⟩ := h
  apply Exists.intro
  · apply qq
    exact h

theorem Covering.nonempty_if_univ_cover (h2 : ∃(f : ℕ → F), @univ X = ⋃ i, f i) : Nonempty (Covering F A) := by
  apply nonempty_antitone_univ
  simp only [nonempty_subtype, mem, univ_subset_iff]
  obtain ⟨w, h⟩ := h2
  use w
  exact h.symm

-- variable {ι : Type*} [Encodable ι]

noncomputable abbrev hat (ρ : X → ℝ≥0∞) (f : ℕ → X) := ∑' i, ρ (f i)



instance : AddCommMonoid ℝ≥0∞ := by infer_instance
instance {X} [Zero X]: Zero (Set X) where
  zero := {0}
instance {X} [Add X] : Add (Set X) := Set.add
-- instance : AddCommMonoid (Set ℝ≥0∞) where

def set_add (X : Type) [AddCommMonoid X] : AddCommMonoid (Set X) where
  add := Set.add.add
  add_assoc := by
    intro a b c
    simp only [←image2_add]
    ext x
    simp only [mem_image2, exists_exists_and_exists_and_eq_and]
    ac_nf
  zero := {0}
  zero_add := by
    intro a
    change {0} + _ = _
    simp only [singleton_add, zero_add, image_id']
  add_zero := by
    intro a
    change _ + {0} = _
    simp only [add_singleton, add_zero, image_id']
  nsmul := nsmulRec
  add_comm := by
    intro a b
    simp only [←image2_add]
    ext x
    simp only [mem_image2]
    conv in _ + _ => rw [add_comm]
    tauto

instance sradd: AddCommMonoid (Set ℝ≥0∞) := set_add ℝ≥0∞

def trivial_topo (X) : TopologicalSpace (X) where
  IsOpen A := True
  isOpen_univ := by trivial
  isOpen_inter := by tauto
  isOpen_sUnion := by tauto


-- theorem setsum_def (A B : Set ℝ≥0∞) : A + B = {a + b | a∈A, b∈B}

-- theorem setsum_inf (A B : Set ℝ≥0∞) : sInf A + sInf B = sInf (A + B) := by
theorem setsum_inf (A B : Set ℝ≥0∞) : sInf A + sInf B = ⨅(a ∈ A)(b ∈ B), a + b := by

  rw [sInf_add]
  -- apply congrArg
  -- congr! with x xA
  -- rw [add_comm]
  -- rw [sInf_add]
  -- congr with y
  -- congr with p
  -- exact add_comm y x

  conv => left; right; intro w1; right; intro w2; rw [add_comm]; rw [sInf_add]; right; intro; right; intro; rw [add_comm]




variable {N : Type} {R : Type} [AddCommMonoid R] [TopologicalSpace R]
-- def Setsum {N : Type} [Encodable N] (A : N → Set ℝ≥0∞) : Set ℝ≥0∞ := { x | ∃f : (i : N) → A i, (∑' i, f i) = x}
def Setsum (A : N → Set R) : Set R := { x | ∃(f : N → R), (∀i, f i ∈ A i) ∧  tsum f = x}
def Condsum (P : Set (N → R)) : Set R := { x | ∃f ∈ P, tsum f = x}
example (P : Set (N → R)) : Condsum P = tsum '' P := by rfl
theorem Setsum.as_image (A : N → Set R) : Setsum A = tsum '' {f | ∀i, f i ∈ A i} := by rfl

#check image2

-- Is this true? if not, is there a topology that satisfies this?
-- theorem Setsum.other (A : N → Set R) : Setsum A = @tsum _ (set_add R) (trivial_topo _) _ A := by
--   sorry
#check sInf_le_of_le
#check sInf_le_sInf_of_isCoinitialFor


lemma sInf_dense (A : Set ℝ≥0∞)(h : Nonempty A)(ε)(ε_pos : ε > 0) : ∃x ∈ A, x ≤ sInf A + ε := by
  obtain ⟨n,ni⟩ := h
  by_cases h' : sInf A = ⊤
  ·
    rw [h']
    refine ⟨n,ni,sup_eq_left.mp rfl⟩
  by_contra! w
  set p := sInf A + ε
  have t1: p ∈ lowerBounds A := by
    intro x xA
    exact le_of_lt (w x xA)
  have t2: sInf A < p := lt_add_right h' (ne_of_lt ε_pos).symm
  rw [lt_iff_not_ge] at t2
  apply t2
  exact CompleteLattice.le_sInf A p t1

theorem Setsum.empty_iff (A : N → Set R) : Nonempty (Setsum A) ↔ ∀i, Nonempty (A i) := by
  simp only [nonempty_subtype]
  simp only [Setsum, exists_prop, mem_setOf_eq]
  constructor
  · intro ⟨s, f, fA, tfs⟩ i
    use f i
    exact fA i
  intro aiA
  let f i := (aiA i).choose
  use (tsum f)
  use f
  simp only [and_true]
  intro i
  exact (aiA i).choose_spec

-- this is known to be true.
theorem convergent_series {ε} (ε_pos : ε > 0) : ∃g : ℕ → ℝ≥0∞, (∀i, g i > 0) ∧  ∑' i, g i ≤ ε :=  by
  -- have := tsum_geometric_inv_two
  use fun n ↦ (2⁻¹ ^ n) * (ε / 2)
  constructor
  ·
    intro i
    simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos, ENNReal.div_pos_iff, ne_eq, ofNat_ne_top,
      not_false_eq_true, and_true]
    constructor
    ·
      refine ENNReal.pow_pos ?_ i
      simp only [ENNReal.inv_pos, ne_eq, ofNat_ne_top, not_false_eq_true]
    exact pos_iff_ne_zero.mp ε_pos
  apply le_of_eq
  rw [ENNReal.tsum_mul_right]
  simp only [tsum_geometric, one_sub_inv_two, inv_inv]
  refine ENNReal.mul_div_cancel' ?_ ?_'
  simp only [OfNat.ofNat_ne_zero, IsEmpty.forall_iff]
  simp only [ofNat_ne_top, IsEmpty.forall_iff]

-- theorem countable_setsum_inf (f : ℕ → Set ℝ≥0∞) : ∑' (i : ℕ), sInf (f i) = sInf (∑' (i : ℕ), (f i)) := by
theorem Setsum.inf (A : ℕ → Set ℝ≥0∞) : ∑' (i : ℕ), sInf (A i) = sInf (Setsum A) := by

  by_cases empt : Nonempty (Setsum A)
  rotate_left
  ·
    have : Setsum A = ∅ := by exact not_nonempty_iff_eq_empty'.mp empt
    rw [this]
    rw [_root_.sInf_empty]
    apply ENNReal.tsum_eq_top_of_eq_top
    have : ∃i, A i = ∅ := by
      rw [Setsum.empty_iff] at empt
      simp only [not_forall, not_exists] at empt
      obtain ⟨i,empt⟩ := empt
      use i
      exact not_nonempty_iff_eq_empty'.mp empt
    obtain ⟨i,t⟩ := this
    use i
    rw [t]
    exact _root_.sInf_empty

  have nonemp : ∀i, Nonempty (A i) := (Setsum.empty_iff (A)).mp empt

  apply le_antisymm
  ·
    simp only [le_sInf_iff]
    intro x ⟨f,fA,tfx⟩
    rw [←tfx]
    refine ENNReal.tsum_le_tsum ?_
    intro i
    specialize fA i
    exact CompleteSemilatticeInf.sInf_le (A i) (f i) fA
  ·
    -- have : sInf (Setsum A) ≤ 5 := by
    --   refine sInf_le_iff.mpr ?_
    -- ⊢ sInf (Setsum A) ≤ ∑' (i : ℕ), sInf (A i)


    suffices ∀ε>0, sInf (Setsum A) ≤ ∑' (i : ℕ), sInf (A i) + ε by
      exact _root_.le_of_forall_pos_le_add this
    intro ε ε_pos

    apply sInf_le_iff.mpr
    intro b w
    -- unfold lowerBounds at w
    simp only [lowerBounds, mem_setOf_eq] at w

    have : ∀c, (∃a ∈ Setsum A, a ≤ c) → b ≤ c := by
      intro c ⟨a, aA, ac⟩
      trans a
      apply w aA
      exact ac
    apply this

    have ⟨g, g_pos,g_spec⟩ : ∃g : ℕ → ℝ≥0∞, (∀i, g i > 0) ∧  ∑' i, g i ≤ ε := convergent_series ε_pos

    --- use sInf_dense to note that g

    have : sInf ∅ = (⊤ : ℝ≥0∞) := by exact _root_.sInf_empty

    have u_ i := sInf_dense (A i) (nonemp i) (g i) (g_pos i)
    let u i := (u_ i).choose
    have u_spec1 i : u i ∈ A i  := (u_ i).choose_spec.left
    have u_spec2 i : u i ≤ sInf (A i) + g i := (u_ i).choose_spec.right

    -- use tsum u
    refine ⟨tsum u,?_,?_⟩
    use u
    -- have : tsum u ≤  := by
    --   exact ENNReal.tsum_le_tsum u_spec2
    trans ∑' i, (sInf (A i) + g i)
    exact ENNReal.tsum_le_tsum u_spec2
    have : ∑' i, (sInf (A i) + g i) = ∑' i, (sInf (A i)) + ∑' i, g i := by exact
      ENNReal.tsum_add
    rw [this]
    exact add_le_add_left g_spec (∑' (i : ℕ), sInf (A i))

theorem Setsum.inf_countable {N : Type} [e : Encodable N] (A : N → Set ℝ≥0∞) : ∑' (i : N), sInf (A i) = sInf (Setsum A) := by

  let B : ℕ → Set ℝ≥0∞ := fun i ↦  (e.decode i).casesOn' {0} A
  have : ∑' (i : N), sInf (A i) = ∑' (i), sInf (B i) := by
    have w (i) : sInf (B i) = (e.decode i).casesOn' 0 (sInf <| A ·) := by
      unfold B
      match (e.decode i) with
      | none => simp only [Option.casesOn'_none, sInf_singleton]
      | some x => simp only [Option.casesOn'_some]
    simp_rw [w]

    sorry
  sorry


def Condsum_comp {N' : Type} (P : N' → Set (N → R)) : Set R := Setsum ( fun j ↦ {∑' i, (B i) | B ∈ P j})
theorem Condsum_comp_simple {N' : Type} (P : N' → Set (N → X)) (m : X → R) :
    Condsum_comp (fun j ↦ { fun i ↦ m (B i) | B ∈ P j}) = Setsum ( fun j ↦ {∑' i, m (B i) | B ∈ P j}) := by
  unfold Condsum_comp
  simp only [mem_setOf_eq, exists_exists_and_eq_and]
theorem Condsum_comp_simple' {N' : Type} (P : N' → Set (N → R)) : Condsum_comp P = Setsum ( fun j ↦ tsum '' (P j)) := by rfl
theorem Condsum_comp_simple'' {N' : Type} (P : N' → Set (N → R)) : Condsum_comp P = tsum '' {f | ∀i, f i ∈ (tsum '' (P i))} := by rfl

-- example : ℕ → ℕ × ℕ

#check tsum_geometric_inv_two

-- theorem Condsum_comp_e (P : ℕ → Set (ℕ → R)) : ∃f : ℕ → Set R, Condsum_comp P = Setsum f := by
--   rw [Condsum_comp_simple']
--   simp only [exists_apply_eq_apply']


theorem inf_nested' {X Y : Type} [CompleteLattice Y] (A : Set X) (B : X → Set Y) : ⨅ x ∈ A, ⨅ y ∈ B x, y = ⨅ y ∈ ⋃ x ∈ A, B x, y := by
  simp only [mem_iUnion, exists_prop,iInf_exists]
  rw [iInf_comm]
  simp_rw [iInf_and]
  congr! with x
  rw [iInf_comm]

theorem inf_nested {X Y : Type} [CompleteLattice Y] (A : Set X) (B : X → Set Y) :
    ⨅ x ∈ A, sInf (B x) = sInf (⋃x ∈ A, B x) := by
  simp only [sInf_eq_iInf]
  exact inf_nested' A B

-- def makeup (μ : Set X → ℝ≥0∞) (𝔸 𝔹 : Set <| Set X) : Prop := ∀ A ∈ 𝔸, μ A = ⨅ B : ℕ → 𝔹, ⨅ (_ : A ⊆ ⋃ i, B i), ∑' i, μ (B i)
def makeup (μ : Set X → ℝ≥0∞) (𝔸 𝔹 : Set <| Set X) : Prop := ∀ A ∈ 𝔸, μ A = ⨅ (N : Type), ⨅ (_ : Encodable N), ⨅ B : N → Set X, ⨅ (codomain : ∀i, B i ∈ 𝔹), ⨅ (cover : A ⊆ ⋃ i, B i), ∑' i, μ (B i)

theorem makeup_composition {𝔸 𝔹 𝔽 : Set <| Set X} (μ : Set X → ℝ≥0∞)
    (h1 : makeup μ 𝔸 𝔹) (h2 : makeup μ 𝔽 𝔸) :
    makeup μ 𝔽 𝔹 := by
  unfold makeup at *

  intro F FiF
  specialize h2 F FiF
  rw [h2]

  apply le_antisymm
  ·
    simp only [le_iInf_iff]
    intros N' countableN'

    intros B B_codomain B_cover_F
    rename_bvar B → A

    apply _root_.le_of_forall_pos_le_add
    intros ε ε_pos
    -- change ⨅ N,⨅ (_ : Countable N),⨅ A, ⨅ (_ : ∀ (i : N), A i ∈ 𝔸), ⨅ (_ : F ⊆ ⋃ i, A i), ∑' (i : N), μ (A i) ≤ ∑' (i : N'), μ (f i) + ε
    conv => {
      enter [-2, -1, N, -1, cN, -1, A, -1, A_codomain, -1, A_cover_F, -2, i]

      rw [h1 (A i) (A_codomain i)]


    }


    sorry
  ·
    simp only [le_iInf_iff]
    intros N' countableN' A A_codomain A_cover_F
    have A_value (i : N') : μ (A i) = _ := h1 (A i) (A_codomain i)
    simp_rw [A_value]

    sorry


#version
-- #check image2

-- hw2e1
example {X : Type} (F : Set <| Set X)
  (h1 : EmptyCollection F)
  (h2 : ∃(B : ℕ → F), @univ X = ⋃ i, B i)
  (ρ : F → ℝ≥0∞) (h3 : ρ ∅ = 0)
  (μ : (Set X) → ENNReal)
  (μ_def : ∀(A : Set X), μ A = sInf  {∑' i, ρ (f i) | f ∈ Covering F A}) : ∃ μ' : MeasureTheory.OuterMeasure X, μ' = μ := by

  have F_has (A) : Nonempty (Covering F A) := by
    exact Covering.nonempty_if_univ_cover F A h2

  change ∀ (A : Set X), μ A = sInf {x | ∃ f ∈ Covering F A, hat ρ f = x} at μ_def

  have μ_def' : ∀ (A : Set X), μ A = sInf (hat ρ '' Covering F A) := μ_def
  refine ⟨⟨μ,?_,?_,?_⟩,rfl⟩
  ·
    rw [μ_def']
    rw [sInf_eq_bot.mpr]
    rfl
    rw [show ⊥ = (0 : ENNReal) by rfl]
    intro b b_pos
    simp only [mem_image, exists_exists_and_eq_and]
    -- simp only [Covering.mem, empty_subset, true_and, mem_setOf_eq, exists_exists_eq_and]
    simp only [Covering.mem]
    simp only [empty_subset, true_and]
    use (fun i ↦ ∅)
    dsimp only [hat]
    rw [h3]
    simp only [tsum_zero]
    exact b_pos
  ·
    intro A B AsB
    simp_rw [μ_def']
    -- [6]
    refine sInf_le_sInf_of_forall_exists_le ?_
    simp only [mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro a ac
    use a
    simp only [le_refl, and_true]
    apply Covering.antitone _ AsB ac

  ·
    intro s pds
    -- rw [←hat]
    simp_rw [μ_def]



    sorry

-- example : False := by
--   have := {f | ∃ (n : ℕ → ℕ+) (g : (i : ℕ) → Fin (n i) → ℝ), g = f}
--   sorry


example (x y : ℝ) (h : ∀ε>0, x ≤ y + ε) : x ≤ y := by
  exact _root_.le_of_forall_pos_le_add h
