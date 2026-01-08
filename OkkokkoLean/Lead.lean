import Mathlib.tactic
import OkkokkoLean.Basic

set_option linter.unusedSimpArgs false
section lead

variable {X : Type}

def sequence_leading  (f : X → X) (a: X) : ℕ → X
    | 0 => a
    | i + 1 => f (sequence_leading f a i)


def is_leading (f : X → X) (s : ℕ → X) := (∀i, f (s i) = s (i + 1))
theorem is_leading_def {f : X → X} {s : ℕ → X} : is_leading f s ↔ (∀i, f (s i) = s (i + 1)) := by rfl
def is_leading_limited (f : X → X) (n : ℕ) (s : ℕ → X) := (∀i < n, f (s i) = s (i + 1))
theorem is_leading_limited_def {f : X → X} {n : ℕ} {s : ℕ → X} : is_leading_limited f n s ↔ (∀i < n, f (s i) = s (i + 1)) := by rfl

theorem is_leading_then_limited {f : X → X} {s : ℕ → X} (h : is_leading f s) (n : ℕ) : is_leading_limited f n s := by
  refine is_leading_limited_def.mpr ?_
  intro i _
  exact h i


def leads (f : X → X) (a b: X) : Prop := ∃n, sequence_leading f a n = b
theorem leads_def {f : X → X} {a b: X} : leads f a b ↔ ∃n, sequence_leading f a n = b := by rfl

@[simp]
theorem sequence_leading_succ {f : X → X} {a: X} {i : ℕ} : sequence_leading f a (i + 1) = f (sequence_leading f a i) := by rfl
@[simp]
theorem sequence_leading_zero {f : X → X} {a: X} : sequence_leading f a 0 = a := by rfl


theorem sequence_leading_def' (f : X → X) (a: X) : sequence_leading f a = fun i ↦ f ^[i] a := by
  ext i
  induction i with
  | zero =>
    simp only [Nat.zero_eq, sequence_leading_zero, Function.iterate_zero, id_eq]
  | succ i' hi =>
    simp only [sequence_leading_succ, Function.iterate_succ', hi, Function.comp_apply]

theorem sequence_leading_apply (f : X → X) (a: X) {i : ℕ} : sequence_leading f a i = f ^[i] a := by rw [sequence_leading_def']


-- @[simp]
theorem sequence_leading_succ' {f : X → X} {a: X} {i : ℕ} : sequence_leading f a (i + 1) = (sequence_leading f (f a) i) := by
  simp_rw [sequence_leading_def']
  rw [Function.iterate_succ, Function.comp_apply]


theorem sequence_leading_tail {f : X → X} {a: X} {n : ℕ} {i : ℕ} :
    (sequence_leading f a) (n + i) = sequence_leading f (sequence_leading f a n) i := by
  simp_rw [sequence_leading_def']
  rw [add_comm]
  rw [Function.iterate_add_apply]


theorem sequence_leading_tail' {f : X → X} {a: X} {n : ℕ} {i : ℕ} :
    (sequence_leading f a) (n + i) = sequence_leading f (sequence_leading f a i) n := by
  rw [show n + i = i + n by group]
  exact sequence_leading_tail


theorem sequence_leading_is_leading {f : X → X} {a: X} : is_leading f (sequence_leading f a) := by
  rw [is_leading_def]
  intro i
  simp only [sequence_leading_succ]


theorem is_leading_eq_sequence_leading {f : X → X} {s : ℕ → X} (h : is_leading f s) : s = sequence_leading f (s 0) := by
  rw [is_leading_def] at h
  ext i
  induction i with
  | zero =>
    exact sequence_leading_zero.symm
  | succ i' hi =>
    rw [←h]
    rw [hi]
    exact sequence_leading_succ


theorem is_leading_limited_eq_sequence_leading {f : X → X} {n : ℕ} {s : ℕ → X} (h : is_leading_limited f n s) : ∀i ≤ n, s i = sequence_leading f (s 0) i := by
  intro i i_n
  rw [is_leading_limited_def] at h
  induction i with
  | zero =>
    exact sequence_leading_zero.symm
  | succ i' hi =>
    rw [sequence_leading_succ]
    have : i' <  n := (by linarith only [i_n])
    specialize hi this.le
    rw [←hi]
    specialize h i' this
    rw [←h]


theorem leads_alt_def {f : X → X} {a b : X} : leads f a b ↔ (∃s : ℕ → X, ∃n, is_leading_limited f n s ∧ s 0 = a ∧ s n = b) := by
  rw [leads_def]
  constructor
  ·
    intro ⟨n,w⟩
    use (sequence_leading f a)
    use n
    refine ⟨?_,?_,?_⟩
    intro i _
    exact sequence_leading_succ
    exact sequence_leading_zero
    exact w
  ·
    intro ⟨s,n,w1,s0a,snb⟩
    use n
    have := is_leading_limited_eq_sequence_leading w1 n (by rfl)
    rw [s0a,snb] at this
    rw [this]








section old_sequence_leading_choose


-- theorem sequence_leading' {X} (f : X → X) (a: X) : ∃!s : ℕ → X, (is_leading f s) ∧ s 0 = a := by
--   use sequence_leading f a
--   refine ⟨⟨?_,?_⟩,?_⟩
--   · unfold is_leading
--     intro i
--     rfl
--   · rfl

--   intro s
--   simp only [and_imp]
--   intro l s0a
--   ext i
--   induction i with
--   | zero =>
--     rw [s0a]
--     rfl
--   | succ i' ih =>
--     have := l i'
--     rw [←this,ih]
--     rfl


-- def sequence_leading_choose {X} (f : X → X) (a: X) : ℕ → X := (sequence_leading' f a).choose

-- theorem sequence_leading_spec_A {X} (f : X → X) (a: X) : is_leading f (sequence_leading_choose f a) := (sequence_leading' f a).choose_spec.left.left

-- theorem sequence_leading_spec_B {X} (f : X → X) (a: X) : (sequence_leading_choose f a) 0 = a := (sequence_leading' f a).choose_spec.left.right


-- theorem sequence_leading_value {X} (f : X → X) (a: X) : (sequence_leading_choose f a) = sequence_leading f a := by
--   -- have t0:= (sequence_leading' f a).choose_spec
--   have seqq: ∀ (y : ℕ → X), (fun s ↦ is_leading f s ∧ s 0 = a) y → y = sequence_leading f a := by
--     -- copied from above
--     intro s
--     simp only [and_imp]
--     intro l s0a
--     ext i
--     induction i with
--     | zero => exact s0a
--     | succ i' ih =>
--       rw [←l i',ih]
--       rfl
--   have := seqq (sequence_leading_choose f a)
--   simp only [and_imp] at this
--   apply this
--   · unfold is_leading
--     intro i
--     apply sequence_leading_spec_A
--   apply sequence_leading_spec_B



-- -- theorem sequence_leading_unique {X} (f : X → X) (a: X) (s) : (is_leading f s) ∧ s 0 = a ↔ s = sequence_leading f a := by sorry
-- -- theorem sequence_leading_unique' {X} (f : X → X) (a: X) (s) : (is_leading f s) → s 0 = a → s = sequence_leading f a := by sorry



-- theorem sequence_leads_iff' {X} (f : X → X) (a b: X) : leads f a b ↔ ∃n, sequence_leading_choose f a n = b := by
--   constructor
--   ·
--     simp_rw [leads_alt_def]

--     intro ⟨ab_s,ab_n,ab_yield,ab_0,ab_1⟩
--     use ab_n
--     rw [←ab_1]
--     have : ∀ i ≤ ab_n, sequence_leading_choose f a i = ab_s i := by
--       intro i i_le
--       induction i with
--       | zero => rw [sequence_leading_spec_B,ab_0]
--       | succ i' ih =>
--         have prev := ih (by linarith )
--         have t1:= sequence_leading_spec_A f a i'
--         have t2:= ab_yield i' (by linarith)
--         exact (prev ▸ t1) ▸ t2
--     exact this ab_n (by linarith only)
--   · intro ⟨n,w⟩

--     simp_rw [leads_alt_def]
--     refine ⟨(sequence_leading_choose f a), n, ?_,?_,?_⟩
--     · intro i _
--       exact sequence_leading_spec_A ..
--     · exact sequence_leading_spec_B ..
--     · exact w

end old_sequence_leading_choose

@[trans]
theorem leads_trans (f : X → X) (a b c: X) : leads f a b → leads f b c → leads f a c := by
  simp_rw [leads_def]
  intro ⟨an,fab⟩ ⟨bn,fbc⟩
  use (an + bn)
  rw [sequence_leading_tail]
  rw [fab,fbc]
  done

@[refl]
theorem leads_self (f : X → X) (a: X) : leads f a a := by
  rw [leads_def]
  use 0
  exact sequence_leading_zero



-- is not a PartialOrder

def leadsPreorder (f : X → X) : Preorder X where
  le := leads f
  le_refl := leads_self f
  le_trans := leads_trans f

@[simp]
theorem leads_succ (f : X → X) (a: X) : leads f a (f a) := by
  rw [leads_def]
  use 1
  exact rfl


theorem leads_preserves  {f : X → X} {a b : X} {p : X → Prop} (hp : ∀x, p x → p (f x)) (l : leads f a b) : p a → p b := by
  intro pa
  simp_rw [leads_def,sequence_leading_apply f a] at l
  obtain ⟨n, w⟩ := l
  have := Function.Iterate.rec p pa hp n
  simp [w] at this
  exact this


theorem leads_preserves_antitone  {f : X → X} {a b : X} {p : X → Prop} (hp : ∀x, p (f x) → p x) (l : leads f a b) : p b → p a := by
  rw [← not_imp_not]
  simp_rw [←@not_imp_not (p _) (p _)] at hp
  exact leads_preserves (p := (¬ p ·)) hp l

theorem leads_preserves_iff  {f : X → X} {a b : X} {p : X → Prop} (hp : ∀x, p x ↔ p (f x)) (l : leads f a b) : p a ↔ p b :=
  ⟨leads_preserves (hp · |>.mp) l, leads_preserves_antitone (hp · |>.mpr) l⟩



lemma leads_connected1  {f : X → X} {a b c : X}
    {nb : ℕ} (wb : sequence_leading f a nb = b)
    {nc : ℕ} (wc : sequence_leading f a nc = c)
    (hn : nb ≤ nc) : sequence_leading f b (nc - nb) = c := by
  -- rw [leads_def]
  -- use nc - nb
  have : nc = nb + (nc - nb) := by
    rw [←Nat.add_sub_assoc hn nb, add_tsub_cancel_left]
  set m := nc - nb
  have t:= wb ▸ sequence_leading_tail ▸ this ▸ wc
  rw [this] at wc
  rw [sequence_leading_tail] at wc
  rw [wb] at wc
  exact wc


theorem leads_connected  {f : X → X} {a b c : X} (lb : leads f a b) (lc : leads f a c) : leads f b c ∨ leads f c b := by
  simp_rw [leads_def] at lb lc ⊢
  obtain ⟨nb,wb⟩ := lb
  obtain ⟨nc,wc⟩ := lc
  by_cases hn : nb ≤ nc
  left
  exact ⟨_,leads_connected1 wb wc hn⟩
  right
  exact ⟨_,leads_connected1 wc wb (by linarith only [hn])⟩


-- untrue:
-- def leads_connected'  {f : X → X} {a b c : X} (lb : leads f b a) (lc : leads f c a) : leads f b c ∨ leads f c b := by sorry

-- #check Nat.find
-- if a leads to b which satisfies p, this gives the first index that satisfies p
-- this is just leads_pred_steps but worse
def leads_first {f : X → X} {a b : X} {p : X → Prop} [DecidablePred p] {nb : ℕ} (wb : sequence_leading f a nb = b) (pb : p b) :=
    Nat.find (p := fun w ↦ p (sequence_leading f a w)) ⟨nb,by simp only [wb,pb]⟩

def leads_steps {f : X → X} [DecidableEq X] (a b : X) (l : leads f a b) : ℕ := Nat.find l

def leads_pred  (f : X → X) (a : X) (p : X → Prop) : Prop := (∃n, p (sequence_leading f a n))

theorem leads_pred_def {f : X → X} {a : X} {p : X → Prop} :
    leads_pred f a p ↔ (∃n, p (sequence_leading f a n)) := by rfl

theorem leads_pred_def' {f : X → X} {a : X} {p : X → Prop} :
    leads_pred f a p ↔ (∃b, p b ∧ leads f a b) := by
  simp only [leads_pred_def,leads_def]
  aesop

@[trans]
theorem leads_pred_trans {X} f (a b : X) p : leads f a b → leads_pred f b p → leads_pred f a p := by
  simp_rw [leads_def]
  intro ⟨an,fab⟩ ⟨bn,fbc⟩
  use (an + bn)
  rw [sequence_leading_tail]
  rw [fab]
  exact fbc



theorem leads_pred_or {f : X → X} {a : X} {p1 p2 : X → Prop} : (leads_pred f a p1 ∨ leads_pred f a p2) ↔ leads_pred f a (p1 ⊔ p2) := by
  reduce
  aesop

def leads_pred_steps {f : X → X}  {a: X} {p : X → Prop} [DecidablePred p] (l : leads_pred f a p) : ℕ := Nat.find l


-- todo: use this form more.
abbrev leads_in (f : X → X) (a b : X) (n : ℕ) : Prop := sequence_leading f a n = b


-- @[trans]
theorem leads_in_connection (f : X → X) (a b c: X) (ab bc) : leads_in f a b ab → leads_in f b c bc → leads_in f a c (ab + bc) := by
  unfold leads_in
  intro a_b b_c
  rw [←b_c,←a_b]
  exact sequence_leading_tail
theorem leads_in_connection' (f : X → X) (a b c: X) (ab bc) : leads_in f a b ab → leads_in f a c (ab + bc) → leads_in f b c bc := by
  unfold leads_in
  intro a_b a_c
  rw [sequence_leading_tail,a_b] at a_c
  exact a_c


-- theorem leads_in_self (f : X → X) (a: X) : leads_in f a a 0 := by
--   rw [leads_def]
--   use 0
--   exact sequence_leading_zero


#check sequence_leading_succ

theorem sequence_leading_pred {f : X → X} {a: X} {i : ℕ} (hi : i ≠ 0) : f (sequence_leading f a (i - 1)) = (sequence_leading f a i) := by
  simp_rw [←sequence_leading_succ]
  have : i - 1 + 1 = i := Nat.succ_pred hi
  rw [this]

-- theorem leads_stage (f1 : X → X) (f2 : X → X) {a b : X} (p : X → Prop) [DecidablePred p] (l : leads (fun x ↦ if) a b) (ind)

-- leads f a b but all intermediate steps including a and b satisfy p
def leads_preserving_in (f : X → X) (p : X → Prop) (a b : X) (n) := leads_in f a b n ∧ ∀i ≤ n, p (sequence_leading f a i)

-- -- if p is monotonous, a leads to b, p a < p b, then the leading can be uniquely split into ¬p and p
-- theorem leads_partition_while (f : X → X) {a b : X} (p : X → Prop) [DecidablePred p] {n} (l : leads_in f a b n) (hp : ∀x, p x → p (f x))
--     (ha : ¬ p a) (hb : p b) : ∃z ≤ n, ∀i, z < i ↔ p (sequence_leading f a i)  := sorry
def leads_partition_while (f : X → X) (a b : X) (p : X → Prop) (z y) :=
    (leads_preserving_in f (¬ p ·) a (sequence_leading f a z) z)
    ∧ (leads_preserving_in f p (f <| sequence_leading f a z) b y)

theorem leads_partition_while_mk (f : X → X) {a b : X} (p : X → Prop) [DecidablePred p] {n} (l : leads_in f a b n) (hp : ∀x, p x → p (f x))
    (ha : ¬ p a) (hb : p b) :
    ∃z < n, leads_partition_while f a b p z (n - z - 1) := by
  have n_pos : 0 < n :=(by
    rw [@Nat.pos_iff_ne_zero]
    intro n0
    have := (n0 ▸ l)
    have : a = b := by exact this
    apply (this ▸ ha) hb
    )
  have have_p: ∃n'<n, p (f (sequence_leading f a n')) := ⟨n-1,Nat.sub_lt n_pos zero_lt_one,by
    simp_rw [←sequence_leading_succ]
    have : n - 1 + 1 = n := Nat.succ_pred n_pos.ne'
    rw [this,l]
    exact hb⟩

  have ⟨z1,z2⟩ := Nat.find_spec have_p
  set z := Nat.find have_p
  use z
  refine ⟨z1,?_,?_⟩
  ·
    refine ⟨?_,?_⟩
    rfl
    intro i iz
    by_cases hi : i = 0
    · simp_all only [Nat.find_lt_iff, and_self_left, zero_le, sequence_leading_zero,
        not_false_eq_true, ha]
    rw [←sequence_leading_pred hi]
    have w := Nat.find_min (m := i - 1) have_p (lt_of_lt_of_le (Nat.sub_lt (Nat.pos_of_ne_zero hi) zero_lt_one) iz)
    intro c
    apply w
    simp only [c, and_true]
    apply lt_of_le_of_lt ?_ z1
    apply le_trans ?_ iz
    exact Nat.sub_le i 1
  ·
    unfold leads_preserving_in leads_in
    simp_rw [←sequence_leading_succ]
    simp only [←sequence_leading_tail]
    refine ⟨?_,?_⟩
    rw [←l]
    apply congrArg
    exact Nat.add_sub_of_le z1
    intro i i_n
    induction i with
    | zero =>
      simp
      exact z2
    | succ i' prev =>
      specialize prev (by linarith)
      change p (sequence_leading f a (z + 1 + i' + 1))
      rw [sequence_leading_succ]
      exact hp (sequence_leading f a (z + 1 + i')) prev


theorem sequence_leading_identity {f : X → X} {a : X} (h : f a = a) (n : ℕ) : sequence_leading f a n = a := by
  induction n with
  | zero => rfl
  | succ n prev => rw [sequence_leading_succ,prev,h]



-- actually, is ha needed?

def leads_pos (f : X → X) (a b: X) : Prop := ∃n>0, sequence_leading f a n = b
theorem leads_pos_def {f : X → X} {a b: X} : leads_pos f a b ↔ ∃n>0, sequence_leading f a n = b := by rfl

theorem leads_pos_def' {f : X → X} {a b: X} : leads_pos f a b ↔ leads f (f a) b := by
  unfold leads
  simp_rw [←sequence_leading_succ']
  unfold leads_pos
  set p := fun n ↦ sequence_leading f a n = b

  change (∃n>0, p n) ↔ ∃n, p (n + 1)
  constructor
  intro ⟨n,n0,pn⟩
  use (n - 1)
  have : n - 1 + 1 = n := by exact Nat.sub_add_cancel n0
  simp_all only [gt_iff_lt, p]
  intro ⟨n,pn1⟩
  use n + 1
  simp_all only [sequence_leading_succ, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_self, p]

theorem leads_pos_def'' {f : X → X} {a b: X} : leads_pos f a b ↔ ∃n, sequence_leading f a (n + 1) = b := by
  rw [leads_pos_def']
  simp_rw [sequence_leading_succ']
  rfl



def leads_pred_pos  (f : X → X) (a : X) (p : X → Prop) : Prop := (∃n > 0, p (sequence_leading f a n))


theorem leads_pred_pos_def {f : X → X} {a : X} {p : X → Prop} :
    leads_pred_pos f a p ↔ (∃b, p b ∧ leads_pos f a b) := by
  unfold leads_pos leads_pred_pos
  simp_all only [gt_iff_lt]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, h⟩ := a_1
    obtain ⟨left, right⟩ := h
    apply Exists.intro
    · apply And.intro
      · exact right
      · apply Exists.intro
        · apply And.intro
          on_goal 2 => {rfl
          }
          · simp_all only
  · intro a_1
    obtain ⟨w, h⟩ := a_1
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    subst right
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {exact left
      }
      · simp_all only


theorem leads_pred_pos_def' {f : X → X} {a : X} {p : X → Prop} :
    leads_pred_pos f a p ↔ leads_pred f (f a) p := by
  rw [leads_pred_pos_def]
  simp_rw [leads_pos_def']
  rw [leads_pred_def']

theorem leads_of_leads_pos {f : X → X} {a b: X} : leads_pos f a b → leads f a b := by
  unfold leads_pos leads
  tauto

theorem leads_pred_of_leads_pred_pos {f : X → X} {a : X} {p : X → Prop} : leads_pred_pos f a p → leads_pred f a p := by
  unfold leads_pred_pos leads_pred
  tauto

theorem leads_pred_pos_if_not_zero {f : X → X} {a : X} {p : X → Prop} (h1: ¬ p a) : leads_pred f a p ↔  leads_pred_pos f a p := by
  rw [leads_pred_pos]
  unfold leads_pred
  constructor
  intro h2
  have ⟨n,w⟩ := h2
  use n
  refine ⟨?_,w⟩
  by_contra n0
  have : n = 0 := by exact Nat.eq_zero_of_not_pos n0
  rw [this] at w
  simp at w
  exact h1 w
  tauto

-- some leads theorems could be solved from leads_pred using "leads f a b ↔ leads_pred f a (· = b)"


theorem leads_pred_pos_as_leads_pred {f : X → X} {a : X} {p : X → Prop} : leads_pred_pos f a p ↔ leads_pred f a (p <| f ·) := by
  rw [leads_pred_pos_def']
  rw [leads_pred_def,leads_pred_def]
  simp only [← sequence_leading_succ, sequence_leading_succ', implies_true]

theorem leads_as_leads_pred {f : X → X} {a b : X} : leads f a b ↔ leads_pred f a (· = b) := by rfl
theorem leads_pos_as_leads_pred_pos {f : X → X} {a b : X} : leads_pos f a b ↔ leads_pred_pos f a (· = b) := by rfl


theorem leads_pred_impl {p p' : X → Prop} (h : ∀x, p x → p' x) {f : X → X} {a} (lp : leads_pred f a p) :  leads_pred f a p' := by
  simp only [leads_pred_def'] at lp ⊢
  obtain ⟨w, h_1⟩ := lp
  obtain ⟨left, right⟩ := h_1
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {exact right
    }
    · simp_all only


theorem leads_pos_next {f : X → X} {a: X} : leads_pos f a (f a) := by
  rw [leads_pos_def']





def leads_always  (f : X → X) (a : X) (p : X → Prop) : Prop := (∀n, p (sequence_leading f a n))

theorem leads_always_def {f : X → X} {a : X} {p : X → Prop} : leads_always f a p ↔ (∀n, p (sequence_leading f a n)) := by rfl

theorem leads_always_def' {f : X → X} {a : X} {p : X → Prop} : leads_always f a p ↔ (∀b, leads f a b → p b) := by
  unfold leads_always leads
  simp only [forall_exists_index, forall_apply_eq_imp_iff]

theorem leads_preserves'  {f : X → X} {p : X → Prop} (hp : ∀x, p x → p (f x)) {a: X} : p a → leads_always f a p := by
  intro pa
  rw [leads_always_def']
  intro b lb
  exact leads_preserves hp lb pa

/--
there exists infinitely many successors that satisfy p
-/
def leads_frequently (f : X → X) (a : X) (p : X → Prop) : Prop := (∀m, ∃n ≥ m, p (sequence_leading f a n))


theorem leads_frequently_def_add {f : X → X} {a : X} {p : X → Prop} : leads_frequently f a p ↔ (∀m, ∃n, p (sequence_leading f a (n + m))) := by
  unfold leads_frequently
  simp only [exists_ge]


theorem leads_frequently_def' {f : X → X} {a : X} {p : X → Prop} : leads_frequently f a p ↔ leads_always f a (leads_pred f · p) := by
  rw [leads_frequently_def_add]
  simp only [sequence_leading_tail']
  rw [leads_always_def]
  simp only [leads_pred_def]


def leads_eventually (f : X → X) (a : X) (p : X → Prop) : Prop := (∃m, ∀n ≥ m, p (sequence_leading f a n))

theorem leads_eventually_def {f : X → X} {a : X} {p : X → Prop} : leads_eventually f a p ↔ (∃m, ∀n ≥ m, p (sequence_leading f a n)) := by rfl

theorem leads_eventually_def_add {f : X → X} {a : X} {p : X → Prop} : leads_eventually f a p ↔ (∃m, ∀n, p (sequence_leading f a (n + m))) := by
  unfold leads_eventually
  simp only [eventually_ge]

theorem leads_eventually_def' {f : X → X} {a : X} {p : X → Prop} : leads_eventually f a p ↔ leads_pred f a (leads_always f · p) := by
  rw [leads_eventually_def_add]
  simp only [sequence_leading_tail']
  rfl


theorem leads_eventually_frequently_inverse {f : X → X} {a : X} {p : X → Prop} :
    (¬ leads_eventually f a p) ↔ leads_frequently f a (¬ p ·)  := by
  unfold leads_eventually leads_frequently
  simp only [ge_iff_le, eventually_ge, not_exists, not_forall, exists_ge]
theorem leads_eventually_frequently_inverse' {f : X → X} {a : X} {p : X → Prop} :
    (¬ leads_eventually f a (¬ p ·)) ↔ leads_frequently f a p  := by
  simp only [leads_eventually_frequently_inverse, not_not]
theorem leads_eventually_frequently_inverse'' {f : X → X} {a : X} {p : X → Prop} :
    (¬ leads_frequently f a (¬ p ·)) ↔ leads_eventually f a p  := by
  simp only [← leads_eventually_frequently_inverse, not_not]

theorem leads_pred_always_inverse {f : X → X} {a : X} {p : X → Prop} :
    (¬ leads_pred f a p) ↔ leads_always f a (¬ p ·)  := by
  unfold leads_pred leads_always
  simp only [not_exists]

theorem leads_pred_always_inverse' {f : X → X} {a : X} {p : X → Prop} :
    (¬ leads_pred f a (¬ p ·)) ↔ leads_always f a p  := by
  simp only [leads_pred_always_inverse, not_not]
theorem leads_pred_always_inverse'' {f : X → X} {a : X} {p : X → Prop} :
    (¬ leads_always f a (¬ p ·)) ↔ leads_pred f a p  := by
  simp only [← leads_pred_always_inverse, not_not]

theorem leads_eventually_of_leads_always {f : X → X} {a : X} {p : X → Prop} : leads_always f a p → leads_eventually f a p := by
  intro alw
  use 0
  simp only [ge_iff_le, zero_le, forall_const]
  exact alw

theorem leads_eventually_of_pred_monotone {f : X → X} {a : X} {p : X → Prop}
    (hp : ∀x, p x → p (f x)) (lp : leads_pred f a p) : leads_eventually f a p := by
  rw [leads_eventually_def']
  exact leads_pred_impl (fun x px ↦ leads_preserves' hp px) lp

theorem leads_pred_of_eventually {f : X → X} {a : X} {p : X → Prop} (lp : leads_eventually f a p) :
    leads_pred f a p := by
  reduce at lp ⊢
  tauto


theorem leads_pred_of_frequently {f : X → X} {a : X} {p : X → Prop} (lp : leads_frequently f a p) :
    leads_pred f a p := by
  reduce at lp ⊢
  specialize lp 0
  tauto

theorem leads_pred_of_always {f : X → X} {a : X} {p : X → Prop} (lp : leads_always f a p) :
    leads_pred f a p := by
  reduce at lp ⊢
  tauto


theorem leads_always_impl {p p' : X → Prop} (h : ∀x, p x → p' x) {f : X → X} {a} (lp : leads_always f a p) :  leads_always f a p' := by
  rw [leads_always_def'] at lp ⊢
  intro b lb
  exact h b (lp b lb)


theorem leads_frequently_impl {p p' : X → Prop} (h : ∀x, p x → p' x) {f : X → X} {a} (lp : leads_frequently f a p) :  leads_frequently f a p' := by
  rw [leads_frequently_def'] at lp ⊢
  refine leads_always_impl ?_ lp
  apply leads_pred_impl
  apply h

@[simp]
theorem leads_pred_idempotent {f : X → X} {a : X} {p : X → Prop} : leads_pred f a (leads_pred f · p) ↔ leads_pred f a p := by
  unfold leads_pred
  simp only [←sequence_leading_tail]
  tauto

@[simp]
theorem leads_always_idempotent {f : X → X} {a : X} {p : X → Prop} : leads_always f a (leads_always f · p) ↔ leads_always f a p := by

  unfold leads_always
  simp only
  simp only [←sequence_leading_tail]
  --conv => left; rw [forall_add]
  simp only [forall_add (p <| sequence_leading f a ·)]


theorem leads_frequently_pred_invariant {f : X → X} {a : X} {p : X → Prop} :
    leads_frequently f a (leads_pred f · p) ↔ leads_frequently f a p  := by
  simp only [leads_frequently_def', leads_pred_idempotent]

theorem leads_frequently_pred_invariant' {f : X → X} {a : X} {p : X → Prop} :
     leads_pred f a (leads_frequently f · p) ↔ leads_frequently f a p := by
  symm
  constructor
  ·
    intro w
    use 0
    exact w

  intro w
  rw [leads_pred_def'] at w
  have ⟨b,lfbp,lab⟩ := w
  unfold leads_frequently at lfbp ⊢
  intro m
  have ⟨k,kb⟩ := lab
  rw [←kb] at lfbp
  simp only [ge_iff_le, exists_ge, ←sequence_leading_tail'] at lfbp
  simp only [ge_iff_le, exists_ge]
  specialize lfbp m
  have ⟨n,ns⟩ := lfbp
  use n + k
  clear * - ns
  have : n + k + m = n + m + k := by group
  rw [this]
  exact ns

@[simp]
theorem leads_frequently_idempotent {f : X → X} {a : X} {p : X → Prop} :
    leads_frequently f a (leads_frequently f · p) ↔ leads_frequently f a p  := by
  nth_rw 1 [leads_frequently_def']
  simp_rw [leads_frequently_pred_invariant']
  simp_rw [leads_frequently_def']
  simp_rw [leads_always_idempotent]

@[simp]
theorem leads_eventually_idempotent {f : X → X} {a : X} {p : X → Prop} :
    leads_eventually f a (leads_eventually f · p) ↔ leads_eventually f a p  := by
  suffices (¬¬leads_eventually f a fun x ↦ ¬ ¬ leads_eventually f x p) ↔ leads_eventually f a p by
    simp_all only [not_not]
  simp only [leads_eventually_frequently_inverse, not_not, leads_frequently_idempotent]
  simp only [← leads_eventually_frequently_inverse, not_not]


theorem leads_always_and {f : X → X} {a : X} {p p' : X → Prop} : (leads_always f a p ∧ leads_always f a p') ↔ leads_always f a (fun x ↦ p x ∧ p' x) := by
  simp only [leads_always_def']
  constructor
  ·
    intro ⟨wl,wr⟩ b lb
    exact ⟨wl b lb, wr b lb⟩
  intro w
  exact forall₂_and.mp w




theorem leads_eventually_connected {f : X → X} {a : X} {p p' : X → Prop}
    (hp : leads_eventually f a p) (hp' : leads_eventually f a p') :
    leads_eventually f a (fun x ↦ p x ∧ p' x) := by
  rw [leads_eventually_def']
  simp_rw [←leads_always_and]
  rw [leads_eventually_def',leads_pred_def'] at hp hp'
  obtain ⟨b,lbp,lab⟩ := hp
  obtain ⟨b',lbp',lab'⟩ := hp'
  have := leads_connected lab lab'
  cases this with
  | inl h =>
    rw [leads_pred_def']
    refine ⟨b',⟨?_,lbp'⟩,lab'⟩
    rw [leads_always_def'] at lbp ⊢
    intro c lb'c
    have : leads f b c := by exact leads_trans f b b' c h lb'c
    exact lbp c this
  | inr h =>
    -- I wonder how this kind of repetition could be avoided.
    rw [leads_pred_def']
    refine ⟨b,⟨lbp,?_⟩,lab⟩
    rw [leads_always_def'] at lbp' ⊢
    intro c lb'c
    have : leads f b' c := by exact leads_trans f b' b c h lb'c
    exact lbp' c this


theorem leads_eventually_frequently_connected {f : X → X} {a : X} {p p' : X → Prop}
    (hp : leads_eventually f a p) (hp' : leads_frequently f a p') :
    leads_frequently f a (fun x ↦ p x ∧ p' x) := by
  unfold leads_frequently at hp' ⊢
  simp only -- [ge_iff_le]
  intro m
  unfold leads_eventually at hp
  obtain ⟨mm,hp⟩ := hp
  have ⟨n,n_m,w⟩ := hp' (max m mm)
  simp only [ge_iff_le, sup_le_iff] at n_m
  refine ⟨n,n_m.left,?_,w⟩
  apply hp
  exact n_m.right


theorem leads_always_leads {f : X → X} {a b : X} : leads f a b ↔ leads_always f b (leads f a) := by
  constructor
  ·
    intro lab
    simp_rw [leads_always_def']
    intro c lbc
    trans
    exact lab
    exact lbc
  intro la_bl
  simp_rw [leads_always_def'] at la_bl
  apply la_bl
  exact leads_self f b


def leads_converge (f : X → X) (a b : X) : Prop := ∃c, leads f a c ∧ leads f b c
theorem leads_converge_def {f : X → X} {a b : X} : leads_converge f a b ↔ ∃c, leads f a c ∧ leads f b c := by rfl

@[symm]
theorem leads_converge_comm {f : X → X} {a b : X} : leads_converge f a b ↔ leads_converge f b a := by
  unfold leads_converge
  simp_rw [and_comm]

@[refl]
theorem leads_converge_refl {f : X → X} {a : X} : leads_converge f a a := by use a
@[trans]
theorem leads_converge_trans {f : X → X} {a b c : X} : leads_converge f a b →  leads_converge f b c →  leads_converge f a c := by
  unfold leads_converge
  intro ⟨ab,a_ab,b_ab⟩ ⟨bc,b_bc,c_bc⟩
  cases leads_connected b_ab b_bc with
  | inl h =>
    use bc
    constructor
    exact leads_trans f a ab bc a_ab h
    exact c_bc
  | inr h =>
    use ab
    constructor
    exact a_ab
    exact leads_trans f c bc ab c_bc h

def leads_converge_equiv (f : X → X) :  @Equivalence X (leads_converge f) where
  refl a := by
    use a
  symm := leads_converge_comm.mp
  trans := leads_converge_trans

-- todo: leads_eventually_, leads_frequently, leads_always etc also hold for all successors.



theorem leads_always_successors {f : X → X} {a b : X} {p} (lab :  leads f a b) (a_ap :  leads_always f a p) : leads_always f b p := by
  revert b
  rw [←leads_always_def']
  simp only [leads_always_idempotent]
  exact a_ap

theorem leads_eventually_successors {f : X → X} {a b : X} {p} (lab : leads f a b) : leads_eventually f a p ↔ leads_eventually f b p := by
  constructor
  intro e_ap
  rw [leads_eventually_def_add] at e_ap ⊢
  obtain ⟨mp,e_ap⟩ := e_ap
  obtain ⟨nb,nb_s⟩ := leads_def.mp lab
  rw [←nb_s]
  simp only [←sequence_leading_tail']
  use mp
  intro n
  have := e_ap (n + nb)
  group at this ⊢
  exact this
  rw [leads_eventually_def'] at ⊢
  intro w
  have := leads_pred_trans _ _ _ _ lab w
  exact leads_eventually_def'.mpr this


theorem leads_frequently_successors {f : X → X} {a b : X} {p} (lab : leads f a b) : leads_frequently f a p ↔ leads_frequently f b p := by
  simp_rw [←leads_eventually_frequently_inverse']
  simp only [leads_eventually_successors lab]


theorem leads_eventually_convergents {f : X → X} {a b : X} {p} (lab : leads_converge f a b) : leads_eventually f a p ↔ leads_eventually f b p := by
  obtain ⟨c,lac,lbc⟩ := leads_converge_def.mp lab
  rw [leads_eventually_successors lbc]
  rw [leads_eventually_successors lac]

theorem leads_frequently_convergents {f : X → X} {a b : X} {p} (lab : leads_converge f a b) : leads_frequently f a p ↔ leads_frequently f b p := by
  simp_rw [←leads_eventually_frequently_inverse']
  simp only [leads_eventually_convergents lab]



abbrev leads_loop (f : X → X) (a: X) : Prop := leads_pos f a a

-- todo: leads_loop turns leads_pred into leads_frequently

def leads_within (f : X → X) (a b : X) (m : ℕ) : Prop := ∃n ≤ m, sequence_leading f a n = b
theorem leads_of_leads_within {f : X → X} {a b : X} {m : ℕ} (h : leads_within f a b m) : leads f a b := by
  reduce at h ⊢
  tauto

def leads_loop_within (f : X → X) (a: X) (m : ℕ) : Prop := ∃n, 0 < n ∧ n ≤ m ∧ sequence_leading f a n = a

theorem leads_loop_of_loop_within {f : X → X} {a : X} {m : ℕ} (h : leads_loop_within f a m) : leads_loop f a := by
  unfold leads_loop_within at h
  tauto

theorem leads_loop_within_of_loop {f : X → X} {a : X} (h : leads_loop f a) : ∃m, leads_loop_within f a m := by
  unfold leads_loop_within
  unfold leads_loop leads_pos at h
  obtain ⟨n,n_pos,w⟩ := h
  use n, n

theorem leads_within_succ_a {f : X → X} {a b : X} {m : ℕ} (h : leads_within f a b m) (d : a ≠ b) : leads_within f (f a) (b) (m - 1) := by
  unfold leads_within at h ⊢
  obtain ⟨n, n_m, lb⟩ := h
  simp only [← sequence_leading_succ']
  have n_pos : n > 0 := by
    by_contra x
    have : n = 0 := by exact Nat.eq_zero_of_not_pos x
    rw [this] at lb
    simp only [sequence_leading_zero] at lb
    exact d lb

  use (n - 1)
  rw [←lb]
  constructor
  bound
  congrm sequence_leading _ _ ?_
  exact Nat.sub_add_cancel n_pos



theorem leads_within_succ_b {f : X → X} {a b : X} {m : ℕ} (h : leads_within f a b m) : leads_within f a (f b) (m + 1) := by
  unfold leads_within at h ⊢
  obtain ⟨n, n_m, lb⟩ := h
  have := congrArg f lb
  simp only [←sequence_leading_succ] at this
  use (n + 1)
  subst lb
  simp_all only [sequence_leading_succ, add_le_add_iff_right, and_self]

theorem leads_loop_eventually {f : X → X} {a b : X} {m : ℕ}
    (lab : leads f a b) (h : leads_loop_within f b m) :
    leads_eventually f a (leads_within f b · m)
     := by
  rw [leads_eventually_def']

  -- simp_rw [←leads_always_leads]
  -- simp_rw [leads_always_def']



  sorry

theorem leads_loop_frequently {f : X → X} {a b : X}
    (lab : leads f a b) (h : leads_loop f b) :
    leads_frequently f a (· = b)
     := by

  sorry


-- todo: leads_frequently from induction.
theorem leads_frequently_induction {X} {f : X → X} (p : X → Prop) (a : X)
    (ha : leads_pred f a p)
    (hx : ∀b, leads f a b → p b → leads_pred_pos f b p)
    : leads_frequently f a p := by
  rw [leads_frequently_def']
  have : leads_always f a (leads f a) := by sorry
  suffices (leads_always f a fun x ↦ leads_pred f x p) ∧ True by tauto
  rw [←eq_true this]
  apply leads_always_and.mpr
  apply leads_preserves' -- todo: this is not enough
  intro x ⟨lxp,lax⟩
  constructor
  rw [leads_pred_def'] at lxp
  obtain ⟨y,py,lxy⟩ := lxp
  have := hx y (leads_trans f a x y lax lxy) py

  -- apply leads_pred_trans (b := y)
  sorry

  sorry

  admit -- exact ha



end lead
