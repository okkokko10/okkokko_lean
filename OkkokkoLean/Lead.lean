import Mathlib.tactic

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


theorem sequence_leading_tail {f : X → X} {a: X} (n : ℕ) {i : ℕ} :
    (sequence_leading f a) (n + i) = sequence_leading f (sequence_leading f a n) i := by
  simp_rw [sequence_leading_def']
  rw [add_comm]
  rw [Function.iterate_add_apply]



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


theorem leads_self (f : X → X) (a: X) : leads f a a := by
  rw [leads_def]
  use 0
  exact sequence_leading_zero



-- is not a PartialOrder

def leadsPreorder (f : X → X) : Preorder X where
  le := leads f
  le_refl := leads_self f
  le_trans := leads_trans f




theorem leads_preserves  {f : X → X} {a b : X} {p : X → Prop} (hp : ∀x, p x → p (f x)) (l : leads f a b) : p a → p b := by
  intro pa
  simp_rw [leads_def,sequence_leading_apply f a] at l
  obtain ⟨n, w⟩ := l
  have := Function.Iterate.rec p hp pa n
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
  have t:= wb ▸ sequence_leading_tail _ ▸ this ▸ wc
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

theorem leads_pred_or {f : X → X} {a : X} {p1 p2 : X → Prop} : (leads_pred f a p1 ∨ leads_pred f a p2) ↔ leads_pred f a (p1 ⊔ p2) := by
  reduce
  aesop

def leads_pred_steps {f : X → X}  {a: X} {p : X → Prop} [DecidablePred p] (l : leads_pred f a p) : ℕ := Nat.find l


-- todo: use this form more.
def leads_in (f : X → X) (a b : X) (n : ℕ) : Prop := sequence_leading f a n = b


-- @[trans]
theorem leads_in_connection (f : X → X) (a b c: X) (ab bc) : leads_in f a b ab → leads_in f b c bc → leads_in f a c (ab + bc) := by
  unfold leads_in
  intro a_b b_c
  rw [←b_c,←a_b]
  exact sequence_leading_tail ab
theorem leads_in_connection' (f : X → X) (a b c: X) (ab bc) : leads_in f a b ab → leads_in f a c (ab + bc) → leads_in f b c bc := by
  unfold leads_in
  intro a_b a_c
  rw [sequence_leading_tail ab,a_b] at a_c
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


end lead
