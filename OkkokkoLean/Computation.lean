import Mathlib.tactic


section ComputationOkko


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




-- actually, is ha needed?


end lead



variable {Q G : Type}  --[DecidableEq G]

-- maybe have both in singleton types
inductive LeftRightChar
| leftChar
| rightChar


def leftChar {A : Type} := Sum.inr (α := A) LeftRightChar.leftChar
def rightChar {A : Type} := Sum.inr (α := A) LeftRightChar.rightChar

-- def TuringMachine.δ_state (M : @TuringMachine state_ alphabet_) (q : M.Q) (a : M.G) := (M.δ q a).1
-- def TuringMachine.δ_alpha (M : @TuringMachine state_ alphabet_) (q : M.Q) (a : M.G) := (M.δ q a).2.1
-- def TuringMachine.δ_direction (M : @TuringMachine state_ alphabet_) (q : M.Q) (a : M.G) := (M.δ q a).2.2

-- instance (M : @TuringMachine Q G _) : Zero M.G := M.Gz


-- TODO: replace ℤ in tape with an arbitrary type. this way it can be generalized to n-tape automata.

-- TODO: Actually the tape rightChar has a purpose in telling the automaton that the finite input has ended.

-- @[ext]
theorem nat_le_ext {a b : ℕ} : (∀i : ℕ, a ≤ i ↔ b ≤ i) → a = b := by
  intro h
  have t1:= h a
  have t2:= h b
  simp only [le_refl, iff_true, true_iff] at t2 t1
  exact Nat.le_antisymm t2 t1




section automatonConfiguration

-- Todo: should I hardcode exclusive_rejects_accepts_immediate?

class AutomatonConfiguration (H : Type) where
  yield' (C : H) : H
  acceptsImmediate (C : H) : Prop
  rejectsImmediate (C : H) : Prop
  acceptsImmediate_decidable : DecidablePred acceptsImmediate
  rejectsImmediate_decidable : DecidablePred rejectsImmediate
  exclusive_rejects_accepts_immediate (C : H) : rejectsImmediate C → acceptsImmediate C → False

-- template
example {H : Type} : AutomatonConfiguration H where
  yield' a := sorry
  acceptsImmediate a := sorry
  rejectsImmediate a := sorry
  acceptsImmediate_decidable := sorry
  rejectsImmediate_decidable := sorry
  exclusive_rejects_accepts_immediate a := sorry

variable {H} [AutomatonConfiguration H]

def AutomatonConfiguration.haltsImmediate (a : H) : Prop :=
  rejectsImmediate a ∨ acceptsImmediate a

-- #check instDecidableOr
-- @[macro_inline]
instance AutomatonConfiguration.haltsImmediate_decidable : @DecidablePred H (haltsImmediate) := by
  unfold haltsImmediate
  intro a
  exact @instDecidableOr _ _ (rejectsImmediate_decidable a) (acceptsImmediate_decidable a)

instance AutomatonConfiguration.acceptsImmediate_decidable' : @DecidablePred H acceptsImmediate := acceptsImmediate_decidable

instance AutomatonConfiguration.rejectsImmediate_decidable' : @DecidablePred H rejectsImmediate := rejectsImmediate_decidable

def AutomatonConfiguration.yield (a : H) : H := if haltsImmediate a then a else yield' a

theorem AutomatonConfiguration.rejectsImmediate_yield_rejectsImmediate (C : H) : rejectsImmediate C → rejectsImmediate (yield C) := by
  intro r
  simp only [yield, haltsImmediate, r, true_or, ite_true]

theorem AutomatonConfiguration.acceptsImmediate_yield_acceptsImmediate (C : H) : acceptsImmediate C → acceptsImmediate (yield C) := by
  intro r
  simp only [yield, haltsImmediate, r, or_true, ite_true]


def AutomatonConfiguration.leads' (a : H) (b : H) : Prop :=
    _root_.leads yield a b




def AutomatonConfiguration.halt_rejects (a : H) : Prop :=
  ∃b, rejectsImmediate b ∧ leads' a b

theorem AutomatonConfiguration.halt_rejects_def (a : H) :
    AutomatonConfiguration.halt_rejects a ↔ ∃b, rejectsImmediate b ∧ leads' a b := by rfl



def AutomatonConfiguration.accepts (a : H) : Prop :=
  ∃b, acceptsImmediate b ∧ leads' a b

def AutomatonConfiguration.halts (a : H) : Prop :=
  accepts a ∨ halt_rejects a

theorem AutomatonConfiguration.halts_def (a : H) : halts a ↔ ∃b, (haltsImmediate b) ∧ leads' a b := by
  unfold haltsImmediate halts accepts halt_rejects
  -- constructor
  -- · intro l
  --   cases' l with l l
  --   obtain ⟨b,w,lea⟩ := l
  --   use b
  --   tauto
  --   obtain ⟨b,w,lea⟩ := l
  --   use b
  --   tauto
  -- · intro ⟨b,imm,lea⟩
  --   cases' imm with _ _
  --   right
  --   use b
  --   left
  --   use b
  aesop


def AutomatonConfiguration.leads_pred' (a : H) (p : H → Prop) : Prop :=
    _root_.leads_pred yield a p
theorem AutomatonConfiguration.halt_rejects_def' {a : H} :
    halt_rejects a ↔ leads_pred' a rejectsImmediate := by
  simp only [halt_rejects_def,leads_pred']
  exact Iff.symm leads_pred_def'
theorem AutomatonConfiguration.accepts_def' {a : H} :
    accepts a ↔ leads_pred' a acceptsImmediate := by
  simp only [accepts,leads_pred']
  exact Iff.symm leads_pred_def'
@[simp]
theorem AutomatonConfiguration.halts_def' {a : H} :
    halts a ↔ leads_pred' a haltsImmediate := by
  simp only [halts_def,leads_pred']
  exact Iff.symm leads_pred_def'

theorem AutomatonConfiguration.haltImmediate_of_acceptsImmediate {a : H} (h : acceptsImmediate a) : haltsImmediate a := by tauto
theorem AutomatonConfiguration.haltImmediate_of_rejectsImmediate {a : H} (h : rejectsImmediate a) : haltsImmediate a := by tauto
theorem AutomatonConfiguration.halts_of_accepts {a : H} (h : accepts a) : halts a := by tauto
theorem AutomatonConfiguration.halts_of_rejects {a : H} (h : halt_rejects a) : halts a := by tauto




theorem AutomatonConfiguration.rejectsImmediate_leads_rejectsImmediate {a b : H}
    (hl : leads' a b) (h : rejectsImmediate a) : rejectsImmediate b := by
  exact leads_preserves rejectsImmediate_yield_rejectsImmediate hl h


theorem AutomatonConfiguration.acceptsImmediate_leads_acceptsImmediate {a b : H}
    (hl : leads' a b) (h : acceptsImmediate a) : acceptsImmediate b := by
  refine leads_preserves acceptsImmediate_yield_acceptsImmediate hl h


-- if C rejects, so does its predecessor and successor
theorem AutomatonConfiguration.rejects_stable (a : H): halt_rejects a ↔ halt_rejects (yield a) := by


  unfold halt_rejects leads'
  by_cases h : rejectsImmediate a
  constructor
  intro _
  use (yield a)
  constructor
  exact rejectsImmediate_yield_rejectsImmediate a h
  exact leads_self yield (yield a)
  sorry
  unfold leads
  simp_rw [←sequence_leading_succ']
  -- simp only [sequence_leading_succ]
  refine ⟨fun ⟨b,r_b,n,se⟩ ↦ ⟨b,r_b,n - 1,?_⟩,fun rig ↦ ?_⟩



  sorry
  sorry


theorem AutomatonConfiguration.exclusive_rejects_accepts (a : H) :
    halt_rejects a → accepts a → False := by
  unfold halt_rejects accepts leads'
  intro ⟨rej,r_q,leads_r⟩
  intro ⟨acc,a_q,leads_a⟩
  have t0 := leads_connected leads_a leads_r
  cases' t0 with t1 t2
  have := acceptsImmediate_leads_acceptsImmediate t1 a_q
  exact exclusive_rejects_accepts_immediate rej r_q this
  have := rejectsImmediate_leads_rejectsImmediate t2 r_q
  exact exclusive_rejects_accepts_immediate acc this a_q


def AutomatonConfiguration.leads_nth (a : H) (n : ℕ) : H :=
    _root_.sequence_leading yield a n

def AutomatonConfiguration.haltsIn (a : H) (h : halts a) : ℕ := Nat.find (halts_def'.mp h)
theorem AutomatonConfiguration.haltsIn_min (a : H) (h : halts a) (m) : m < haltsIn a h → ¬ haltsImmediate (leads_nth a m) := by
  intro mh
  exact Nat.find_min (halts_def'.mp h) mh



def AutomatonConfiguration.result (a : H) (h : accepts a) : H := leads_nth a (haltsIn a (halts_of_accepts h))


theorem AutomatonConfiguration.accepts_never_rejectsImmediate (a : H) (h : accepts a) (b : H) : leads' a b → rejectsImmediate b → False := by
  intro a_b hb
  have := (halt_rejects_def a).mpr ⟨b,hb,a_b⟩
  exact exclusive_rejects_accepts a this h

theorem AutomatonConfiguration.rejects_never_acceptsImmediate (a : H) (h : halt_rejects a) (b : H) : leads' a b → acceptsImmediate b → False := by
  intro a_b hb
  have  : accepts a := ⟨b,hb,a_b⟩
  exact exclusive_rejects_accepts a h this

-- todo: same for rejects
theorem AutomatonConfiguration.accepts_then_haltsImmediate_accepts (a : H) (h : accepts a) (b : H) (l : leads' a b) : haltsImmediate b ↔ acceptsImmediate b := by
  refine ⟨?_,haltImmediate_of_acceptsImmediate⟩
  intro hb
  by_contra hb'
  have hb'': rejectsImmediate b := by
    cases hb
    assumption
    exfalso
    tauto
  -- have  : halt_rejects a := ⟨b,hb'',a_b⟩
  exact accepts_never_rejectsImmediate a h b l hb''


def AutomatonConfiguration.acceptsIn (a : H) (h : accepts a) : ℕ := Nat.find (accepts_def'.mp h)
theorem AutomatonConfiguration.acceptsIn_def (a : H) (h : accepts a) : acceptsIn a h = Nat.find (accepts_def'.mp h) := by rfl
-- @[simp]
theorem AutomatonConfiguration.acceptsIn_eq_haltsIn (a : H) (h : accepts a) : acceptsIn a h = haltsIn a (halts_of_accepts h) := by
  unfold acceptsIn
  refine nat_le_ext ?_
  intro i
  unfold haltsIn
  rw [@Nat.find_le_iff]
  rw [@Nat.find_le_iff]
  suffices ∀m, haltsImmediate (sequence_leading yield a m) ↔ acceptsImmediate (sequence_leading yield a m) by simp_rw [this]
  intro m
  rw [accepts_then_haltsImmediate_accepts a h _ _]
  use m -- todo: make a proper theorem


theorem AutomatonConfiguration.result_def (a : H) (h : accepts a) : result a h = leads_nth a (acceptsIn a h) := by
  simp only [acceptsIn_eq_haltsIn]
  rfl

theorem AutomatonConfiguration.result_accepts (a : H) (h : accepts a)  : acceptsImmediate (result a h) := by
  rw [result_def]
  exact Nat.find_spec (accepts_def'.mp h)

end automatonConfiguration


section stateAutomaton

-- automaton with an input/output tape and an internal state

structure StateAutomaton (I : Type) (O : Type)
  where
  H : Type
  auto : AutomatonConfiguration H
  init (t : I) : H
  get (a : H) : O

variable {I O : Type} (M : StateAutomaton I O) (tape : I)

def StateAutomaton.accepts : Prop := (auto M).accepts ((init M) tape)
def StateAutomaton.halt_rejects : Prop := (auto M).halt_rejects ((init M) tape)

def StateAutomaton.halts : Prop := (auto M).halts ((init M) tape)

def StateAutomaton.total : Prop := ∀ t : I, (auto M).halts ((init M) t)

def StateAutomaton.result (h : accepts M tape) : O := get M ((auto M).result ((init M) tape) h)


-- on all inputs, both automata have the same acceptance.
def StateAutomaton.same_accept {O' : Type} (A : StateAutomaton I O) (B : StateAutomaton I O') : Prop := ∀ t : I, accepts A t ↔ accepts B t


-- def StateAutomaton.same_result (A B : StateAutomaton I O) (h : same_accept A B) : Prop := ∀ t : I, result A t = (fun (c : accepts A t) ↦ result B t ((h t).mp c))
-- the acceptance and results are the same
def StateAutomaton.same_result (A B : StateAutomaton I O): Prop := ∃(h : same_accept A B), ∀ t : I, ∀(c : accepts A t), result A t c = result B t ((h t).mp c)
theorem StateAutomaton.same_result_def (A B : StateAutomaton I O) : same_result A B ↔
    same_accept A B ∧ ∀ (t : I) (ac : accepts A t) (bc : accepts B t), result A t ac = result B t bc := by
  unfold same_result
  aesop



def StateAutomaton.models_function_accept (f : I → Prop) : Prop := ∀t : I, accepts M t ↔ (f t)
def StateAutomaton.models_function (f : I → Option O) : Prop :=
    (models_function_accept M (f · |>.isSome)) ∧  ∀t : I, ∀(c : accepts M t), match (f t) with | some w => result M t c = w | none => False

-- #check Equivalence
-- #check RelEmbedding
-- #check Function.Embedding
instance StateAutomaton.same_accept_equiv : @Equivalence (StateAutomaton I O) same_accept where
  refl M := by
    unfold same_accept
    intro t
    rfl
  symm := by
    unfold same_accept
    -- aesop
    intro A B h t
    symm
    apply h
  trans := by
    unfold same_accept
    intro x y z xy yz t
    rw [xy,yz]

-- theorem StateAutomaton.same_accept_equiv' (A B : StateAutomaton I O) : same_accept A B ↔ StateAutomaton.same_accept_equiv A B := by rfl

def StateAutomaton.same_result_equiv : @Equivalence (StateAutomaton I O) same_result where
  refl M := by
    unfold same_result
    simp only [implies_true, exists_prop, and_true]
    apply same_accept_equiv.refl
  symm := by
    simp_rw [same_result_def]
    intro x y ⟨xy_a,xy_eq⟩
    refine ⟨same_accept_equiv.symm xy_a,?_⟩
    intro t yc xc
    exact xy_eq t xc yc |>.symm
  trans := by
    simp_rw [same_result_def]
    intro x y z ⟨xy_a,xy_eq⟩ ⟨yz_a,yz_eq⟩
    refine ⟨same_accept_equiv.trans xy_a yz_a,?_⟩
    intro t xc zc
    have yc:= (xy_a t).mp xc
    rw [xy_eq t xc yc]
    exact yz_eq t yc zc

-- todo: a relation for models_function



def StateAutomaton.conversion : O := get M <| init M tape

section utilities

def StateAutomaton.comp_auto  {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) :
    AutomatonConfiguration (A.H ⊕ B.H) where
  yield' a := Sum.elim (
    fun a ↦if (auto A).acceptsImmediate a then .inr (init B (get A a)) else .inl ((auto A).yield a)
    ) (fun b ↦ .inr ((auto B).yield b)) a
  acceptsImmediate := Sum.elim (fun _ ↦ false) ((auto B).acceptsImmediate)
  rejectsImmediate := Sum.elim ((auto A).rejectsImmediate) ((auto B).rejectsImmediate)
  acceptsImmediate_decidable := by
    intro a
    cases a with
    | inl a =>
      simp only [Sum.elim_inl]
      simp only [Bool.false_eq_true]
      exact instDecidableFalse
    | inr b =>
      simp only [Sum.elim_inr]
      exact (auto B).acceptsImmediate_decidable' b
  rejectsImmediate_decidable := by
    intro a
    cases h : a with
    | inl a =>
      simp only [Sum.elim_inl]
      exact (auto A).rejectsImmediate_decidable' a
    | inr b =>
      simp only [Sum.elim_inr]
      exact (auto B).rejectsImmediate_decidable' b

  exclusive_rejects_accepts_immediate := by
    simp only [imp_false, Sum.forall, Sum.elim_inl, not_false_eq_true, implies_true, Sum.elim_inr,
      true_and]
    simp only [Bool.false_eq_true, not_false_eq_true, implies_true, true_and]
    exact (auto B).exclusive_rejects_accepts_immediate

theorem StateAutomaton.comp_auto_not_accept_A {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) :
  ¬(comp_auto A B).acceptsImmediate (.inl a) := by
  intro h
  unfold comp_auto at h
  simp only [Sum.elim_inl] at h
  simp_all only [Bool.false_eq_true]


theorem StateAutomaton.comp_auto_halts_A {X : Type} {A : StateAutomaton I X} {B : StateAutomaton X O} {a : A.H} :
  (comp_auto A B).haltsImmediate (.inl a) ↔ (auto A).rejectsImmediate a := by
  unfold AutomatonConfiguration.haltsImmediate
  unfold comp_auto
  simp only [Sum.elim_inl, or_false]
  simp_all only [Bool.false_eq_true, or_false]

theorem StateAutomaton.comp_auto_ee {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h) (n' : ℕ)
    (nv : n' ≤ ((auto A).acceptsIn a h)):
    (comp_auto A B).leads_nth (.inl a) n' = .inl ((auto A).leads_nth (a) n') := by
  rw [(auto A).acceptsIn_eq_haltsIn] at nv
  set n := ((auto A).haltsIn a ((auto A).halts_of_accepts h))
  unfold AutomatonConfiguration.leads_nth
  revert nv
  induction n' with
  | zero =>
    simp only [Nat.zero_eq, zero_le, sequence_leading_zero, forall_true_left]
  | succ n' prev =>
    intro s
    have s': n' < n := s
    simp only [sequence_leading_succ]
    specialize prev s'.le
    simp only [prev]
    -- unfold AutomatonConfiguration.yield
    simp_rw [AutomatonConfiguration.yield]
    set w := (sequence_leading (auto A).yield a n') with w_def

    have not_haltIm := (auto A).haltsIn_min a ((auto A).halts_of_accepts h) n' s'
    unfold AutomatonConfiguration.leads_nth at not_haltIm
    rw [←w_def] at not_haltIm
    split
    {
    rename_i hh
    have := (auto A).haltImmediate_of_rejectsImmediate (comp_auto_halts_A.mp hh)
    simp_all only [n, w]
    }
    -- aesop
    rename_i hh
    rw [comp_auto_halts_A] at hh
    unfold comp_auto
    simp only [Sum.elim_inl]




    split
    {
      rename_i hhh
      simp only [reduceCtorEq, n, w]
      exact not_haltIm ((auto A).haltImmediate_of_acceptsImmediate hhh)
    }
    apply congrArg
    unfold AutomatonConfiguration.yield
    rename_i h_1
    simp_all only [ite_false]


theorem StateAutomaton.comp_auto_e {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h):
    (comp_auto A B).leads_nth (.inl a) ((auto A).acceptsIn a h) = .inl ((auto A).result a h) := by
  rw [(auto A).result_def]
  apply comp_auto_ee
  rfl


theorem StateAutomaton.comp_auto_b_leads_b {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (b : B.H) :
    Sum.isRight ((comp_auto A B).yield (.inr b)) := by
  unfold AutomatonConfiguration.yield
  split
  · simp only [Sum.isRight_inr]
  rfl

theorem StateAutomaton.comp_auto_result_b {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (x : A.H ⊕ B.H) (h) :
    Sum.isRight ((comp_auto A B).result x h) := by
  set b := (comp_auto A B).result _ _
  have hb : (comp_auto A B).acceptsImmediate b := (comp_auto A B).result_accepts _ _
  simp only [comp_auto, Sum.elim_inl, eq_mpr_eq_cast, Sum.elim_inr, cast_eq, id_eq] at hb
  by_contra lft
  simp only [ne_eq, Bool.not_eq_true, Sum.isRight_eq_false,Sum.isLeft_iff] at lft
  obtain ⟨y,y_re⟩ := lft
  rw [y_re] at hb
  simp only [Sum.elim_inl] at hb
  simp_all only [Bool.false_eq_true]


#check leads_partition_while

-- example
theorem StateAutomaton.comp_auto_split {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h : (comp_auto A B).accepts (.inl a)) :
    ∃z<((comp_auto A B).acceptsIn (Sum.inl a) h), leads_partition_while (comp_auto A B).yield (Sum.inl a) ((comp_auto A B).result (.inl a) h) (Sum.isRight ·) z (((comp_auto A B).acceptsIn (Sum.inl a) h) - z - 1)
     := by

  set b := (comp_auto A B).result (.inl a) h with b_def
  rw [(comp_auto A B).result_def] at b_def
  set n := ((comp_auto A B).acceptsIn (Sum.inl a) _)

  let p (v : A.H ⊕ B.H) : Prop := Sum.isRight v
  let f := (comp_auto A B).yield
  let l : leads_in f (.inl a) b n := by
    exact b_def.symm
  -- (comp_auto A B).leads_nth (.inl a)
  -- have : (comp_auto A B).leads_nth
  have hp : ∀ (x : A.H ⊕ B.H), p x → p (f x) := by
    simp only [Sum.forall, Sum.isRight_inl, Bool.false_eq_true, IsEmpty.forall_iff, implies_true,
      Sum.isRight_inr, forall_const, true_and, p]
    intro b'
    exact comp_auto_b_leads_b A B b'
  have ha : ¬p (Sum.inl a) := by exact Sum.not_isRight.mpr rfl
  have hb : p b := by
    exact comp_auto_result_b A B (Sum.inl a) h


  have := leads_partition_while_mk f p l hp ha hb
  tauto




theorem StateAutomaton.comp_auto_ew {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h)
    (n' : ℕ) (nv : n' > ((auto A).haltsIn a ((auto A).halts_of_accepts h))) :
    (comp_auto A B).leads_nth (.inl a) ((auto A).haltsIn a ((auto A).halts_of_accepts h) + n')
    = .inr ((auto B).leads_nth (init B <| get A <| (auto A).result a h) n') := by
  -- possibly off by one.



  sorry


-- todo: attempt some rule where an automaton simulating another contains steps corresponding to steps in the simulated automaton, and each simulated step finishes in finite time.

def StateAutomaton.comp {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) : StateAutomaton I O where
  H := A.H ⊕ B.H
  auto := comp_auto A B
  init (t) := .inl (A.init t)
  get (a) := Sum.elim (get B <| init B <| get A ·) (get B ·) a -- if get is called on a state before A halts, `get A` is fed into `conversion B`

-- theorem StateAutomaton.comp.get_ready {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) :


theorem StateAutomaton.comp.accepts_A {X : Type} {A : StateAutomaton I X} {B : StateAutomaton X O} {t : I} : accepts (comp A B) t →  accepts A t := by
  sorry

theorem StateAutomaton.comp.spec {X : Type} {A : StateAutomaton I X} {B : StateAutomaton X O} {fa : I → Option X} {fb : X → Option O}
  (ma : models_function A fa) (mb : models_function B fb) :
  models_function (comp A B) (fun t ↦ Option.bind (fa t) fb) := by
    unfold models_function
    simp only

    have acc : models_function_accept (comp A B) fun x ↦ Option.isSome (Option.bind (fa x) fb) = true := sorry

    refine ⟨acc,?_⟩
    intro t c
    have a_accept := comp.accepts_A c
    match h : Option.bind (fa t) fb with
      | some w =>
        simp only
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨x,atx, bxw⟩ := h
        have a_v := ma.right t a_accept
        simp [atx] at a_v


        unfold result
        have a_halt := ((auto A).halts_of_accepts a_accept)

        have a_lead:= comp_auto_e A B (init A t) a_accept
        set a_n := (auto A).haltsIn (init A t) a_halt

        unfold comp
        simp only

        -- unfold AutomatonConfiguration.result
        set e := @AutomatonConfiguration.result _ (auto (comp A B)) (Sum.inl (init A t)) c
        cases hh : e with
        | inl v =>
          simp only [Sum.elim_inl]
          -- I think it's exfalso unless B halts immediately
          -- simp only at hh

          sorry
        | inr y =>
        unfold Sum.elim

        simp only


        sorry
      | none =>
        simp only
        simp only [models_function_accept] at acc
        have := acc t |>.mp c
        rw [h,Option.isSome_none] at this
        tauto


-- todo:

-- And:  A.I × B.I → A.O × B.O
-- Or (parallel):  A.I × B.I → A.O ⊕ B.O
-- Map : A.I ⊕ B.I → A.O ⊕ B.O




end utilities


end stateAutomaton



section tape

structure Tape (G : Type) where
  toFun : ℕ → Sum G LeftRightChar
  start : toFun 0 = leftChar
  non_start : (∀ i, i = 0 ↔ toFun i = leftChar) -- replace start with this altogether
  trail : ∃n, (∀ i, n ≤ i ↔ toFun i = rightChar)

instance {G : Type} : CoeFun (Tape G) (fun _ ↦ ℕ → Sum G LeftRightChar) where
  coe w := w.toFun




theorem Tape.trail_specific (t : Tape G) : ∃!n, (∀ i, n ≤ i ↔ t i = rightChar) := by
  have ⟨n,n_spec⟩ := t.trail
  use n
  constructor
  simp
  exact fun i ↦ n_spec i
  simp
  intro y y_spec
  have tt(i) : y ≤ i ↔ n ≤ i := by rw [y_spec i,n_spec i]
  exact nat_le_ext tt

noncomputable def Tape.edge (t : Tape G) := t.trail_specific.choose

theorem Tape.edge_spec (t : Tape G) : ∀i, t.edge ≤ i ↔ t i = rightChar := t.trail_specific.choose_spec.1

theorem Tape.edge_pos (t : Tape G) : 0 < t.edge := by
  -- if it was 0, t.start would be contradicted.
  refine Nat.pos_of_ne_zero ?_
  intro w
  have := t.edge_spec 0 |>.mp w.le
  rw [t.start] at this
  unfold leftChar rightChar at this
  simp [Sum.inr.injEq] at this


def tapeAlpha (a : G) := Sum.inl (β := LeftRightChar) a

@[simp]
theorem tapeAlpha_not_char {a : G} : ¬ tapeAlpha a = rightChar := by
    unfold tapeAlpha rightChar
    simp

@[simp]
theorem tapeAlpha_not_char' {a : G} : ¬ tapeAlpha a = leftChar := by
    unfold tapeAlpha leftChar
    simp


def Tape.update (t : Tape G) (i : ℕ) (h : i ≠ 0) (hn : i ≤ t.edge) (a : G) : Tape G where
  -- toFun := Function.update t.toFun i (tapeAlpha a)
  toFun := fun n ↦ if n = i then tapeAlpha a else t.toFun n
  start := by
    -- unfold Function.update
    simp only [h.symm, ite_false]
    exact t.start
  non_start := sorry
  trail := by
    -- have ⟨n, n_spec, n_unique⟩ := t.trail_specific
    let n := t.edge
    have n_spec := t.edge_spec

    by_cases hw : i < n
    {
    use n
    intro ii
    refine ⟨?_,?_⟩
    intro nii
    have : ¬ii = i := by linarith only [nii, hw]
    simp only [this, ite_false]
    exact (n_spec ii).mp nii
    intro w
    split at w
    {
    exfalso
    exact tapeAlpha_not_char w
    }
    exact (n_spec ii).mpr w
    }
    -- have : i ≤ n := by linarith  -- TODO: this must be required
    have e: i = n := by linarith only [hw, hn]
    use n + 1
    intro ii
    split
    {
      simp only [tapeAlpha_not_char, iff_false, not_le]
      linarith
    }
    by_cases hhh : n + 1 ≤ ii
    simp only [hhh, true_iff]
    rw [← (n_spec ii)]
    linarith
    simp only [hhh, false_iff]
    rw [← (n_spec ii)]
    simp only [not_le]
    simp only [not_le] at hhh
    rename_i hx
    rw [e] at hx
    have : ii ≤ n := by linarith
    exact Nat.lt_of_le_of_ne this hx

-- theorem Tape.update_apply {t : Tape G} {a : G} (i : ℕ) (h : i ≠ 0) (hn : i ≤ t.edge) (j : ℕ) : if j = i then (t.update i h (hn) a) j = a else

theorem Tape.unupdated_edge {t : Tape G} {a : G} (i : ℕ) (h : i ≠ 0) (hn : i < t.edge) : (t.update i h (hn.le) a).edge = t.edge := by
  set f :=  (t.update i h (hn.le) a)
  have (j) : f j = rightChar ↔ t j = rightChar := by
    change (if j = i then tapeAlpha a else toFun t j) = _ ↔ _
    split
    · simp only [tapeAlpha_not_char, false_iff]
      intro q
      rw [←t.edge_spec j] at q
      linarith
    rfl
  simp only [edge, this]

theorem Tape.updated_edge {t : Tape G} {a : G} : (t.update t.edge (t.edge_pos.ne') (Nat.le_refl _) a).edge = t.edge + 1 := by
  -- unfold update
  set f := (t.update t.edge (t.edge_pos.ne') (Nat.le_refl _) a)
  -- #check
  apply nat_le_ext
  intro i
  rw [f.edge_spec i]
  change (if i = edge t then tapeAlpha a else toFun t i) = _ ↔ _
  split
  · simp only [tapeAlpha_not_char, false_iff]
    linarith
  rw [←t.edge_spec i]
  rename_i h
  constructor
  intro w
  exact Ne.lt_of_le' h w
  intro w
  exact Nat.le_of_lt w


-- def Tape.updateRight {G : Type} (t : Tape G) {i : ℕ} (h : 0 < i) (a : G) : Tape G where
--   toFun := fun n ↦ if n = i then tapeAlpha a else t.toFun n
--   start := by
--     simp only [h.ne, ite_false]
--     exact t.start

end tape


-- a looser ruleset
structure TuringMachine (Q : Type) (G : Type)
  where
  -- δ : Q → G → Q × G × Bool
  -- Q := state_ -- states
  -- G := alphabet_ -- tape alphabet plus leftChar and rightChar
  -- Gz: Zero G := by infer_instance
  δ : Q → G → Q × G × Bool -- transition
  -- δ : state_ → alphabet_ → state_ × alphabet_ × Bool -- transition
  qAcc : Q -- accept state
  qRej : Q -- reject state
  q0 : Q -- start state
  acc_neq_rej : qAcc ≠ qRej
  δ_state (q : Q) (a : G) := (δ q a).1
  δ_alpha (q : Q) (a : G) := (δ q a).2.1
  δ_direction (q : Q) (a : G) := (δ q a).2.2
  -- rej_loop (a) : δ_state qRej a = qRej
  -- acc_loop (a) : δ_state qAcc a = qAcc

  δ_left : Q → Q -- the case when a = leftChar
  δ_right : Q → Q -- the case when a = rightChar
  δ_right_alpha : Q → (Option (G × Bool)) -- the case when a = rightChar. `none` travels left automatically
  -- δ_left_rej_loop : δ_left qRej = qRej -- the case when a = leftChar




def TuringMachine.δ_complete (M : TuringMachine Q G) (q : Q) (a : Sum G LeftRightChar) : Q × (Sum G LeftRightChar) × Bool := by
  -- by_cases C.q = M.qAcc ∨ C.q = M.qRej
  -- · exact C
  cases a with
  | inl a =>
    have x := (M.δ q a)
    exact ⟨x.1,Sum.inl a,x.2.2⟩
  | inr rlc =>
    exact match rlc with
    | LeftRightChar.leftChar =>
      ⟨(M.δ_left q),leftChar,true⟩
    | LeftRightChar.rightChar =>
      ⟨(M.δ_right q),
        match M.δ_right_alpha q with
          | some (a, b) => ⟨Sum.inl a,b⟩
          | none => ⟨rightChar,false⟩
        ⟩

-- def TuringMachine_mk' {Q G : Type} (δ_complete : Q → (Sum G LeftRightChar) → Q × (Sum G LeftRightChar) × Bool) (qAcc qRej q0: Q) := 0



variable {M : TuringMachine Q G}

section turingConfiguration

structure TuringConfiguration (M : TuringMachine Q G) where
  q : Q
  -- tape : ℕ → M.G
  -- tape : Finsupp ℕ M.G M.Gz
  tape : Tape G
  index : ℕ
  -- u : List M.G

  -- v : List M.G
  index_bounded : index ≤ tape.edge


def TuringConfiguration.a (C : TuringConfiguration M)  : Sum G LeftRightChar := C.tape C.index

def TuringConfiguration.at_left (C : TuringConfiguration M) : Prop := C.a = leftChar
def TuringConfiguration.at_right (C : TuringConfiguration M) : Prop := C.a = rightChar

theorem TuringConfiguration.at_left_0 {C : TuringConfiguration M} : C.at_left ↔ C.index = 0 := sorry
theorem TuringConfiguration.at_right_edge {C : TuringConfiguration M} : C.at_right ↔ C.index = C.tape.edge := sorry


def TuringConfiguration.yield_base (M : TuringMachine Q G) (tape : Tape G) (index : ℕ) (h : index ≠ 0) (hn : index < tape.edge) (q : Q) (a : G) : TuringConfiguration M where
  q := M.δ_state q a
  tape := Tape.update tape index h hn.le (M.δ_alpha q a)
  index := if TuringMachine.δ_direction M q a = true then index + 1 else index - 1
  index_bounded := by
    rw [Tape.unupdated_edge index h hn]
    refine le_trans ?_ (hn : index + 1 ≤ tape.edge)
    split
    rfl
    simp only [tsub_le_iff_right]
    linarith


-- deprecated
-- def TuringConfiguration.yield2 (C : TuringConfiguration M) : TuringConfiguration M where
--   q := by
--     cases C.a with
--     | inl a =>   exact M.δ_state C.q a
--     | inr rlc => exact M.δ_left C.q
--   -- M.δ_state C.q C.a
--   tape := by
--     cases C.a with
--     | inl a =>   exact Tape.update C.tape (i := C.index) sorry (M.δ_alpha C.q a)
--     | inr rlc => exact C.tape
--   -- tape := C.tape.update C.index (M.δ_alpha C.q C.a)
--   index := by
--     cases C.a with
--     | inl a => exact if (M.δ_direction C.q a) then C.index + 1 else C.index - 1
--     | inr rlc =>
--       match rlc with
--       | LeftRightChar.leftChar => exact C.index + 1
--       | LeftRightChar.rightChar => exact C.index - 1
--   -- if (M.δ_direction C.q C.a) then C.index + 1 else C.index - 1

def TuringConfiguration.yield_left (C : TuringConfiguration M) (h : C.at_left) : TuringConfiguration M where
  q := M.δ_left C.q
  tape := C.tape
  index := C.index + 1
  index_bounded := by
    have t1:= at_left_0.mp h
    have t2:= C.tape.edge_pos
    exact Eq.trans_le (congrFun (congrArg HAdd.hAdd t1) 1) t2
    -- linarith only [at_left_0.mp h,C.tape.edge_pos]

def TuringConfiguration.yield_right (C : TuringConfiguration M) (h : C.at_right)  : TuringConfiguration M where
  q := M.δ_right C.q
  tape :=
    -- have atEdge := at_right_edge.mp h
    match M.δ_right_alpha C.q with
    | some ⟨a,_⟩  => Tape.update C.tape C.index (by rw [at_right_edge.mp h]; exact (Tape.edge_pos _).ne') (at_right_edge.mp h).le a
    | none => C.tape
  index := match M.δ_right_alpha C.q with
    | some (a, true) => C.index + 1
    | _ => C.index - 1
    -- | none => exact C.index - 1
    -- | some ⟨a,d⟩  => exact C.index - 1
  --if Option.any (fun ⟨a,d⟩ ↦ d) (M.δ_right_alpha C.q) then C.index + 1 else C.index - 1
  index_bounded := by
    have atEdge := at_right_edge.mp h
    simp only [atEdge] -- for some reason `rw` fails: "motive is not type correct"
    match M.δ_right_alpha C.q with
    | some (a, true) =>
      simp only
      rw [Tape.updated_edge]
    | some (a, false) =>
      --C.index - 1
      simp only [tsub_le_iff_right, ge_iff_le]
      rw [C.tape.updated_edge]
      linarith only
    | none => simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]




-- def TuringConfiguration.yield1 (C : TuringConfiguration M) : TuringConfiguration M :=
--   if C.q = M.qAcc ∨ C.q = M.qRej then C
--   else
--   Sum.casesOn (motive := fun t ↦ C.a = t → TuringConfiguration M) C.a
--     (fun a _ ↦ yield_base M C.tape C.index C.q a)
--     (fun rlc _ ↦
--       match rlc with
--       | LeftRightChar.leftChar => yield_left C
--       | LeftRightChar.rightChar => yield_right C)
--     (by rfl)

def TuringConfiguration.yield (C : TuringConfiguration M) : TuringConfiguration M := by
  cases h : C.a with
  | inl a =>
    exact TuringConfiguration.yield_base M C.tape C.index
      (by
      unfold TuringConfiguration.a at h
      intro c0
      rw [c0] at h
      rw [Tape.start] at h
      apply tapeAlpha_not_char'
      rw [h]
      rfl) (by
      unfold TuringConfiguration.a at h
      rw [←not_le]
      intro c0
      apply tapeAlpha_not_char
      simp only [Tape.edge_spec] at c0
      rw [←c0,h]
      rfl) C.q a
  | inr rlc =>
    match rlc with
    | LeftRightChar.leftChar => exact C.yield_left h
    | LeftRightChar.rightChar => exact C.yield_right h


def TuringConfiguration.acceptsImmediate (a : TuringConfiguration M) : Prop :=
  a.q = M.qAcc

def TuringConfiguration.rejectsImmediate (a : TuringConfiguration M) : Prop :=
  a.q = M.qRej



-- theorem TuringConfiguration.rejectsImmediate_yield_rejectsImmediate (a : TuringConfiguration M)
--     (h : a.rejectsImmediate) : a.yield.rejectsImmediate := by
--   unfold rejectsImmediate yield
--   rw [h]
--   simp only [or_true, dite_eq_ite, ite_true]
--   rw [h]

-- theorem TuringConfiguration.acceptsImmediate_yield_acceptsImmediate (a : TuringConfiguration M)
--     (h : a.acceptsImmediate) : a.yield.acceptsImmediate := by
--   unfold acceptsImmediate yield
--   rw [h]
--   simp only [true_or, dite_eq_ite, ite_true]
--   rw [h]

theorem TuringConfiguration.exclusive_rejects_accepts_immediate {a : TuringConfiguration M} :
    a.acceptsImmediate → a.rejectsImmediate → False := by
  intro aa ar
  -- unfold rejectsImmediate at ar
  -- unfold acceptsImmediate at aa
  exact M.acc_neq_rej (aa ▸ ar)


instance : AutomatonConfiguration (TuringConfiguration M) where
  yield' (C) := TuringConfiguration.yield C
  acceptsImmediate (C) := TuringConfiguration.acceptsImmediate C
  rejectsImmediate (C) := TuringConfiguration.rejectsImmediate C
  acceptsImmediate_decidable := sorry -- TODO: bring back DecidableEq Q
  rejectsImmediate_decidable := sorry
  -- rejectsImmediate_yield_rejectsImmediate (C) (h) := TuringConfiguration.rejectsImmediate_yield_rejectsImmediate C h
  -- acceptsImmediate_yield_acceptsImmediate (C) (h) := TuringConfiguration.acceptsImmediate_yield_acceptsImmediate C h
  exclusive_rejects_accepts_immediate (_) (hr) (ha) := TuringConfiguration.exclusive_rejects_accepts_immediate ha hr

end turingConfiguration





def TuringMachine.use (tape : Tape G) : TuringConfiguration M where
  q := M.q0
  tape := tape
  index := 0
  index_bounded := Nat.zero_le _
def TuringMachine.accepts (tape : Tape G) : Prop := AutomatonConfiguration.accepts (M.use tape)
def TuringMachine.halt_rejects (tape : Tape G) : Prop := AutomatonConfiguration.halt_rejects (M.use tape)

def TuringMachine.total : Prop := ∀ tape : Tape G, AutomatonConfiguration.halts (M.use tape)


-- on all inputs, both turing machines have the same output.
def TuringMachine.same {Q1 Q2 : Type} {G : Type} --[DecidableEq Q1] [DecidableEq Q2] [DecidableEq G]
    (A : TuringMachine Q1 G) (B : TuringMachine Q2 G) := ∀ tape : Tape G, AutomatonConfiguration.accepts (A.use tape) ↔ AutomatonConfiguration.accepts (B.use tape)


theorem TuringConfiguration.output_theorem (C : TuringConfiguration M) (h : AutomatonConfiguration.halts C) : ∃ b,
  (AutomatonConfiguration.rejectsImmediate b ∨ AutomatonConfiguration.acceptsImmediate b) ∧ AutomatonConfiguration.leads' C b := ((AutomatonConfiguration.halts_def C).mp h)

noncomputable def TuringConfiguration.output (C : TuringConfiguration M) (h : AutomatonConfiguration.halts C) := (C.output_theorem h).choose
theorem TuringConfiguration.output_halts (C : TuringConfiguration M) (h : AutomatonConfiguration.halts C) :AutomatonConfiguration.haltsImmediate (C.output h) := (C.output_theorem h).choose_spec.left
theorem TuringConfiguration.output_leads (C : TuringConfiguration M) (h : AutomatonConfiguration.halts C) : AutomatonConfiguration.leads' C (C.output h) := (C.output_theorem h).choose_spec.right

noncomputable def TuringMachine.output (tape : Tape G) := (M.use tape).output
-- #check Option
noncomputable def TuringMachine.total_output (h_total : M.total) (tape : Tape G) := (M.use tape).output (h_total tape)


def Comp (Q1 Q2 : Type) : Type := Sum Q1 Q2

noncomputable def comp_switch {Q1 Q2 : Type} {G : Type} --[DecidableEq G]
    (A : TuringMachine Q1 G) (B : TuringMachine Q2 G) (x : Q1) : Sum Q1 Q2 := by
  by_cases x = A.qAcc
  · exact Sum.inr B.q0
  by_cases x = A.qRej
  · exact Sum.inr B.qRej
  exact Sum.inl x

-- when A accepts, its finishing state is fed into B
noncomputable def TuringMachine.comp {Q1 Q2 : Type} {G : Type} --[DecidableEq G]
    (A : TuringMachine Q1 G) (B : TuringMachine Q2 G) : TuringMachine (Comp Q1 Q2) G where
  δ (q a) := by
    cases q with
    | inl l =>
      have ⟨x,y⟩ := (A.δ l a)
      exact ⟨comp_switch A B x,y⟩
    | inr r =>
      have ⟨x,y⟩ := (B.δ r a)
      exact ⟨Sum.inr x,y⟩
  qAcc := Sum.inr B.qAcc
  qRej := Sum.inr B.qRej
  q0 := Sum.inl A.q0
  acc_neq_rej := by
    intro w
    apply B.acc_neq_rej
    exact Sum.inr_injective w
  δ_left (q) := by
    cases q with
    | inl l =>
      have x := (A.δ_left l)
      exact comp_switch A B x
    | inr r =>
      have x := (B.δ_left r)
      exact Sum.inr x
  δ_right (q) := by -- this could be generalized with δ_left and δ
    cases q with
    | inl l =>
      have x := (A.δ_right l)
      exact comp_switch A B x
    | inr r =>
      have x := (B.δ_right r)
      exact Sum.inr x
  δ_right_alpha (q) := Sum.elim (A.δ_right_alpha) B.δ_right_alpha q


theorem comp_total {Q1 Q2 : Type} {G : Type}
    (A : TuringMachine Q1 G) (B : TuringMachine Q2 G) (hA : A.total) (hB : B.total) : (A.comp B).total := by sorry

-- def TuringMachine.binary {n : ℕ} (repr : G → Fin n) (h: Function.Bijective repr) :=

section decidability

def TuringMachine.language (M : TuringMachine Q G) := {l | M.accepts l}

def decidableLanguage (L : Set (Tape G)) : Prop := ∃(Q : Type), Finite Q ∧ ∃(m : TuringMachine Q G), m.language = L ∧ m.total

theorem decidable_union (a b : Set (Tape G)) (ha : decidableLanguage a) (hb : decidableLanguage b) : decidableLanguage (a ∪ b) := by
  sorry
theorem decidable_complement (a : Set (Tape G)) (ha : decidableLanguage a)  : decidableLanguage aᶜ := by
  sorry
theorem decidable_inter (a b : Set (Tape G)) (ha : decidableLanguage a) (hb : decidableLanguage b) : decidableLanguage (a ∩ b) := by
  sorry

def semi_decidableLanguage (L : Set (Tape G)) : Prop := ∃(Q : Type), Finite Q ∧ ∃(m : TuringMachine Q G), m.language = L

theorem semi_decidable_of_decidable (a : Set (Tape G)) (ha : decidableLanguage a) : semi_decidableLanguage a := by
  unfold semi_decidableLanguage
  unfold decidableLanguage at ha
  tauto
-- theorem
theorem semi_decidable_union (a b : Set (Tape G)) (ha : semi_decidableLanguage a) (hb : semi_decidableLanguage b) : semi_decidableLanguage (a ∪ b) := by
  sorry

theorem semi_decidable_inter (a b : Set (Tape G)) (ha : semi_decidableLanguage a) (hb : semi_decidableLanguage b) : semi_decidableLanguage (a ∩ b) := by
  sorry

theorem decidable_iff_semi_decidable_self_and_complement (a : Set (Tape G)) : decidableLanguage a ↔ (semi_decidableLanguage a ∧ semi_decidableLanguage aᶜ) := by
  sorry
-- def UniversalTuringMachine : TuringMachine Q G where

end decidability


end ComputationOkko
