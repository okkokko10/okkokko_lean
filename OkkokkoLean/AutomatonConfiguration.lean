import Mathlib
import OkkokkoLean.Basic
import OkkokkoLean.Lead
section automatonConfiguration

-- Todo: should I hardcode exclusive_rejects_accepts_immediate?

class AutomatonConfiguration (H : Type) where
  yield' (C : H) : H
  acceptsImmediate' (C : H) : Prop
  rejectsImmediate' (C : H) : Prop
  acceptsImmediate_decidable : DecidablePred acceptsImmediate'
  rejectsImmediate_decidable : DecidablePred rejectsImmediate'
  exclusive_rejects_accepts_immediate (C : H) : rejectsImmediate' C → acceptsImmediate' C → False

-- template
example {H : Type} : AutomatonConfiguration H where
  yield' a := sorry
  acceptsImmediate' a := sorry
  rejectsImmediate' a := sorry
  acceptsImmediate_decidable := sorry
  rejectsImmediate_decidable := sorry
  exclusive_rejects_accepts_immediate a := sorry

variable {H} (ac : AutomatonConfiguration H)

@[reducible]
def AutomatonConfiguration.acceptsImmediate : H → Prop := ac.acceptsImmediate'
@[reducible]
def AutomatonConfiguration.rejectsImmediate : H → Prop := ac.rejectsImmediate'

def AutomatonConfiguration.haltsImmediate (a : H) : Prop :=
  ac.rejectsImmediate a ∨ ac.acceptsImmediate a

-- #check instDecidableOr
-- @[macro_inline]
instance AutomatonConfiguration.haltsImmediate_decidable : @DecidablePred H (ac.haltsImmediate) := by
  unfold haltsImmediate
  intro a
  exact @instDecidableOr _ _ (rejectsImmediate_decidable a) (acceptsImmediate_decidable a)

instance AutomatonConfiguration.acceptsImmediate_decidable' : @DecidablePred H ac.acceptsImmediate := acceptsImmediate_decidable

instance AutomatonConfiguration.rejectsImmediate_decidable' : @DecidablePred H ac.rejectsImmediate := rejectsImmediate_decidable

def AutomatonConfiguration.yield (a : H) : H := if ac.haltsImmediate a then a else ac.yield' a
theorem AutomatonConfiguration.yield_of_haltsImmediate (a : H) (h : ac.haltsImmediate a) : ac.yield a = a := by
  unfold yield
  simp_all only [↓reduceIte]

theorem AutomatonConfiguration.yield_of_not_haltsImmediate (a : H) (h : ¬ ac.haltsImmediate a) : ac.yield a = ac.yield' a:= by
  unfold yield
  simp_all only [↓reduceIte]

-- same as yield_of_haltsImmediate
theorem AutomatonConfiguration.yield_constant (a : H) (h : ac.haltsImmediate a) : ac.yield a = a := by
  unfold yield
  simp [h]

theorem AutomatonConfiguration.rejectsImmediate_yield_rejectsImmediate (C : H) : ac.rejectsImmediate C → ac.rejectsImmediate (ac.yield C) := by
  intro r
  simp only [yield, haltsImmediate, r, true_or, ite_true]

theorem AutomatonConfiguration.acceptsImmediate_yield_acceptsImmediate (C : H) : ac.acceptsImmediate C → ac.acceptsImmediate (ac.yield C) := by
  intro r
  simp only [yield, haltsImmediate, r, or_true, ite_true]


def AutomatonConfiguration.leads' (a : H) (b : H) : Prop :=
    _root_.leads ac.yield a b




def AutomatonConfiguration.halt_rejects (a : H) : Prop :=
  ∃b, ac.rejectsImmediate b ∧ ac.leads' a b

theorem AutomatonConfiguration.halt_rejects_def (a : H) :
    ac.halt_rejects a ↔ ∃b, ac.rejectsImmediate b ∧ ac.leads' a b := by rfl



def AutomatonConfiguration.accepts (a : H) : Prop :=
  ∃b, ac.acceptsImmediate b ∧ ac.leads' a b

def AutomatonConfiguration.halts (a : H) : Prop :=
  ac.accepts a ∨ ac.halt_rejects a

theorem AutomatonConfiguration.halts_def (a : H) : ac.halts a ↔ ∃b, (ac.haltsImmediate b) ∧ ac.leads' a b := by
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

-- note that this can be 0 steps
@[reducible]
def AutomatonConfiguration.leads_pred' (a : H) (p : H → Prop) : Prop :=
    _root_.leads_pred ac.yield a p
theorem AutomatonConfiguration.halt_rejects_def' {a : H} :
    ac.halt_rejects a ↔ ac.leads_pred' a ac.rejectsImmediate := by
  simp only [halt_rejects_def,leads_pred']
  exact Iff.symm leads_pred_def'
theorem AutomatonConfiguration.accepts_def' {a : H} :
    ac.accepts a ↔ ac.leads_pred' a ac.acceptsImmediate := by
  simp only [accepts,leads_pred']
  exact Iff.symm leads_pred_def'
@[simp]
theorem AutomatonConfiguration.halts_def' {a : H} :
    ac.halts a ↔ ac.leads_pred' a ac.haltsImmediate := by
  simp only [halts_def,leads_pred']
  exact Iff.symm leads_pred_def'

theorem AutomatonConfiguration.haltImmediate_of_acceptsImmediate {a : H} (h : ac.acceptsImmediate a) : ac.haltsImmediate a := by tauto
theorem AutomatonConfiguration.haltImmediate_of_rejectsImmediate {a : H} (h : ac.rejectsImmediate a) : ac.haltsImmediate a := by tauto
theorem AutomatonConfiguration.halts_of_accepts {a : H} (h : ac.accepts a) : ac.halts a := by tauto
theorem AutomatonConfiguration.halts_of_rejects {a : H} (h : ac.halt_rejects a) : ac.halts a := by tauto




theorem AutomatonConfiguration.rejectsImmediate_leads_rejectsImmediate {a b : H}
    (hl : ac.leads' a b) (h : ac.rejectsImmediate a) : ac.rejectsImmediate b := by
  exact leads_preserves ac.rejectsImmediate_yield_rejectsImmediate hl h


theorem AutomatonConfiguration.acceptsImmediate_leads_acceptsImmediate {a b : H}
    (hl : ac.leads' a b) (h : ac.acceptsImmediate a) : ac.acceptsImmediate b := by
  refine leads_preserves ac.acceptsImmediate_yield_acceptsImmediate hl h


-- -- if C rejects, so does its predecessor and successor
-- theorem AutomatonConfiguration.rejects_stable (a : H): halt_rejects a ↔ halt_rejects (yield a) := by


--   unfold halt_rejects leads'
--   by_cases h : rejectsImmediate a
--   constructor
--   intro _
--   use (yield a)
--   constructor
--   exact rejectsImmediate_yield_rejectsImmediate a h
--   exact leads_self yield (yield a)
--   sorry
--   unfold leads
--   simp_rw [←sequence_leading_succ']
--   -- simp only [sequence_leading_succ]
--   refine ⟨fun ⟨b,r_b,n,se⟩ ↦ ⟨b,r_b,n - 1,?_⟩,fun rig ↦ ?_⟩



--   sorry
--   sorry


theorem AutomatonConfiguration.exclusive_rejects_accepts (a : H) :
    ac.halt_rejects a → ac.accepts a → False := by
  unfold halt_rejects accepts leads'
  intro ⟨rej,r_q,leads_r⟩
  intro ⟨acc,a_q,leads_a⟩
  have t0 := leads_connected leads_a leads_r
  cases' t0 with t1 t2
  have := ac.acceptsImmediate_leads_acceptsImmediate t1 a_q
  exact ac.exclusive_rejects_accepts_immediate rej r_q this
  have := ac.rejectsImmediate_leads_rejectsImmediate t2 r_q
  exact ac.exclusive_rejects_accepts_immediate acc this a_q


def AutomatonConfiguration.leads_nth (a : H) (n : ℕ) : H :=
    _root_.sequence_leading ac.yield a n

@[simp]
theorem AutomatonConfiguration.leads_nth_def {a : H} {n : ℕ} : _root_.sequence_leading ac.yield a n = ac.leads_nth a n := rfl

@[simp]
theorem AutomatonConfiguration.leads_nth_leads {a : H} {n : ℕ} : ac.leads' a (ac.leads_nth a n) := by
  unfold leads' leads
  simp only [leads_nth_def, exists_apply_eq_apply]


def AutomatonConfiguration.haltsIn (a : H) (h : ac.halts a) : ℕ := Nat.find (ac.halts_def'.mp h)
theorem AutomatonConfiguration.haltsIn_min (a : H) (h : ac.halts a) (m) : m < ac.haltsIn a h → ¬ ac.haltsImmediate (ac.leads_nth a m) := by
  intro mh
  exact Nat.find_min (ac.halts_def'.mp h) mh



def AutomatonConfiguration.result (a : H) (h : ac.accepts a) : H := ac.leads_nth a (ac.haltsIn a (ac.halts_of_accepts h))


theorem AutomatonConfiguration.accepts_never_rejectsImmediate (a : H) (h : ac.accepts a) (b : H) : ac.leads' a b → ac.rejectsImmediate b → False := by
  intro a_b hb
  have := (ac.halt_rejects_def a).mpr ⟨b,hb,a_b⟩
  exact ac.exclusive_rejects_accepts a this h

theorem AutomatonConfiguration.rejects_never_acceptsImmediate (a : H) (h : ac.halt_rejects a) (b : H) : ac.leads' a b → ac.acceptsImmediate b → False := by
  intro a_b hb
  have  : ac.accepts a := ⟨b,hb,a_b⟩
  exact ac.exclusive_rejects_accepts a h this

-- todo: same for rejects
theorem AutomatonConfiguration.accepts_then_haltsImmediate_accepts (a : H) (h : ac.accepts a) (b : H) (l : ac.leads' a b) : ac.haltsImmediate b ↔ ac.acceptsImmediate b := by
  refine ⟨?_,ac.haltImmediate_of_acceptsImmediate⟩
  intro hb
  by_contra hb'
  have hb'': ac.rejectsImmediate b := by
    cases hb
    assumption
    exfalso
    tauto
  -- have  : halt_rejects a := ⟨b,hb'',a_b⟩
  exact ac.accepts_never_rejectsImmediate a h b l hb''


def AutomatonConfiguration.acceptsIn (a : H) (h : ac.accepts a) : ℕ := Nat.find (ac.accepts_def'.mp h)
theorem AutomatonConfiguration.acceptsIn_def (a : H) (h : ac.accepts a) : ac.acceptsIn a h = Nat.find (ac.accepts_def'.mp h) := by rfl
-- @[simp]
theorem AutomatonConfiguration.acceptsIn_eq_haltsIn (a : H) (h : ac.accepts a) : ac.acceptsIn a h = ac.haltsIn a (ac.halts_of_accepts h) := by
  unfold acceptsIn
  refine nat_le_ext ?_
  intro i
  unfold haltsIn
  rw [@Nat.find_le_iff]
  rw [@Nat.find_le_iff]
  suffices ∀m, ac.haltsImmediate (sequence_leading ac.yield a m) ↔ ac.acceptsImmediate (sequence_leading ac.yield a m) by simp_rw [this]
  intro m
  rw [ac.accepts_then_haltsImmediate_accepts a h _ _]
  use m -- todo: make a proper theorem


theorem AutomatonConfiguration.result_def (a : H) (h : ac.accepts a) : ac.result a h = ac.leads_nth a (ac.acceptsIn a h) := by
  simp only [acceptsIn_eq_haltsIn]
  rfl

theorem AutomatonConfiguration.result_accepts (a : H) (h : ac.accepts a)  : ac.acceptsImmediate (ac.result a h) := by
  rw [result_def]
  exact Nat.find_spec (ac.accepts_def'.mp h)



theorem AutomatonConfiguration.haltsImmediate_leads_nth_self
    (a : H) (h : ac.haltsImmediate a) (n: ℕ) : (ac.leads_nth a n) = a := by
  apply sequence_leading_identity (ac.yield_of_haltsImmediate a h)


-- if a leads to a acceptsImmediate state, that state is the result.
theorem AutomatonConfiguration.result_of_acceptsImmediate (a b : H) (l : ac.leads' a b) (h : ac.acceptsImmediate b) : b = (ac.result a ⟨b, h,l⟩) := by
  have aa: ac.accepts a := ⟨b, h, l⟩
  change ∃n, ac.leads_nth a n = b at l
  obtain ⟨n,l⟩ := l
  have : ac.acceptsIn a aa ≤ n := by
    unfold acceptsIn
    rw [@Nat.find_le_iff]
    simp only [leads_nth_def]
    use n
    simp only [le_refl, true_and]
    rw [l]
    exact h

  have := leads_connected ⟨n,l⟩ ⟨ac.acceptsIn a aa, (by simp only [leads_nth_def, ← result_def]; rfl)⟩
  set c :=(ac.result a aa)
  cases this
  rename_i ht
  change ∃n, ac.leads_nth b n = c at ht
  simp only [ac.haltsImmediate_leads_nth_self b (ac.haltImmediate_of_acceptsImmediate h),
    exists_const] at ht
  exact ht
  rename_i ht
  change ∃n, ac.leads_nth c n = b at ht
  simp only [ac.haltsImmediate_leads_nth_self c (ac.haltImmediate_of_acceptsImmediate (ac.result_accepts a aa)),
    exists_const] at ht
  exact ht.symm

theorem AutomatonConfiguration.leads_nth_halts (a : H) (h : ac.halts a) (n: ℕ) : ac.halts (ac.leads_nth a n) := by
  simp only [halts_def']
  rw [show ac.leads_pred' (ac.leads_nth a n) ac.haltsImmediate =
    ∃ n_1, ac.haltsImmediate (sequence_leading ac.yield (ac.leads_nth a n) n_1) from rfl]
  simp only [halts_def'] at h
  rw [show ac.leads_pred' a ac.haltsImmediate = ∃ n, ac.haltsImmediate (sequence_leading ac.yield a n) from rfl] at h
  obtain ⟨n',w⟩ := h
  by_cases pw : n ≤ n'
  · simp only [←leads_nth_def]
    simp only [←sequence_leading_tail]
    -- simp only [leads_nth_def]

    use (n' - n)
    have : (n + (n' - n)) = n' := by omega
    rw [this]
    exact w
  use 0
  simp only [sequence_leading_zero]
  have ⟨m,mw⟩ : ∃m, n = n' + m := by
    use (n - n')
    omega
  rw [mw]
  simp only [←leads_nth_def]
  simp only [sequence_leading_tail]
  set pp := (sequence_leading ac.yield a n')
  simp only [leads_nth_def]
  sorry




theorem AutomatonConfiguration.haltsIn_assoc (a : H) (h : ac.halts a) (n m : ℕ) : ac.haltsIn a h = n + m ↔ ac.haltsIn (ac.leads_nth a n) (ac.leads_nth_halts a h n) = m  := by

  sorry

def LeadHom.hom_yields {A B : Type} (ac : AutomatonConfiguration A) (bc : AutomatonConfiguration B) (f : A → B) (a : A) : Prop :=
    f (ac.yield a) = bc.yield (f a)
def LeadHom.hom_yields_cond {A B : Type} (ac : AutomatonConfiguration A) (bc : AutomatonConfiguration B) (f : A → B) (p : A → Prop) : Prop :=
    ∀ a, p a → f (ac.yield a) = bc.yield (f a)

--
def LeadHom.hom_leads {A B : Type} (ac : AutomatonConfiguration A) (bc : AutomatonConfiguration B) (f : A → B) (a : A) : Prop :=
    bc.leads' (f a) (f (ac.yield a))

def LeadHom.hom_leads_cond {A B : Type} (ac : AutomatonConfiguration A) (bc : AutomatonConfiguration B) (f : A → B) (p : A → Prop) : Prop :=
    ∀ a, p a → bc.leads' (f a) (f (ac.yield a))

-- if a and b have a relation r a b, then successors of a (a') that satisfy p are related by g to a successor of b
def LeadHom.hom {A B : Type} (ac : AutomatonConfiguration A) (bc : AutomatonConfiguration B) (r : A → B → Prop) (p : A → Prop) (g : A → B → Prop) :=
    ∀a b, r a b → ∀ a', ac.leads' a a' → p a' → bc.leads_pred' b (g a')

theorem LeadHom.hom_def' {A B : Type} (ac : AutomatonConfiguration A) (bc : AutomatonConfiguration B) (r : A → B → Prop) (p : A → Prop) (g : A → B → Prop) :
    LeadHom.hom ac bc r p g ↔ ∀a b, r a b → ∀ a', ac.leads' a a' → p a' → ∃b', (g a' b') ∧ bc.leads' b b' := by
  unfold hom
  rw [show bc.leads_pred' = leads_pred bc.yield from rfl]
  simp_rw [leads_pred_def']
  rfl

-- same as hom, but p and g can use a and b
def LeadHom.hom_vary {A B : Type} (ac : AutomatonConfiguration A) (bc : AutomatonConfiguration B) (r : A → B → Prop) (p : A → B → A → Prop) (g : A → B → A → B → Prop) :=
    ∀a b, r a b → ∀ a', ac.leads' a a' → p a b a' → bc.leads_pred' b (g a b a')


def Instant.simple (f : H → Option H) : AutomatonConfiguration H where
  yield' a := sorry
  acceptsImmediate' a := sorry
  rejectsImmediate' a := sorry
  acceptsImmediate_decidable := sorry
  rejectsImmediate_decidable := sorry
  exclusive_rejects_accepts_immediate a := sorry

-- bc simulates ac, such that each valid state of ac corresponds to a state in bc that leads to the yield in finite steps.
-- r a b : a corresponds to b
def LeadHom.simulated {A B : Type}
    (ac : AutomatonConfiguration A) (bc : AutomatonConfiguration B)
    (r : A → B → Prop) : Prop :=
    ∀a b, r a b → bc.leads_pred' b (r (ac.yield a))

-- this state accepts, and the final state satisfies p
def AutomatonConfiguration.accepts_cond {H : Type} (ac : AutomatonConfiguration H) (a : H) (p : H → Prop) : Prop :=
    ac.leads_pred' a (fun x ↦ ac.acceptsImmediate x ∧ p x)

theorem AutomatonConfiguration.accepts_cond_accepts {H : Type} {ac : AutomatonConfiguration H} {a : H} {p : H → Prop} :
    ac.accepts_cond a p → ac.accepts a := by
  unfold accepts_cond accepts leads_pred' leads_pred
  tauto

theorem LeadHom.simulated_leads {A B : Type}
    {ac : AutomatonConfiguration A} {bc : AutomatonConfiguration B}
    {r : A → B → Prop}
    --(a b) (hx: r a b) : ∀a', ac.leads' a a' → ∃b', bc.leads' b b' ∧ r a' b'
    : simulated ac bc r ↔ ∀a b a', r a b → ac.leads' a a' → bc.leads_pred' b (r a')
      := by
    -- might be ↔
    constructor
    ·
      intro hs
      intro a b a' rab la'
      unfold AutomatonConfiguration.leads' at la'
      have := leads_preserves (p := fun x ↦ bc.leads_pred' b (r x)) ?_ la'
      · simp only at this
        apply this
        unfold AutomatonConfiguration.leads_pred' leads_pred
        use 0
        simp only [sequence_leading_zero]
        exact rab
      simp only
      intro x lbx
      unfold AutomatonConfiguration.leads_pred'
      have ⟨q, rxq, lbq⟩: ∃y, r x y ∧ bc.leads' b y := by
        have ⟨n,rxn⟩ := lbx
        refine ⟨_, rxn, ?_⟩
        simp_all only [AutomatonConfiguration.leads_nth_def, AutomatonConfiguration.leads_nth_leads]
      apply leads_pred_trans _ _ q _ lbq
      exact hs _ _ rxq
    intro w
    have (a b) := w a b (ac.yield a)
    unfold AutomatonConfiguration.leads' at this
    simp only [leads_next, forall_const] at this
    exact this

-- if b
-- theorem LeadHom.simulated_leads_reverse {A B : Type}
--     {ac : AutomatonConfiguration A} {bc : AutomatonConfiguration B}
--     {r : A → B → Prop}
--     --(a b) (hx: r a b) : ∀a', ac.leads' a a' → ∃b', bc.leads' b b' ∧ r a' b'
--     : simulated ac bc r → ∀a b a', r a b → ac.leads' a a' → bc.leads_pred' b (r a')
--       := by

@[reducible]
def AutomatonConfiguration.leads_pred_pos (a : H) (p : H → Prop) : Prop :=
    _root_.leads_pred_pos ac.yield a p
@[reducible]
def AutomatonConfiguration.leads_pos (a b: H) : Prop :=
    _root_.leads_pos ac.yield a b

def LeadHom.simulated2 {A B : Type}
    (ac : AutomatonConfiguration A) (bc : AutomatonConfiguration B)
    (r : A → B → Prop) : Prop :=
    ∀a b, r a b → bc.leads_pred_pos b (r (ac.yield a))

theorem LeadHom.simulated2_leads {A B : Type}
    {ac : AutomatonConfiguration A} {bc : AutomatonConfiguration B}
    {r : A → B → Prop}
    --(a b) (hx: r a b) : ∀a', ac.leads' a a' → ∃b', bc.leads' b b' ∧ r a' b'
    : simulated2 ac bc r ↔ ∀a b a', r a b → ac.leads_pos a a' → bc.leads_pred_pos b (r a')
      := by
    -- might be ↔
    constructor
    ·
      intro hs
      intro a b a' rab la'
      unfold AutomatonConfiguration.leads_pos at la'
      rw [leads_pos_def'] at la'

      have := leads_preserves (p := fun x ↦ bc.leads_pred_pos b (r x)) ?_ la'
      · simp only at this
        exact this (hs a b rab)

      simp only
      intro x lbx

      -- unfold AutomatonConfiguration.leads_pred'
      have ⟨q, rxq, lbq⟩: ∃y, r x y ∧ bc.leads_pos b y := by
        have ⟨n,n0,rxn⟩ := lbx
        refine ⟨_, rxn, ?_⟩
        unfold AutomatonConfiguration.leads_pos
        rw [leads_pos_def]
        use n
      unfold AutomatonConfiguration.leads_pred_pos
      rw [leads_pred_pos_def']
      unfold AutomatonConfiguration.leads_pos at lbq
      rw [leads_pos_def'] at lbq

      apply leads_pred_trans _ _ q _ lbq
      exact leads_pred_of_leads_pred_pos (hs x q rxq)
    intro w

    have (a b) := w a b (ac.yield a)
    unfold AutomatonConfiguration.leads_pos at this
    simp_rw [leads_pos_def'] at this
    simp only [leads_self, forall_const] at this
    exact this



-- same for reject and halt
theorem AutomatonConfiguration.accepts_leads_pos {H} {ac : AutomatonConfiguration H} {a : H} :
    ac.accepts a ↔ ac.leads_pred_pos a ac.acceptsImmediate := by

  by_cases h : ac.acceptsImmediate a
  -- todo: acceptsImmediate_accepts
  have true1: ac.accepts a := by
    refine ⟨a,h,?_⟩
    rw [leads']
    exact leads_self ac.yield a
  simp only [true1, true_iff]


  unfold leads_pred_pos
  rw [leads_pred_pos_def']
  refine ⟨0,?_⟩
  simp only [sequence_leading_zero]
  exact acceptsImmediate_yield_acceptsImmediate ac a h

  simp [accepts_def']
  unfold leads_pred'
  exact leads_pred_pos_if_not_zero h




end automatonConfiguration
