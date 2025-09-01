import Mathlib
import OkkokkoLean.Basic
import OkkokkoLean.Lead
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

variable {H} (ac : AutomatonConfiguration H)

def AutomatonConfiguration.haltsImmediate (a : H) : Prop :=
  ac.rejectsImmediate a ∨ ac.acceptsImmediate a

-- #check instDecidableOr
-- @[macro_inline]
instance AutomatonConfiguration.haltsImmediate_decidable : @DecidablePred H (ac.haltsImmediate) := by
  unfold haltsImmediate
  intro a
  exact @instDecidableOr _ _ (rejectsImmediate_decidable a) (acceptsImmediate_decidable a)

instance AutomatonConfiguration.acceptsImmediate_decidable' : @DecidablePred H acceptsImmediate := acceptsImmediate_decidable

instance AutomatonConfiguration.rejectsImmediate_decidable' : @DecidablePred H rejectsImmediate := rejectsImmediate_decidable

def AutomatonConfiguration.yield (a : H) : H := if ac.haltsImmediate a then a else yield' a

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

theorem AutomatonConfiguration.haltImmediate_of_acceptsImmediate {a : H} (h : acceptsImmediate a) : ac.haltsImmediate a := by tauto
theorem AutomatonConfiguration.haltImmediate_of_rejectsImmediate {a : H} (h : rejectsImmediate a) : ac.haltsImmediate a := by tauto
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
  have hb'': rejectsImmediate b := by
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

end automatonConfiguration
