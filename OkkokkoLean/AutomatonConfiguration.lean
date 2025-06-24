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

@[simp]
theorem AutomatonConfiguration.leads_nth_def {a : H} {n : ℕ} : _root_.sequence_leading yield a n = leads_nth a n := rfl

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
