import Mathlib.tactic
import OkkokkoLean.Lead
import OkkokkoLean.AutomatonConfiguration

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

-- todo: use halts in the definition
def StateAutomaton.total : Prop := ∀ t : I, (auto M).halts ((init M) t)

def StateAutomaton.result (h : accepts M tape) : O := get M ((auto M).result ((init M) tape) h)


-- on all inputs, both automata have the same acceptance.
def StateAutomaton.same_accept {O' : Type} (A : StateAutomaton I O) (B : StateAutomaton I O') : Prop := ∀ t : I, accepts A t ↔ accepts B t

def StateAutomaton.same_halt {O' : Type} (A : StateAutomaton I O) (B : StateAutomaton I O') : Prop := ∀ t : I, halts A t ↔ halts B t


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

theorem StateAutomaton.models_function_def (f : I → Option O) : models_function M f ↔
    (models_function_accept M (f · |>.isSome)) ∧  ∀t : I, ∀(c : accepts M t), (f t) = some (result M t c)  := by
  have (t) (c): (match (f t) with | some w => result M t c = w | none => False) ↔ (f t) = some (result M t c) := by
    apply Iff.intro
    · intro a
      split at a
      next x w heq =>
        subst a
        simp_all only
      next x heq => simp_all only
    · intro a
      simp_all only

  simp_rw [←this]
  rfl


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

theorem StateAutomaton.models_function_apply (f : I → Option O) (m : models_function M f) (t : I) (c : accepts M t) :
    -- match (f t) with | some w => result M t c = w | none => False := by
    (f t) = some (result M t c) := by
  rw [models_function_def] at m
  have ⟨tw,tm⟩ := m
  -- unfold models_function_accept at tw
  -- -- simp only at tw
  -- -- have qw:= tw t |>.mp c
  exact tm t c


-- old:
-- does this go one-way? can B halt when A doesn't?
-- if a state in B halts, then each corresponding state's yield also corresponds.
-- given A never halts on any state, yet corresponds to every state in B, then yes.
--
-- wait, same_result does not distinguish between reject and no halt
-- wait, what if all states of A correspond to the starting state of B, and A never halts but B does?
theorem StateAutomaton.simulated_same_result (A B : StateAutomaton I O) (r : A.H → B.H → Prop)
    (hi : ∀i, r (A.init i) (B.init i))
    -- (ho: ∀a b, A.auto.acceptsImmediate a → r a b → (A.get a = B.get b ∧ B.auto.acceptsImmediate b))
    (ho: ∀a b, r a b → A.auto.acceptsImmediate a → (B.auto.accepts_cond b (A.get a = B.get ·)))
    (ha: ∀a b, r a b → A.auto.rejectsImmediate a → B.auto.halt_rejects b)
    (hhx: ∀a b, r a b → B.auto.acceptsImmediate b → A.auto.acceptsImmediate a)
    (hhy: ∀a b, r a b → B.auto.rejectsImmediate b → A.auto.rejectsImmediate a)
    (hs: LeadHom.simulated A.auto B.auto r) : StateAutomaton.same_result A B ∧ StateAutomaton.same_halt A B := by

  rw [same_result_def]
  constructor
  constructor
  ·
    unfold same_accept
    intro t
    unfold accepts
    unfold LeadHom.simulated at hs
    have init_r := hi t
    have hs' := LeadHom.simulated_leads.mp hs
    have tt (a) (l : A.auto.leads' (A.init t) a) := hs' (A.init t) _ a init_r l

    constructor
    ·
      intro ax
      have ⟨ar,ar_acc,ar_l⟩ := ax
      have := tt ar ar_l
      have pp (b rarb) := ho ar b rarb ar_acc
      unfold AutomatonConfiguration.leads_pred' at this
      rw [leads_pred_def'] at this
      have ⟨b, rarb,lb⟩ := this
      specialize pp b rarb
      have qq := B.auto.accepts_cond_accepts pp

      -- accepts transitivity
      rw [AutomatonConfiguration.accepts_def', AutomatonConfiguration.leads_pred'] at qq ⊢
      exact leads_pred_trans B.auto.yield (B.init t) b B.auto.acceptsImmediate lb qq


    intro bx

    have ⟨br,br_acc,br_l⟩ := bx

    have := (hhx · br · br_acc) -- this doesn't necessarily come into effect



    sorry
  ·
    intro t ax bx


    sorry

  sorry

theorem StateAutomaton.simulated2_same_result (A B : StateAutomaton I O) (r : A.H → B.H → Prop)
    (hi : ∀i, r (A.init i) (B.init i))
    -- (ho: ∀a b, A.auto.acceptsImmediate a → r a b → (A.get a = B.get b ∧ B.auto.acceptsImmediate b))
    (ho: ∀a b, r a b → A.auto.acceptsImmediate a → (B.auto.accepts_cond b (A.get a = B.get ·)))
    (ha: ∀a b, r a b → A.auto.rejectsImmediate a → B.auto.halt_rejects b)
    (hhx: ∀a b, r a b → B.auto.acceptsImmediate b → A.auto.acceptsImmediate a)
    (hhy: ∀a b, r a b → B.auto.rejectsImmediate b → A.auto.rejectsImmediate a)
    (hs: LeadHom.simulated2 A.auto B.auto r) : StateAutomaton.same_result A B ∧ StateAutomaton.same_halt A B := by

  rw [same_result_def]
  constructor
  constructor
  ·
    unfold same_accept
    intro t
    unfold accepts
    unfold LeadHom.simulated2 at hs
    have init_r := hi t
    have hs' := LeadHom.simulated2_leads.mp hs
    have tt (a) (l : A.auto.leads_pos (A.init t) a) := hs' (A.init t) _ a init_r l

    constructor
    ·
      intro ax
      #check AutomatonConfiguration.accepts_leads_pos
      have ⟨ar,ar_acc,ar_l⟩ := ax
      have := tt ar ar_l
      have pp (b rarb) := ho ar b rarb ar_acc
      unfold AutomatonConfiguration.leads_pred' at this
      rw [leads_pred_def'] at this
      have ⟨b, rarb,lb⟩ := this
      specialize pp b rarb
      have qq := B.auto.accepts_cond_accepts pp

      -- accepts transitivity
      rw [AutomatonConfiguration.accepts_def', AutomatonConfiguration.leads_pred'] at qq ⊢
      exact leads_pred_trans B.auto.yield (B.init t) b B.auto.acceptsImmediate lb qq


    intro bx

    have ⟨br,br_acc,br_l⟩ := bx

    have := (hhx · br · br_acc) -- this doesn't necessarily come into effect



    sorry
  ·
    intro t ax bx


    sorry

  sorry


end stateAutomaton
