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
