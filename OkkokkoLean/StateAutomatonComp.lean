import Mathlib.tactic
import OkkokkoLean.Lead
import OkkokkoLean.AutomatonConfiguration
import OkkokkoLean.StateAutomaton


variable {I O : Type} (M : StateAutomaton I O) (tape : I)

section utilities

def StateAutomaton.conversion : O := get M <| init M tape

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

lemma StateAutomaton.comp_auto_acceptsImmediate_def {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a) :
  (comp_auto A B).acceptsImmediate a ↔ ∃b, (auto B).acceptsImmediate b ∧ (.inr b) = a := by
  rw [show (comp_auto A B).acceptsImmediate a =
    Sum.elim (fun x ↦ false = true) (auto B).acceptsImmediate a from rfl]
  simp only [Bool.false_eq_true]
  cases a with
  | inl val => simp_all only [Sum.elim_inl, reduceCtorEq, and_false, exists_false]
  | inr val_1 => simp_all only [Sum.elim_inr, Sum.inr.injEq, exists_eq_right]



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

-- given that `a` does not halt before `n'` steps, A and comp A B coincide in `n'` steps
theorem StateAutomaton.comp_auto_coincide_A {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h) (n' : ℕ)
    (nv : n' ≤ ((auto A).haltsIn a h)):
    (comp_auto A B).leads_nth (.inl a) n'
    = .inl ((auto A).leads_nth (a) n') := by
  have h' := h -- ((auto A).halts_of_accepts h)
  -- rw [(auto A).acceptsIn_eq_haltsIn] at nv
  set n := ((auto A).haltsIn a h')
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

    have not_haltIm := (auto A).haltsIn_min a h' n' s'
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

-- given that A accepts `a`, A and comp A B coincide at the step that it accepts it at
theorem StateAutomaton.comp_auto_e {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h):
    (comp_auto A B).leads_nth (.inl a) ((auto A).acceptsIn a h) = .inl ((auto A).result a h) := by
  rw [(auto A).result_def]
  rw [(auto A).acceptsIn_eq_haltsIn]
  apply comp_auto_coincide_A (h:= ((auto A).halts_of_accepts h))
  rfl

-- a B state leads to a B state
theorem StateAutomaton.comp_auto_b_leads_b' {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (b : B.H) :
    Sum.isRight ((comp_auto A B).yield (.inr b)) := by
  unfold AutomatonConfiguration.yield
  split
  · simp only [Sum.isRight_inr]
  rfl

-- a B state leads to the next B state
theorem StateAutomaton.comp_auto_b_leads_b {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (b : B.H) :
    (comp_auto A B).yield (.inr b) = .inr ((auto B).yield b) := by
  unfold AutomatonConfiguration.yield
  split
  · simp only [Sum.inr.injEq, left_eq_ite_iff]
    tauto
  rfl

-- the result of comp A B is a B state
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
theorem StateAutomaton.comp_auto_split {X : Type} (A : StateAutomaton I X)
    (B : StateAutomaton X O) (a : A.H) (h : (comp_auto A B).accepts (.inl a)) :
    ∃z<((comp_auto A B).acceptsIn (Sum.inl a) h),
      leads_partition_while (comp_auto A B).yield
      (Sum.inl a) ((comp_auto A B).result (.inl a) h) (Sum.isRight ·)
      z (((comp_auto A B).acceptsIn (Sum.inl a) h) - z - 1)
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
    have := comp_auto_b_leads_b A B b'
    simp_all only [Sum.isRight_inr, p, f]
  have ha : ¬p (Sum.inl a) := by exact Sum.not_isRight.mpr rfl
  have hb : p b := by
    exact comp_auto_result_b A B (Sum.inl a) h


  have := leads_partition_while_mk f p l hp ha hb
  tauto


open AutomatonConfiguration

theorem StateAutomaton.comp_auto_coincide_B {X : Type} (A : StateAutomaton I X)
    (B : StateAutomaton X O) (b : B.H) (n' : ℕ)
    --(nv : n' ≤ ((auto A).haltsIn a h))
    :
    (comp_auto A B).leads_nth (.inr b) n' = .inr ((auto B).leads_nth (b) n') := by
  induction n' with
  | zero =>
    rfl
  | succ n prev =>
    unfold leads_nth
    simp only [sequence_leading_succ, leads_nth_def]
    rw [prev]
    set u := (auto B).leads_nth b n
    exact comp_auto_b_leads_b A B u

lemma StateAutomaton.comp_auto_A_acc_no_halt {X : Type} (A : StateAutomaton I X)
    (B : StateAutomaton X O) (a : A.H) (h) :
    ¬(comp_auto A B).haltsImmediate (Sum.inl ((auto A).result a h)) := by
  rw [comp_auto_halts_A]
  intro w
  have := (auto A).result_accepts a h
  exact  (auto A).exclusive_rejects_accepts_immediate _ w this

theorem StateAutomaton.comp_auto_A_acc_yields_B {X : Type} (A : StateAutomaton I X)
    (B : StateAutomaton X O) (a : A.H) (h) :
    (comp_auto A B).yield (Sum.inl ((auto A).result a h))
    = .inr (init B (get A ((auto A).result a h))) := by
  rw [show (comp_auto A B).yield (Sum.inl ((auto A).result a h)) =
    if (comp_auto A B).haltsImmediate (Sum.inl ((auto A).result a h)) then
      Sum.inl ((auto A).result a h)
    else (comp_auto A B).yield' (Sum.inl ((auto A).result a h)) from rfl]
  simp only [comp_auto_A_acc_no_halt, ↓reduceIte]
  rw [show (comp_auto A B).yield' (Sum.inl ((auto A).result a h)) =
    if (auto A).acceptsImmediate ((auto A).result a h) then
      Sum.inr (B.init (A.get ((auto A).result a h)))
    else Sum.inl ((auto A).yield ((auto A).result a h)) from rfl]
  simp only [ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not]
  exact (auto A).result_accepts a h




theorem StateAutomaton.comp_auto_coincide_after_A' {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h)
    (n' : ℕ) :
    (comp_auto A B).leads_nth (.inl a) (((auto A).acceptsIn a h) + 1 + n')
    = .inr ((auto B).leads_nth (init B <| get A <| (auto A).result a h) n') := by
  -- possibly off by one.
  -- simp only [leads_nth_def]
  unfold leads_nth

  simp only [sequence_leading_tail, leads_nth_def]
  rw [comp_auto_e]
  simp only [← leads_nth_def, sequence_leading_succ, sequence_leading_zero]
  simp [leads_nth_def]

  simp only [comp_auto_A_acc_yields_B A B a h]
  apply comp_auto_coincide_B

-- #check StateAutomaton.comp_auto_coincide_A

theorem StateAutomaton.comp_auto_coincide_after_A {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h)
    (n : ℕ) (nv : n > (auto A).acceptsIn a h) :
    (comp_auto A B).leads_nth (.inl a) n
    = .inr ((auto B).leads_nth (init B <| get A <| (auto A).result a h) (n - ((auto A).acceptsIn a h) - 1)) := by
  have := comp_auto_coincide_after_A' A B a h (n - ((auto A).acceptsIn a h) - 1)
  rw [←this]
  apply congrArg
  omega

theorem StateAutomaton.comp_auto_coincide {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h)
    (n : ℕ)  :
    (comp_auto A B).leads_nth (.inl a) n =
    if (n ≤ (auto A).acceptsIn a h) then
    .inl ((auto A).leads_nth (a) n)
    else
    .inr ((auto B).leads_nth (init B <| get A <| (auto A).result a h) (n - ((auto A).acceptsIn a h) - 1))
    := by
  split
  · refine comp_auto_coincide_A A B a ?_ n ?_
    exact (auto A).halts_of_accepts h
    rw [←(auto A).acceptsIn_eq_haltsIn]
    assumption
  refine comp_auto_coincide_after_A A B a h n ?_
  simp_all only [not_le, gt_iff_lt]



theorem StateAutomaton.comp_auto_coincide_result {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h) (hb)
     :
    (comp_auto A B).leads_nth (.inl a)
    (((auto A).acceptsIn a h) + 1 + ((auto B).acceptsIn (init B <| get A <| (auto A).result a h) hb))
    = .inr ((auto B).result (init B <| get A <| (auto A).result a h) hb) := by
  rw [comp_auto_coincide_after_A']
  simp only [Sum.inr.injEq]
  exact Eq.symm ((auto B).result_def (B.init (A.get ((auto A).result a h))) hb)

-- todo: expand on ^^^, show that this is the result.

#check AutomatonConfiguration.result_of_acceptsImmediate


-- the result equals this.
theorem StateAutomaton.comp_auto_coincide_result'' {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (h) (hb) (hab)
     :
    (comp_auto A B).result (.inl a) (hab)
    = .inr ((auto B).result (init B <| get A <| (auto A).result a h) hb) := by
  set res := @Sum.inr A.H B.H ((auto B).result (B.init (A.get ((auto A).result a h))) hb)
  have res_w : _ = res := comp_auto_coincide_result ..
  set nn := ((auto A).acceptsIn a h + 1 + (auto B).acceptsIn (B.init (A.get ((auto A).result a h))) hb)
  have res_leads : (comp_auto A B).leads' (.inl a) res := by
    -- unfold leads'
    -- unfold leads
    -- unfold leads_nth at res_w
    exact ⟨_ , res_w⟩
  have res_accepts : (comp_auto A B).acceptsImmediate res := by
    refine (comp_auto_acceptsImmediate_def A B res).mpr ?_

    let ww := @AutomatonConfiguration.result B.H B.auto (B.init (A.get ((auto A).result a h))) hb
    refine ⟨ww,?_,by rfl⟩
    apply (auto B).result_accepts ..
  symm
  refine (comp_auto A B).result_of_acceptsImmediate _ _ res_leads res_accepts


theorem StateAutomaton.comp_auto_coincide_result' {X : Type} (A : StateAutomaton I X) (B : StateAutomaton X O) (a : A.H) (hh) (h) (hb)
     :
    (comp_auto A B).acceptsIn (.inl a) hh = (((auto A).acceptsIn a h) + ((auto B).acceptsIn (init B <| get A <| (auto A).result a h) hb) + 1) := by
  unfold acceptsIn
  refine nat_le_ext ?_
  intro i
  -- unfold haltsIn
  rw [@Nat.find_le_iff]
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


        unfold result at a_v ⊢
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



theorem sum_elim_func_distrib{X Y Z W : Type} (f : X → W) (g : Y → X) (w : Z → X) (x) :
    Sum.elim (fun a ↦ f (g a)) (fun a ↦ f (w a)) x =
    f (Sum.elim (fun a ↦ (g a)) (fun a ↦ (w a)) x) := by
  cases x with
  | inl val => simp_all only [Sum.elim_inl]
  | inr val_1 => simp_all only [Sum.elim_inr]


theorem StateAutomaton.comp.spec' {X : Type} {A : StateAutomaton I X} {B : StateAutomaton X O} {fa : I → Option X} {fb : X → Option O}
  (ma : models_function A fa) (mb : models_function B fb) :
  models_function (comp A B) (fun t ↦ Option.bind (fa t) fb) := by

  have bin (t) : Option.bind (fa t) fb = match (fa t) with | some w => fb w | none => none
    := by aesop
  -- simp_rw [bin]
  rw [StateAutomaton.models_function_def] at ma mb ⊢
  have models_accept : ((A.comp B).models_function_accept fun x ↦ ((fa x).bind fb).isSome = true) := sorry
  simp only [models_accept, true_and]
  intro t c
  rw [show (A.comp B).result t c =
    Sum.elim (fun x ↦ B.get (B.init (A.get x))) (fun x ↦ B.get x)
      ((comp_auto A B).result (.inl <| A.init t) c) from rfl]

  set ww := @AutomatonConfiguration.result (A.H ⊕ B.H) (A.comp_auto B) (Sum.inl (A.init t)) c
  have ww_right : Sum.isRight ww := by exact comp_auto_result_b A B (Sum.inl (A.init t)) c
  have ⟨wwr,wwr_spec⟩: ∃wwr, ww = (.inr wwr) := Sum.isRight_iff.mp ww_right
  rw [wwr_spec]
  simp only [Sum.elim_inr]
  -- have : _ = ww := comp_auto_coincide_result'' A B _
  have := ma.right t (accepts_A c)
  rw [this]
  simp only [Option.bind_some]
  have := mb.right (A.result t (accepts_A c)) ?_
  ·
    rw [this]
    simp only [Option.some.injEq]
    rw [result]
    apply congrArg
    apply Sum.inr_injective
    rw [←wwr_spec]
    -- might be the wrong direction
    sorry



  -- rw [show
  --   Sum.elim (fun x ↦ B.get (B.init (A.get x))) (fun x ↦ B.get x)
  --     ((comp_auto A B).result (.inl <| A.init t) c) =
  --   B.get ( Sum.elim (fun x ↦ (B.init (A.get x))) (fun x ↦ x)
  --     ((comp_auto A B).result (.inl <| A.init t) c) ) from rfl]

  sorry
-- todo:

-- And:  A.I × B.I → A.O × B.O
-- Or (parallel):  A.I × B.I → A.O ⊕ B.O
-- Map : A.I ⊕ B.I → A.O ⊕ B.O




end utilities
