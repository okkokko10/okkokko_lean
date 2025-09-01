import Mathlib.tactic
import OkkokkoLean.Lead
import OkkokkoLean.AutomatonConfiguration
import OkkokkoLean.StateAutomaton

section ComputationOkko




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


instance tc : AutomatonConfiguration (TuringConfiguration M) where
  yield' (C) := TuringConfiguration.yield C
  acceptsImmediate' (C) := TuringConfiguration.acceptsImmediate C
  rejectsImmediate' (C) := TuringConfiguration.rejectsImmediate C
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
def TuringMachine.accepts (tape : Tape G) : Prop := tc.accepts (M.use tape)
def TuringMachine.halt_rejects (tape : Tape G) : Prop := tc.halt_rejects (M.use tape)

def TuringMachine.total : Prop := ∀ tape : Tape G, tc.halts (M.use tape)


-- on all inputs, both turing machines have the same output.
def TuringMachine.same {Q1 Q2 : Type} {G : Type} --[DecidableEq Q1] [DecidableEq Q2] [DecidableEq G]
    (A : TuringMachine Q1 G) (B : TuringMachine Q2 G) := ∀ tape : Tape G, tc.accepts (A.use tape) ↔ tc.accepts (B.use tape)


theorem TuringConfiguration.output_theorem (C : TuringConfiguration M) (h : tc.halts C) : ∃ b,
  (tc.rejectsImmediate b ∨ tc.acceptsImmediate b) ∧ tc.leads' C b := ((tc.halts_def C).mp h)

noncomputable def TuringConfiguration.output (C : TuringConfiguration M) (h : tc.halts C) := (C.output_theorem h).choose
theorem TuringConfiguration.output_halts (C : TuringConfiguration M) (h : tc.halts C) :tc.haltsImmediate (C.output h) := (C.output_theorem h).choose_spec.left
theorem TuringConfiguration.output_leads (C : TuringConfiguration M) (h : tc.halts C) : tc.leads' C (C.output h) := (C.output_theorem h).choose_spec.right

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
