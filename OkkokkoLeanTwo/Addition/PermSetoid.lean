import OkkokkoLeanTwo.Perm
import Mathlib

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}


#check LinearMap

abbrev perm.dep (a b : (ι : Type v) × (ι → X)) := perm a.snd b.snd

instance perm.setoid : Setoid ((ι : Type v) × (ι → X)) where
  r := perm.dep
  iseqv := {
    refl x := perm.refl x.snd
    symm := perm.symm
    trans := perm.trans
  }
instance perm.restrict.setoid (p : X → Prop) : Setoid ((ι : Type v) × (ι → X)) where
  r a b := perm.restrict p a.snd b.snd
  iseqv := {
    refl _ := perm.refl _
    symm := perm.symm
    trans := perm.trans
  }
-- #check Quotient perm.setoid
-- #check Quotient.map₂
-- #check Cardinal

--todo: idea: perm.restrict is "don't care about 0" quotients with perm

-- set_option pp.universes true

@[pp_with_univ]
def perm.quotient (X : Type u) := Quotient (@perm.setoid.{u, v} X)
def perm.restrict.quotient (p : X → Prop) := Quotient (perm.restrict.setoid p)
open scoped Cardinal

-- the cardinal's universe must be as high as X
def perm.quotient.mk_range (r : X → Cardinal.{v}) : perm.quotient.{u, max u v} X :=
  ⟦⟨Sigma (r · |>.out),Sigma.fst⟩⟧
def perm.quotient.range (q : perm.quotient.{u, v} X) (x : X) : Cardinal.{v} :=
  q.liftOn (fun s ↦ #{i : s.1 // s.2 i = x}) <|
  by
  simp only
  intro a b ⟨e,w⟩
  refine Cardinal.mk_congr ?_
  apply Equiv.subtypeEquiv e
  exact fun a_2 ↦ Eq.congr (congrFun w a_2) rfl
def perm.quotient.range_out (q : perm.quotient.{u, v} X) (x : X)
  :range q x = #{i : q.out.1 // q.out.2 i = x} := by
  unfold range
  set r := (fun s : (ι : Type v) × (ι → X) ↦ #{ i // s.snd i = x })
  change Quotient.liftOn q r _ = r (Quotient.out q)
  nth_rw 1 [←Quotient.out_eq q]
  exact rfl


theorem perm.quotient.mk_range_range (r : X → Cardinal.{max u v}) :
  (mk_range r).range = r := by
  unfold mk_range range
  simp only [Quotient.lift_mk]
  funext x
  rw [show (r x) = #((r x).out) by exact Eq.symm (Cardinal.mk_out (r x))]
  refine Cardinal.mk_congr ?_
  exact Equiv.sigmaSubtype x
theorem perm.quotient.mk_range.card_lift (r : X → Cardinal.{v}) :
  mk_range r = mk_range (Cardinal.lift.{u, v} ∘ r) := by
  unfold mk_range
  simp only [Function.comp_apply]
  apply Quotient.eq.mpr
  unfold setoid
  simp only
  unfold perm
  refine ⟨?_,?_⟩
  apply Equiv.sigmaCongrRight
  intro a
  symm
  exact (Cardinal.out_lift_equiv _).some
  simp_rw [funext_iff]
  simp only [Function.comp_apply, Equiv.sigmaCongrRight_apply, implies_true]
theorem perm.quotient.mk_range_range' (r : X → Cardinal.{v}) :
  (mk_range r).range = Cardinal.lift ∘ r := by
  rw [mk_range.card_lift]
  exact mk_range_range (Cardinal.lift.{u, v} ∘ r)

-- theorem perm.quotient.range_invertw : Function.Bijective (quotient.range (X := X)) := by

--   sorry
theorem perm.quotient.range_mk_range (q : quotient.{u, max u v} X) :
  mk_range q.range = q := by
  have tq q' : ∃(r : X → Cardinal.{max u v}), mk_range r = q' := by
    refine ⟨?_,?_⟩


    #check range_out
    apply fun x ↦  #{ i // (Quotient.out q).snd i = x }
    -- sorry
    unfold mk_range
    simp only

    sorry
  specialize tq q
  obtain ⟨r, w⟩ := tq
  rw [←w, mk_range_range', ←mk_range.card_lift]



theorem perm.quotient.mk_range_s (r : X → Cardinal.{v}) (s : X → (Type v)) (h : ∀i, #(s i) = r i) :
  mk_range (r) = ⟦⟨Sigma s,Sigma.fst⟩⟧ := by


  sorry

theorem perm.quotient.range_mk_range' (q : quotient.{u, max u v} X) :
  mk_range q.range = q := by


  -- have tq q' : ∃(r : X → Cardinal), mk_range r = q' := by sorry

  unfold mk_range --range



  -- obtain ⟨ι, q'⟩ := q

  rw [Quotient.mk_eq_iff_out]
  rewrite [← show ⟦q.out⟧ = q by exact Quotient.out_eq _]


  refine ⟨?_,?_⟩
  {
  simp only

  -- #check Quotient.liftOn_mk
  trans
  {
    -- simp_rw [Quotient.liftOn_mk _ _ _]

    have tt x :Quotient.out #{ i // (Quotient.out q).snd i = x } ≃ { i // (Quotient.out q).snd i = x } := Cardinal.outMkEquiv
    exact Equiv.sigmaCongrRight tt
  }
  simp only [Quotient.out_eq]

  exact Equiv.sigmaFiberEquiv (Quotient.out q).snd

  }
  funext x
  have : ⟦Quotient.out q⟧ = q := by exact Quotient.out_eq q
  -- what is happening?
  simp only [Quotient.lift_mk, eq_mpr_eq_cast, id_eq, Equiv.coe_trans, Function.comp_apply,
    Equiv.sigmaCongrRight_apply]


  -- change x.fst = Sigma.snd (⟦q.out⟧.out) _


  sorry

-- todo: this range is a homomorphism

theorem perm.quotient.range_inverse : Function.LeftInverse (quotient.range (X := X)) quotient.mk_range := mk_range_range
theorem perm.quotient.mk_range_invese : Function.RightInverse (quotient.range (X := X)) quotient.mk_range := range_mk_range


theorem perm.quotient.range_bijective : Function.Bijective (mk_range.{u,max u v} (X := X)) := by
  refine Function.bijective_iff_has_inverse.mpr ?_

  use range
  constructor
  exact range_inverse
  exact mk_range_invese

-- uses sorry
noncomputable def perm.quotient.range_equiv := Equiv.ofBijective (mk_range.{u,max u v} (X := X)) range_bijective

-- #check LinearEquiv

#check Quotient.lift

-- note : Empty.elim is what I was looking for.

noncomputable instance perm.instZero : Zero (perm.quotient.{u,v} X) where
  zero := ⟦⟨ULift Empty,fun w ↦ w.down.elim⟩⟧

abbrev perm.quotient.add'_op := (fun (a₁ b₁ : (ι : Type v) × (ι → X)) ↦ (⟨a₁.fst ⊕ b₁.fst, Sum.elim a₁.snd b₁.snd⟩ : (ι : Type v) × (ι → X)))

theorem perm.quotient.add'_proof {X : Type u} :
∀ ⦃a₁ a₂ : (ι : Type v) × (ι → X)⦄,
  a₁ ≈ a₂ →
    ∀ ⦃b₁ b₂ : (ι : Type v) × (ι → X)⦄,
      b₁ ≈ b₂ →
  add'_op a₁ b₁
  ≈ add'_op a₂ b₂ := by
    -- simp only
    intro a1 a2 ⟨ae,ac⟩ b1 b2 ⟨be,bc⟩
    change perm _ _
    refine ⟨?_,?_⟩
    simp only
    exact ae.sumCongr be
    simp only [id_eq]
    simp_all only
    obtain ⟨fst, snd⟩ := a1
    obtain ⟨fst_1, snd_1⟩ := a2
    obtain ⟨fst_2, snd_2⟩ := b1
    obtain ⟨fst_3, snd_3⟩ := b2
    simp_all only
    ext x : 1
    simp_all only [Function.comp_apply, Equiv.sumCongr_apply]
    cases x with
    | inl val => simp_all only [Sum.elim_inl, Function.comp_apply, Sum.map_inl]
    | inr val_1 => simp_all only [Sum.elim_inr, Function.comp_apply, Sum.map_inr]

theorem perm.quotient.add'.extracted_1' {X : Type u} {a₁ a₂ : (ι : Type v) × (ι → X)}
  (ha : a₁ ≈ a₂) {b₁ b₂ : (ι : Type v) × (ι → X)} (hb : b₁ ≈ b₂ )
  : (⟨a₁.fst ⊕ b₁.fst, Sum.elim a₁.snd b₁.snd⟩ : (ι : Type v) × (ι → X)) ≈ ⟨a₂.fst ⊕ b₂.fst, Sum.elim a₂.snd b₂.snd⟩
  := add'_proof ha hb

def perm.quotient.add' (a b : quotient.{u,v} X) : quotient.{u,v} X
  := Quotient.map₂ add'_op (add'_proof) a b

noncomputable instance perm.instAdd : Add (perm.quotient.{u,v} X) where
  add := quotient.add'

theorem perm.quotient.add_def (a b : perm.quotient.{u,v} X)
  : add' a b = ⟦add'_op a.out b.out⟧
  := by
  change add' _ _ = _
  unfold add'
  nth_rw 1 [← Quotient.out_eq a]
  nth_rw 1 [← Quotient.out_eq b]
  rfl

theorem perm.quotient.add_assoc' (a b c : (ι : Type v) × (ι → X) )
  : dep (add'_op (add'_op a b) c) (add'_op a (add'_op b c)) := by
  unfold add'_op
  simp only

  sorry

noncomputable instance perm.instAddCommMonoid : AddCommMonoid (perm.quotient.{u, v} X) where

  add_assoc a b c :=
    by
    -- let w : perm.quotient.{u,v} X :=
    --   (Quotient.map₂ (sc := perm.setoid.{u,v}) (fun (a b : ((ι : Type v) × (ι → X))) ↦ (⟨a.1 ⊕ b.1, Sum.elim a.2 b.2⟩ : ((ι : Type v) × (ι → X)))) sorry a b)

    -- simp_rw [quotient.add_def _ _]
    -- apply Quotient.eq.mpr
    -- change perm _ _
    -- simp only

    change (a.add' b).add' c = a.add' (b.add' c)
    nth_rewrite 2 [quotient.add_def _ _]

    unfold quotient.add'

    -- apply Quotient.map₂_mk





    sorry

  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  add_comm := sorry
-- #check Sigma.curry_add
-- #check Function.uncurry
-- #check Sigma.map


instance perm.instMonoid [Monoid X] : Monoid (perm.quotient X) where
  -- mul := Quotient.map₂ (fun a b ↦ ⟨a.1 × b.1, (Function.uncurry <| (a.2 · * b.2 ·))⟩) (by
  mul := Quotient.map₂ (fun a b ↦ ⟨a.1 × b.1, (fun m ↦ (a.2 m.1) * (b.2 m.2))⟩) (by

    simp only
    intro a1 a2 ⟨ae,ac⟩ b1 b2 ⟨be,bc⟩

    refine ⟨ae.prodCongr be,?_⟩
    simp_all only [Function.comp_apply, Equiv.prodCongr_apply]
    obtain ⟨fst, snd⟩ := a1
    obtain ⟨fst_1, snd_1⟩ := a2
    obtain ⟨fst_2, snd_2⟩ := b1
    obtain ⟨fst_3, snd_3⟩ := b2
    simp_all only
    rfl)
  mul_assoc := sorry
  one := ⟦⟨(1 : Cardinal).out,fun _ ↦ 1⟩⟧
  -- one := Quotient.map (fun i ↦ ⟨i, fun _ ↦ 1⟩) ( by exact fun a b ⟨(e : a ≃ b)⟩ ↦  ⟨e,by rfl⟩ ) (1 : Cardinal)
  one_mul := sorry
  mul_one := sorry


-- instance instCombined' [Group X] : Semiring (Quotient (@perm.setoid X)) where
--   add := Quotient.map₂ (fun a b ↦ ⟨a.1 ⊕ b.1, Sum.elim a.2 b.2⟩) (by
--     simp only
--     intro a1 a2 ⟨ae,ac⟩ b1 b2 ⟨be,bc⟩
--     change perm _ _
--     refine ⟨?_,?_⟩
--     simp only
--     exact ae.sumCongr be
--     simp only [id_eq]
--     simp_all only
--     obtain ⟨fst, snd⟩ := a1
--     obtain ⟨fst_1, snd_1⟩ := a2
--     obtain ⟨fst_2, snd_2⟩ := b1
--     obtain ⟨fst_3, snd_3⟩ := b2
--     simp_all only
--     ext x : 1
--     simp_all only [Function.comp_apply, Equiv.sumCongr_apply]
--     cases x with
--     | inl val => simp_all only [Sum.elim_inl, Function.comp_apply, Sum.map_inl]
--     | inr val_1 => simp_all only [Sum.elim_inr, Function.comp_apply, Sum.map_inr]
--     )
--   add_assoc := sorry
--   zero := ⟦⟨Empty, _⟩⟧
--   zero_add := sorry
--   add_zero := sorry
--   nsmul := sorry
--   add_comm := sorry
--   mul := Quotient.map₂ (fun a b ↦ ⟨a.1 × b.1, (fun m ↦ (a.2 m.1) * (b.2 m.2))⟩) (by
--     simp only
--     intro a1 a2 ⟨ae,ac⟩ b1 b2 ⟨be,bc⟩
--     refine ⟨ae.prodCongr be,?_⟩
--     simp_all only [Function.comp_apply, Equiv.prodCongr_apply]
--     obtain ⟨fst, snd⟩ := a1
--     obtain ⟨fst_1, snd_1⟩ := a2
--     obtain ⟨fst_2, snd_2⟩ := b1
--     obtain ⟨fst_3, snd_3⟩ := b2
--     simp_all only
--     rfl)
--   left_distrib := sorry
--   right_distrib := sorry
--   zero_mul := sorry
--   mul_zero := sorry
--   mul_assoc := sorry
--   one := sorry
--   one_mul := sorry
--   mul_one := sorry
