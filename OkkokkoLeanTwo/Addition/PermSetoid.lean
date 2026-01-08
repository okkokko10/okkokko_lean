import OkkokkoLeanTwo.Perm


universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}


#check LinearMap

instance perm.setoid : Setoid ((ι : Type v) × (ι → X)) where
  r a b := perm a.snd b.snd
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
#check Quotient perm.setoid
#check Quotient.map₂
-- #check Cardinal

--todo: idea: perm.restrict is "don't care about 0" quotients with perm

noncomputable def perm.get_equiv {a : ι → X} {b : ι' → X} (p : perm a b) : ι ≃ ι' := p.choose

-- note : Empty.elim is what I was looking for.

noncomputable instance perm.instZero : Zero (Quotient (@perm.setoid X)) where
  zero := ⟦⟨Empty, Empty.elim⟩⟧
noncomputable instance perm.instAdd : Add (Quotient (@perm.setoid X)) where
  add := Quotient.map₂ (fun a b ↦ ⟨a.1 ⊕ b.1, Sum.elim a.2 b.2⟩) (by
    simp only
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
    )

noncomputable def perm.instAddCommMonoid : AddCommMonoid (Quotient (@perm.setoid X)) where

  add_assoc := sorry

  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  add_comm := sorry
-- #check Sigma.curry_add
-- #check Function.uncurry
-- #check Sigma.map


instance perm.instMonoid [Monoid X] : Monoid (Quotient (@perm.setoid X)) where
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
