import OkkokkoLeanTwo.IndexedFamily.Basic
import OkkokkoLeanTwo.IndexedFamily.BasicDefs
import OkkokkoLeanTwo.IndexedFamily.Hom
import OkkokkoLeanTwo.IndexedFamily.Equivalence
namespace IndexedFamily

universe u v v' v''

variable {X : Type u}


section quotient

#check Equiv.symm

instance setoid {X : Type u} : Setoid (IndexedFamily X) where
  r := equivalence
  iseqv := {
    refl := equivalence.refl
    symm := equivalence.symm
    trans := equivalence.trans
  }

-- def setoid {X : Type u} : Setoid (IndexedFamily X) :=
--   Setoid.ker (preimageCard)

theorem setoid.equ {f g : IndexedFamily X} : setoid f g ↔ f ≃' g := by rfl

-- theorem basic.equivalence.add (f : IndexedFamily.{u,v} X) ( g : IndexedFamily.{u,v'} X) : basic.add f g

instance basic.smul : SMul Cardinal (IndexedFamily X) where
  smul := basic.mulCard

#check ModuleCon

instance setoid.instAddCon : AddCon (IndexedFamily.{u,v} X) where
  add' := by
    intros
    simp only [setoid.equ, equivalence.elemCard_addMonoid_iff, ↓CardinalLiftFunEq.same, map_add] at *
    simp_all only

instance setoid.instModuleCon : ModuleCon (Cardinal.{v}) (IndexedFamily.{u,v} X) where
  add' := setoid.instAddCon.add'
  smul := by
    simp only [setoid.equ]
    intro c x y xy
    have := equivalence.equiv_map xy
    apply equivalence.ofEquiv ?_ ?_
    refine Equiv.prodCongr (Equiv.refl _) (xy.equiv)
    funext w
    exact equivalence.equiv_map' xy w.2


def quotient := Quotient (setoid (X := X))
lemma quotient.is_module :  quotient.{u,v} (X:=X) = (setoid.instModuleCon.{u,v} (X:=X)).Quotient := rfl


abbrev quotient.mk (f : IndexedFamily.{u,v} X) : @quotient.{u,v} X := Quotient.mk setoid f


@[simp high]
lemma quotient.equ {f g : IndexedFamily.{u,v} X} : (⟦f⟧ : quotient) = ⟦g⟧ ↔ f ≃' g := by
  simp only [← setoid.equ]
  simp only [Quotient.eq]

@[simp]
lemma quotient.equ' {f g : IndexedFamily.{u,v} X} : f ≈ g ↔ f ≃' g := by
  simp only [← setoid.equ]
  simp only [HasEquiv.Equiv]


instance quotient.instAddZeroClass: AddZeroClass (@quotient.{u,v} X) where
  add := Quotient.map₂ (fun a b ↦ a + b) <| by
    intros
    simp only [equ', equivalence.elemCard_addMonoid_iff, ↓CardinalLiftFunEq.same, map_add] at *
    simp_all only
  zero := ⟦0⟧
  zero_add := by
    apply Quotient.ind
    intro a
    change Quotient.map₂ (fun a b ↦ a + b) _ ⟦0⟧ ⟦a⟧ = ⟦a⟧
    simp only [Quotient.map₂_mk, equ]
    simp only [equivalence.elemCard_addMonoid_iff, ↓CardinalLiftFunEq.same]
    simp only [map_add, map_zero, zero_add]
  add_zero := by
    apply Quotient.ind
    intro a
    change Quotient.map₂ (fun a b ↦ a + b) _ ⟦a⟧ ⟦0⟧ = ⟦a⟧
    simp only [Quotient.map₂_mk, quotient.equ]
    simp only [equivalence.elemCard_addMonoid_iff, ↓CardinalLiftFunEq.same]
    simp only [map_add, map_zero, add_zero]
instance quotient.instAddCommMonoid: AddCommMonoid (@quotient.{u,v} X) where
  add_assoc := by
    intro a b c
    cases a using Quotient.ind
    cases b using Quotient.ind
    cases c using Quotient.ind
    rename_i a b c
    -- simp [· + ·,Add.add]
    apply equ.mpr
    simp only [equivalence.elemCard_addMonoid_iff, ↓CardinalLiftFunEq.same]
    simp only [map_add]
    group
  add_comm a b := by
    cases a using Quotient.ind
    cases b using Quotient.ind
    rename_i a b
    change ⟦a + b⟧ = ⟦b + a⟧
    simp only [quotient.equ]
    simp only [equivalence.elemCard_addMonoid_iff, ↓CardinalLiftFunEq.same]
    simp only [map_add]
    group
  nsmul := nsmulRec


theorem quotient.add_apply {a b : IndexedFamily.{u,v} X} : instAddZeroClass.add ⟦a⟧ ⟦b⟧ = ⟦a + b⟧
  := by simp only [Add.add, Quotient.map₂_mk]

-- lemma basic.smul.def (c : Cardinal.{v}) (f : IndexedFamily.{u,v} X)
--   : c • f = ⟨f.fst × c.out, fun m ↦ f.snd m.1⟩ := by rfl

/-- it's weird that this didn't exist -/
noncomputable instance _root_.Cardinal.one_unique : Unique (Quotient.out (1 : Cardinal.{v})) := by
    have : (1 : Cardinal.{v}).out ≃ PUnit.{v+1} := by
      change (1 : Cardinal.{v}).out ≃ PUnit.{v + 1}
      refine Cardinal.eq.mp ?_ |>.some
      simp only [Cardinal.mk_out, Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one]
    apply Equiv.unique this


def quotient.elemCard_lift (f : @quotient.{u,v} X) (x : X) : Cardinal.{v} := f.lift (elemCard_addMonoidHom · x) <| by
  intro a b ab
  simp
  simp only [equ', equivalence.elemCard_iff, ↓CardinalLiftFunEq.same] at ab
  exact congrFun ab x

instance quotient.elemCard_addMonoidHom' : AddMonoidHom (@quotient.{u,v} X) (X → Cardinal) where
  toFun := elemCard_lift
  map_zero' := elemCard.zeroHom.map_zero
  map_add' := by
    apply Quotient.ind₂
    intro x y
    unfold elemCard_lift
    ext w
    simp only [Quotient.lift_mk, Pi.add_apply]
    change Quotient.lift (fun x ↦ elemCard_addMonoidHom x w) _ (instAddZeroClass.add ⟦x⟧ ⟦y⟧) = x.elemCard w + y.elemCard w
    simp only [add_apply, Quotient.lift_mk]
    simp only [map_add, Pi.add_apply]
    tauto

@[aesop norm]
theorem quotient.elemCard_lift_iff {f g : @quotient.{u,v} X} : f = g ↔ f.elemCard_addMonoidHom' = g.elemCard_addMonoidHom' := by
  cases f,g using Quotient.ind₂
  rename_i a b
  unfold elemCard_addMonoidHom'
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [equ]
  simp only [equivalence.elemCard_iff, ↓CardinalLiftFunEq.same]
  rfl

open Cardinal in



instance quotient.instSmul : SMul Cardinal.{v} (@quotient.{u,v} X) where
  smul c := Quotient.map (basic.mulCard c) <| by
    intro a b ab
    simp only [quotient.equ'] at *
    -- change basic.mulCard c a ≃' basic.mulCard c b
    unfold basic.mulCard
    refine equivalence.ofEquiv ?_ ?_
    simp only
    exact Equiv.prodCongr (Equiv.refl _) ab.equiv
    simp only [id_eq]
    have := ab.equiv_map
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl]
    funext x
    simp only [Function.comp_apply, Prod.map_snd]
    simp [funext_iff] at this
    simp_all only


-- #check MulActionHom

-- @[simp]
lemma quotient.smul_elemCard {c : Cardinal.{v}} {f : @quotient.{u,v} X} : elemCard_addMonoidHom' (c • f) = c • elemCard_addMonoidHom' f
  := by
  ext x
  simp only [Pi.smul_apply, smul_eq_mul]
  cases f using Quotient.ind
  simp only [elemCard_addMonoidHom', AddMonoidHom.coe_mk, ZeroHom.coe_mk, elemCard_lift,
    Quotient.lift_mk]
  rename_i f
  simp only [HSMul.hSMul, SMul.smul, Quotient.map_mk, Quotient.lift_mk]

  -- todo: should be its own lemma



  sorry

instance quotient.instModule : Module Cardinal.{v} (@quotient.{u,v} X) where
  one_smul := by
    intro b
    simp_all only [elemCard_lift_iff, smul_elemCard, one_smul]
  mul_smul x y := by
    intro b
    simp_all only [elemCard_lift_iff, smul_elemCard]
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    group
  smul_zero := by
    intro a
    simp_all only [elemCard_lift_iff, smul_elemCard, map_zero, smul_zero]
  smul_add := by
    intro a x y
    simp_all only [elemCard_lift_iff, smul_elemCard, map_add, smul_add]
  add_smul := by
    intro r s x
    simp_all only [elemCard_lift_iff, smul_elemCard, map_add]
    ext x_1 : 1
    simp_all only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    apply add_mul
  zero_smul := by
    intro x
    simp_all only [elemCard_lift_iff, smul_elemCard, zero_smul, map_zero]


-- X * Y = ∑x : X, x * Y = ∑x : X, (x * ·) '' Y
def basic.hmul {Y Z : Type*} (m : X → Y → Z) (f : IndexedFamily X) (g : IndexedFamily Y) : IndexedFamily Z
  := multiImage (fun x ↦ image (m x) g) f

-- todo: mul where x * x = x, x * y = 0. univ is one

def basic.mul (f : IndexedFamily X) (g : IndexedFamily X) : IndexedFamily X
  := ⟨{w : f.fst × g.fst // f.snd w.1 = g.snd w.2},fun w ↦ f.snd w.val.1⟩

def quotient.mul : CommMonoid (IndexedFamily.{u,v} X) where
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  npow_zero := sorry
  npow_succ := sorry
  mul_comm := sorry


#check LinearMap
-- theorem basic.mul_linear

end quotient
end IndexedFamily
