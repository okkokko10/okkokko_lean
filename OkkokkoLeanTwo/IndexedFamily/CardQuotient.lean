import OkkokkoLeanTwo.IndexedFamily.Basic
import OkkokkoLeanTwo.IndexedFamily.BasicDefs
import OkkokkoLeanTwo.IndexedFamily.Hom
import OkkokkoLeanTwo.IndexedFamily.Equivalence
namespace IndexedFamily

universe v v' v'' u

variable {X : Type u}


section quotient

#check Equiv.symm

instance setoid {X : Type u} : Setoid (IndexedFamily.{v} X) where
  r := equivalence
  iseqv := {
    refl := equivalence.refl
    symm := equivalence.symm
    trans := equivalence.trans
  }

-- def setoid {X : Type u} : Setoid (IndexedFamily X) :=
--   Setoid.ker (preimageCard)

theorem setoid.equ {f g : IndexedFamily X} : setoid f g ↔ f ≃' g := by rfl

-- theorem basic.equivalence.add (f : IndexedFamily.{v} X) ( g : IndexedFamily.{v'} X) : basic.add f g

instance basic.smul : SMul Cardinal (IndexedFamily X) where
  smul := basic.mulCard

#check ModuleCon

instance setoid.instAddCon : AddCon (IndexedFamily.{v} X) where
  add' := by
    intros
    simp only [setoid.equ, equivalence.elemCard_addMonoid_iff, ↓CardinalLiftFunEq.same, map_add] at *
    simp_all only

instance setoid.instModuleCon : ModuleCon (Cardinal.{v}) (IndexedFamily.{v} X) where
  add' := setoid.instAddCon.add'
  smul := by
    simp only [setoid.equ]
    intro c x y xy
    have := equivalence.equiv_map xy
    apply equivalence.ofEquiv ?_ ?_
    refine Equiv.prodCongr (Equiv.refl _) (xy.equiv)
    funext w
    exact equivalence.equiv_map' xy w.2


def quotient := Quotient (setoid.{v} (X := X))
lemma quotient.is_module :  quotient.{v} (X:=X) = (setoid.instModuleCon.{v} (X:=X)).Quotient := rfl


abbrev quotient.mk (f : IndexedFamily.{v} X) : @quotient.{v} X := Quotient.mk setoid f


@[simp high]
lemma quotient.equ {f g : IndexedFamily.{v} X} : (⟦f⟧ : quotient) = ⟦g⟧ ↔ f ≃' g := by
  simp only [← setoid.equ]
  simp only [Quotient.eq]

@[simp]
lemma quotient.equ' {f g : IndexedFamily.{v} X} : f ≈ g ↔ f ≃' g := by
  simp only [← setoid.equ]
  simp only [HasEquiv.Equiv]


instance quotient.instAddZeroClass: AddZeroClass (@quotient.{v} X) where
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
instance quotient.instAddCommMonoid: AddCommMonoid (@quotient.{v} X) where
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


theorem quotient.add_apply {a b : IndexedFamily.{v} X} : instAddZeroClass.add ⟦a⟧ ⟦b⟧ = ⟦a + b⟧
  := by simp only [Add.add, Quotient.map₂_mk]

-- lemma basic.smul.def (c : Cardinal.{v}) (f : IndexedFamily.{v} X)
--   : c • f = ⟨f.fst × c.out, fun m ↦ f.snd m.1⟩ := by rfl

/-- it's weird that this didn't exist -/
noncomputable instance _root_.Cardinal.one_unique : Unique (Quotient.out (1 : Cardinal.{v})) := by
    have : (1 : Cardinal.{v}).out ≃ PUnit.{v+1} := by
      change (1 : Cardinal.{v}).out ≃ PUnit.{v + 1}
      refine Cardinal.eq.mp ?_ |>.some
      simp only [Cardinal.mk_out, Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one]
    apply Equiv.unique this


def quotient.elemCard_lift (f : @quotient.{v} X) (x : X) : Cardinal.{v} := f.lift (elemCard_addMonoidHom · x) <| by
  intro a b ab
  simp
  simp only [equ', equivalence.elemCard_iff, ↓CardinalLiftFunEq.same] at ab
  exact congrFun ab x

instance quotient.elemCard_addMonoidHom' : AddMonoidHom (@quotient.{v} X) (X → Cardinal) where
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
theorem quotient.elemCard_lift_iff {f g : @quotient.{v} X} : f = g ↔ f.elemCard_addMonoidHom' = g.elemCard_addMonoidHom' := by
  cases f,g using Quotient.ind₂
  rename_i a b
  unfold elemCard_addMonoidHom'
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [equ]
  simp only [equivalence.elemCard_iff, ↓CardinalLiftFunEq.same]
  rfl

open Cardinal in



instance quotient.instSmul : SMul Cardinal.{v} (@quotient.{v} X) where
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
lemma quotient.smul_elemCard {c : Cardinal.{v}} {f : @quotient.{v} X} : elemCard_addMonoidHom' (c • f) = c • elemCard_addMonoidHom' f
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

instance quotient.instModule : Module Cardinal.{v} (@quotient.{v} X) where
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


-- actually does not express mul. for that Z has to be IndexedFamily X, and a flatten at the end
-- X * Y = ∑x : X, x * Y = ∑x : X, (x * ·) '' Y
def basic.hmul {Y Z : Type*} (m : X → Y → Z) (f : IndexedFamily X) (g : IndexedFamily Y) : IndexedFamily Z
  := multiImage (fun x ↦ image (m x) g) f

-- todo: mul where x * x = x, x * y = 0. univ is one
set_option linter.unusedVariables false in
def both {X : Sort*} (a b : X) (h : a = b) : X := a

theorem both.lhs {X : Sort*} {a b : X} {h : a = b} : both a b h = a := rfl
theorem both.rhs {X : Sort*} {a b : X} {h : a = b} : both a b h = b := h


-- todo: show this is equivalent to if it had fun w ↦ g.snd w.val.2
def basic.mul (f : IndexedFamily X) (g : IndexedFamily X) : IndexedFamily X
  := ⟨{w : f.fst × g.fst // f.snd w.1 = g.snd w.2},fun w ↦ f.snd w.val.1⟩


def basic.mul.both' (f : IndexedFamily X) (g : IndexedFamily X) : IndexedFamily X
  := ⟨{w : f.fst × g.fst // f.snd w.1 = g.snd w.2},fun w ↦ both (f.snd w.val.1) (g.snd w.val.2) (w.property)⟩

-- theorem basic.mul.right (f : IndexedFamily X) (g : IndexedFamily X)
--   : basic.mul f g = ⟨{w : f.fst × g.fst // f.snd w.1 = g.snd w.2},fun w ↦ g.snd w.val.2⟩ := by

--   sorry


instance basic.instHMul : HMul (IndexedFamily.{v} X) (IndexedFamily.{v'} X) (IndexedFamily.{max v v'} X) where
  hMul := basic.mul

instance basic.instMul : Mul (IndexedFamily X) where
  mul := basic.mul
-- #check (fun x ↦ 1) ∘ (fun x ↦ 2)


#check Con

theorem algebra.mulCon.{va,va',vb,vb'}
  {a : IndexedFamily.{va} X}
  {a' : IndexedFamily.{va'} X}
  {b : IndexedFamily.{vb} X}
  {b' : IndexedFamily.{vb'} X}
  (sa : a ≃' a') (sb : b ≃' b')
  : (a * b) ≃' ((a' * b') : IndexedFamily.{max va' vb'} X) := by
  simp only [HMul.hMul,basic.mul]
  apply equivalence.ofEquiv ?_ ?_
  -- #check Equiv.prodShear
  refine Equiv.subtypeEquiv (Equiv.prodCongr sa.equiv sb.equiv) ?_
  · simp only [Equiv.prodCongr_apply, Prod.map_fst, equivalence.equiv_map', Prod.map_snd,
      implies_true]
  funext w'
  simp only [Function.comp_apply, Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst]
  exact equivalence.equiv_map' sa (w'.val).1


instance setoid.instCon : Con (IndexedFamily.{v} X) where
  mul' := fun {_ _ _ _} sa sb ↦ algebra.mulCon sa sb

def basic.univ'' {X_down : Type v} (up : X_down ≃ X) : IndexedFamily.{v} X := ⟨X_down, up⟩

-- idea: multiplication where the pairs just have to be related
open basic
-- multiplication could be a special case of a filter-mapped prod a × b
-- todo: change X to α
#check Finset.filterMap
-- def operation.filterMap {α β : Type*} (f : α → )
#check basic.multiImage
def basic.prod {Y : Type*} (f : IndexedFamily X) (g : IndexedFamily Y) : IndexedFamily (X × Y)
  := ⟨f.fst × g.fst,fun w ↦ (f.snd w.1, g.snd w.2)⟩
-- #check basic.hAdd
#check Finset.filter
def basic.filter (p : X → Prop) (A : IndexedFamily.{v} X) : IndexedFamily.{v} X := ⟨{x : A.fst // p (A.snd x)},A.snd ∘ (Subtype.val)⟩

-- todo: a Option/Subsingleton property

-- todo: a general lift/map/map₂ on quotient.
-- property: respects ≃'

-- def quotient.map

theorem operation.mul_as_prod (a b : IndexedFamily X)
  : a * b ≃' basic.multiImage (fun ⟨a,b⟩ ↦ open scoped Classical in if a = b then (basic.singleton a) else basic.zero) (basic.prod a b ) := sorry


-- hm. what if I made X dependent? Nah, I'll want multiple universes anyway
#check MulAction
#check HVAdd -- was there a Mul variant?
-- idea: try category

-- todo: supply this as an Equiv
theorem algebra.mul_assoc {a b c : IndexedFamily.{_} X} : a * b * c ≃' a * (b * c) := by

  simp only [HMul.hMul, basic.mul]
  apply equivalence.ofEquiv ?_ ?_
  exact {
    toFun := fun ⟨⟨⟨⟨a,b⟩,q⟩,c⟩,p⟩ ↦ ⟨⟨a,⟨⟨b,c⟩,by simp_all only⟩⟩,q⟩
    invFun := fun  ⟨⟨a,⟨⟨b,c⟩,p⟩⟩,q⟩ ↦  ⟨⟨⟨⟨a,b⟩,q⟩,c⟩,by simp_all only⟩
    left_inv := congrFun rfl
    right_inv := congrFun rfl
  }
  rfl




def quotient.mul {X_down : Type v} (up : X_down ≃ X)  : CommMonoid (@quotient.{v} X) where
  mul := Quotient.map₂ (fun a b ↦ a * b) <| fun ⦃a a'⦄ sa ⦃b b'⦄ sb ↦ algebra.mulCon sa sb
  mul_assoc a b c := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    exact equ.mpr algebra.mul_assoc
  one := ⟦basic.univ'' up⟧
  one_mul := by
    apply Quotient.ind
    intro A
    -- simp only [HMul.hMul]
    change Quotient.map₂ (fun a b ↦ Mul.mul a b) _ ⟦basic.univ'' up⟧ ⟦A⟧ = ⟦A⟧
    simp only [Quotient.map₂_mk, equ]
    simp only [Mul.mul, basic.mul, basic.univ'']
    apply equivalence.ofEquiv ?_ ?_
    simp only
    have ewe x y : up x = A.snd y ↔ (up.symm ∘ A.snd) y = x := by
      simp [Equiv.symm_apply_eq up, eq_comm]
    -- simp only [ewe, Function.comp_apply]
    -- apply Equiv.subtypeFi
    exact {
      toFun := fun ⟨⟨d,a⟩,p⟩ ↦ a
      invFun := fun a ↦ ⟨⟨up.symm (A.snd a),a⟩,by simp only [Equiv.apply_symm_apply]⟩
      left_inv := by
        unfold Function.LeftInverse
        simp only [Subtype.forall, Subtype.mk.injEq, Prod.forall, Prod.mk.injEq,
          Equiv.symm_apply_eq, and_true]
        tauto
      right_inv := by tauto
    }
    simp only [id_eq, Equiv.coe_fn_mk]
    funext w
    simp only [Function.comp_apply, w.property]
  mul_one := sorry
  mul_comm := by
    apply Quotient.ind₂
    intro A B
    simp only [HMul.hMul, Quotient.map₂_mk]
    apply equ.mpr
    -- todo: make its own theorem
    unfold basic.mul
    refine equivalence.ofEquiv ?_ ?_
    -- simp only
    refine Equiv.subtypeEquiv (Equiv.prodComm A.fst B.fst) (by tauto)
    simp only
    funext ⟨x,hx⟩
    rw [hx]
    simp only [Function.comp_apply, Equiv.subtypeEquiv_apply, Equiv.prodComm_apply, Prod.fst_swap]
-- idea: a macro that translates Equiv into equivalence?

-- todo: decomposition into finite and infinite components. maybe even of certain cardinality. then theorems like ⊔ and ⊓ working like + and * for the infinite component

#check LinearMap
-- theorem basic.mul_linear

end quotient


end IndexedFamily
