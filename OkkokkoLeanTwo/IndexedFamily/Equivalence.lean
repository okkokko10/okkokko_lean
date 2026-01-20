import OkkokkoLeanTwo.IndexedFamily.Basic

namespace IndexedFamily

universe u v v' v''

variable {X : Type u}


lemma elemCard_preimageCard_iff (f g : IndexedFamily X)
  : f.preimageCard =cl g.preimageCard ↔ f.elemCard =cl g.elemCard
  := by
    unfold elemCard preimageCard
    refine ⟨?_,?_⟩
    {
      rw [CardinalLiftFunEq.funext_iff]
      rw [CardinalLiftFunEq.funext_iff]
      intro w x
      exact (w {x})
    }
    rw [CardinalLiftFunEq.funext_iff]
    rw [CardinalLiftFunEq.funext_iff]
    intro w s
    simp_rw [Cardinal.lift_mk_eq'] at w ⊢
    refine ⟨?_⟩
    change {i // f.snd i ∈ s} ≃ {i // g.snd i ∈ s}

    have tf: { i // f.snd i ∈ s } ≃ Σ (x : s), { i // f.snd i = x } := by
      refine (Equiv.sigmaSubtypeFiberEquivSubtype f.snd ?_).symm
      simp only [implies_true]
    have tg: { i // g.snd i ∈ s } ≃ Σ (x : s), { i // g.snd i = x } := by
      refine (Equiv.sigmaSubtypeFiberEquivSubtype g.snd ?_).symm
      simp only [implies_true]
    apply Equiv.trans tf
    symm
    apply Equiv.trans tg
    symm
    refine Equiv.sigmaCongr ?_ fun a ↦ ?_
    exact Equiv.refl _
    simp only [Equiv.refl_apply]
    apply (w a).some


theorem equivalence.preimageCard_iff {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  : f ≃' g ↔ f.preimageCard =cl g.preimageCard := by rw [equivalence.elemCard_iff,elemCard_preimageCard_iff f g]


-- section restrict
-- -- noncomputable def IndexedFamily.preimage_card.restrict (p : Set X → Prop) (f : IndexedFamily X) : Set X → Cardinal.{v}
-- --   := Set.indicator p f.preimage_card
--   -- := open scoped Classical in if p x then preimage_card f x else 0


-- def preimageCard_restrict (p : Set X) (f : IndexedFamily.{u,v} X) (x : Set X) : Cardinal.{v}
--   := preimageCard f (p ∩ x)

-- -- theorem preimage_card.restrict.as

-- def elemCard_restrict (p : Set X) (f : IndexedFamily X) (x : X) : Cardinal.{v} := preimageCard_restrict p f {x}

-- theorem elemCard_preimageCard_iff_restrict (p : Set X) (f g : IndexedFamily X)
--   : f.preimageCard_restrict p = g.preimageCard_restrict p ↔ f.elemCard_restrict p = g.elemCard_restrict p
--   := by sorry

-- -- def restrict (p : Set X) (f : IndexedFamily X) : IndexedFamily X := ⟨_, restrict_range p f.snd⟩
-- end restrict
-- #check fun p ↦ (· = ·) on (preimage_card_restrict p)

-- todo: further quotients where IndexedFamilies are given equivalences, like disjoint union additivity
-- restriction could just be that f is equated with restrict p f.
-- for some things, equate countable and uncountable.


-- theorem setoid_equiv :

-- this file describes how to define homomorphisms:
-- #check DFunLike
-- also could this be used for quotient? quotient.out

-- #check Equiv

section equivalence_iffs


lemma equivalence.iff_elementwise_equiv_sets (f g : IndexedFamily X)
  : f ≃' g ↔ Nonempty (∀(x : Set X), ↑(f.snd ⁻¹' x) ≃ ↑(g.snd ⁻¹' x))
  := by
  rw [equivalence.preimageCard_iff]
  simp only [funext_iff]
  unfold preimageCard
  constructor
  {
    exact fun fg ↦ ⟨fun x ↦ (Cardinal.lift_mk_eq'.mp (fg x)).some⟩
  }
  intro ⟨ee⟩ x
  apply Cardinal.lift_mk_eq'.mpr ⟨ee x⟩

theorem equivalence.iff_elementwise_equiv (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X)
  : f ≃' g ↔ Nonempty (∀(x : X), ↑(f.snd ⁻¹' {x}) ≃ ↑(g.snd ⁻¹' {x}))
  := by
  rw [equivalence.elemCard_iff]
  simp only [funext_iff]
  unfold elemCard preimageCard
  simp only [Function.comp_apply]
  constructor
  {
    intro fg
    refine ⟨?_⟩
    intro x
    exact (Cardinal.lift_mk_eq'.mp (fg x)).some
  }
  intro ⟨ee⟩ x
  apply Cardinal.lift_mk_eq'.mpr ⟨ee x⟩


lemma equivalence.iff_elementwise_equiv_fiber (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X)
  :  f ≃' g ↔ Nonempty (∀(x : X), {i // f.snd i = x} ≃ {i // g.snd i = x})
  := by
    rw [equivalence.iff_elementwise_equiv]
    obtain ⟨fst, snd⟩ := f
    obtain ⟨fst_1, snd_1⟩ := g
    simp_all only
    rfl

open scoped Function

theorem equivalence.iff_equiv (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X)
  :  f ≃' g ↔ ∃e : _ ≃ _, g.snd ∘ e = f.snd
  := by
  rw [equivalence.iff_elementwise_equiv_fiber]
  constructor
  {
    intro ⟨ee⟩
    refine ⟨?_,?_⟩
    apply Equiv.ofFiberEquiv (γ := X) (g := g.snd) (f := f.snd) ee
    funext x
    simp only [Function.comp_apply]
    exact Equiv.ofFiberEquiv_map _ _
  }
  intro ⟨e,e_p⟩
  refine ⟨?_⟩
  intro x
  apply Equiv.subtypeEquiv e
  exact fun a ↦ Eq.congr (congrFun (id (Eq.symm e_p)) a) rfl

#check Equiv.ofFiberEquiv_apply

-- structure EquivF (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X) extends (f.fst ≃ g.fst) where
--   isComp' : g.snd ∘ toFun = f.snd
-- instance (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X) : EquivLike (EquivF f g) f.fst g.fst :=

def equivalence.asSubtype (f : IndexedFamily.{u,v} X) (g : IndexedFamily.{u,v'} X)
  :=  {e : f.fst ≃ g.fst // g.snd ∘ e = f.snd}

-- infixl:25 " ≃ " => equivalence.asSubtype
-- theorem equivalence.subtype_iff {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
--   :  f ≃' g ↔ Nonempty (f ≃ g) := Trans.simple (iff_equiv f g) (Iff.symm nonempty_subtype)



noncomputable def equivalence.equiv {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  (e' : f ≃' g) : f.fst ≃ g.fst := Equiv.ofFiberEquiv (equivalence.iff_elementwise_equiv_fiber _ _ |>.mp e').some


theorem equivalence.equiv_map' {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  (e' : f ≃' g) (x) : g.snd (e'.equiv x) = f.snd x := by
  exact Equiv.ofFiberEquiv_map _ x

theorem equivalence.equiv_map {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  (e' : f ≃' g) : g.snd ∘ e'.equiv = f.snd := by
  funext x
  simp only [Function.comp_apply]
  exact Equiv.ofFiberEquiv_map _ x


-- I wonder, is it possible to use coe to automatically convert propositions

theorem equivalence.ofEquiv {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X}
  (e : f.fst ≃ g.fst) (h : g.snd ∘ e = f.snd) : f ≃' g := iff_equiv f g |>.mpr ⟨e,h⟩

variable {f : IndexedFamily.{u,v} X} {g : IndexedFamily.{u,v'} X} {h : IndexedFamily.{u,v''} X}

@[refl]
theorem equivalence.refl (f : IndexedFamily.{u,v} X) : f ≃' f := by
  apply ofEquiv (Equiv.refl _) rfl

@[symm]
theorem equivalence.symm  : f ≃' g → g ≃' f := by
  intro w
  refine ofEquiv w.equiv.symm ?_
  have := equiv_map w
  exact (Equiv.comp_symm_eq w.equiv g.snd f.snd).mpr (id (Eq.symm this))

@[trans]
theorem equivalence.trans  : f ≃' g → g ≃' h → f ≃' h := by
  intro fg gh
  have := fg.equiv.trans gh.equiv
  refine ofEquiv (fg.equiv.trans gh.equiv) ?_
  rw [←fg.equiv_map, ← gh.equiv_map]
  rfl





end equivalence_iffs
