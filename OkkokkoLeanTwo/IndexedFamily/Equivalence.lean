import OkkokkoLeanTwo.IndexedFamily.Basic

namespace IndexedFamily

universe  v v' v'' u

variable {X : Type u}

def equivalence (f : IndexedFamily.{v} X) (g : IndexedFamily.{v'} X)
  :=  {e : f.fst ≃ g.fst // g.snd ∘ e = f.snd}

-- irreducible_def equivalence_exists (f : IndexedFamily.{v} X) (g : IndexedFamily.{v'} X) : Prop
--   := f.elemCard =cl g.elemCard

infixl:25 " ≃' " => equivalence
-- infixl:25 " ≃'' " => equivalence_exists


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

section equivalence_iffs


lemma iff_elementwise_equiv_sets (f g : IndexedFamily X)
  : f.preimageCard =cl g.preimageCard ↔ Nonempty (∀(x : Set X), ↑(f.snd ⁻¹' x) ≃ ↑(g.snd ⁻¹' x))
  := by
  simp only [funext_iff]
  unfold preimageCard
  constructor
  {
    exact fun fg ↦ ⟨fun x ↦ (Cardinal.lift_mk_eq'.mp (fg x)).some⟩
  }
  intro ⟨ee⟩ x
  apply Cardinal.lift_mk_eq'.mpr ⟨ee x⟩

lemma iff_elementwise_equiv (f : IndexedFamily.{v} X) (g : IndexedFamily.{v'} X)
  : f.elemCard =cl g.elemCard ↔ Nonempty (∀(x : X), ↑(f.snd ⁻¹' {x}) ≃ ↑(g.snd ⁻¹' {x}))
  := by
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


lemma iff_elementwise_equiv_fiber (f : IndexedFamily.{v} X) (g : IndexedFamily.{v'} X)
  :  f.elemCard =cl g.elemCard ↔ Nonempty (∀(x : X), {i // f.snd i = x} ≃ {i // g.snd i = x})
  := by
    rw [iff_elementwise_equiv]
    obtain ⟨fst, snd⟩ := f
    obtain ⟨fst_1, snd_1⟩ := g
    simp_all only
    rfl

open scoped Function

lemma iff_equiv (f : IndexedFamily.{v} X) (g : IndexedFamily.{v'} X)
  :  f.elemCard =cl g.elemCard  ↔ ∃e : _ ≃ _, g.snd ∘ e = f.snd
  := by
  rw [iff_elementwise_equiv_fiber]
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


theorem equivalence.elemCard_iff {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
  : Nonempty (f ≃' g) ↔ (f.elemCard =cl g.elemCard) := by
    simp [iff_equiv]
    simp only [equivalence, nonempty_subtype]

theorem equivalence.preimageCard_iff {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
  : Nonempty (f ≃' g) ↔ f.preimageCard =cl g.preimageCard := by rw [equivalence.elemCard_iff,elemCard_preimageCard_iff f g]


-- structure EquivF (f : IndexedFamily.{v} X) (g : IndexedFamily.{v'} X) extends (f.fst ≃ g.fst) where
--   isComp' : g.snd ∘ toFun = f.snd
-- instance (f : IndexedFamily.{v} X) (g : IndexedFamily.{v'} X) : EquivLike (EquivF f g) f.fst g.fst :=

def equivalence.asSubtype (f : IndexedFamily.{v} X) (g : IndexedFamily.{v'} X)
  :=  {e : f.fst ≃ g.fst // g.snd ∘ e = f.snd}

-- infixl:25 " ≃ " => equivalence.asSubtype
-- theorem equivalence.subtype_iff {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
--   :  f ≃' g ↔ Nonempty (f ≃ g) := Trans.simple (iff_equiv f g) (Iff.symm nonempty_subtype)



-- noncomputable def equivalence.equiv {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
--   (e' : f ≃' g) : f.fst ≃ g.fst := Equiv.ofFiberEquiv (equivalence.iff_elementwise_equiv_fiber _ _ |>.mp e').some

def equivalence.equiv {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
  (e : f ≃' g) : f.fst ≃ g.fst := e.val

theorem equivalence.equiv_map' {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
  (e' : f ≃' g) (x) : g.snd (e'.equiv x) = f.snd x := by
  rw [←e'.property]
  rfl


theorem equivalence.equiv_map {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
  (e' : f ≃' g) : g.snd ∘ e'.equiv = f.snd := by
  exact e'.prop


-- I wonder, is it possible to use coe to automatically convert propositions

def equivalence.ofEquiv {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X}
  (e : f.fst ≃ g.fst) (h : g.snd ∘ e = f.snd) : f ≃' g := ⟨e,h⟩

variable {f : IndexedFamily.{v} X} {g : IndexedFamily.{v'} X} {h : IndexedFamily.{v''} X}

@[refl]
def equivalence.refl (f : IndexedFamily.{v} X) : f ≃' f := by
  apply ofEquiv (Equiv.refl _) rfl

@[symm]
def equivalence.symm  : f ≃' g → g ≃' f := by
  intro w
  refine ofEquiv w.equiv.symm ?_
  have := equiv_map w
  exact (Equiv.comp_symm_eq w.equiv g.snd f.snd).mpr (id (Eq.symm this))

@[trans]
def equivalence.trans  : f ≃' g → g ≃' h → f ≃' h := by
  intro fg gh
  have := fg.equiv.trans gh.equiv
  refine ofEquiv (fg.equiv.trans gh.equiv) ?_
  rw [←fg.equiv_map, ← gh.equiv_map]
  rfl





end equivalence_iffs
