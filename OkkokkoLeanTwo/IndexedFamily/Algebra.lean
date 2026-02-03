import OkkokkoLeanTwo.IndexedFamily.Basic
import OkkokkoLeanTwo.IndexedFamily.BasicDefs
import OkkokkoLeanTwo.IndexedFamily.Hom
import OkkokkoLeanTwo.IndexedFamily.Equivalence
namespace IndexedFamily

universe v v' v'' u

variable {X : Type u}


-- todo: show this is equivalent to if it had fun w ↦ g.snd w.val.2
def basic.mul (f : IndexedFamily X) (g : IndexedFamily X) : IndexedFamily X
  := ⟨{w : f.fst × g.fst // f.snd w.1 = g.snd w.2},fun w ↦ f.snd w.val.1⟩


instance algebra.instHMul : HMul (IndexedFamily.{v} X) (IndexedFamily.{v'} X) (IndexedFamily.{max v v'} X) where
  hMul := basic.mul




def algebra.mulCon.{va,va',vb,vb'}
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



def basic.univ'' {X_down : Type v} (up : X_down ≃ X) : IndexedFamily.{v} X := ⟨X_down, up⟩

def basic.prod {Y : Type*} (f : IndexedFamily X) (g : IndexedFamily Y) : IndexedFamily (X × Y)
  := ⟨f.fst × g.fst,fun w ↦ (f.snd w.1, g.snd w.2)⟩
-- #check basic.hAdd
#check Finset.filter
def basic.filter (p : X → Prop) (A : IndexedFamily.{v} X) : IndexedFamily.{v} X := ⟨{x : A.fst // p (A.snd x)},A.snd ∘ (Subtype.val)⟩

def operation.mul_as_prod (a b : IndexedFamily X)
  : a * b ≃' basic.multiImage (fun ⟨a,b⟩ ↦ open scoped Classical in if a = b then (basic.singleton a) else basic.zero) (basic.prod a b ) := sorry

def algebra.mul_assoc {a b c : IndexedFamily.{_} X} : a * b * c ≃' a * (b * c) := by

  simp only [HMul.hMul, basic.mul]
  apply equivalence.ofEquiv ?_ ?_
  exact {
    toFun := fun ⟨⟨⟨⟨a,b⟩,q⟩,c⟩,p⟩ ↦ ⟨⟨a,⟨⟨b,c⟩,by simp_all only⟩⟩,q⟩
    invFun := fun  ⟨⟨a,⟨⟨b,c⟩,p⟩⟩,q⟩ ↦  ⟨⟨⟨⟨a,b⟩,q⟩,c⟩,by simp_all only⟩
    left_inv := congrFun rfl
    right_inv := congrFun rfl
  }
  rfl
