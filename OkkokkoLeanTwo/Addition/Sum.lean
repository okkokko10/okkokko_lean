import OkkokkoLeanTwo.Addition.Add
import OkkokkoLeanTwo.Addition.FuncSum

universe u v v' v''

variable {X : Type u} {func : X → ℕ∞} {F : Set (Set X)} {ι : Type v} {ι' : Type v'} {series: ι → Set X} {series': ι' → Set X}

#check ENat.instWellFoundedRelation
#check WellFoundedRelation



theorem CoverDecomposes.sum_eq {al : ι → X → ℕ∞} {sl : ι → ι' → _}
  (lh : ∀i, CoverDecomposes (al i) F (sl i))
  : CoverDecomposes (func_sum al) F (fun w : ι × ι' ↦ sl w.1 w.2)
  := by sorry

theorem ComposeCover.sum_singletons {a : X → ℕ∞} {series : ι → Set X}
  : ComposeCover series = func_sum (series · |>.indicator 1)
  := by sorry


open scoped MeasureTheory
open MeasureTheory
-- instance [S : MeasurableSpace X] : Semiring <| MultiCover ℕ (MeasurableSet[S]) where

def CoverDecomposesIn.measurex [S : MeasurableSpace X] : Subsemiring (X → ℕ∞) where
  carrier := MultiCover ℕ (MeasurableSet[S])
  add_mem' {a b} ha hb := by
    apply by_equiv (?_) |>.mp
    apply add ha hb
    exact instEquivPairInfinite
  zero_mem' := zero MeasurableSet.empty
  mul_mem' {a b} ha hb := by

    sorry
  one_mem' := sorry
