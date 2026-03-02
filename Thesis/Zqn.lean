import Mathlib
open MeasureTheory
noncomputable section

def uniform_over_Zqn (n q : ℕ) [NeZero q] : ProbabilityMeasure (Fin n → ZMod q) :=
  ⟨ProbabilityTheory.uniformOn Set.univ,
  ProbabilityTheory.uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty⟩

#check ProbabilityTheory.uniformOn_univ


-- #check int_gaussian
